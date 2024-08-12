+++
title = 'LLVM Note(1)'
date = 2024-08-05T23:24:18+08:00
draft = false
+++
## 自定义Pass

### 1. 何为Pass
在编写pass之前，有必要搞清楚LLVM是如何管理pass的。Pass实际上是一个接口，其功能是便利IR并且执行相关的操作，比如`Analyze`或者`Transform`。要编写一个Pass，具体来说可以分为如下几步:

1. 编写自己的Pass类，并且完成相关操作。
2. 将自定义的Pass注册到LLVM并且编译成静态库。
3. 使用`opt`加载和使用Pass。

在2021年以前，也就是LLVM5-12版本，LLVM使用`Legacy Passmanager`来管理Pass，在LLVM13版本，LLVM推出了新一代PassManager，下面将分别介绍两个Passmanger。

#### 1.1 Legacy Passmanager
传统的PassManager定义了7种Pass：
1. `ImmutablePass`: 用于不必运行、不更改状态且永远不需要更新的pass
2. `ModulePass`: 表示将整个程序作为一个单元，以不可预测的顺序引用函数体，或者添加和删除函数。
3. `CallGraphSCCPass`: 用于需要在调用图上自下而上遍历程序的传递
4. `FunctionPass`: 与 ModulePass 子类相比，FunctionPass 子类具有系统可以预期的可预测的本地行为
5. `LoopPass`: 所有 LoopPass 都在函数中的每个循环上执行，独立于函数中的所有其他循环。
6. `RegionPass`: 类似于 LoopPass，但在函数中的每个单一入口单一出口区域上执行。
7. `MachineFunctionPass`: MachineFunctionPass 是 LLVM 代码生成器的一部分，它在程序中每个 LLVM 函数的机器依赖表示上执行。

下面将使用一个`FunctionPass`举例，直接上代码:
```cpp
// StaticAnalysisPass.cpp from cis547/lab2, University of Pennsylvania
#include "Instrument.h"
#include "Utils.h"
using namespace llvm;

namespace instrument {
    class Instrument: public FunctionPass{}; // 这里只是为了表现继承关系

const auto PASS_NAME = "MyPass";
const auto PASS_DESC = "Static Analysis Pass";

bool Instrument::runOnFunction(Function &F) {
  auto FunctionName = F.getName().str();
  outs() << "Running " << PASS_DESC << " on function " << FunctionName << "\n";

  outs() << "Locating Instructions\n";
  for (inst_iterator Iter = inst_begin(F), E = inst_end(F); Iter != E; ++Iter) {
    Instruction &Inst = (*Iter);
    llvm::DebugLoc DebugLoc = Inst.getDebugLoc();
    if (!DebugLoc) {
      // Skip Instruction if it doesn't have debug information.
      continue;
    }

    int Line = DebugLoc.getLine();
    int Col = DebugLoc.getCol();
    outs() << Line << ", " << Col << "\n";
    if (Inst.isBinaryOp()) {
        outs << Inst.getOperand(0);
        outs << Inst.getOperand(1) << "\n";
    }
  }
  return false;
}

char Instrument::ID = 1;
static RegisterPass<Instrument> X(PASS_NAME, PASS_NAME, false, false);

} // namespace instrument
```
在这个例子中，新建了一个子类，继承了`FunctionPass`并且实现了`runOnFunction`方法，在该方法中对每一个指令进行了一些操作，同时每一个Pass还有独特的ID，如果使用Plugin的形式使用Pass的话，这个值应该是可以随便写的。在程序最后，使用`RegisterPass`进行注册，该类需要几个参数，分别是`Pass Arg`, `Pass Name`, `CFGOnly`和`is_analysis`。第二个参数是命令行加载时要填入的名称，后两个参数根据pass的操作进行判断填写即可。

在编写完成后，可以使用[模板](新建项目)进行编译。编译完成后，使用`opt`命令进行加载和使用，首先准备一个测试文件`test.c`，内容如下：
```c
int main() {
  int x = 3;
  int y = 2;
  int z = x / y;
  return 0;
}

```
然后使用clang将其转为IR文件
```sh
clang -emit-llvm -S -fno-discard-value-names -c -o test.ll test.c -g
```
得到`test.ll`文件后，使用`opt`进行静态分析
```sh
> opt -load ./build/MyPass.so -MyPass -S test.ll -o test.static.ll
Running Static Analysis Pass on function main
Locating Instructions
2, 7
2, 7
3, 7
3, 7
4, 7
4, 11
4, 15
4, 13
Division on Line 4, Column 13 with first operand %0 and second operand %1
4, 7
5, 3
```
由输出结果可以看到，我们编写的pass成功的检测到了二元运算符并且打印出了相关的信息。

#### 1.2 New Passmanager
LLVM13后引入了新的Passmanager，代码中继承的基类和要重写的方法也发生了改变。还是以上面的例子，直接上代码！
```cpp
namespace llvm {
class MyPass: public PassInfoMixin<MyPass> {
    public:
    PreservedAnalyses run(Function &f, FunctionAnalysisManager &FAM);

    static int num = 0;
    PreservedAnalyses MyPass::run(Function &F, FunctionAnalysisManager& FAM) {
        for (auto inst = inst_begin(F), end = inst_end(F);inst != end;inst++) {
            Instruction &Inst = (*Iter);
            llvm::DebugLoc DebugLoc = Inst.getDebugLoc();
            if (!DebugLoc) {
            // Skip Instruction if it doesn't have debug information.
            continue;
            }

            int Line = DebugLoc.getLine();
            int Col = DebugLoc.getCol();
            outs() << Line << ", " << Col << "\n";
            if (Inst.isBinaryOp()) {
                outs << Inst.getOperand(0);
                outs << Inst.getOperand(1) << "\n";
            }
        }
        return PreservedAnalyses::all();
    }

    extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
    llvmGetPassPluginInfo() {
        return {
            LLVM_PLUGIN_API_VERSION, 
            "MyPass", 
            "v0.1",
            [](llvm::PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](llvm::StringRef Name, llvm::FunctionPassManager &FPM,
                llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                  if(Name == "MyPass"){
                    FPM.addPass(llvm::MyPass());
                    return true;
                  }
                  return false;
                }
            );
            }
        };
    }
}
```
可以看到与`Legacy Passmanager`不同的有几点：
1. 继承的基类变成了`PassInfoMixin<>`
2. 重写的方法变成了`run`
3. 注册Pass的方法变成了编写函数

还是使用上面的代码来进行测试，但是要注意这里在生成IR时要添加参数
```sh
clang -emit-llvm -S -fno-discard-value-names -Xclang -disable-optnone -c -o test.ll test.c -g
```
得到IR后，使用`opt`进行，这里也需要修改一下参数
```sh
> opt -load-pass-plugin=./build/MyPass.so -passes="MyPass" -S test.ll -o test.static.ll
Running Static Analysis Pass on function main
Locating Instructions
2, 7
2, 7
3, 7
3, 7
4, 7
4, 11
4, 15
4, 13
Division on Line 4, Column 13 with first operand %0 and second operand %1
4, 7
5, 3
```

### 2. 项目模板
LLVM支持CMake，所以选择使用CMake进行开发，同时在根目录文件夹下新建一个`src`目录用于存放Pass的源码，如果进行动态插桩，比如进行覆盖率收集等，可以新建一个目录`lib`用于存放外部函数。整体目录结构如下所示:
```
.
│
├── CMakeLists.txt
├── lib
│   └── runtime.c
├── src
    ├── MyPass.cpp
    └── MyPass.h 

```
使用的CMakeList也很简单，如下所示
```
cmake_minimum_required(VERSION 3.25.0)

project(MyPass)

set(CMKAE_CXX_STANDARD 14)
find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM in ${LLVM_PATH}")

include(AddLLVM)
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

# 如果想要增加pass，使用add_llvm_pass_plugin即可
add_llvm_pass_plugin(MyPass src/MyPass.cpp)

# 这是为了将runtime编译成共享库
add_library(runtime SHARED lib/runtime.c)
```
