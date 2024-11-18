./Benchmark/PLDI/SVComp/loop-invgen/seq-3.c
[info] Using default compilation options.
TranslationUnitDecl 0x5645cb788dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5645cb789660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5645cb789360 '__int128'
|-TypedefDecl 0x5645cb7896d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5645cb789380 'unsigned __int128'
|-TypedefDecl 0x5645cb7899d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5645cb7897b0 'struct __NSConstantString_tag'
|   `-Record 0x5645cb789728 '__NSConstantString_tag'
|-TypedefDecl 0x5645cb789a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5645cb789a30 'char *'
|   `-BuiltinType 0x5645cb788e60 'char'
|-TypedefDecl 0x5645cb789d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5645cb789d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5645cb789b50 'struct __va_list_tag'
|     `-Record 0x5645cb789ac8 '__va_list_tag'
|-FunctionDecl 0x5645cb7e8d18 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5645cb7e8db8 prev 0x5645cb7e8d18 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5645cb7e9138 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5645cb7e8e70 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x5645cb7e8ef0 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x5645cb7e8f70 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x5645cb7e8ff0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x5645cb7e91f8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x5645cb7e9578 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5645cb7e92b0 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x5645cb7e9330 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x5645cb7e93b0 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x5645cb7e9430 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x5645cb7e9638 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x5645cb7e98c8 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5645cb7e96a8 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x5645cb7e9728 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x5645cb7e97a8 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x5645cb7e9980 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x5645cb7e9a28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5645cb805328 <col:20, col:33>
|   `-ParenExpr 0x5645cb805308 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x5645cb8052e8 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x5645cb7e9bc8 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x5645cb7e9b98 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x5645cb7e9b78 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x5645cb7e9b48 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x5645cb7e9ae8 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x5645cb7e9ac8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x5645cb7e9b08 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x5645cb7e9b28 <col:32> 'int' 0
|       `-UnaryOperator 0x5645cb8052d0 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x5645cb8052b0 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x5645cb805298 <line:108:51, line:113:5>
|             `-IfStmt 0x5645cb805270 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x5645cb7e9bf0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x5645cb7e9c10 </usr/include/assert.h:110:9>
|               `-CallExpr 0x5645cb8051a0 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x5645cb805188 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x5645cb804f20 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5645cb7e9138 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x5645cb8051f8 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x5645cb8051e0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x5645cb804f78 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x5645cb805228 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x5645cb805210 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x5645cb804fd8 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x5645cb805240 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x5645cb805058 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x5645cb805258 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x5645cb805140 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x5645cb805128 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x5645cb8050f8 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x5645cb8053d8 prev 0x5645cb7e8db8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5645cb805558 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x5645cb805490 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x5645cb805700 <col:36, line:7:1>
|   `-IfStmt 0x5645cb8056e8 <line:6:3, col:22>
|     |-UnaryOperator 0x5645cb805638 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5645cb805620 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5645cb805600 <col:7> 'int' lvalue ParmVar 0x5645cb805490 'cond' 'int'
|     `-CompoundStmt 0x5645cb8056d0 <col:13, col:22>
|       `-CallExpr 0x5645cb8056b0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x5645cb805698 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5645cb805650 <col:14> 'void (void) __attribute__((noreturn))' Function 0x5645cb8053d8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5645cb8057c0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5645cb805730 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5645cb805a80 <col:34, line:13:1>
|   |-IfStmt 0x5645cb805a58 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x5645cb8058c0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5645cb8058a8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5645cb805888 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5645cb805868 <col:9> 'int' lvalue ParmVar 0x5645cb805730 'cond' 'int'
|   | `-CompoundStmt 0x5645cb805a40 <col:16, line:11:3>
|   |   `-LabelStmt 0x5645cb805a28 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5645cb8059b8 <col:12, col:35>
|   |       |-CallExpr 0x5645cb805940 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5645cb805928 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5645cb8058d8 <col:13> 'void ()' Function 0x5645cb7e9a28 'reach_error' 'void ()'
|   |       `-CallExpr 0x5645cb805998 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5645cb805980 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5645cb805960 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5645cb8053d8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5645cb805a70 <line:12:3>
|-FunctionDecl 0x5645cb805af0 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x5645cb805bb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:3:1, line:30:1> line:3:5 main 'int ()'
  `-CompoundStmt 0x5645cb806a38 <col:12, line:30:1>
    |-DeclStmt 0x5645cb805d70 <line:4:3, col:13>
    | |-VarDecl 0x5645cb805c70 <col:3, col:7> col:7 used n0 'int'
    | `-VarDecl 0x5645cb805cf0 <col:3, col:11> col:11 used n1 'int'
    |-DeclStmt 0x5645cb805e28 <line:5:3, col:13>
    | `-VarDecl 0x5645cb805da0 <col:3, col:12> col:7 used i0 'int' cinit
    |   `-IntegerLiteral 0x5645cb805e08 <col:12> 'int' 0
    |-DeclStmt 0x5645cb805ee0 <line:6:3, col:12>
    | `-VarDecl 0x5645cb805e58 <col:3, col:11> col:7 used k 'int' cinit
    |   `-IntegerLiteral 0x5645cb805ec0 <col:11> 'int' 0
    |-BinaryOperator 0x5645cb805fb0 <line:8:3, col:30> 'int' '='
    | |-DeclRefExpr 0x5645cb805ef8 <col:3> 'int' lvalue Var 0x5645cb805c70 'n0' 'int'
    | `-CallExpr 0x5645cb805f90 <col:8, col:30> 'int'
    |   `-ImplicitCastExpr 0x5645cb805f78 <col:8> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x5645cb805f30 <col:8> 'int ()' Function 0x5645cb805af0 '__VERIFIER_nondet_int' 'int ()'
    |-BinaryOperator 0x5645cb806048 <line:9:3, col:30> 'int' '='
    | |-DeclRefExpr 0x5645cb805fd0 <col:3> 'int' lvalue Var 0x5645cb805cf0 'n1' 'int'
    | `-CallExpr 0x5645cb806028 <col:8, col:30> 'int'
    |   `-ImplicitCastExpr 0x5645cb806010 <col:8> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x5645cb805ff0 <col:8> 'int ()' Function 0x5645cb805af0 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x5645cb8061f8 <line:10:3, col:53>
    | |-UnaryOperator 0x5645cb8061b0 <col:7, col:43> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5645cb806190 <col:8, col:43> 'int'
    | |   `-BinaryOperator 0x5645cb806170 <col:9, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '&&'
    | |     |-BinaryOperator 0x5645cb8060d8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:10:9, col:23> 'int' '<='
    | |     | |-UnaryOperator 0x5645cb806088 <col:9, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' prefix '-'
    | |     | | `-IntegerLiteral 0x5645cb806068 <col:19> 'int' 1000000
    | |     | `-ImplicitCastExpr 0x5645cb8060c0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:10:23> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x5645cb8060a0 <col:23> 'int' lvalue Var 0x5645cb805c70 'n0' 'int'
    | |     `-BinaryOperator 0x5645cb806150 <col:29, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '<'
    | |       |-ImplicitCastExpr 0x5645cb806138 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:10:29> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5645cb8060f8 <col:29> 'int' lvalue Var 0x5645cb805c70 'n0' 'int'
    | |       `-IntegerLiteral 0x5645cb806118 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' 1000000
    | `-ReturnStmt 0x5645cb8061e8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:10:46, col:53>
    |   `-IntegerLiteral 0x5645cb8061c8 <col:53> 'int' 0
    |-IfStmt 0x5645cb8063a0 <line:11:3, col:53>
    | |-UnaryOperator 0x5645cb806358 <col:7, col:43> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5645cb806338 <col:8, col:43> 'int'
    | |   `-BinaryOperator 0x5645cb806318 <col:9, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '&&'
    | |     |-BinaryOperator 0x5645cb806280 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:11:9, col:23> 'int' '<='
    | |     | |-UnaryOperator 0x5645cb806230 <col:9, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' prefix '-'
    | |     | | `-IntegerLiteral 0x5645cb806210 <col:19> 'int' 1000000
    | |     | `-ImplicitCastExpr 0x5645cb806268 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:11:23> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x5645cb806248 <col:23> 'int' lvalue Var 0x5645cb805cf0 'n1' 'int'
    | |     `-BinaryOperator 0x5645cb8062f8 <col:29, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '<'
    | |       |-ImplicitCastExpr 0x5645cb8062e0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:11:29> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5645cb8062a0 <col:29> 'int' lvalue Var 0x5645cb805cf0 'n1' 'int'
    | |       `-IntegerLiteral 0x5645cb8062c0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' 1000000
    | `-ReturnStmt 0x5645cb806390 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/seq-3.c:11:46, col:53>
    |   `-IntegerLiteral 0x5645cb806370 <col:53> 'int' 0
    |-WhileStmt 0x5645cb8064d8 <line:13:3, line:16:3>
    | |-BinaryOperator 0x5645cb806428 <line:13:10, col:15> 'int' '<'
    | | |-ImplicitCastExpr 0x5645cb8063f8 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5645cb8063b8 <col:10> 'int' lvalue Var 0x5645cb805da0 'i0' 'int'
    | | `-ImplicitCastExpr 0x5645cb806410 <col:15> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x5645cb8063d8 <col:15> 'int' lvalue Var 0x5645cb805c70 'n0' 'int'
    | `-CompoundStmt 0x5645cb8064b8 <col:20, line:16:3>
    |   |-UnaryOperator 0x5645cb806468 <line:14:5, col:7> 'int' postfix '++'
    |   | `-DeclRefExpr 0x5645cb806448 <col:5> 'int' lvalue Var 0x5645cb805da0 'i0' 'int'
    |   `-UnaryOperator 0x5645cb8064a0 <line:15:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x5645cb806480 <col:5> 'int' lvalue Var 0x5645cb805e58 'k' 'int'
    |-DeclStmt 0x5645cb806590 <line:18:3, col:13>
    | `-VarDecl 0x5645cb806508 <col:3, col:12> col:7 used i1 'int' cinit
    |   `-IntegerLiteral 0x5645cb806570 <col:12> 'int' 0
    |-WhileStmt 0x5645cb8066c8 <line:19:3, line:22:3>
    | |-BinaryOperator 0x5645cb806618 <line:19:10, col:15> 'int' '<'
    | | |-ImplicitCastExpr 0x5645cb8065e8 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5645cb8065a8 <col:10> 'int' lvalue Var 0x5645cb806508 'i1' 'int'
    | | `-ImplicitCastExpr 0x5645cb806600 <col:15> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x5645cb8065c8 <col:15> 'int' lvalue Var 0x5645cb805cf0 'n1' 'int'
    | `-CompoundStmt 0x5645cb8066a8 <col:20, line:22:3>
    |   |-UnaryOperator 0x5645cb806658 <line:20:5, col:7> 'int' postfix '++'
    |   | `-DeclRefExpr 0x5645cb806638 <col:5> 'int' lvalue Var 0x5645cb806508 'i1' 'int'
    |   `-UnaryOperator 0x5645cb806690 <line:21:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x5645cb806670 <col:5> 'int' lvalue Var 0x5645cb805e58 'k' 'int'
    |-DeclStmt 0x5645cb806780 <line:24:3, col:13>
    | `-VarDecl 0x5645cb8066f8 <col:3, col:12> col:7 used j1 'int' cinit
    |   `-IntegerLiteral 0x5645cb806760 <col:12> 'int' 0
    `-WhileStmt 0x5645cb806a20 <line:25:3, line:29:3>
      |-BinaryOperator 0x5645cb806860 <line:25:10, col:20> 'int' '<'
      | |-ImplicitCastExpr 0x5645cb806848 <col:10> 'int' <LValueToRValue>
      | | `-DeclRefExpr 0x5645cb806798 <col:10> 'int' lvalue Var 0x5645cb8066f8 'j1' 'int'
      | `-BinaryOperator 0x5645cb806828 <col:15, col:20> 'int' '+'
      |   |-ImplicitCastExpr 0x5645cb8067f8 <col:15> 'int' <LValueToRValue>
      |   | `-DeclRefExpr 0x5645cb8067b8 <col:15> 'int' lvalue Var 0x5645cb805c70 'n0' 'int'
      |   `-ImplicitCastExpr 0x5645cb806810 <col:20> 'int' <LValueToRValue>
      |     `-DeclRefExpr 0x5645cb8067d8 <col:20> 'int' lvalue Var 0x5645cb805cf0 'n1' 'int'
      `-CompoundStmt 0x5645cb8069f8 <col:25, line:29:3>
        |-CallExpr 0x5645cb806960 <line:26:7, col:30> 'void'
        | |-ImplicitCastExpr 0x5645cb806948 <col:7> 'void (*)(int)' <FunctionToPointerDecay>
        | | `-DeclRefExpr 0x5645cb806880 <col:7> 'void (int)' Function 0x5645cb8057c0 '__VERIFIER_assert' 'void (int)'
        | `-BinaryOperator 0x5645cb8068f8 <col:25, col:29> 'int' '>'
        |   |-ImplicitCastExpr 0x5645cb8068e0 <col:25> 'int' <LValueToRValue>
        |   | `-DeclRefExpr 0x5645cb8068a0 <col:25> 'int' lvalue Var 0x5645cb805e58 'k' 'int'
        |   `-IntegerLiteral 0x5645cb8068c0 <col:29> 'int' 0
        |-UnaryOperator 0x5645cb8069a8 <line:27:7, col:9> 'int' postfix '++'
        | `-DeclRefExpr 0x5645cb806988 <col:7> 'int' lvalue Var 0x5645cb8066f8 'j1' 'int'
        `-UnaryOperator 0x5645cb8069e0 <line:28:7, col:8> 'int' postfix '--'
          `-DeclRefExpr 0x5645cb8069c0 <col:7> 'int' lvalue Var 0x5645cb805e58 'k' 'int'
