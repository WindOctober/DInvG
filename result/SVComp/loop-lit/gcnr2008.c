./Benchmark/PLDI/SVComp/loop-lit/gcnr2008.c
[info] Using default compilation options.
TranslationUnitDecl 0x564a6c10ddc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x564a6c10e660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x564a6c10e360 '__int128'
|-TypedefDecl 0x564a6c10e6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x564a6c10e380 'unsigned __int128'
|-TypedefDecl 0x564a6c10e9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x564a6c10e7b0 'struct __NSConstantString_tag'
|   `-Record 0x564a6c10e728 '__NSConstantString_tag'
|-TypedefDecl 0x564a6c10ea70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x564a6c10ea30 'char *'
|   `-BuiltinType 0x564a6c10de60 'char'
|-TypedefDecl 0x564a6c10ed68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x564a6c10ed10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x564a6c10eb50 'struct __va_list_tag'
|     `-Record 0x564a6c10eac8 '__va_list_tag'
|-FunctionDecl 0x564a6c16dd88 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564a6c16de28 prev 0x564a6c16dd88 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564a6c16e1a8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564a6c16dee0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x564a6c16df60 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x564a6c16dfe0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x564a6c16e060 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x564a6c16e268 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564a6c16e5e8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564a6c16e320 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x564a6c16e3a0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x564a6c16e420 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x564a6c16e4a0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x564a6c16e6a8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564a6c16e938 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564a6c16e718 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x564a6c16e798 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x564a6c16e818 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x564a6c16e9f0 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564a6c16ea98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x564a6c18a398 <col:20, col:33>
|   `-ParenExpr 0x564a6c18a378 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x564a6c18a358 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x564a6c16ec38 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x564a6c16ec08 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x564a6c16ebe8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x564a6c16ebb8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x564a6c16eb58 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x564a6c16eb38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x564a6c16eb78 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x564a6c16eb98 <col:32> 'int' 0
|       `-UnaryOperator 0x564a6c18a340 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x564a6c18a320 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x564a6c18a308 <line:108:51, line:113:5>
|             `-IfStmt 0x564a6c18a2e0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x564a6c16ec60 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x564a6c16ec80 </usr/include/assert.h:110:9>
|               `-CallExpr 0x564a6c18a210 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x564a6c18a1f8 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x564a6c189f90 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x564a6c16e1a8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x564a6c18a268 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x564a6c18a250 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x564a6c189fe8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x564a6c18a298 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x564a6c18a280 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x564a6c18a048 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x564a6c18a2b0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x564a6c18a0c8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x564a6c18a2c8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x564a6c18a1b0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x564a6c18a198 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x564a6c18a168 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x564a6c18a448 prev 0x564a6c16de28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564a6c18a5c8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x564a6c18a500 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x564a6c18a770 <col:36, line:7:1>
|   `-IfStmt 0x564a6c18a758 <line:6:3, col:22>
|     |-UnaryOperator 0x564a6c18a6a8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x564a6c18a690 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x564a6c18a670 <col:7> 'int' lvalue ParmVar 0x564a6c18a500 'cond' 'int'
|     `-CompoundStmt 0x564a6c18a740 <col:13, col:22>
|       `-CallExpr 0x564a6c18a720 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x564a6c18a708 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x564a6c18a6c0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x564a6c18a448 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x564a6c18a830 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x564a6c18a7a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x564a6c18aaf0 <col:34, line:13:1>
|   |-IfStmt 0x564a6c18aac8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x564a6c18a930 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x564a6c18a918 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x564a6c18a8f8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x564a6c18a8d8 <col:9> 'int' lvalue ParmVar 0x564a6c18a7a0 'cond' 'int'
|   | `-CompoundStmt 0x564a6c18aab0 <col:16, line:11:3>
|   |   `-LabelStmt 0x564a6c18aa98 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x564a6c18aa28 <col:14, col:37>
|   |       |-CallExpr 0x564a6c18a9b0 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x564a6c18a998 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x564a6c18a948 <col:15> 'void ()' Function 0x564a6c16ea98 'reach_error' 'void ()'
|   |       `-CallExpr 0x564a6c18aa08 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x564a6c18a9f0 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x564a6c18a9d0 <col:29> 'void (void) __attribute__((noreturn))' Function 0x564a6c18a448 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x564a6c18aae0 <line:12:3>
|-FunctionDecl 0x564a6c18ab60 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x564a6c18ac28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gcnr2008.c:6:1, line:26:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x564a6c18bc18 <col:12, line:26:1>
    |-DeclStmt 0x564a6c18aef0 <line:7:5, col:16>
    | |-VarDecl 0x564a6c18ace0 <col:5, col:9> col:9 used x 'int'
    | |-VarDecl 0x564a6c18ad60 <col:5, col:11> col:11 used y 'int'
    | |-VarDecl 0x564a6c18ade0 <col:5, col:13> col:13 used z 'int'
    | `-VarDecl 0x564a6c18ae60 <col:5, col:15> col:15 used w 'int'
    |-BinaryOperator 0x564a6c18b020 <line:8:5, col:21> 'int' '='
    | |-DeclRefExpr 0x564a6c18af08 <col:5> 'int' lvalue Var 0x564a6c18ace0 'x' 'int'
    | `-BinaryOperator 0x564a6c18b000 <col:9, col:21> 'int' '='
    |   |-DeclRefExpr 0x564a6c18af28 <col:9> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |   `-BinaryOperator 0x564a6c18afe0 <col:13, col:21> 'int' '='
    |     |-DeclRefExpr 0x564a6c18af48 <col:13> 'int' lvalue Var 0x564a6c18ade0 'z' 'int'
    |     `-BinaryOperator 0x564a6c18afc0 <col:17, col:21> 'int' '='
    |       |-DeclRefExpr 0x564a6c18af68 <col:17> 'int' lvalue Var 0x564a6c18ae60 'w' 'int'
    |       `-IntegerLiteral 0x564a6c18afa0 <col:21> 'int' 0
    |-WhileStmt 0x564a6c18ba38 <line:9:5, line:23:5>
    | |-BinaryOperator 0x564a6c18b138 <line:9:12, col:43> 'int' '&&'
    | | |-CallExpr 0x564a6c18b0a0 <col:12, col:34> 'int'
    | | | `-ImplicitCastExpr 0x564a6c18b088 <col:12> 'int (*)()' <FunctionToPointerDecay>
    | | |   `-DeclRefExpr 0x564a6c18b040 <col:12> 'int ()' Function 0x564a6c18ab60 '__VERIFIER_nondet_int' 'int ()'
    | | `-BinaryOperator 0x564a6c18b118 <col:39, col:43> 'int' '<'
    | |   |-ImplicitCastExpr 0x564a6c18b100 <col:39> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x564a6c18b0c0 <col:39> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    | |   `-IntegerLiteral 0x564a6c18b0e0 <col:43> 'int' 10000
    | `-CompoundStmt 0x564a6c18ba10 <col:50, line:23:5>
    |   |-IfStmt 0x564a6c18b878 <line:10:2, line:20:2> has_else
    |   | |-CallExpr 0x564a6c18b190 <line:10:6, col:28> 'int'
    |   | | `-ImplicitCastExpr 0x564a6c18b178 <col:6> 'int (*)()' <FunctionToPointerDecay>
    |   | |   `-DeclRefExpr 0x564a6c18b158 <col:6> 'int ()' Function 0x564a6c18ab60 '__VERIFIER_nondet_int' 'int ()'
    |   | |-CompoundStmt 0x564a6c18b320 <col:31, line:13:2>
    |   | | |-BinaryOperator 0x564a6c18b248 <line:11:6, col:14> 'int' '='
    |   | | | |-DeclRefExpr 0x564a6c18b1b0 <col:6> 'int' lvalue Var 0x564a6c18ace0 'x' 'int'
    |   | | | `-BinaryOperator 0x564a6c18b228 <col:10, col:14> 'int' '+'
    |   | | |   |-ImplicitCastExpr 0x564a6c18b210 <col:10> 'int' <LValueToRValue>
    |   | | |   | `-DeclRefExpr 0x564a6c18b1d0 <col:10> 'int' lvalue Var 0x564a6c18ace0 'x' 'int'
    |   | | |   `-IntegerLiteral 0x564a6c18b1f0 <col:14> 'int' 1
    |   | | `-BinaryOperator 0x564a6c18b300 <line:12:6, col:14> 'int' '='
    |   | |   |-DeclRefExpr 0x564a6c18b268 <col:6> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |   | |   `-BinaryOperator 0x564a6c18b2e0 <col:10, col:14> 'int' '+'
    |   | |     |-ImplicitCastExpr 0x564a6c18b2c8 <col:10> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x564a6c18b288 <col:10> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |   | |     `-IntegerLiteral 0x564a6c18b2a8 <col:14> 'int' 100
    |   | `-IfStmt 0x564a6c18b850 <line:13:9, line:20:2> has_else
    |   |   |-CallExpr 0x564a6c18b378 <line:13:13, col:35> 'int'
    |   |   | `-ImplicitCastExpr 0x564a6c18b360 <col:13> 'int (*)()' <FunctionToPointerDecay>
    |   |   |   `-DeclRefExpr 0x564a6c18b340 <col:13> 'int ()' Function 0x564a6c18ab60 '__VERIFIER_nondet_int' 'int ()'
    |   |   |-CompoundStmt 0x564a6c18b5b8 <col:38, line:18:2>
    |   |   | `-IfStmt 0x564a6c18b5a0 <line:14:6, line:17:6>
    |   |   |   |-BinaryOperator 0x564a6c18b3f0 <line:14:10, col:15> 'int' '>='
    |   |   |   | |-ImplicitCastExpr 0x564a6c18b3d8 <col:10> 'int' <LValueToRValue>
    |   |   |   | | `-DeclRefExpr 0x564a6c18b398 <col:10> 'int' lvalue Var 0x564a6c18ace0 'x' 'int'
    |   |   |   | `-IntegerLiteral 0x564a6c18b3b8 <col:15> 'int' 4
    |   |   |   `-CompoundStmt 0x564a6c18b580 <col:18, line:17:6>
    |   |   |     |-BinaryOperator 0x564a6c18b4a8 <line:15:3, col:11> 'int' '='
    |   |   |     | |-DeclRefExpr 0x564a6c18b410 <col:3> 'int' lvalue Var 0x564a6c18ace0 'x' 'int'
    |   |   |     | `-BinaryOperator 0x564a6c18b488 <col:7, col:11> 'int' '+'
    |   |   |     |   |-ImplicitCastExpr 0x564a6c18b470 <col:7> 'int' <LValueToRValue>
    |   |   |     |   | `-DeclRefExpr 0x564a6c18b430 <col:7> 'int' lvalue Var 0x564a6c18ace0 'x' 'int'
    |   |   |     |   `-IntegerLiteral 0x564a6c18b450 <col:11> 'int' 1
    |   |   |     `-BinaryOperator 0x564a6c18b560 <line:16:3, col:11> 'int' '='
    |   |   |       |-DeclRefExpr 0x564a6c18b4c8 <col:3> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |   |   |       `-BinaryOperator 0x564a6c18b540 <col:7, col:11> 'int' '+'
    |   |   |         |-ImplicitCastExpr 0x564a6c18b528 <col:7> 'int' <LValueToRValue>
    |   |   |         | `-DeclRefExpr 0x564a6c18b4e8 <col:7> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |   |   |         `-IntegerLiteral 0x564a6c18b508 <col:11> 'int' 1
    |   |   `-IfStmt 0x564a6c18b838 <line:18:9, line:20:2>
    |   |     |-BinaryOperator 0x564a6c18b770 <line:18:13, col:34> 'int' '&&'
    |   |     | |-BinaryOperator 0x564a6c18b680 <col:13, col:20> 'int' '>'
    |   |     | | |-ImplicitCastExpr 0x564a6c18b668 <col:13> 'int' <LValueToRValue>
    |   |     | | | `-DeclRefExpr 0x564a6c18b5d0 <col:13> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |   |     | | `-BinaryOperator 0x564a6c18b648 <col:17, col:20> 'int' '*'
    |   |     | |   |-IntegerLiteral 0x564a6c18b5f0 <col:17> 'int' 10
    |   |     | |   `-ImplicitCastExpr 0x564a6c18b630 <col:20> 'int' <LValueToRValue>
    |   |     | |     `-DeclRefExpr 0x564a6c18b610 <col:20> 'int' lvalue Var 0x564a6c18ae60 'w' 'int'
    |   |     | `-BinaryOperator 0x564a6c18b750 <col:25, col:34> 'int' '>='
    |   |     |   |-ImplicitCastExpr 0x564a6c18b738 <col:25> 'int' <LValueToRValue>
    |   |     |   | `-DeclRefExpr 0x564a6c18b6a0 <col:25> 'int' lvalue Var 0x564a6c18ade0 'z' 'int'
    |   |     |   `-BinaryOperator 0x564a6c18b718 <col:30, col:34> 'int' '*'
    |   |     |     |-IntegerLiteral 0x564a6c18b6c0 <col:30> 'int' 100
    |   |     |     `-ImplicitCastExpr 0x564a6c18b700 <col:34> 'int' <LValueToRValue>
    |   |     |       `-DeclRefExpr 0x564a6c18b6e0 <col:34> 'int' lvalue Var 0x564a6c18ace0 'x' 'int'
    |   |     `-CompoundStmt 0x564a6c18b820 <col:37, line:20:2>
    |   |       `-BinaryOperator 0x564a6c18b800 <line:19:6, col:11> 'int' '='
    |   |         |-DeclRefExpr 0x564a6c18b790 <col:6> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |   |         `-UnaryOperator 0x564a6c18b7e8 <col:10, col:11> 'int' prefix '-'
    |   |           `-ImplicitCastExpr 0x564a6c18b7d0 <col:11> 'int' <LValueToRValue>
    |   |             `-DeclRefExpr 0x564a6c18b7b0 <col:11> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |   |-BinaryOperator 0x564a6c18b938 <line:21:2, col:10> 'int' '='
    |   | |-DeclRefExpr 0x564a6c18b8a0 <col:2> 'int' lvalue Var 0x564a6c18ae60 'w' 'int'
    |   | `-BinaryOperator 0x564a6c18b918 <col:6, col:10> 'int' '+'
    |   |   |-ImplicitCastExpr 0x564a6c18b900 <col:6> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x564a6c18b8c0 <col:6> 'int' lvalue Var 0x564a6c18ae60 'w' 'int'
    |   |   `-IntegerLiteral 0x564a6c18b8e0 <col:10> 'int' 1
    |   `-BinaryOperator 0x564a6c18b9f0 <line:22:2, col:10> 'int' '='
    |     |-DeclRefExpr 0x564a6c18b958 <col:2> 'int' lvalue Var 0x564a6c18ade0 'z' 'int'
    |     `-BinaryOperator 0x564a6c18b9d0 <col:6, col:10> 'int' '+'
    |       |-ImplicitCastExpr 0x564a6c18b9b8 <col:6> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x564a6c18b978 <col:6> 'int' lvalue Var 0x564a6c18ade0 'z' 'int'
    |       `-IntegerLiteral 0x564a6c18b998 <col:10> 'int' 10
    |-CallExpr 0x564a6c18bbc0 <line:24:5, col:39> 'void'
    | |-ImplicitCastExpr 0x564a6c18bba8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x564a6c18ba50 <col:5> 'void (int)' Function 0x564a6c18a830 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x564a6c18bb60 <col:23, col:38> 'int' '&&'
    |   |-BinaryOperator 0x564a6c18bac8 <col:23, col:28> 'int' '>='
    |   | |-ImplicitCastExpr 0x564a6c18bab0 <col:23> 'int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x564a6c18ba70 <col:23> 'int' lvalue Var 0x564a6c18ace0 'x' 'int'
    |   | `-IntegerLiteral 0x564a6c18ba90 <col:28> 'int' 4
    |   `-BinaryOperator 0x564a6c18bb40 <col:33, col:38> 'int' '<='
    |     |-ImplicitCastExpr 0x564a6c18bb28 <col:33> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x564a6c18bae8 <col:33> 'int' lvalue Var 0x564a6c18ad60 'y' 'int'
    |     `-IntegerLiteral 0x564a6c18bb08 <col:38> 'int' 2
    `-ReturnStmt 0x564a6c18bc08 <line:25:5, col:12>
      `-IntegerLiteral 0x564a6c18bbe8 <col:12> 'int' 0
