./Benchmark/PLDI/SVComp/loop-invgen/fragtest_simple.c
[info] Using default compilation options.
TranslationUnitDecl 0x55574e2f4ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55574e2f5780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55574e2f5480 '__int128'
|-TypedefDecl 0x55574e2f57f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55574e2f54a0 'unsigned __int128'
|-TypedefDecl 0x55574e2f5af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55574e2f58d0 'struct __NSConstantString_tag'
|   `-Record 0x55574e2f5848 '__NSConstantString_tag'
|-TypedefDecl 0x55574e2f5b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55574e2f5b50 'char *'
|   `-BuiltinType 0x55574e2f4f80 'char'
|-TypedefDecl 0x55574e2f5e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55574e2f5e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55574e2f5c70 'struct __va_list_tag'
|     `-Record 0x55574e2f5be8 '__va_list_tag'
|-FunctionDecl 0x55574e354ea8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55574e354f48 prev 0x55574e354ea8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55574e3552c8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55574e355000 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x55574e355080 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x55574e355100 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55574e355180 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55574e355388 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55574e355708 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55574e355440 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x55574e3554c0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x55574e355540 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55574e3555c0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55574e3557c8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55574e355a58 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55574e355838 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x55574e3558b8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x55574e355938 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x55574e355b10 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55574e355bb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55574e371408 <col:20, col:33>
|   `-ParenExpr 0x55574e3713e8 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x55574e3713c8 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x55574e355d58 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x55574e355d28 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x55574e355d08 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x55574e355cd8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x55574e355c78 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x55574e355c58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x55574e355c98 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x55574e355cb8 <col:32> 'int' 0
|       `-UnaryOperator 0x55574e3713b0 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x55574e371390 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x55574e371378 <line:108:51, line:113:5>
|             `-IfStmt 0x55574e371350 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x55574e355d80 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x55574e355da0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x55574e371280 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x55574e371268 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x55574e371000 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55574e3552c8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x55574e3712d8 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55574e3712c0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55574e371058 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x55574e371308 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55574e3712f0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55574e3710b8 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x55574e371320 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x55574e371138 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x55574e371338 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x55574e371220 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x55574e371208 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x55574e3711d8 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x55574e3714b8 prev 0x55574e354f48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55574e371638 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55574e371570 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55574e3717e0 <col:36, line:7:1>
|   `-IfStmt 0x55574e3717c8 <line:6:3, col:22>
|     |-UnaryOperator 0x55574e371718 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55574e371700 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55574e3716e0 <col:7> 'int' lvalue ParmVar 0x55574e371570 'cond' 'int'
|     `-CompoundStmt 0x55574e3717b0 <col:13, col:22>
|       `-CallExpr 0x55574e371790 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55574e371778 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55574e371730 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55574e3714b8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55574e3718a0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55574e371810 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55574e371b60 <col:34, line:13:1>
|   |-IfStmt 0x55574e371b38 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x55574e3719a0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55574e371988 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55574e371968 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55574e371948 <col:9> 'int' lvalue ParmVar 0x55574e371810 'cond' 'int'
|   | `-CompoundStmt 0x55574e371b20 <col:16, line:11:3>
|   |   `-LabelStmt 0x55574e371b08 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55574e371a98 <col:12, col:35>
|   |       |-CallExpr 0x55574e371a20 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55574e371a08 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55574e3719b8 <col:13> 'void ()' Function 0x55574e355bb8 'reach_error' 'void ()'
|   |       `-CallExpr 0x55574e371a78 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55574e371a60 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55574e371a40 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55574e3714b8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55574e371b50 <line:12:3>
|-FunctionDecl 0x55574e371bd0 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x55574e371c98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/fragtest_simple.c:3:1, line:43:1> line:3:5 main 'int ()'
  `-CompoundStmt 0x55574e372df8 <col:11, line:43:1>
    |-DeclStmt 0x55574e371e50 <line:4:3, col:15>
    | |-VarDecl 0x55574e371d50 <col:3, col:7> col:7 used i 'int'
    | `-VarDecl 0x55574e371dd0 <col:3, col:9> col:9 used pvlen 'int'
    |-DeclStmt 0x55574e371ee8 <line:5:3, col:15>
    | `-VarDecl 0x55574e371e80 <col:3, col:7> col:7 used tmp___1 'int'
    |-DeclStmt 0x55574e371fa0 <line:6:3, col:12>
    | `-VarDecl 0x55574e371f18 <col:3, col:11> col:7 used k 'int' cinit
    |   `-IntegerLiteral 0x55574e371f80 <col:11> 'int' 0
    |-DeclStmt 0x55574e372078 <line:7:3, col:8>
    | `-VarDecl 0x55574e372010 <col:3, col:7> col:7 used n 'int'
    |-BinaryOperator 0x55574e3720d0 <line:9:3, col:7> 'int' '='
    | |-DeclRefExpr 0x55574e372090 <col:3> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    | `-IntegerLiteral 0x55574e3720b0 <col:7> 'int' 0
    |-BinaryOperator 0x55574e372190 <line:10:3, col:33> 'int' '='
    | |-DeclRefExpr 0x55574e3720f0 <col:3> 'int' lvalue Var 0x55574e371dd0 'pvlen' 'int'
    | `-CallExpr 0x55574e372170 <col:11, col:33> 'int'
    |   `-ImplicitCastExpr 0x55574e372158 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55574e372110 <col:11> 'int ()' Function 0x55574e371bd0 '__VERIFIER_nondet_int' 'int ()'
    |-WhileStmt 0x55574e372370 <line:13:3, line:15:3>
    | |-BinaryOperator 0x55574e372280 <line:13:11, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '&&'
    | | |-CallExpr 0x55574e3721e8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/fragtest_simple.c:13:11, col:33> 'int'
    | | | `-ImplicitCastExpr 0x55574e3721d0 <col:11> 'int (*)()' <FunctionToPointerDecay>
    | | |   `-DeclRefExpr 0x55574e3721b0 <col:11> 'int ()' Function 0x55574e371bd0 '__VERIFIER_nondet_int' 'int ()'
    | | `-BinaryOperator 0x55574e372260 <col:38, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '<='
    | |   |-ImplicitCastExpr 0x55574e372248 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/fragtest_simple.c:13:38> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x55574e372208 <col:38> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    | |   `-IntegerLiteral 0x55574e372228 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' 1000000
    | `-CompoundStmt 0x55574e372358 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/fragtest_simple.c:13:54, line:15:3>
    |   `-BinaryOperator 0x55574e372338 <line:14:5, col:13> 'int' '='
    |     |-DeclRefExpr 0x55574e3722a0 <col:5> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |     `-BinaryOperator 0x55574e372318 <col:9, col:13> 'int' '+'
    |       |-ImplicitCastExpr 0x55574e372300 <col:9> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55574e3722c0 <col:9> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |       `-IntegerLiteral 0x55574e3722e0 <col:13> 'int' 1
    |-IfStmt 0x55574e3724a8 <line:18:3, line:20:3>
    | |-BinaryOperator 0x55574e3723f8 <line:18:7, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55574e3723c8 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55574e372388 <col:7> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    | | `-ImplicitCastExpr 0x55574e3723e0 <col:11> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55574e3723a8 <col:11> 'int' lvalue Var 0x55574e371dd0 'pvlen' 'int'
    | `-CompoundStmt 0x55574e372490 <col:18, line:20:3>
    |   `-BinaryOperator 0x55574e372470 <line:19:5, col:13> 'int' '='
    |     |-DeclRefExpr 0x55574e372418 <col:5> 'int' lvalue Var 0x55574e371dd0 'pvlen' 'int'
    |     `-ImplicitCastExpr 0x55574e372458 <col:13> 'int' <LValueToRValue>
    |       `-DeclRefExpr 0x55574e372438 <col:13> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |-BinaryOperator 0x55574e372500 <line:21:3, col:7> 'int' '='
    | |-DeclRefExpr 0x55574e3724c0 <col:3> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    | `-IntegerLiteral 0x55574e3724e0 <col:7> 'int' 0
    |-WhileStmt 0x55574e372820 <line:23:3, line:27:3>
    | |-BinaryOperator 0x55574e3725f0 <line:23:11, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '&&'
    | | |-CallExpr 0x55574e372558 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/fragtest_simple.c:23:11, col:33> 'int'
    | | | `-ImplicitCastExpr 0x55574e372540 <col:11> 'int (*)()' <FunctionToPointerDecay>
    | | |   `-DeclRefExpr 0x55574e372520 <col:11> 'int ()' Function 0x55574e371bd0 '__VERIFIER_nondet_int' 'int ()'
    | | `-BinaryOperator 0x55574e3725d0 <col:38, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '<='
    | |   |-ImplicitCastExpr 0x55574e3725b8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/fragtest_simple.c:23:38> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x55574e372578 <col:38> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    | |   `-IntegerLiteral 0x55574e372598 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' 1000000
    | `-CompoundStmt 0x55574e3727f8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/fragtest_simple.c:23:54, line:27:3>
    |   |-BinaryOperator 0x55574e372668 <line:24:5, col:15> 'int' '='
    |   | |-DeclRefExpr 0x55574e372610 <col:5> 'int' lvalue Var 0x55574e371e80 'tmp___1' 'int'
    |   | `-ImplicitCastExpr 0x55574e372650 <col:15> 'int' <LValueToRValue>
    |   |   `-DeclRefExpr 0x55574e372630 <col:15> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |   |-BinaryOperator 0x55574e372720 <line:25:5, col:13> 'int' '='
    |   | |-DeclRefExpr 0x55574e372688 <col:5> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |   | `-BinaryOperator 0x55574e372700 <col:9, col:13> 'int' '+'
    |   |   |-ImplicitCastExpr 0x55574e3726e8 <col:9> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55574e3726a8 <col:9> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |   |   `-IntegerLiteral 0x55574e3726c8 <col:13> 'int' 1
    |   `-BinaryOperator 0x55574e3727d8 <line:26:5, col:13> 'int' '='
    |     |-DeclRefExpr 0x55574e372740 <col:5> 'int' lvalue Var 0x55574e371f18 'k' 'int'
    |     `-BinaryOperator 0x55574e3727b8 <col:9, col:13> 'int' '+'
    |       |-ImplicitCastExpr 0x55574e3727a0 <col:9> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55574e372760 <col:9> 'int' lvalue Var 0x55574e371f18 'k' 'int'
    |       `-IntegerLiteral 0x55574e372780 <col:13> 'int' 1
    |-DeclStmt 0x55574e3728d8 <line:29:3, col:12>
    | `-VarDecl 0x55574e372850 <col:3, col:11> col:7 used j 'int' cinit
    |   `-IntegerLiteral 0x55574e3728b8 <col:11> 'int' 0
    |-BinaryOperator 0x55574e372948 <line:30:3, col:7> 'int' '='
    | |-DeclRefExpr 0x55574e3728f0 <col:3> 'int' lvalue Var 0x55574e372010 'n' 'int'
    | `-ImplicitCastExpr 0x55574e372930 <col:7> 'int' <LValueToRValue>
    |   `-DeclRefExpr 0x55574e372910 <col:7> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |-WhileStmt 0x55574e372db0 <line:31:3, line:40:3>
    | |-IntegerLiteral 0x55574e372968 <line:31:10> 'int' 1
    | `-CompoundStmt 0x55574e372d78 <col:13, line:40:3>
    |   |-CallExpr 0x55574e372a60 <line:33:5, col:29> 'void'
    |   | |-ImplicitCastExpr 0x55574e372a48 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |   | | `-DeclRefExpr 0x55574e372988 <col:5> 'void (int)' Function 0x55574e3718a0 '__VERIFIER_assert' 'void (int)'
    |   | `-BinaryOperator 0x55574e372a00 <col:23, col:28> 'int' '>='
    |   |   |-ImplicitCastExpr 0x55574e3729e8 <col:23> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55574e3729a8 <col:23> 'int' lvalue Var 0x55574e371f18 'k' 'int'
    |   |   `-IntegerLiteral 0x55574e3729c8 <col:28> 'int' 0
    |   |-BinaryOperator 0x55574e372b20 <line:34:5, col:12> 'int' '='
    |   | |-DeclRefExpr 0x55574e372a88 <col:5> 'int' lvalue Var 0x55574e371f18 'k' 'int'
    |   | `-BinaryOperator 0x55574e372b00 <col:9, col:12> 'int' '-'
    |   |   |-ImplicitCastExpr 0x55574e372ae8 <col:9> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55574e372aa8 <col:9> 'int' lvalue Var 0x55574e371f18 'k' 'int'
    |   |   `-IntegerLiteral 0x55574e372ac8 <col:12> 'int' 1
    |   |-BinaryOperator 0x55574e372bd8 <line:35:5, col:13> 'int' '='
    |   | |-DeclRefExpr 0x55574e372b40 <col:5> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |   | `-BinaryOperator 0x55574e372bb8 <col:9, col:13> 'int' '-'
    |   |   |-ImplicitCastExpr 0x55574e372ba0 <col:9> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55574e372b60 <col:9> 'int' lvalue Var 0x55574e371d50 'i' 'int'
    |   |   `-IntegerLiteral 0x55574e372b80 <col:13> 'int' 1
    |   |-BinaryOperator 0x55574e372c90 <line:36:5, col:13> 'int' '='
    |   | |-DeclRefExpr 0x55574e372bf8 <col:5> 'int' lvalue Var 0x55574e372850 'j' 'int'
    |   | `-BinaryOperator 0x55574e372c70 <col:9, col:13> 'int' '+'
    |   |   |-ImplicitCastExpr 0x55574e372c58 <col:9> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55574e372c18 <col:9> 'int' lvalue Var 0x55574e372850 'j' 'int'
    |   |   `-IntegerLiteral 0x55574e372c38 <col:13> 'int' 1
    |   `-IfStmt 0x55574e372d60 <line:37:5, line:39:5>
    |     |-BinaryOperator 0x55574e372d20 <line:37:9, col:14> 'int' '>='
    |     | |-ImplicitCastExpr 0x55574e372cf0 <col:9> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55574e372cb0 <col:9> 'int' lvalue Var 0x55574e372850 'j' 'int'
    |     | `-ImplicitCastExpr 0x55574e372d08 <col:14> 'int' <LValueToRValue>
    |     |   `-DeclRefExpr 0x55574e372cd0 <col:14> 'int' lvalue Var 0x55574e372010 'n' 'int'
    |     `-CompoundStmt 0x55574e372d48 <col:17, line:39:5>
    |       `-BreakStmt 0x55574e372d40 <line:38:7>
    `-ReturnStmt 0x55574e372de8 <line:41:3, col:10>
      `-IntegerLiteral 0x55574e372dc8 <col:10> 'int' 0
