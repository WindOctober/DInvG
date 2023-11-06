./Benchmark/PLDI/SVComp/loop-lit/hhk2008.c
[info] Using default compilation options.
TranslationUnitDecl 0x561af2a00dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x561af2a01660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x561af2a01360 '__int128'
|-TypedefDecl 0x561af2a016d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x561af2a01380 'unsigned __int128'
|-TypedefDecl 0x561af2a019d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x561af2a017b0 'struct __NSConstantString_tag'
|   `-Record 0x561af2a01728 '__NSConstantString_tag'
|-TypedefDecl 0x561af2a01a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x561af2a01a30 'char *'
|   `-BuiltinType 0x561af2a00e60 'char'
|-TypedefDecl 0x561af2a01d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x561af2a01d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x561af2a01b50 'struct __va_list_tag'
|     `-Record 0x561af2a01ac8 '__va_list_tag'
|-FunctionDecl 0x561af2a60d38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x561af2a60dd8 prev 0x561af2a60d38 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x561af2a61158 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x561af2a60e90 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x561af2a60f10 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x561af2a60f90 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x561af2a61010 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x561af2a61218 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x561af2a61598 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x561af2a612d0 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x561af2a61350 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x561af2a613d0 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x561af2a61450 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x561af2a61658 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x561af2a618e8 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x561af2a616c8 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x561af2a61748 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x561af2a617c8 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x561af2a619a0 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x561af2a61a48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x561af2a7d348 <col:20, col:33>
|   `-ParenExpr 0x561af2a7d328 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x561af2a7d308 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x561af2a61be8 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x561af2a61bb8 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x561af2a61b98 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x561af2a61b68 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x561af2a61b08 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x561af2a61ae8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x561af2a61b28 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x561af2a61b48 <col:32> 'int' 0
|       `-UnaryOperator 0x561af2a7d2f0 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x561af2a7d2d0 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x561af2a7d2b8 <line:108:51, line:113:5>
|             `-IfStmt 0x561af2a7d290 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x561af2a61c10 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x561af2a61c30 </usr/include/assert.h:110:9>
|               `-CallExpr 0x561af2a7d1c0 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x561af2a7d1a8 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x561af2a7cf40 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x561af2a61158 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x561af2a7d218 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x561af2a7d200 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x561af2a7cf98 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x561af2a7d248 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x561af2a7d230 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x561af2a7cff8 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x561af2a7d260 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x561af2a7d078 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x561af2a7d278 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x561af2a7d160 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x561af2a7d148 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x561af2a7d118 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x561af2a7d3f8 prev 0x561af2a60dd8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x561af2a7d578 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x561af2a7d4b0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x561af2a7d720 <col:36, line:7:1>
|   `-IfStmt 0x561af2a7d708 <line:6:3, col:22>
|     |-UnaryOperator 0x561af2a7d658 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x561af2a7d640 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x561af2a7d620 <col:7> 'int' lvalue ParmVar 0x561af2a7d4b0 'cond' 'int'
|     `-CompoundStmt 0x561af2a7d6f0 <col:13, col:22>
|       `-CallExpr 0x561af2a7d6d0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x561af2a7d6b8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x561af2a7d670 <col:14> 'void (void) __attribute__((noreturn))' Function 0x561af2a7d3f8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x561af2a7d7e0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x561af2a7d750 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x561af2a7daa0 <col:34, line:13:1>
|   |-IfStmt 0x561af2a7da78 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x561af2a7d8e0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x561af2a7d8c8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x561af2a7d8a8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x561af2a7d888 <col:9> 'int' lvalue ParmVar 0x561af2a7d750 'cond' 'int'
|   | `-CompoundStmt 0x561af2a7da60 <col:16, line:11:3>
|   |   `-LabelStmt 0x561af2a7da48 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x561af2a7d9d8 <col:14, col:37>
|   |       |-CallExpr 0x561af2a7d960 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x561af2a7d948 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x561af2a7d8f8 <col:15> 'void ()' Function 0x561af2a61a48 'reach_error' 'void ()'
|   |       `-CallExpr 0x561af2a7d9b8 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x561af2a7d9a0 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x561af2a7d980 <col:29> 'void (void) __attribute__((noreturn))' Function 0x561af2a7d3f8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x561af2a7da90 <line:12:3>
|-FunctionDecl 0x561af2a7db10 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x561af2a7dbd8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/hhk2008.c:6:1, line:20:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x561af2a7e728 <col:12, line:20:1>
    |-DeclStmt 0x561af2a7dd80 <line:7:5, col:36>
    | `-VarDecl 0x561af2a7dc90 <col:5, col:35> col:9 used a 'int' cinit
    |   `-CallExpr 0x561af2a7dd60 <col:13, col:35> 'int'
    |     `-ImplicitCastExpr 0x561af2a7dd48 <col:13> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x561af2a7dcf8 <col:13> 'int ()' Function 0x561af2a7db10 '__VERIFIER_nondet_int' 'int ()'
    |-DeclStmt 0x561af2a7de70 <line:8:5, col:36>
    | `-VarDecl 0x561af2a7ddb0 <col:5, col:35> col:9 used b 'int' cinit
    |   `-CallExpr 0x561af2a7de50 <col:13, col:35> 'int'
    |     `-ImplicitCastExpr 0x561af2a7de38 <col:13> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x561af2a7de18 <col:13> 'int ()' Function 0x561af2a7db10 '__VERIFIER_nondet_int' 'int ()'
    |-DeclStmt 0x561af2a7dfd0 <line:9:5, col:17>
    | |-VarDecl 0x561af2a7dea0 <col:5, col:9> col:9 used res 'int'
    | `-VarDecl 0x561af2a7df50 <col:5, col:14> col:14 used cnt 'int'
    |-IfStmt 0x561af2a7e0c8 <line:10:5, col:33>
    | |-UnaryOperator 0x561af2a7e080 <col:9, col:23> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x561af2a7e060 <col:10, col:23> 'int'
    | |   `-BinaryOperator 0x561af2a7e040 <col:11, col:16> 'int' '<='
    | |     |-ImplicitCastExpr 0x561af2a7e028 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x561af2a7dfe8 <col:11> 'int' lvalue Var 0x561af2a7dc90 'a' 'int'
    | |     `-IntegerLiteral 0x561af2a7e008 <col:16> 'int' 1000000
    | `-ReturnStmt 0x561af2a7e0b8 <col:26, col:33>
    |   `-IntegerLiteral 0x561af2a7e098 <col:33> 'int' 0
    |-IfStmt 0x561af2a7e258 <line:11:5, col:43>
    | |-UnaryOperator 0x561af2a7e210 <col:9, col:33> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x561af2a7e1f0 <col:10, col:33> 'int'
    | |   `-BinaryOperator 0x561af2a7e1d0 <col:11, col:26> 'int' '&&'
    | |     |-BinaryOperator 0x561af2a7e138 <col:11, col:16> 'int' '<='
    | |     | |-IntegerLiteral 0x561af2a7e0e0 <col:11> 'int' 0
    | |     | `-ImplicitCastExpr 0x561af2a7e120 <col:16> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x561af2a7e100 <col:16> 'int' lvalue Var 0x561af2a7ddb0 'b' 'int'
    | |     `-BinaryOperator 0x561af2a7e1b0 <col:21, col:26> 'int' '<='
    | |       |-ImplicitCastExpr 0x561af2a7e198 <col:21> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x561af2a7e158 <col:21> 'int' lvalue Var 0x561af2a7ddb0 'b' 'int'
    | |       `-IntegerLiteral 0x561af2a7e178 <col:26> 'int' 1000000
    | `-ReturnStmt 0x561af2a7e248 <col:36, col:43>
    |   `-IntegerLiteral 0x561af2a7e228 <col:43> 'int' 0
    |-BinaryOperator 0x561af2a7e2c8 <line:12:5, col:11> 'int' '='
    | |-DeclRefExpr 0x561af2a7e270 <col:5> 'int' lvalue Var 0x561af2a7dea0 'res' 'int'
    | `-ImplicitCastExpr 0x561af2a7e2b0 <col:11> 'int' <LValueToRValue>
    |   `-DeclRefExpr 0x561af2a7e290 <col:11> 'int' lvalue Var 0x561af2a7dc90 'a' 'int'
    |-BinaryOperator 0x561af2a7e340 <line:13:5, col:11> 'int' '='
    | |-DeclRefExpr 0x561af2a7e2e8 <col:5> 'int' lvalue Var 0x561af2a7df50 'cnt' 'int'
    | `-ImplicitCastExpr 0x561af2a7e328 <col:11> 'int' <LValueToRValue>
    |   `-DeclRefExpr 0x561af2a7e308 <col:11> 'int' lvalue Var 0x561af2a7ddb0 'b' 'int'
    |-WhileStmt 0x561af2a7e568 <line:14:5, line:17:5>
    | |-BinaryOperator 0x561af2a7e3b8 <line:14:12, col:18> 'int' '>'
    | | |-ImplicitCastExpr 0x561af2a7e3a0 <col:12> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x561af2a7e360 <col:12> 'int' lvalue Var 0x561af2a7df50 'cnt' 'int'
    | | `-IntegerLiteral 0x561af2a7e380 <col:18> 'int' 0
    | `-CompoundStmt 0x561af2a7e548 <col:21, line:17:5>
    |   |-BinaryOperator 0x561af2a7e470 <line:15:2, col:14> 'int' '='
    |   | |-DeclRefExpr 0x561af2a7e3d8 <col:2> 'int' lvalue Var 0x561af2a7df50 'cnt' 'int'
    |   | `-BinaryOperator 0x561af2a7e450 <col:8, col:14> 'int' '-'
    |   |   |-ImplicitCastExpr 0x561af2a7e438 <col:8> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x561af2a7e3f8 <col:8> 'int' lvalue Var 0x561af2a7df50 'cnt' 'int'
    |   |   `-IntegerLiteral 0x561af2a7e418 <col:14> 'int' 1
    |   `-BinaryOperator 0x561af2a7e528 <line:16:2, col:14> 'int' '='
    |     |-DeclRefExpr 0x561af2a7e490 <col:2> 'int' lvalue Var 0x561af2a7dea0 'res' 'int'
    |     `-BinaryOperator 0x561af2a7e508 <col:8, col:14> 'int' '+'
    |       |-ImplicitCastExpr 0x561af2a7e4f0 <col:8> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x561af2a7e4b0 <col:8> 'int' lvalue Var 0x561af2a7dea0 'res' 'int'
    |       `-IntegerLiteral 0x561af2a7e4d0 <col:14> 'int' 1
    |-CallExpr 0x561af2a7e6d0 <line:18:5, col:35> 'void'
    | |-ImplicitCastExpr 0x561af2a7e6b8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x561af2a7e580 <col:5> 'void (int)' Function 0x561af2a7d7e0 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x561af2a7e668 <col:23, col:34> 'int' '=='
    |   |-ImplicitCastExpr 0x561af2a7e650 <col:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x561af2a7e5a0 <col:23> 'int' lvalue Var 0x561af2a7dea0 'res' 'int'
    |   `-BinaryOperator 0x561af2a7e630 <col:30, col:34> 'int' '+'
    |     |-ImplicitCastExpr 0x561af2a7e600 <col:30> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x561af2a7e5c0 <col:30> 'int' lvalue Var 0x561af2a7dc90 'a' 'int'
    |     `-ImplicitCastExpr 0x561af2a7e618 <col:34> 'int' <LValueToRValue>
    |       `-DeclRefExpr 0x561af2a7e5e0 <col:34> 'int' lvalue Var 0x561af2a7ddb0 'b' 'int'
    `-ReturnStmt 0x561af2a7e718 <line:19:5, col:12>
      `-IntegerLiteral 0x561af2a7e6f8 <col:12> 'int' 0
