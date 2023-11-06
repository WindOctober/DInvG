./Benchmark/PLDI/SVComp/loop-lit/gsv2008.c
[info] Using default compilation options.
TranslationUnitDecl 0x556fc37d6dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x556fc37d7660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x556fc37d7360 '__int128'
|-TypedefDecl 0x556fc37d76d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x556fc37d7380 'unsigned __int128'
|-TypedefDecl 0x556fc37d79d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x556fc37d77b0 'struct __NSConstantString_tag'
|   `-Record 0x556fc37d7728 '__NSConstantString_tag'
|-TypedefDecl 0x556fc37d7a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x556fc37d7a30 'char *'
|   `-BuiltinType 0x556fc37d6e60 'char'
|-TypedefDecl 0x556fc37d7d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x556fc37d7d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x556fc37d7b50 'struct __va_list_tag'
|     `-Record 0x556fc37d7ac8 '__va_list_tag'
|-FunctionDecl 0x556fc3836ca8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556fc3836d48 prev 0x556fc3836ca8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556fc38370c8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556fc3836e00 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x556fc3836e80 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x556fc3836f00 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556fc3836f80 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556fc3837188 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556fc3837508 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556fc3837240 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x556fc38372c0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x556fc3837340 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556fc38373c0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556fc38375c8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556fc3837858 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556fc3837638 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x556fc38376b8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x556fc3837738 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x556fc3837910 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556fc38379b8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x556fc38532b8 <col:20, col:33>
|   `-ParenExpr 0x556fc3853298 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x556fc3853278 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x556fc3837b58 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x556fc3837b28 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x556fc3837b08 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x556fc3837ad8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x556fc3837a78 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x556fc3837a58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x556fc3837a98 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x556fc3837ab8 <col:32> 'int' 0
|       `-UnaryOperator 0x556fc3853260 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x556fc3853240 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x556fc3853228 <line:108:51, line:113:5>
|             `-IfStmt 0x556fc3853200 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x556fc3837b80 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x556fc3837ba0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x556fc3853130 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x556fc3853118 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x556fc3852eb0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x556fc38370c8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x556fc3853188 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556fc3853170 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556fc3852f08 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x556fc38531b8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556fc38531a0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556fc3852f68 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x556fc38531d0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x556fc3852fe8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x556fc38531e8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x556fc38530d0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x556fc38530b8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x556fc3853088 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x556fc3853368 prev 0x556fc3836d48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556fc38534e8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x556fc3853420 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x556fc3853690 <col:36, line:7:1>
|   `-IfStmt 0x556fc3853678 <line:6:3, col:22>
|     |-UnaryOperator 0x556fc38535c8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x556fc38535b0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x556fc3853590 <col:7> 'int' lvalue ParmVar 0x556fc3853420 'cond' 'int'
|     `-CompoundStmt 0x556fc3853660 <col:13, col:22>
|       `-CallExpr 0x556fc3853640 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x556fc3853628 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x556fc38535e0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x556fc3853368 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x556fc3853750 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x556fc38536c0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x556fc3853a10 <col:34, line:13:1>
|   |-IfStmt 0x556fc38539e8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x556fc3853850 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x556fc3853838 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x556fc3853818 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x556fc38537f8 <col:9> 'int' lvalue ParmVar 0x556fc38536c0 'cond' 'int'
|   | `-CompoundStmt 0x556fc38539d0 <col:16, line:11:3>
|   |   `-LabelStmt 0x556fc38539b8 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x556fc3853948 <col:14, col:37>
|   |       |-CallExpr 0x556fc38538d0 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x556fc38538b8 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x556fc3853868 <col:15> 'void ()' Function 0x556fc38379b8 'reach_error' 'void ()'
|   |       `-CallExpr 0x556fc3853928 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x556fc3853910 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x556fc38538f0 <col:29> 'void (void) __attribute__((noreturn))' Function 0x556fc3853368 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x556fc3853a00 <line:12:3>
|-FunctionDecl 0x556fc3853a80 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x556fc3853b48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c:5:1, line:16:1> line:5:5 main 'int ()'
  `-CompoundStmt 0x556fc38542f8 <col:12, line:16:1>
    |-DeclStmt 0x556fc3853d00 <line:6:5, col:12>
    | |-VarDecl 0x556fc3853c00 <col:5, col:9> col:9 used x 'int'
    | `-VarDecl 0x556fc3853c80 <col:5, col:11> col:11 used y 'int'
    |-BinaryOperator 0x556fc3853d70 <line:7:5, col:10> 'int' '='
    | |-DeclRefExpr 0x556fc3853d18 <col:5> 'int' lvalue Var 0x556fc3853c00 'x' 'int'
    | `-UnaryOperator 0x556fc3853d58 <col:9, col:10> 'int' prefix '-'
    |   `-IntegerLiteral 0x556fc3853d38 <col:10> 'int' 50
    |-BinaryOperator 0x556fc3853e30 <line:8:5, col:31> 'int' '='
    | |-DeclRefExpr 0x556fc3853d90 <col:5> 'int' lvalue Var 0x556fc3853c80 'y' 'int'
    | `-CallExpr 0x556fc3853e10 <col:9, col:31> 'int'
    |   `-ImplicitCastExpr 0x556fc3853df8 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x556fc3853db0 <col:9> 'int ()' Function 0x556fc3853a80 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x556fc3853ff8 <line:9:5, col:47>
    | |-UnaryOperator 0x556fc3853fb0 <col:9, col:37> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x556fc3853f90 <col:10, col:37> 'int'
    | |   `-BinaryOperator 0x556fc3853f70 <col:11, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '&&'
    | |     |-BinaryOperator 0x556fc3853ed8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c:9:11, col:19> 'int' '<'
    | |     | |-UnaryOperator 0x556fc3853e70 <col:11, col:12> 'int' prefix '-'
    | |     | | `-IntegerLiteral 0x556fc3853e50 <col:12> 'int' 1000
    | |     | `-ImplicitCastExpr 0x556fc3853ec0 <col:19> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x556fc3853e88 <col:19> 'int' lvalue Var 0x556fc3853c80 'y' 'int'
    | |     `-BinaryOperator 0x556fc3853f50 <col:24, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '<'
    | |       |-ImplicitCastExpr 0x556fc3853f38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c:9:24> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x556fc3853ef8 <col:24> 'int' lvalue Var 0x556fc3853c80 'y' 'int'
    | |       `-IntegerLiteral 0x556fc3853f18 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' 1000000
    | `-ReturnStmt 0x556fc3853fe8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c:9:40, col:47>
    |   `-IntegerLiteral 0x556fc3853fc8 <col:47> 'int' 0
    |-WhileStmt 0x556fc38541b0 <line:10:5, line:13:5>
    | |-BinaryOperator 0x556fc3854068 <line:10:12, col:16> 'int' '<'
    | | |-ImplicitCastExpr 0x556fc3854050 <col:12> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x556fc3854010 <col:12> 'int' lvalue Var 0x556fc3853c00 'x' 'int'
    | | `-IntegerLiteral 0x556fc3854030 <col:16> 'int' 0
    | `-CompoundStmt 0x556fc3854190 <col:19, line:13:5>
    |   |-BinaryOperator 0x556fc3854138 <line:11:2, col:10> 'int' '='
    |   | |-DeclRefExpr 0x556fc3854088 <col:2> 'int' lvalue Var 0x556fc3853c00 'x' 'int'
    |   | `-BinaryOperator 0x556fc3854118 <col:6, col:10> 'int' '+'
    |   |   |-ImplicitCastExpr 0x556fc38540e8 <col:6> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x556fc38540a8 <col:6> 'int' lvalue Var 0x556fc3853c00 'x' 'int'
    |   |   `-ImplicitCastExpr 0x556fc3854100 <col:10> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x556fc38540c8 <col:10> 'int' lvalue Var 0x556fc3853c80 'y' 'int'
    |   `-UnaryOperator 0x556fc3854178 <line:12:2, col:3> 'int' postfix '++'
    |     `-DeclRefExpr 0x556fc3854158 <col:2> 'int' lvalue Var 0x556fc3853c80 'y' 'int'
    |-CallExpr 0x556fc38542a0 <line:14:5, col:28> 'void'
    | |-ImplicitCastExpr 0x556fc3854288 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x556fc38541c8 <col:5> 'void (int)' Function 0x556fc3853750 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x556fc3854240 <col:23, col:27> 'int' '>'
    |   |-ImplicitCastExpr 0x556fc3854228 <col:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x556fc38541e8 <col:23> 'int' lvalue Var 0x556fc3853c80 'y' 'int'
    |   `-IntegerLiteral 0x556fc3854208 <col:27> 'int' 0
    `-ReturnStmt 0x556fc38542e8 <line:15:5, col:12>
      `-IntegerLiteral 0x556fc38542c8 <col:12> 'int' 0
