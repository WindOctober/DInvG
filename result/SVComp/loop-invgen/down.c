./Benchmark/PLDI/SVComp/loop-invgen/down.c
[info] Using default compilation options.
TranslationUnitDecl 0x556972a36dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x556972a37660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x556972a37360 '__int128'
|-TypedefDecl 0x556972a376d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x556972a37380 'unsigned __int128'
|-TypedefDecl 0x556972a379d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x556972a377b0 'struct __NSConstantString_tag'
|   `-Record 0x556972a37728 '__NSConstantString_tag'
|-TypedefDecl 0x556972a37a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x556972a37a30 'char *'
|   `-BuiltinType 0x556972a36e60 'char'
|-TypedefDecl 0x556972a37d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x556972a37d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x556972a37b50 'struct __va_list_tag'
|     `-Record 0x556972a37ac8 '__va_list_tag'
|-FunctionDecl 0x556972a96ab8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556972a96b58 prev 0x556972a96ab8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556972a96ed8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556972a96c10 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x556972a96c90 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x556972a96d10 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556972a96d90 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556972a96f98 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556972a97318 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556972a97050 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x556972a970d0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x556972a97150 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556972a971d0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556972a973d8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556972a97668 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556972a97448 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x556972a974c8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x556972a97548 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x556972a97720 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556972a977c8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x556972ab3258 <col:20, col:33>
|   `-ParenExpr 0x556972ab3238 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x556972ab3218 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x556972a97968 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x556972a97938 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x556972a97918 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x556972a978e8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x556972a97888 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x556972a97868 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x556972a978a8 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x556972a978c8 <col:32> 'int' 0
|       `-UnaryOperator 0x556972ab3200 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x556972ab31e0 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x556972ab31c8 <line:108:51, line:113:5>
|             `-IfStmt 0x556972ab31a0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x556972a97990 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x556972a979b0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x556972ab30d0 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x556972ab30b8 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x556972ab2e50 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x556972a96ed8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x556972ab3128 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556972ab3110 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556972ab2ea8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x556972ab3158 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556972ab3140 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556972ab2f08 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x556972ab3170 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x556972ab2f88 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x556972ab3188 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x556972ab3070 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x556972ab3058 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x556972ab3028 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x556972ab3308 prev 0x556972a96b58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556972ab3488 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x556972ab33c0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x556972ab3630 <col:36, line:7:1>
|   `-IfStmt 0x556972ab3618 <line:6:3, col:22>
|     |-UnaryOperator 0x556972ab3568 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x556972ab3550 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x556972ab3530 <col:7> 'int' lvalue ParmVar 0x556972ab33c0 'cond' 'int'
|     `-CompoundStmt 0x556972ab3600 <col:13, col:22>
|       `-CallExpr 0x556972ab35e0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x556972ab35c8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x556972ab3580 <col:14> 'void (void) __attribute__((noreturn))' Function 0x556972ab3308 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x556972ab36f0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x556972ab3660 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x556972ab39b0 <col:34, line:13:1>
|   |-IfStmt 0x556972ab3988 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x556972ab37f0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x556972ab37d8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x556972ab37b8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x556972ab3798 <col:9> 'int' lvalue ParmVar 0x556972ab3660 'cond' 'int'
|   | `-CompoundStmt 0x556972ab3970 <col:16, line:11:3>
|   |   `-LabelStmt 0x556972ab3958 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x556972ab38e8 <col:12, col:35>
|   |       |-CallExpr 0x556972ab3870 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x556972ab3858 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x556972ab3808 <col:13> 'void ()' Function 0x556972a977c8 'reach_error' 'void ()'
|   |       `-CallExpr 0x556972ab38c8 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x556972ab38b0 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x556972ab3890 <col:27> 'void (void) __attribute__((noreturn))' Function 0x556972ab3308 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x556972ab39a0 <line:12:3>
|-FunctionDecl 0x556972ab3a20 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x556972ab3ae8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/down.c:3:1, line:19:1> line:3:5 main 'int ()'
  `-CompoundStmt 0x556972ab42c8 <col:12, line:19:1>
    |-DeclStmt 0x556972ab3c08 <line:4:3, col:8>
    | `-VarDecl 0x556972ab3ba0 <col:3, col:7> col:7 used n 'int'
    |-DeclStmt 0x556972ab3cc0 <line:5:3, col:12>
    | `-VarDecl 0x556972ab3c38 <col:3, col:11> col:7 used k 'int' cinit
    |   `-IntegerLiteral 0x556972ab3ca0 <col:11> 'int' 0
    |-DeclStmt 0x556972ab3d78 <line:6:3, col:12>
    | `-VarDecl 0x556972ab3cf0 <col:3, col:11> col:7 used i 'int' cinit
    |   `-IntegerLiteral 0x556972ab3d58 <col:11> 'int' 0
    |-BinaryOperator 0x556972ab3e30 <line:7:3, col:29> 'int' '='
    | |-DeclRefExpr 0x556972ab3d90 <col:3> 'int' lvalue Var 0x556972ab3ba0 'n' 'int'
    | `-CallExpr 0x556972ab3e10 <col:7, col:29> 'int'
    |   `-ImplicitCastExpr 0x556972ab3df8 <col:7> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x556972ab3db0 <col:7> 'int ()' Function 0x556972ab3a20 '__VERIFIER_nondet_int' 'int ()'
    |-WhileStmt 0x556972ab3f80 <line:8:3, line:11:3>
    | |-BinaryOperator 0x556972ab3ed0 <line:8:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x556972ab3ea0 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x556972ab3e60 <col:10> 'int' lvalue Var 0x556972ab3cf0 'i' 'int'
    | | `-ImplicitCastExpr 0x556972ab3eb8 <col:14> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x556972ab3e80 <col:14> 'int' lvalue Var 0x556972ab3ba0 'n' 'int'
    | `-CompoundStmt 0x556972ab3f60 <col:18, line:11:3>
    |   |-UnaryOperator 0x556972ab3f10 <line:9:7, col:8> 'int' postfix '++'
    |   | `-DeclRefExpr 0x556972ab3ef0 <col:7> 'int' lvalue Var 0x556972ab3cf0 'i' 'int'
    |   `-UnaryOperator 0x556972ab3f48 <line:10:7, col:8> 'int' postfix '++'
    |     `-DeclRefExpr 0x556972ab3f28 <col:7> 'int' lvalue Var 0x556972ab3c38 'k' 'int'
    |-DeclStmt 0x556972ab4050 <line:12:3, col:12>
    | `-VarDecl 0x556972ab3fb0 <col:3, col:11> col:7 used j 'int' cinit
    |   `-ImplicitCastExpr 0x556972ab4038 <col:11> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x556972ab4018 <col:11> 'int' lvalue Var 0x556972ab3ba0 'n' 'int'
    |-WhileStmt 0x556972ab4280 <line:13:3, line:17:3>
    | |-BinaryOperator 0x556972ab40c0 <line:13:10, col:14> 'int' '>'
    | | |-ImplicitCastExpr 0x556972ab40a8 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x556972ab4068 <col:10> 'int' lvalue Var 0x556972ab3fb0 'j' 'int'
    | | `-IntegerLiteral 0x556972ab4088 <col:14> 'int' 0
    | `-CompoundStmt 0x556972ab4258 <col:18, line:17:3>
    |   |-CallExpr 0x556972ab41c0 <line:14:7, col:30> 'void'
    |   | |-ImplicitCastExpr 0x556972ab41a8 <col:7> 'void (*)(int)' <FunctionToPointerDecay>
    |   | | `-DeclRefExpr 0x556972ab40e0 <col:7> 'void (int)' Function 0x556972ab36f0 '__VERIFIER_assert' 'void (int)'
    |   | `-BinaryOperator 0x556972ab4158 <col:25, col:29> 'int' '>'
    |   |   |-ImplicitCastExpr 0x556972ab4140 <col:25> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x556972ab4100 <col:25> 'int' lvalue Var 0x556972ab3c38 'k' 'int'
    |   |   `-IntegerLiteral 0x556972ab4120 <col:29> 'int' 0
    |   |-UnaryOperator 0x556972ab4208 <line:15:7, col:8> 'int' postfix '--'
    |   | `-DeclRefExpr 0x556972ab41e8 <col:7> 'int' lvalue Var 0x556972ab3fb0 'j' 'int'
    |   `-UnaryOperator 0x556972ab4240 <line:16:7, col:8> 'int' postfix '--'
    |     `-DeclRefExpr 0x556972ab4220 <col:7> 'int' lvalue Var 0x556972ab3c38 'k' 'int'
    `-ReturnStmt 0x556972ab42b8 <line:18:3, col:10>
      `-IntegerLiteral 0x556972ab4298 <col:10> 'int' 0
