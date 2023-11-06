./Benchmark/PLDI/SVComp/loop-invgen/SpamAssassin-loop.c
[info] Using default compilation options.
TranslationUnitDecl 0x55b60c692ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55b60c693780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55b60c693480 '__int128'
|-TypedefDecl 0x55b60c6937f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55b60c6934a0 'unsigned __int128'
|-TypedefDecl 0x55b60c693af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55b60c6938d0 'struct __NSConstantString_tag'
|   `-Record 0x55b60c693848 '__NSConstantString_tag'
|-TypedefDecl 0x55b60c693b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55b60c693b50 'char *'
|   `-BuiltinType 0x55b60c692f80 'char'
|-TypedefDecl 0x55b60c693e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55b60c693e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55b60c693c70 'struct __va_list_tag'
|     `-Record 0x55b60c693be8 '__va_list_tag'
|-FunctionDecl 0x55b60c6f31a8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b60c6f3248 prev 0x55b60c6f31a8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b60c6f35c8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55b60c6f3300 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x55b60c6f3380 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x55b60c6f3400 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55b60c6f3480 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55b60c6f3688 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55b60c6f3a08 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55b60c6f3740 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x55b60c6f37c0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x55b60c6f3840 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55b60c6f38c0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55b60c6f3ac8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55b60c6f3d58 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55b60c6f3b38 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x55b60c6f3bb8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x55b60c6f3c38 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x55b60c6f3e10 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55b60c6f3eb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55b60c70f708 <col:20, col:33>
|   `-ParenExpr 0x55b60c70f6e8 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x55b60c70f6c8 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x55b60c6f4058 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x55b60c6f4028 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x55b60c6f4008 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x55b60c6f3fd8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x55b60c6f3f78 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x55b60c6f3f58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x55b60c6f3f98 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x55b60c6f3fb8 <col:32> 'int' 0
|       `-UnaryOperator 0x55b60c70f6b0 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x55b60c70f690 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x55b60c70f678 <line:108:51, line:113:5>
|             `-IfStmt 0x55b60c70f650 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x55b60c6f4080 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x55b60c6f40a0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x55b60c70f580 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x55b60c70f568 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x55b60c70f300 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55b60c6f35c8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x55b60c70f5d8 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55b60c70f5c0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55b60c70f358 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x55b60c70f608 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55b60c70f5f0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55b60c70f3b8 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x55b60c70f620 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x55b60c70f438 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x55b60c70f638 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x55b60c70f520 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x55b60c70f508 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x55b60c70f4d8 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x55b60c70f7b8 prev 0x55b60c6f3248 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b60c70f938 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55b60c70f870 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55b60c70fae0 <col:36, line:7:1>
|   `-IfStmt 0x55b60c70fac8 <line:6:3, col:22>
|     |-UnaryOperator 0x55b60c70fa18 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55b60c70fa00 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55b60c70f9e0 <col:7> 'int' lvalue ParmVar 0x55b60c70f870 'cond' 'int'
|     `-CompoundStmt 0x55b60c70fab0 <col:13, col:22>
|       `-CallExpr 0x55b60c70fa90 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55b60c70fa78 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55b60c70fa30 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55b60c70f7b8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55b60c70fba0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55b60c70fb10 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55b60c70fe60 <col:34, line:13:1>
|   |-IfStmt 0x55b60c70fe38 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x55b60c70fca0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55b60c70fc88 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55b60c70fc68 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55b60c70fc48 <col:9> 'int' lvalue ParmVar 0x55b60c70fb10 'cond' 'int'
|   | `-CompoundStmt 0x55b60c70fe20 <col:16, line:11:3>
|   |   `-LabelStmt 0x55b60c70fe08 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55b60c70fd98 <col:12, col:35>
|   |       |-CallExpr 0x55b60c70fd20 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55b60c70fd08 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55b60c70fcb8 <col:13> 'void ()' Function 0x55b60c6f3eb8 'reach_error' 'void ()'
|   |       `-CallExpr 0x55b60c70fd78 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55b60c70fd60 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55b60c70fd40 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55b60c70f7b8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55b60c70fe50 <line:12:3>
|-FunctionDecl 0x55b60c70fed0 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x55b60c70ff98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/SpamAssassin-loop.c:3:1, line:51:1> line:3:5 main 'int ()'
  `-CompoundStmt 0x55b60c7124f0 <line:4:1, line:51:1>
    |-DeclStmt 0x55b60c7100b8 <line:5:5, col:12>
    | `-VarDecl 0x55b60c710050 <col:5, col:9> col:9 used len 'int'
    |-DeclStmt 0x55b60c710150 <line:6:5, col:10>
    | `-VarDecl 0x55b60c7100e8 <col:5, col:9> col:9 used i 'int'
    |-DeclStmt 0x55b60c7101e8 <line:7:5, col:10>
    | `-VarDecl 0x55b60c710180 <col:5, col:9> col:9 used j 'int'
    |-DeclStmt 0x55b60c710280 <line:9:5, col:16>
    | `-VarDecl 0x55b60c710218 <col:5, col:9> col:9 used bufsize 'int'
    |-BinaryOperator 0x55b60c710370 <line:10:5, col:37> 'int' '='
    | |-DeclRefExpr 0x55b60c710298 <col:5> 'int' lvalue Var 0x55b60c710218 'bufsize' 'int'
    | `-CallExpr 0x55b60c710350 <col:15, col:37> 'int'
    |   `-ImplicitCastExpr 0x55b60c710338 <col:15> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55b60c7102b8 <col:15> 'int ()' Function 0x55b60c70fed0 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x55b60c710438 <line:11:5, col:29>
    | |-BinaryOperator 0x55b60c7103e8 <col:9, col:19> 'int' '<'
    | | |-ImplicitCastExpr 0x55b60c7103d0 <col:9> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55b60c710390 <col:9> 'int' lvalue Var 0x55b60c710218 'bufsize' 'int'
    | | `-IntegerLiteral 0x55b60c7103b0 <col:19> 'int' 0
    | `-ReturnStmt 0x55b60c710428 <col:22, col:29>
    |   `-IntegerLiteral 0x55b60c710408 <col:29> 'int' 0
    |-BinaryOperator 0x55b60c7104c8 <line:12:5, col:33> 'int' '='
    | |-DeclRefExpr 0x55b60c710450 <col:5> 'int' lvalue Var 0x55b60c710050 'len' 'int'
    | `-CallExpr 0x55b60c7104a8 <col:11, col:33> 'int'
    |   `-ImplicitCastExpr 0x55b60c710490 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55b60c710470 <col:11> 'int ()' Function 0x55b60c70fed0 '__VERIFIER_nondet_int' 'int ()'
    |-DeclStmt 0x55b60c7105e0 <line:13:5, col:28>
    | `-VarDecl 0x55b60c710500 <col:5, col:27> col:9 used limit 'int' cinit
    |   `-BinaryOperator 0x55b60c7105c0 <col:17, col:27> 'int' '-'
    |     |-ImplicitCastExpr 0x55b60c7105a8 <col:17> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x55b60c710568 <col:17> 'int' lvalue Var 0x55b60c710218 'bufsize' 'int'
    |     `-IntegerLiteral 0x55b60c710588 <col:27> 'int' 4
    |-ForStmt 0x55b60c712488 <line:16:5, line:49:5>
    | |-BinaryOperator 0x55b60c710638 <line:16:10, col:14> 'int' '='
    | | |-DeclRefExpr 0x55b60c7105f8 <col:10> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    | | `-IntegerLiteral 0x55b60c710618 <col:14> 'int' 0
    | |-<<<NULL>>>
    | |-BinaryOperator 0x55b60c7106c8 <col:17, col:21> 'int' '<'
    | | |-ImplicitCastExpr 0x55b60c710698 <col:17> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55b60c710658 <col:17> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    | | `-ImplicitCastExpr 0x55b60c7106b0 <col:21> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55b60c710678 <col:21> 'int' lvalue Var 0x55b60c710050 'len' 'int'
    | |-<<<NULL>>>
    | `-CompoundStmt 0x55b60c712470 <col:28, line:49:5>
    |   `-ForStmt 0x55b60c712438 <line:17:9, line:48:9>
    |     |-BinaryOperator 0x55b60c710728 <line:17:14, col:18> 'int' '='
    |     | |-DeclRefExpr 0x55b60c7106e8 <col:14> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |     | `-IntegerLiteral 0x55b60c710708 <col:18> 'int' 0
    |     |-<<<NULL>>>
    |     |-BinaryOperator 0x55b60c710868 <col:21, col:36> 'int' '&&'
    |     | |-BinaryOperator 0x55b60c7107b8 <col:21, col:25> 'int' '<'
    |     | | |-ImplicitCastExpr 0x55b60c710788 <col:21> 'int' <LValueToRValue>
    |     | | | `-DeclRefExpr 0x55b60c710748 <col:21> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |     | | `-ImplicitCastExpr 0x55b60c7107a0 <col:25> 'int' <LValueToRValue>
    |     | |   `-DeclRefExpr 0x55b60c710768 <col:25> 'int' lvalue Var 0x55b60c710050 'len' 'int'
    |     | `-BinaryOperator 0x55b60c710848 <col:32, col:36> 'int' '<'
    |     |   |-ImplicitCastExpr 0x55b60c710818 <col:32> 'int' <LValueToRValue>
    |     |   | `-DeclRefExpr 0x55b60c7107d8 <col:32> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |     |   `-ImplicitCastExpr 0x55b60c710830 <col:36> 'int' <LValueToRValue>
    |     |     `-DeclRefExpr 0x55b60c7107f8 <col:36> 'int' lvalue Var 0x55b60c710500 'limit' 'int'
    |     |-<<<NULL>>>
    |     `-CompoundStmt 0x55b60c712420 <col:44, line:48:9>
    |       `-IfStmt 0x55b60c7123f8 <line:18:13, line:47:13> has_else
    |         |-BinaryOperator 0x55b60c710938 <line:18:17, col:25> 'int' '<'
    |         | |-BinaryOperator 0x55b60c7108e0 <col:17, col:21> 'int' '+'
    |         | | |-ImplicitCastExpr 0x55b60c7108c8 <col:17> 'int' <LValueToRValue>
    |         | | | `-DeclRefExpr 0x55b60c710888 <col:17> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | | `-IntegerLiteral 0x55b60c7108a8 <col:21> 'int' 1
    |         | `-ImplicitCastExpr 0x55b60c710920 <col:25> 'int' <LValueToRValue>
    |         |   `-DeclRefExpr 0x55b60c710900 <col:25> 'int' lvalue Var 0x55b60c710050 'len' 'int'
    |         |-CompoundStmt 0x55b60c711f00 <col:29, line:39:13>
    |         | |-CallExpr 0x55b60c710a90 <line:19:17, col:42> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c710a78 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c710958 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c710a28 <col:35, col:39> 'int' '<'
    |         | |   |-BinaryOperator 0x55b60c7109d0 <col:35, col:37> 'int' '+'
    |         | |   | |-ImplicitCastExpr 0x55b60c7109b8 <col:35> 'int' <LValueToRValue>
    |         | |   | | `-DeclRefExpr 0x55b60c710978 <col:35> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | |   | `-IntegerLiteral 0x55b60c710998 <col:37> 'int' 1
    |         | |   `-ImplicitCastExpr 0x55b60c710a10 <col:39> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c7109f0 <col:39> 'int' lvalue Var 0x55b60c710050 'len' 'int'
    |         | |-CallExpr 0x55b60c710b68 <line:20:17, col:39> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c710b50 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c710ab8 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c710b30 <col:35, col:38> 'int' '<='
    |         | |   |-IntegerLiteral 0x55b60c710ad8 <col:35> 'int' 0
    |         | |   `-ImplicitCastExpr 0x55b60c710b18 <col:38> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c710af8 <col:38> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | |-IfStmt 0x55b60c710c50 <line:21:17, col:52>
    |         | | |-CallExpr 0x55b60c710bc8 <col:21, col:43> 'int'
    |         | | | `-ImplicitCastExpr 0x55b60c710bb0 <col:21> 'int (*)()' <FunctionToPointerDecay>
    |         | | |   `-DeclRefExpr 0x55b60c710b90 <col:21> 'int ()' Function 0x55b60c70fed0 '__VERIFIER_nondet_int' 'int ()'
    |         | | `-GotoStmt 0x55b60c710c38 <col:47, col:52> 'ELSE' 0x55b60c710be8
    |         | |-CallExpr 0x55b60c710d30 <line:22:17, col:40> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c710d18 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c710c68 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c710cf8 <col:35, col:37> 'int' '<'
    |         | |   |-ImplicitCastExpr 0x55b60c710cc8 <col:35> 'int' <LValueToRValue>
    |         | |   | `-DeclRefExpr 0x55b60c710c88 <col:35> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | |   `-ImplicitCastExpr 0x55b60c710ce0 <col:37> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c710ca8 <col:37> 'int' lvalue Var 0x55b60c710050 'len' 'int'
    |         | |-CallExpr 0x55b60c710e08 <line:23:17, col:39> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c710df0 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c710d58 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c710dd0 <col:35, col:38> 'int' '<='
    |         | |   |-IntegerLiteral 0x55b60c710d78 <col:35> 'int' 0
    |         | |   `-ImplicitCastExpr 0x55b60c710db8 <col:38> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c710d98 <col:38> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | |-CallExpr 0x55b60c710ef8 <line:24:17, col:44> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c710ee0 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c710e30 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c710ec0 <col:35, col:37> 'int' '<'
    |         | |   |-ImplicitCastExpr 0x55b60c710e90 <col:35> 'int' <LValueToRValue>
    |         | |   | `-DeclRefExpr 0x55b60c710e50 <col:35> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         | |   `-ImplicitCastExpr 0x55b60c710ea8 <col:37> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c710e70 <col:37> 'int' lvalue Var 0x55b60c710218 'bufsize' 'int'
    |         | |-CallExpr 0x55b60c710fd0 <line:25:17, col:39> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c710fb8 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c710f20 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c710f98 <col:35, col:38> 'int' '<='
    |         | |   |-IntegerLiteral 0x55b60c710f40 <col:35> 'int' 0
    |         | |   `-ImplicitCastExpr 0x55b60c710f80 <col:38> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c710f60 <col:38> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         | |-UnaryOperator 0x55b60c711018 <line:27:17, col:18> 'int' postfix '++'
    |         | | `-DeclRefExpr 0x55b60c710ff8 <col:17> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         | |-UnaryOperator 0x55b60c711050 <line:28:17, col:18> 'int' postfix '++'
    |         | | `-DeclRefExpr 0x55b60c711030 <col:17> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | |-CallExpr 0x55b60c711130 <line:29:17, col:40> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c711118 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c711068 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c7110f8 <col:35, col:37> 'int' '<'
    |         | |   |-ImplicitCastExpr 0x55b60c7110c8 <col:35> 'int' <LValueToRValue>
    |         | |   | `-DeclRefExpr 0x55b60c711088 <col:35> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | |   `-ImplicitCastExpr 0x55b60c7110e0 <col:37> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c7110a8 <col:37> 'int' lvalue Var 0x55b60c710050 'len' 'int'
    |         | |-CallExpr 0x55b60c711208 <line:30:17, col:39> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c7111f0 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c711158 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c7111d0 <col:35, col:38> 'int' '<='
    |         | |   |-IntegerLiteral 0x55b60c711178 <col:35> 'int' 0
    |         | |   `-ImplicitCastExpr 0x55b60c7111b8 <col:38> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c711198 <col:38> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | |-CallExpr 0x55b60c711b90 <line:31:17, col:44> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c7112e0 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c711230 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c7112c0 <col:35, col:37> 'int' '<'
    |         | |   |-ImplicitCastExpr 0x55b60c711290 <col:35> 'int' <LValueToRValue>
    |         | |   | `-DeclRefExpr 0x55b60c711250 <col:35> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         | |   `-ImplicitCastExpr 0x55b60c7112a8 <col:37> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c711270 <col:37> 'int' lvalue Var 0x55b60c710218 'bufsize' 'int'
    |         | |-CallExpr 0x55b60c711c68 <line:32:17, col:39> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c711c50 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c711bb8 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c711c30 <col:35, col:38> 'int' '<='
    |         | |   |-IntegerLiteral 0x55b60c711bd8 <col:35> 'int' 0
    |         | |   `-ImplicitCastExpr 0x55b60c711c18 <col:38> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c711bf8 <col:38> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         | |-UnaryOperator 0x55b60c711cb0 <line:34:17, col:18> 'int' postfix '++'
    |         | | `-DeclRefExpr 0x55b60c711c90 <col:17> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         | |-UnaryOperator 0x55b60c711ce8 <line:35:17, col:18> 'int' postfix '++'
    |         | | `-DeclRefExpr 0x55b60c711cc8 <col:17> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |         | |-CallExpr 0x55b60c711dc8 <line:36:17, col:44> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c711db0 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c711d00 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c711d90 <col:35, col:37> 'int' '<'
    |         | |   |-ImplicitCastExpr 0x55b60c711d60 <col:35> 'int' <LValueToRValue>
    |         | |   | `-DeclRefExpr 0x55b60c711d20 <col:35> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         | |   `-ImplicitCastExpr 0x55b60c711d78 <col:37> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c711d40 <col:37> 'int' lvalue Var 0x55b60c710218 'bufsize' 'int'
    |         | |-CallExpr 0x55b60c711ea0 <line:37:17, col:39> 'void'
    |         | | |-ImplicitCastExpr 0x55b60c711e88 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |         | | | `-DeclRefExpr 0x55b60c711df0 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |         | | `-BinaryOperator 0x55b60c711e68 <col:35, col:38> 'int' '<='
    |         | |   |-IntegerLiteral 0x55b60c711e10 <col:35> 'int' 0
    |         | |   `-ImplicitCastExpr 0x55b60c711e50 <col:38> 'int' <LValueToRValue>
    |         | |     `-DeclRefExpr 0x55b60c711e30 <col:38> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         | `-UnaryOperator 0x55b60c711ee8 <line:38:17, col:18> 'int' postfix '++'
    |         |   `-DeclRefExpr 0x55b60c711ec8 <col:17> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |         `-CompoundStmt 0x55b60c7123b8 <line:39:20, line:47:13>
    |           |-LabelStmt 0x55b60c712090 <line:40:1, line:41:40> 'ELSE'
    |           | `-CallExpr 0x55b60c712068 <col:17, col:40> 'void'
    |           |   |-ImplicitCastExpr 0x55b60c712050 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |           |   | `-DeclRefExpr 0x55b60c711fa0 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |           |   `-BinaryOperator 0x55b60c712030 <col:35, col:37> 'int' '<'
    |           |     |-ImplicitCastExpr 0x55b60c712000 <col:35> 'int' <LValueToRValue>
    |           |     | `-DeclRefExpr 0x55b60c711fc0 <col:35> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |           |     `-ImplicitCastExpr 0x55b60c712018 <col:37> 'int' <LValueToRValue>
    |           |       `-DeclRefExpr 0x55b60c711fe0 <col:37> 'int' lvalue Var 0x55b60c710050 'len' 'int'
    |           |-CallExpr 0x55b60c712158 <line:42:17, col:39> 'void'
    |           | |-ImplicitCastExpr 0x55b60c712140 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |           | | `-DeclRefExpr 0x55b60c7120a8 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |           | `-BinaryOperator 0x55b60c712120 <col:35, col:38> 'int' '<='
    |           |   |-IntegerLiteral 0x55b60c7120c8 <col:35> 'int' 0
    |           |   `-ImplicitCastExpr 0x55b60c712108 <col:38> 'int' <LValueToRValue>
    |           |     `-DeclRefExpr 0x55b60c7120e8 <col:38> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    |           |-CallExpr 0x55b60c712248 <line:43:17, col:44> 'void'
    |           | |-ImplicitCastExpr 0x55b60c712230 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |           | | `-DeclRefExpr 0x55b60c712180 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |           | `-BinaryOperator 0x55b60c712210 <col:35, col:37> 'int' '<'
    |           |   |-ImplicitCastExpr 0x55b60c7121e0 <col:35> 'int' <LValueToRValue>
    |           |   | `-DeclRefExpr 0x55b60c7121a0 <col:35> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |           |   `-ImplicitCastExpr 0x55b60c7121f8 <col:37> 'int' <LValueToRValue>
    |           |     `-DeclRefExpr 0x55b60c7121c0 <col:37> 'int' lvalue Var 0x55b60c710218 'bufsize' 'int'
    |           |-CallExpr 0x55b60c712320 <line:44:17, col:39> 'void'
    |           | |-ImplicitCastExpr 0x55b60c712308 <col:17> 'void (*)(int)' <FunctionToPointerDecay>
    |           | | `-DeclRefExpr 0x55b60c712270 <col:17> 'void (int)' Function 0x55b60c70fba0 '__VERIFIER_assert' 'void (int)'
    |           | `-BinaryOperator 0x55b60c7122e8 <col:35, col:38> 'int' '<='
    |           |   |-IntegerLiteral 0x55b60c712290 <col:35> 'int' 0
    |           |   `-ImplicitCastExpr 0x55b60c7122d0 <col:38> 'int' <LValueToRValue>
    |           |     `-DeclRefExpr 0x55b60c7122b0 <col:38> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |           |-UnaryOperator 0x55b60c712368 <line:45:17, col:18> 'int' postfix '++'
    |           | `-DeclRefExpr 0x55b60c712348 <col:17> 'int' lvalue Var 0x55b60c710180 'j' 'int'
    |           `-UnaryOperator 0x55b60c7123a0 <line:46:17, col:18> 'int' postfix '++'
    |             `-DeclRefExpr 0x55b60c712380 <col:17> 'int' lvalue Var 0x55b60c7100e8 'i' 'int'
    `-ReturnStmt 0x55b60c7124e0 <line:50:5, col:12>
      `-IntegerLiteral 0x55b60c7124c0 <col:12> 'int' 0
