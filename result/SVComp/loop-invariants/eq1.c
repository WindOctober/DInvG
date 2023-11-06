./Benchmark/PLDI/SVComp/loop-invariants/eq1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/eq1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55ea93294dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55ea93295660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55ea93295360 '__int128'
|-TypedefDecl 0x55ea932956d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55ea93295380 'unsigned __int128'
|-TypedefDecl 0x55ea932959d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55ea932957b0 'struct __NSConstantString_tag'
|   `-Record 0x55ea93295728 '__NSConstantString_tag'
|-TypedefDecl 0x55ea93295a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55ea93295a30 'char *'
|   `-BuiltinType 0x55ea93294e60 'char'
|-TypedefDecl 0x55ea93295d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55ea93295d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55ea93295b50 'struct __va_list_tag'
|     `-Record 0x55ea93295ac8 '__va_list_tag'
|-FunctionDecl 0x55ea932f4ab8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/eq1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ea932f4b58 prev 0x55ea932f4ab8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ea932f4ed8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55ea932f4c10 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55ea932f4c90 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55ea932f4d10 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55ea932f4d90 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55ea932f4f98 <col:99>
|-FunctionDecl 0x55ea932f5088 <line:3:1, col:69> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55ea932f53b8 <col:20, col:69>
|   `-CallExpr 0x55ea932f52d0 <col:22, col:66> 'void'
|     |-ImplicitCastExpr 0x55ea932f52b8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55ea932f5128 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55ea932f4ed8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55ea932f5328 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55ea932f5310 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55ea932f5188 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55ea932f5358 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55ea932f5340 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55ea932f51e8 <col:41> 'char [6]' lvalue "eq1.c"
|     |-ImplicitCastExpr 0x55ea932f5370 <col:50> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55ea932f5208 <col:50> 'int' 3
|     `-ImplicitCastExpr 0x55ea932f53a0 <col:53> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55ea932f5388 <col:53> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55ea932f5268 <col:53> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55ea932f54a0 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55ea932f5618 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55ea932f5558 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55ea932f58f8 <col:34, line:10:1>
|   |-IfStmt 0x55ea932f58d0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55ea932f5718 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55ea932f5700 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55ea932f56e0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55ea932f56c0 <col:9> 'int' lvalue ParmVar 0x55ea932f5558 'cond' 'int'
|   | `-CompoundStmt 0x55ea932f58b8 <col:16, line:8:3>
|   |   `-LabelStmt 0x55ea932f58a0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55ea932f5830 <col:12, col:35>
|   |       |-CallExpr 0x55ea932f5790 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55ea932f5778 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55ea932f5730 <col:13> 'void ()' Function 0x55ea932f5088 'reach_error' 'void ()'
|   |       `-CallExpr 0x55ea932f5810 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55ea932f57f8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55ea932f57b0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55ea932f4b58 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55ea932f58e8 <line:9:3>
`-FunctionDecl 0x55ea932f73e8 <line:11:1, line:25:1> line:11:5 main 'int (void)'
  `-CompoundStmt 0x55ea932f7c88 <col:16, line:25:1>
    |-DeclStmt 0x55ea932f75c0 <line:12:3, col:44>
    | `-VarDecl 0x55ea932f74d0 <col:3, col:43> col:16 used w 'unsigned int' cinit
    |   `-CallExpr 0x55ea932f75a0 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55ea932f7588 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55ea932f7538 <col:20> 'unsigned int (void)' Function 0x55ea932f54a0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x55ea932f7690 <line:13:3, col:21>
    | `-VarDecl 0x55ea932f75f0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55ea932f7678 <col:20> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55ea932f7658 <col:20> 'unsigned int' lvalue Var 0x55ea932f74d0 'w' 'unsigned int'
    |-DeclStmt 0x55ea932f7780 <line:14:3, col:44>
    | `-VarDecl 0x55ea932f76c0 <col:3, col:43> col:16 used y 'unsigned int' cinit
    |   `-CallExpr 0x55ea932f7760 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55ea932f7748 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55ea932f7728 <col:20> 'unsigned int (void)' Function 0x55ea932f54a0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x55ea932f7850 <line:15:3, col:21>
    | `-VarDecl 0x55ea932f77b0 <col:3, col:20> col:16 used z 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55ea932f7838 <col:20> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55ea932f7818 <col:20> 'unsigned int' lvalue Var 0x55ea932f76c0 'y' 'unsigned int'
    |-WhileStmt 0x55ea932f7a78 <line:16:3, line:22:3>
    | |-CallExpr 0x55ea932f78a0 <line:16:10, col:33> 'unsigned int'
    | | `-ImplicitCastExpr 0x55ea932f7888 <col:10> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    | |   `-DeclRefExpr 0x55ea932f7868 <col:10> 'unsigned int (void)' Function 0x55ea932f54a0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    | `-CompoundStmt 0x55ea932f7a60 <col:36, line:22:3>
    |   `-IfStmt 0x55ea932f7a38 <line:17:5, line:21:5> has_else
    |     |-CallExpr 0x55ea932f78f8 <line:17:9, col:32> 'unsigned int'
    |     | `-ImplicitCastExpr 0x55ea932f78e0 <col:9> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |     |   `-DeclRefExpr 0x55ea932f78c0 <col:9> 'unsigned int (void)' Function 0x55ea932f54a0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |     |-CompoundStmt 0x55ea932f7988 <col:35, line:19:5>
    |     | |-UnaryOperator 0x55ea932f7938 <line:18:7, col:9> 'unsigned int' prefix '++'
    |     | | `-DeclRefExpr 0x55ea932f7918 <col:9> 'unsigned int' lvalue Var 0x55ea932f74d0 'w' 'unsigned int'
    |     | `-UnaryOperator 0x55ea932f7970 <col:12, col:14> 'unsigned int' prefix '++'
    |     |   `-DeclRefExpr 0x55ea932f7950 <col:14> 'unsigned int' lvalue Var 0x55ea932f75f0 'x' 'unsigned int'
    |     `-CompoundStmt 0x55ea932f7a18 <line:19:12, line:21:5>
    |       |-UnaryOperator 0x55ea932f79c8 <line:20:7, col:9> 'unsigned int' prefix '--'
    |       | `-DeclRefExpr 0x55ea932f79a8 <col:9> 'unsigned int' lvalue Var 0x55ea932f76c0 'y' 'unsigned int'
    |       `-UnaryOperator 0x55ea932f7a00 <col:12, col:14> 'unsigned int' prefix '--'
    |         `-DeclRefExpr 0x55ea932f79e0 <col:14> 'unsigned int' lvalue Var 0x55ea932f77b0 'z' 'unsigned int'
    |-CallExpr 0x55ea932f7c30 <line:23:3, col:37> 'void'
    | |-ImplicitCastExpr 0x55ea932f7c18 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55ea932f7a90 <col:3> 'void (int)' Function 0x55ea932f5618 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55ea932f7bd0 <col:21, col:36> 'int' '&&'
    |   |-BinaryOperator 0x55ea932f7b20 <col:21, col:26> 'int' '=='
    |   | |-ImplicitCastExpr 0x55ea932f7af0 <col:21> 'unsigned int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x55ea932f7ab0 <col:21> 'unsigned int' lvalue Var 0x55ea932f74d0 'w' 'unsigned int'
    |   | `-ImplicitCastExpr 0x55ea932f7b08 <col:26> 'unsigned int' <LValueToRValue>
    |   |   `-DeclRefExpr 0x55ea932f7ad0 <col:26> 'unsigned int' lvalue Var 0x55ea932f75f0 'x' 'unsigned int'
    |   `-BinaryOperator 0x55ea932f7bb0 <col:31, col:36> 'int' '=='
    |     |-ImplicitCastExpr 0x55ea932f7b80 <col:31> 'unsigned int' <LValueToRValue>
    |     | `-DeclRefExpr 0x55ea932f7b40 <col:31> 'unsigned int' lvalue Var 0x55ea932f76c0 'y' 'unsigned int'
    |     `-ImplicitCastExpr 0x55ea932f7b98 <col:36> 'unsigned int' <LValueToRValue>
    |       `-DeclRefExpr 0x55ea932f7b60 <col:36> 'unsigned int' lvalue Var 0x55ea932f77b0 'z' 'unsigned int'
    `-ReturnStmt 0x55ea932f7c78 <line:24:3, col:10>
      `-IntegerLiteral 0x55ea932f7c58 <col:10> 'int' 0
1 warning generated.
