./Benchmark/PLDI/SVComp/loop-zilu/benchmark43_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark43_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x5652ddf65f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5652ddf667e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5652ddf664e0 '__int128'
|-TypedefDecl 0x5652ddf66850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5652ddf66500 'unsigned __int128'
|-TypedefDecl 0x5652ddf66b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5652ddf66930 'struct __NSConstantString_tag'
|   `-Record 0x5652ddf668a8 '__NSConstantString_tag'
|-TypedefDecl 0x5652ddf66bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5652ddf66bb0 'char *'
|   `-BuiltinType 0x5652ddf65fe0 'char'
|-TypedefDecl 0x5652ddf66ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5652ddf66e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5652ddf66cd0 'struct __va_list_tag'
|     `-Record 0x5652ddf66c48 '__va_list_tag'
|-FunctionDecl 0x5652ddfc5e58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark43_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x5652ddfc60e8 <col:24, col:35>
|   `-CallExpr 0x5652ddfc60c0 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x5652ddfc60a8 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5652ddfc6040 <col:25> 'int ()' Function 0x5652ddfc5f90 'assert' 'int ()'
|     `-IntegerLiteral 0x5652ddfc6060 <col:32> 'int' 0
|-FunctionDecl 0x5652ddfc61d0 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x5652ddfc6338 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x5652ddfc64b8 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5652ddfc63f0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5652ddfc6660 <col:34, line:10:1>
|   `-IfStmt 0x5652ddfc6648 <line:7:3, line:9:3>
|     |-UnaryOperator 0x5652ddfc6598 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5652ddfc6580 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5652ddfc6560 <col:8> 'int' lvalue ParmVar 0x5652ddfc63f0 'cond' 'int'
|     `-CompoundStmt 0x5652ddfc6630 <col:14, line:9:3>
|       `-CallExpr 0x5652ddfc6610 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x5652ddfc65f8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5652ddfc65b0 <col:5> 'void (void)' Function 0x5652ddfc5e58 'reach_error' 'void (void)'
`-FunctionDecl 0x5652ddfc66a0 <line:12:1, line:22:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x5652ddfc7358 <col:12, line:22:1>
    |-DeclStmt 0x5652ddfc6840 <line:13:3, col:34>
    | `-VarDecl 0x5652ddfc6758 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x5652ddfc6820 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5652ddfc6808 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5652ddfc67c0 <col:11> 'int (void)' Function 0x5652ddfc61d0 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x5652ddfc6930 <line:14:3, col:34>
    | `-VarDecl 0x5652ddfc6870 <col:3, col:33> col:7 used y 'int' cinit
    |   `-CallExpr 0x5652ddfc6910 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5652ddfc68f8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5652ddfc68d8 <col:11> 'int (void)' Function 0x5652ddfc61d0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x5652ddfc6ac0 <line:15:3, col:37>
    | |-UnaryOperator 0x5652ddfc6a78 <col:7, col:27> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5652ddfc6a58 <col:8, col:27> 'int'
    | |   `-BinaryOperator 0x5652ddfc6a38 <col:9, col:24> 'int' '&&'
    | |     |-BinaryOperator 0x5652ddfc69a0 <col:9, col:13> 'int' '<'
    | |     | |-ImplicitCastExpr 0x5652ddfc6988 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x5652ddfc6948 <col:9> 'int' lvalue Var 0x5652ddfc6758 'x' 'int'
    | |     | `-IntegerLiteral 0x5652ddfc6968 <col:13> 'int' 100
    | |     `-BinaryOperator 0x5652ddfc6a18 <col:20, col:24> 'int' '<'
    | |       |-ImplicitCastExpr 0x5652ddfc6a00 <col:20> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5652ddfc69c0 <col:20> 'int' lvalue Var 0x5652ddfc6870 'y' 'int'
    | |       `-IntegerLiteral 0x5652ddfc69e0 <col:24> 'int' 100
    | `-ReturnStmt 0x5652ddfc6ab0 <col:30, col:37>
    |   `-IntegerLiteral 0x5652ddfc6a90 <col:37> 'int' 0
    |-WhileStmt 0x5652ddfc6d78 <line:16:3, line:19:3>
    | |-BinaryOperator 0x5652ddfc6bc8 <line:16:10, col:25> 'int' '&&'
    | | |-BinaryOperator 0x5652ddfc6b30 <col:10, col:14> 'int' '<'
    | | | |-ImplicitCastExpr 0x5652ddfc6b18 <col:10> 'int' <LValueToRValue>
    | | | | `-DeclRefExpr 0x5652ddfc6ad8 <col:10> 'int' lvalue Var 0x5652ddfc6758 'x' 'int'
    | | | `-IntegerLiteral 0x5652ddfc6af8 <col:14> 'int' 100
    | | `-BinaryOperator 0x5652ddfc6ba8 <col:21, col:25> 'int' '<'
    | |   |-ImplicitCastExpr 0x5652ddfc6b90 <col:21> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x5652ddfc6b50 <col:21> 'int' lvalue Var 0x5652ddfc6870 'y' 'int'
    | |   `-IntegerLiteral 0x5652ddfc6b70 <col:25> 'int' 100
    | `-CompoundStmt 0x5652ddfc6d58 <col:30, line:19:3>
    |   |-BinaryOperator 0x5652ddfc6c80 <line:17:5, col:9> 'int' '='
    |   | |-DeclRefExpr 0x5652ddfc6be8 <col:5> 'int' lvalue Var 0x5652ddfc6758 'x' 'int'
    |   | `-BinaryOperator 0x5652ddfc6c60 <col:7, col:9> 'int' '+'
    |   |   |-ImplicitCastExpr 0x5652ddfc6c48 <col:7> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x5652ddfc6c08 <col:7> 'int' lvalue Var 0x5652ddfc6758 'x' 'int'
    |   |   `-IntegerLiteral 0x5652ddfc6c28 <col:9> 'int' 1
    |   `-BinaryOperator 0x5652ddfc6d38 <line:18:5, col:9> 'int' '='
    |     |-DeclRefExpr 0x5652ddfc6ca0 <col:5> 'int' lvalue Var 0x5652ddfc6870 'y' 'int'
    |     `-BinaryOperator 0x5652ddfc6d18 <col:7, col:9> 'int' '+'
    |       |-ImplicitCastExpr 0x5652ddfc6d00 <col:7> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x5652ddfc6cc0 <col:7> 'int' lvalue Var 0x5652ddfc6870 'y' 'int'
    |       `-IntegerLiteral 0x5652ddfc6ce0 <col:9> 'int' 1
    |-CallExpr 0x5652ddfc7300 <line:20:3, col:41> 'void'
    | |-ImplicitCastExpr 0x5652ddfc72e8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5652ddfc7190 <col:3> 'void (int)' Function 0x5652ddfc64b8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5652ddfc72a0 <col:21, col:38> 'int' '||'
    |   |-BinaryOperator 0x5652ddfc7208 <col:21, col:26> 'int' '=='
    |   | |-ImplicitCastExpr 0x5652ddfc71f0 <col:21> 'int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x5652ddfc71b0 <col:21> 'int' lvalue Var 0x5652ddfc6758 'x' 'int'
    |   | `-IntegerLiteral 0x5652ddfc71d0 <col:26> 'int' 100
    |   `-BinaryOperator 0x5652ddfc7280 <col:33, col:38> 'int' '=='
    |     |-ImplicitCastExpr 0x5652ddfc7268 <col:33> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x5652ddfc7228 <col:33> 'int' lvalue Var 0x5652ddfc6870 'y' 'int'
    |     `-IntegerLiteral 0x5652ddfc7248 <col:38> 'int' 100
    `-ReturnStmt 0x5652ddfc7348 <line:21:3, col:10>
      `-IntegerLiteral 0x5652ddfc7328 <col:10> 'int' 0
1 warning generated.
