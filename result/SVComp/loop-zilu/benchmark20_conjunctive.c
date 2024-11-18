./Benchmark/PLDI/SVComp/loop-zilu/benchmark20_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark20_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55c7877b7f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55c7877b87e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55c7877b84e0 '__int128'
|-TypedefDecl 0x55c7877b8850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55c7877b8500 'unsigned __int128'
|-TypedefDecl 0x55c7877b8b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55c7877b8930 'struct __NSConstantString_tag'
|   `-Record 0x55c7877b88a8 '__NSConstantString_tag'
|-TypedefDecl 0x55c7877b8bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55c7877b8bb0 'char *'
|   `-BuiltinType 0x55c7877b7fe0 'char'
|-TypedefDecl 0x55c7877b8ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55c7877b8e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55c7877b8cd0 'struct __va_list_tag'
|     `-Record 0x55c7877b8c48 '__va_list_tag'
|-FunctionDecl 0x55c787817f38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark20_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55c7878181c8 <col:24, col:35>
|   `-CallExpr 0x55c7878181a0 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55c787818188 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55c787818120 <col:25> 'int ()' Function 0x55c787818070 'assert' 'int ()'
|     `-IntegerLiteral 0x55c787818140 <col:32> 'int' 0
|-FunctionDecl 0x55c7878182b0 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55c787818418 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55c787818598 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55c7878184d0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55c787818740 <col:34, line:10:1>
|   `-IfStmt 0x55c787818728 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55c787818678 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55c787818660 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55c787818640 <col:8> 'int' lvalue ParmVar 0x55c7878184d0 'cond' 'int'
|     `-CompoundStmt 0x55c787818710 <col:14, line:9:3>
|       `-CallExpr 0x55c7878186f0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55c7878186d8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55c787818690 <col:5> 'void (void)' Function 0x55c787817f38 'reach_error' 'void (void)'
`-FunctionDecl 0x55c787818780 <line:23:1, line:35:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x55c7878194e8 <col:12, line:35:1>
    |-DeclStmt 0x55c787818920 <line:24:3, col:34>
    | `-VarDecl 0x55c787818838 <col:3, col:33> col:7 used i 'int' cinit
    |   `-CallExpr 0x55c787818900 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55c7878188e8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55c7878188a0 <col:11> 'int (void)' Function 0x55c7878182b0 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55c787818a10 <line:25:3, col:34>
    | `-VarDecl 0x55c787818950 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x55c7878189f0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55c7878189d8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55c7878189b8 <col:11> 'int (void)' Function 0x55c7878182b0 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55c787818b00 <line:26:3, col:36>
    | `-VarDecl 0x55c787818a40 <col:3, col:35> col:7 used sum 'int' cinit
    |   `-CallExpr 0x55c787818ae0 <col:13, col:35> 'int'
    |     `-ImplicitCastExpr 0x55c787818ac8 <col:13> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55c787818aa8 <col:13> 'int (void)' Function 0x55c7878182b0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55c787818dc0 <line:28:3, col:51>
    | |-UnaryOperator 0x55c787818d78 <col:7, col:41> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55c787818d58 <col:8, col:41> 'int'
    | |   `-BinaryOperator 0x55c787818d38 <col:9, col:40> 'int' '&&'
    | |     |-BinaryOperator 0x55c787818ca0 <col:9, col:28> 'int' '&&'
    | |     | |-BinaryOperator 0x55c787818c08 <col:9, col:20> 'int' '&&'
    | |     | | |-BinaryOperator 0x55c787818b70 <col:9, col:12> 'int' '=='
    | |     | | | |-ImplicitCastExpr 0x55c787818b58 <col:9> 'int' <LValueToRValue>
    | |     | | | | `-DeclRefExpr 0x55c787818b18 <col:9> 'int' lvalue Var 0x55c787818838 'i' 'int'
    | |     | | | `-IntegerLiteral 0x55c787818b38 <col:12> 'int' 0
    | |     | | `-BinaryOperator 0x55c787818be8 <col:17, col:20> 'int' '>='
    | |     | |   |-ImplicitCastExpr 0x55c787818bd0 <col:17> 'int' <LValueToRValue>
    | |     | |   | `-DeclRefExpr 0x55c787818b90 <col:17> 'int' lvalue Var 0x55c787818950 'n' 'int'
    | |     | |   `-IntegerLiteral 0x55c787818bb0 <col:20> 'int' 0
    | |     | `-BinaryOperator 0x55c787818c80 <col:25, col:28> 'int' '<='
    | |     |   |-ImplicitCastExpr 0x55c787818c68 <col:25> 'int' <LValueToRValue>
    | |     |   | `-DeclRefExpr 0x55c787818c28 <col:25> 'int' lvalue Var 0x55c787818950 'n' 'int'
    | |     |   `-IntegerLiteral 0x55c787818c48 <col:28> 'int' 100
    | |     `-BinaryOperator 0x55c787818d18 <col:35, col:40> 'int' '=='
    | |       |-ImplicitCastExpr 0x55c787818d00 <col:35> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x55c787818cc0 <col:35> 'int' lvalue Var 0x55c787818a40 'sum' 'int'
    | |       `-IntegerLiteral 0x55c787818ce0 <col:40> 'int' 0
    | `-ReturnStmt 0x55c787818db0 <col:44, col:51>
    |   `-IntegerLiteral 0x55c787818d90 <col:51> 'int' 0
    |-WhileStmt 0x55c787819398 <line:29:3, line:32:3>
    | |-BinaryOperator 0x55c787818e48 <line:29:10, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x55c787818e18 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55c787818dd8 <col:10> 'int' lvalue Var 0x55c787818838 'i' 'int'
    | | `-ImplicitCastExpr 0x55c787818e30 <col:12> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55c787818df8 <col:12> 'int' lvalue Var 0x55c787818950 'n' 'int'
    | `-CompoundStmt 0x55c787819378 <col:15, line:32:3>
    |   |-BinaryOperator 0x55c787819320 <line:30:5, col:17> 'int' '='
    |   | |-DeclRefExpr 0x55c787819270 <col:5> 'int' lvalue Var 0x55c787818a40 'sum' 'int'
    |   | `-BinaryOperator 0x55c787819300 <col:11, col:17> 'int' '+'
    |   |   |-ImplicitCastExpr 0x55c7878192d0 <col:11> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55c787819290 <col:11> 'int' lvalue Var 0x55c787818a40 'sum' 'int'
    |   |   `-ImplicitCastExpr 0x55c7878192e8 <col:17> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x55c7878192b0 <col:17> 'int' lvalue Var 0x55c787818838 'i' 'int'
    |   `-UnaryOperator 0x55c787819360 <line:31:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x55c787819340 <col:5> 'int' lvalue Var 0x55c787818838 'i' 'int'
    |-CallExpr 0x55c787819490 <line:33:3, col:27> 'void'
    | |-ImplicitCastExpr 0x55c787819478 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55c7878193b0 <col:3> 'void (int)' Function 0x55c787818598 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55c787819428 <col:21, col:26> 'int' '>='
    |   |-ImplicitCastExpr 0x55c787819410 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55c7878193d0 <col:21> 'int' lvalue Var 0x55c787818a40 'sum' 'int'
    |   `-IntegerLiteral 0x55c7878193f0 <col:26> 'int' 0
    `-ReturnStmt 0x55c7878194d8 <line:34:3, col:10>
      `-IntegerLiteral 0x55c7878194b8 <col:10> 'int' 0
1 warning generated.
