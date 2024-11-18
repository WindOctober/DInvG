./Benchmark/PLDI/SVComp/loop-zilu/benchmark10_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark10_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55b7d9463f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55b7d94647e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55b7d94644e0 '__int128'
|-TypedefDecl 0x55b7d9464850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55b7d9464500 'unsigned __int128'
|-TypedefDecl 0x55b7d9464b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55b7d9464930 'struct __NSConstantString_tag'
|   `-Record 0x55b7d94648a8 '__NSConstantString_tag'
|-TypedefDecl 0x55b7d9464bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55b7d9464bb0 'char *'
|   `-BuiltinType 0x55b7d9463fe0 'char'
|-TypedefDecl 0x55b7d9464ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55b7d9464e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55b7d9464cd0 'struct __va_list_tag'
|     `-Record 0x55b7d9464c48 '__va_list_tag'
|-FunctionDecl 0x55b7d94c3f08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark10_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55b7d94c4198 <col:24, col:35>
|   `-CallExpr 0x55b7d94c4170 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55b7d94c4158 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55b7d94c40f0 <col:25> 'int ()' Function 0x55b7d94c4040 'assert' 'int ()'
|     `-IntegerLiteral 0x55b7d94c4110 <col:32> 'int' 0
|-FunctionDecl 0x55b7d94c4280 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55b7d94c43e8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55b7d94c4568 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55b7d94c44a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55b7d94c4710 <col:34, line:10:1>
|   `-IfStmt 0x55b7d94c46f8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55b7d94c4648 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55b7d94c4630 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55b7d94c4610 <col:8> 'int' lvalue ParmVar 0x55b7d94c44a0 'cond' 'int'
|     `-CompoundStmt 0x55b7d94c46e0 <col:14, line:9:3>
|       `-CallExpr 0x55b7d94c46c0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55b7d94c46a8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55b7d94c4660 <col:5> 'void (void)' Function 0x55b7d94c3f08 'reach_error' 'void (void)'
`-FunctionDecl 0x55b7d94c4750 <line:23:1, line:35:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x55b7d94c5718 <col:12, line:35:1>
    |-DeclStmt 0x55b7d94c48f0 <line:24:3, col:34>
    | `-VarDecl 0x55b7d94c4808 <col:3, col:33> col:7 used i 'int' cinit
    |   `-CallExpr 0x55b7d94c48d0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55b7d94c48b8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55b7d94c4870 <col:11> 'int (void)' Function 0x55b7d94c4280 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55b7d94c49e0 <line:25:3, col:34>
    | `-VarDecl 0x55b7d94c4920 <col:3, col:33> col:7 used c 'int' cinit
    |   `-CallExpr 0x55b7d94c49c0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55b7d94c49a8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55b7d94c4988 <col:11> 'int (void)' Function 0x55b7d94c4280 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55b7d94c4b70 <line:27:3, col:31>
    | |-UnaryOperator 0x55b7d94c4b28 <col:7, col:21> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55b7d94c4b08 <col:8, col:21> 'int'
    | |   `-BinaryOperator 0x55b7d94c4ae8 <col:9, col:20> 'int' '&&'
    | |     |-BinaryOperator 0x55b7d94c4a50 <col:9, col:12> 'int' '=='
    | |     | |-ImplicitCastExpr 0x55b7d94c4a38 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x55b7d94c49f8 <col:9> 'int' lvalue Var 0x55b7d94c4920 'c' 'int'
    | |     | `-IntegerLiteral 0x55b7d94c4a18 <col:12> 'int' 0
    | |     `-BinaryOperator 0x55b7d94c4ac8 <col:17, col:20> 'int' '=='
    | |       |-ImplicitCastExpr 0x55b7d94c4ab0 <col:17> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x55b7d94c4a70 <col:17> 'int' lvalue Var 0x55b7d94c4808 'i' 'int'
    | |       `-IntegerLiteral 0x55b7d94c4a90 <col:20> 'int' 0
    | `-ReturnStmt 0x55b7d94c4b60 <col:24, col:31>
    |   `-IntegerLiteral 0x55b7d94c4b40 <col:31> 'int' 0
    |-WhileStmt 0x55b7d94c55c8 <line:28:3, line:32:3>
    | |-BinaryOperator 0x55b7d94c4be0 <line:28:10, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x55b7d94c4bc8 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55b7d94c4b88 <col:10> 'int' lvalue Var 0x55b7d94c4808 'i' 'int'
    | | `-IntegerLiteral 0x55b7d94c4ba8 <col:12> 'int' 100
    | `-CompoundStmt 0x55b7d94c55a0 <col:17, line:32:3>
    |   |-BinaryOperator 0x55b7d94c4cb0 <line:29:5, col:9> 'int' '='
    |   | |-DeclRefExpr 0x55b7d94c4c00 <col:5> 'int' lvalue Var 0x55b7d94c4920 'c' 'int'
    |   | `-BinaryOperator 0x55b7d94c4c90 <col:7, col:9> 'int' '+'
    |   |   |-ImplicitCastExpr 0x55b7d94c4c60 <col:7> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55b7d94c4c20 <col:7> 'int' lvalue Var 0x55b7d94c4920 'c' 'int'
    |   |   `-ImplicitCastExpr 0x55b7d94c4c78 <col:9> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x55b7d94c4c40 <col:9> 'int' lvalue Var 0x55b7d94c4808 'i' 'int'
    |   |-BinaryOperator 0x55b7d94c4d68 <line:30:5, col:9> 'int' '='
    |   | |-DeclRefExpr 0x55b7d94c4cd0 <col:5> 'int' lvalue Var 0x55b7d94c4808 'i' 'int'
    |   | `-BinaryOperator 0x55b7d94c4d48 <col:7, col:9> 'int' '+'
    |   |   |-ImplicitCastExpr 0x55b7d94c4d30 <col:7> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55b7d94c4cf0 <col:7> 'int' lvalue Var 0x55b7d94c4808 'i' 'int'
    |   |   `-IntegerLiteral 0x55b7d94c4d10 <col:9> 'int' 1
    |   `-IfStmt 0x55b7d94c4e08 <line:31:5, col:15>
    |     |-BinaryOperator 0x55b7d94c4de0 <col:9, col:12> 'int' '<='
    |     | |-ImplicitCastExpr 0x55b7d94c4dc8 <col:9> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55b7d94c4d88 <col:9> 'int' lvalue Var 0x55b7d94c4808 'i' 'int'
    |     | `-IntegerLiteral 0x55b7d94c4da8 <col:12> 'int' 0
    |     `-BreakStmt 0x55b7d94c4e00 <col:15>
    |-CallExpr 0x55b7d94c56c0 <line:33:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55b7d94c56a8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55b7d94c55e0 <col:3> 'void (int)' Function 0x55b7d94c4568 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55b7d94c5658 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x55b7d94c5640 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55b7d94c5600 <col:21> 'int' lvalue Var 0x55b7d94c4920 'c' 'int'
    |   `-IntegerLiteral 0x55b7d94c5620 <col:24> 'int' 0
    `-ReturnStmt 0x55b7d94c5708 <line:34:3, col:10>
      `-IntegerLiteral 0x55b7d94c56e8 <col:10> 'int' 0
1 warning generated.
