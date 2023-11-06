./Benchmark/PLDI/VMCAI2019/malardalen/fabs_inline.c
[info] Using default compilation options.
TranslationUnitDecl 0x55f3e6f44eb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55f3e6f45750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55f3e6f45450 '__int128'
|-TypedefDecl 0x55f3e6f457c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55f3e6f45470 'unsigned __int128'
|-TypedefDecl 0x55f3e6f45ac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55f3e6f458a0 'struct __NSConstantString_tag'
|   `-Record 0x55f3e6f45818 '__NSConstantString_tag'
|-TypedefDecl 0x55f3e6f45b60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55f3e6f45b20 'char *'
|   `-BuiltinType 0x55f3e6f44f50 'char'
|-TypedefDecl 0x55f3e6f45e58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55f3e6f45e00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55f3e6f45c40 'struct __va_list_tag'
|     `-Record 0x55f3e6f45bb8 '__va_list_tag'
|-FunctionDecl 0x55f3e6fa4ce0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/malardalen/fabs_inline.c:2:1, line:19:1> line:2:15 fabs 'double (double, int *, int *)' static
| |-ParmVarDecl 0x55f3e6fa4ac8 <col:20, col:27> col:27 used n 'double'
| |-ParmVarDecl 0x55f3e6fa4b70 <line:3:9, col:15> col:15 used cptr_fabs_1 'int *'
| |-ParmVarDecl 0x55f3e6fa4bf0 <line:4:9, col:15> col:15 used cptr_fabs_2 'int *'
| `-CompoundStmt 0x55f3e6fa5358 <line:5:1, line:19:1>
|   |-DeclStmt 0x55f3e6fa4e60 <line:6:3, col:12>
|   | `-VarDecl 0x55f3e6fa4df8 <col:3, col:10> col:10 used f 'double'
|   |-BinaryOperator 0x55f3e6fa4ee8 <line:7:3, col:18> 'int' '='
|   | |-UnaryOperator 0x55f3e6fa4eb0 <col:3, col:4> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x55f3e6fa4e98 <col:4> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55f3e6fa4e78 <col:4> 'int *' lvalue ParmVar 0x55f3e6fa4b70 'cptr_fabs_1' 'int *'
|   | `-IntegerLiteral 0x55f3e6fa4ec8 <col:18> 'int' 0
|   |-BinaryOperator 0x55f3e6fa4f78 <line:8:3, col:18> 'int' '='
|   | |-UnaryOperator 0x55f3e6fa4f40 <col:3, col:4> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x55f3e6fa4f28 <col:4> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55f3e6fa4f08 <col:4> 'int *' lvalue ParmVar 0x55f3e6fa4bf0 'cptr_fabs_2' 'int *'
|   | `-IntegerLiteral 0x55f3e6fa4f58 <col:18> 'int' 0
|   `-CompoundStmt 0x55f3e6fa5338 <line:9:3, line:18:1>
|     |-IfStmt 0x55f3e6fa52a8 <line:10:3, line:16:3> has_else
|     | |-BinaryOperator 0x55f3e6fa5030 <line:10:7, col:21> 'int' '>='
|     | | |-ImplicitCastExpr 0x55f3e6fa5018 <col:7> 'double' <LValueToRValue>
|     | | | `-DeclRefExpr 0x55f3e6fa4f98 <col:7> 'double' lvalue ParmVar 0x55f3e6fa4ac8 'n' 'double'
|     | | `-CStyleCastExpr 0x55f3e6fa4ff0 <col:12, col:21> 'double' <IntegralToFloating>
|     | |   `-IntegerLiteral 0x55f3e6fa4fb8 <col:21> 'int' 0
|     | |-CompoundStmt 0x55f3e6fa5150 <col:24, line:13:3>
|     | | |-UnaryOperator 0x55f3e6fa50c0 <line:11:5, col:20> 'int' postfix '++'
|     | | | `-ParenExpr 0x55f3e6fa50a0 <col:5, col:18> 'int' lvalue
|     | | |   `-UnaryOperator 0x55f3e6fa5088 <col:6, col:7> 'int' lvalue prefix '*' cannot overflow
|     | | |     `-ImplicitCastExpr 0x55f3e6fa5070 <col:7> 'int *' <LValueToRValue>
|     | | |       `-DeclRefExpr 0x55f3e6fa5050 <col:7> 'int *' lvalue ParmVar 0x55f3e6fa4b70 'cptr_fabs_1' 'int *'
|     | | `-BinaryOperator 0x55f3e6fa5130 <line:12:5, col:9> 'double' '='
|     | |   |-DeclRefExpr 0x55f3e6fa50d8 <col:5> 'double' lvalue Var 0x55f3e6fa4df8 'f' 'double'
|     | |   `-ImplicitCastExpr 0x55f3e6fa5118 <col:9> 'double' <LValueToRValue>
|     | |     `-DeclRefExpr 0x55f3e6fa50f8 <col:9> 'double' lvalue ParmVar 0x55f3e6fa4ac8 'n' 'double'
|     | `-CompoundStmt 0x55f3e6fa5288 <line:13:10, line:16:3>
|     |   |-UnaryOperator 0x55f3e6fa51e0 <line:14:5, col:20> 'int' postfix '++'
|     |   | `-ParenExpr 0x55f3e6fa51c0 <col:5, col:18> 'int' lvalue
|     |   |   `-UnaryOperator 0x55f3e6fa51a8 <col:6, col:7> 'int' lvalue prefix '*' cannot overflow
|     |   |     `-ImplicitCastExpr 0x55f3e6fa5190 <col:7> 'int *' <LValueToRValue>
|     |   |       `-DeclRefExpr 0x55f3e6fa5170 <col:7> 'int *' lvalue ParmVar 0x55f3e6fa4bf0 'cptr_fabs_2' 'int *'
|     |   `-BinaryOperator 0x55f3e6fa5268 <line:15:5, col:11> 'double' '='
|     |     |-DeclRefExpr 0x55f3e6fa51f8 <col:5> 'double' lvalue Var 0x55f3e6fa4df8 'f' 'double'
|     |     `-UnaryOperator 0x55f3e6fa5250 <col:9, col:11> 'double' prefix '-'
|     |       `-ImplicitCastExpr 0x55f3e6fa5238 <col:11> 'double' <LValueToRValue>
|     |         `-DeclRefExpr 0x55f3e6fa5218 <col:11> 'double' lvalue ParmVar 0x55f3e6fa4ac8 'n' 'double'
|     `-ReturnStmt 0x55f3e6fa5328 <line:17:3, col:12>
|       `-ImplicitCastExpr 0x55f3e6fa5310 <col:10, col:12> 'double' <LValueToRValue>
|         `-ParenExpr 0x55f3e6fa52f0 <col:10, col:12> 'double' lvalue
|           `-DeclRefExpr 0x55f3e6fa52d0 <col:11> 'double' lvalue Var 0x55f3e6fa4df8 'f' 'double'
`-FunctionDecl 0x55f3e6fa53e0 <line:21:1, line:45:1> line:21:5 main 'int ()'
  `-CompoundStmt 0x55f3e6fa70e8 <line:22:1, line:45:1>
    |-DeclStmt 0x55f3e6fa5500 <line:23:5, col:13>
    | `-VarDecl 0x55f3e6fa5498 <col:5, col:12> col:12 used n 'double'
    |-DeclStmt 0x55f3e6fa5598 <line:24:5, col:20>
    | `-VarDecl 0x55f3e6fa5530 <col:5, col:9> col:9 used cptr_fabs_1 'int'
    |-DeclStmt 0x55f3e6fa5630 <line:25:5, col:20>
    | `-VarDecl 0x55f3e6fa55c8 <col:5, col:9> col:9 used cptr_fabs_2 'int'
    |-DeclStmt 0x55f3e6fa56c8 <line:27:5, col:13>
    | `-VarDecl 0x55f3e6fa5660 <col:5, col:12> col:12 used r 'double'
    |-CompoundStmt 0x55f3e6fa7080 <line:28:5, line:41:5>
    | |-DeclStmt 0x55f3e6fa5760 <line:29:9, col:17>
    | | `-VarDecl 0x55f3e6fa56f8 <col:9, col:16> col:16 used f 'double'
    | |-BinaryOperator 0x55f3e6fa57b8 <line:30:9, col:23> 'int' '='
    | | |-DeclRefExpr 0x55f3e6fa5778 <col:9> 'int' lvalue Var 0x55f3e6fa5530 'cptr_fabs_1' 'int'
    | | `-IntegerLiteral 0x55f3e6fa5798 <col:23> 'int' 0
    | |-BinaryOperator 0x55f3e6fa5818 <line:31:9, col:23> 'int' '='
    | | |-DeclRefExpr 0x55f3e6fa57d8 <col:9> 'int' lvalue Var 0x55f3e6fa55c8 'cptr_fabs_2' 'int'
    | | `-IntegerLiteral 0x55f3e6fa57f8 <col:23> 'int' 0
    | |-IfStmt 0x55f3e6fa6fe0 <line:33:9, line:39:9> has_else
    | | |-BinaryOperator 0x55f3e6fa58d0 <line:33:12, col:25> 'int' '>='
    | | | |-ImplicitCastExpr 0x55f3e6fa58b8 <col:12> 'double' <LValueToRValue>
    | | | | `-DeclRefExpr 0x55f3e6fa5838 <col:12> 'double' lvalue Var 0x55f3e6fa5498 'n' 'double'
    | | | `-CStyleCastExpr 0x55f3e6fa5890 <col:17, col:25> 'double' <IntegralToFloating>
    | | |   `-IntegerLiteral 0x55f3e6fa5858 <col:25> 'int' 0
    | | |-CompoundStmt 0x55f3e6fa59a0 <col:28, line:36:9>
    | | | |-UnaryOperator 0x55f3e6fa5910 <line:34:13, col:24> 'int' postfix '++'
    | | | | `-DeclRefExpr 0x55f3e6fa58f0 <col:13> 'int' lvalue Var 0x55f3e6fa5530 'cptr_fabs_1' 'int'
    | | | `-BinaryOperator 0x55f3e6fa5980 <line:35:13, col:17> 'double' '='
    | | |   |-DeclRefExpr 0x55f3e6fa5928 <col:13> 'double' lvalue Var 0x55f3e6fa56f8 'f' 'double'
    | | |   `-ImplicitCastExpr 0x55f3e6fa5968 <col:17> 'double' <LValueToRValue>
    | | |     `-DeclRefExpr 0x55f3e6fa5948 <col:17> 'double' lvalue Var 0x55f3e6fa5498 'n' 'double'
    | | `-CompoundStmt 0x55f3e6fa5a88 <line:36:16, line:39:9>
    | |   |-UnaryOperator 0x55f3e6fa59e0 <line:37:13, col:24> 'int' postfix '++'
    | |   | `-DeclRefExpr 0x55f3e6fa59c0 <col:13> 'int' lvalue Var 0x55f3e6fa55c8 'cptr_fabs_2' 'int'
    | |   `-BinaryOperator 0x55f3e6fa5a68 <line:38:13, col:18> 'double' '='
    | |     |-DeclRefExpr 0x55f3e6fa59f8 <col:13> 'double' lvalue Var 0x55f3e6fa56f8 'f' 'double'
    | |     `-UnaryOperator 0x55f3e6fa5a50 <col:17, col:18> 'double' prefix '-'
    | |       `-ImplicitCastExpr 0x55f3e6fa5a38 <col:18> 'double' <LValueToRValue>
    | |         `-DeclRefExpr 0x55f3e6fa5a18 <col:18> 'double' lvalue Var 0x55f3e6fa5498 'n' 'double'
    | `-BinaryOperator 0x55f3e6fa7060 <line:40:9, col:13> 'double' '='
    |   |-DeclRefExpr 0x55f3e6fa7008 <col:9> 'double' lvalue Var 0x55f3e6fa5660 'r' 'double'
    |   `-ImplicitCastExpr 0x55f3e6fa7048 <col:13> 'double' <LValueToRValue>
    |     `-DeclRefExpr 0x55f3e6fa7028 <col:13> 'double' lvalue Var 0x55f3e6fa56f8 'f' 'double'
    `-ReturnStmt 0x55f3e6fa70d8 <line:44:5, col:12>
      `-IntegerLiteral 0x55f3e6fa70b8 <col:12> 'int' 0
