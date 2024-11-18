./Benchmark/PLDI/VMCAI2019/tiny/indirect.c
[info] Using default compilation options.
TranslationUnitDecl 0x55c5f8839dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55c5f883a660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55c5f883a360 '__int128'
|-TypedefDecl 0x55c5f883a6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55c5f883a380 'unsigned __int128'
|-TypedefDecl 0x55c5f883a9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55c5f883a7b0 'struct __NSConstantString_tag'
|   `-Record 0x55c5f883a728 '__NSConstantString_tag'
|-TypedefDecl 0x55c5f883aa70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55c5f883aa30 'char *'
|   `-BuiltinType 0x55c5f8839e60 'char'
|-TypedefDecl 0x55c5f883ad68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55c5f883ad10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55c5f883ab50 'struct __va_list_tag'
|     `-Record 0x55c5f883aac8 '__va_list_tag'
|-FunctionDecl 0x55c5f889a148 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/indirect.c:28:1, line:53:1> line:28:6 used indirect 'void (int *, int, int, int, int)'
| |-ParmVarDecl 0x55c5f8899e40 <col:15, col:21> col:21 used r 'int *'
| |-ParmVarDecl 0x55c5f8899ec0 <col:24, col:28> col:28 used a 'int'
| |-ParmVarDecl 0x55c5f8899f40 <col:31, col:35> col:35 used b 'int'
| |-ParmVarDecl 0x55c5f8899fc0 <col:38, col:42> col:42 used c 'int'
| |-ParmVarDecl 0x55c5f889a040 <col:45, col:49> col:49 used n 'int'
| `-CompoundStmt 0x55c5f889a958 <line:29:1, line:53:1>
|   |-IfStmt 0x55c5f889a2e0 <line:30:5, line:31:8>
|   | |-BinaryOperator 0x55c5f889a2b0 <line:30:8, col:12> 'int' '<'
|   | | |-ImplicitCastExpr 0x55c5f889a298 <col:8> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55c5f889a258 <col:8> 'int' lvalue ParmVar 0x55c5f889a040 'n' 'int'
|   | | `-IntegerLiteral 0x55c5f889a278 <col:12> 'int' 0
|   | `-ReturnStmt 0x55c5f889a2d0 <line:31:8>
|   |-DeclStmt 0x55c5f889a378 <line:33:5, col:10>
|   | `-VarDecl 0x55c5f889a310 <col:5, col:9> col:9 used i 'int'
|   |-DeclStmt 0x55c5f889a410 <line:34:5, col:10>
|   | `-VarDecl 0x55c5f889a3a8 <col:5, col:9> col:9 used j 'int'
|   |-BinaryOperator 0x55c5f889a468 <line:36:5, col:9> 'int' '='
|   | |-DeclRefExpr 0x55c5f889a428 <col:5> 'int' lvalue Var 0x55c5f889a310 'i' 'int'
|   | `-IntegerLiteral 0x55c5f889a448 <col:9> 'int' 0
|   |-BinaryOperator 0x55c5f889a4c8 <line:37:5, col:9> 'int' '='
|   | |-DeclRefExpr 0x55c5f889a488 <col:5> 'int' lvalue Var 0x55c5f889a3a8 'j' 'int'
|   | `-IntegerLiteral 0x55c5f889a4a8 <col:9> 'int' 0
|   |-WhileStmt 0x55c5f889a708 <line:39:5, line:43:5>
|   | |-BinaryOperator 0x55c5f889a558 <line:39:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x55c5f889a528 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55c5f889a4e8 <col:11> 'int' lvalue Var 0x55c5f889a310 'i' 'int'
|   | | `-ImplicitCastExpr 0x55c5f889a540 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55c5f889a508 <col:15> 'int' lvalue ParmVar 0x55c5f889a040 'n' 'int'
|   | `-CompoundStmt 0x55c5f889a6e8 <line:40:5, line:43:5>
|   |   |-BinaryOperator 0x55c5f889a610 <line:41:9, col:17> 'int' '='
|   |   | |-DeclRefExpr 0x55c5f889a578 <col:9> 'int' lvalue Var 0x55c5f889a310 'i' 'int'
|   |   | `-BinaryOperator 0x55c5f889a5f0 <col:13, col:17> 'int' '+'
|   |   |   |-ImplicitCastExpr 0x55c5f889a5d8 <col:13> 'int' <LValueToRValue>
|   |   |   | `-DeclRefExpr 0x55c5f889a598 <col:13> 'int' lvalue Var 0x55c5f889a310 'i' 'int'
|   |   |   `-IntegerLiteral 0x55c5f889a5b8 <col:17> 'int' 1
|   |   `-BinaryOperator 0x55c5f889a6c8 <line:42:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x55c5f889a630 <col:9> 'int' lvalue Var 0x55c5f889a3a8 'j' 'int'
|   |     `-BinaryOperator 0x55c5f889a6a8 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x55c5f889a690 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x55c5f889a650 <col:13> 'int' lvalue Var 0x55c5f889a3a8 'j' 'int'
|   |       `-IntegerLiteral 0x55c5f889a670 <col:17> 'int' 1
|   `-IfStmt 0x55c5f889a930 <line:45:5, line:52:5> has_else
|     |-BinaryOperator 0x55c5f889a790 <line:45:8, col:13> 'int' '>='
|     | |-ImplicitCastExpr 0x55c5f889a760 <col:8> 'int' <LValueToRValue>
|     | | `-DeclRefExpr 0x55c5f889a720 <col:8> 'int' lvalue Var 0x55c5f889a3a8 'j' 'int'
|     | `-ImplicitCastExpr 0x55c5f889a778 <col:13> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55c5f889a740 <col:13> 'int' lvalue ParmVar 0x55c5f8899fc0 'c' 'int'
|     |-CompoundStmt 0x55c5f889a858 <line:46:5, line:48:5>
|     | `-BinaryOperator 0x55c5f889a838 <line:47:9, col:14> 'int' '='
|     |   |-UnaryOperator 0x55c5f889a7e8 <col:9, col:10> 'int' lvalue prefix '*' cannot overflow
|     |   | `-ImplicitCastExpr 0x55c5f889a7d0 <col:10> 'int *' <LValueToRValue>
|     |   |   `-DeclRefExpr 0x55c5f889a7b0 <col:10> 'int *' lvalue ParmVar 0x55c5f8899e40 'r' 'int *'
|     |   `-ImplicitCastExpr 0x55c5f889a820 <col:14> 'int' <LValueToRValue>
|     |     `-DeclRefExpr 0x55c5f889a800 <col:14> 'int' lvalue ParmVar 0x55c5f8899ec0 'a' 'int'
|     `-CompoundStmt 0x55c5f889a918 <line:50:5, line:52:5>
|       `-BinaryOperator 0x55c5f889a8f8 <line:51:9, col:14> 'int' '='
|         |-UnaryOperator 0x55c5f889a8a8 <col:9, col:10> 'int' lvalue prefix '*' cannot overflow
|         | `-ImplicitCastExpr 0x55c5f889a890 <col:10> 'int *' <LValueToRValue>
|         |   `-DeclRefExpr 0x55c5f889a870 <col:10> 'int *' lvalue ParmVar 0x55c5f8899e40 'r' 'int *'
|         `-ImplicitCastExpr 0x55c5f889a8e0 <col:14> 'int' <LValueToRValue>
|           `-DeclRefExpr 0x55c5f889a8c0 <col:14> 'int' lvalue ParmVar 0x55c5f8899f40 'b' 'int'
`-FunctionDecl 0x55c5f889a9e8 <line:55:1, line:64:1> line:55:6 test 'void ()'
  `-CompoundStmt 0x55c5f889b2b8 <line:56:1, line:64:1>
    |-DeclStmt 0x55c5f889ab08 <line:57:5, col:10>
    | `-VarDecl 0x55c5f889aaa0 <col:5, col:9> col:9 used r 'int'
    |-DeclStmt 0x55c5f889aba0 <line:58:5, col:10>
    | `-VarDecl 0x55c5f889ab38 <col:5, col:9> col:9 used a 'int'
    |-DeclStmt 0x55c5f889ac38 <line:59:5, col:10>
    | `-VarDecl 0x55c5f889abd0 <col:5, col:9> col:9 used b 'int'
    |-DeclStmt 0x55c5f889acd0 <line:60:5, col:10>
    | `-VarDecl 0x55c5f889ac68 <col:5, col:9> col:9 used c 'int'
    |-DeclStmt 0x55c5f889ad68 <line:61:5, col:10>
    | `-VarDecl 0x55c5f889ad00 <col:5, col:9> col:9 used n 'int'
    `-CallExpr 0x55c5f889b210 <line:63:5, col:28> 'void'
      |-ImplicitCastExpr 0x55c5f889b1f8 <col:5> 'void (*)(int *, int, int, int, int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55c5f889ad80 <col:5> 'void (int *, int, int, int, int)' Function 0x55c5f889a148 'indirect' 'void (int *, int, int, int, int)'
      |-UnaryOperator 0x55c5f889adc0 <col:14, col:15> 'int *' prefix '&' cannot overflow
      | `-DeclRefExpr 0x55c5f889ada0 <col:15> 'int' lvalue Var 0x55c5f889aaa0 'r' 'int'
      |-ImplicitCastExpr 0x55c5f889b258 <col:18> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x55c5f889add8 <col:18> 'int' lvalue Var 0x55c5f889ab38 'a' 'int'
      |-ImplicitCastExpr 0x55c5f889b270 <col:21> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x55c5f889b170 <col:21> 'int' lvalue Var 0x55c5f889abd0 'b' 'int'
      |-ImplicitCastExpr 0x55c5f889b288 <col:24> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x55c5f889b190 <col:24> 'int' lvalue Var 0x55c5f889ac68 'c' 'int'
      `-ImplicitCastExpr 0x55c5f889b2a0 <col:27> 'int' <LValueToRValue>
        `-DeclRefExpr 0x55c5f889b1b0 <col:27> 'int' lvalue Var 0x55c5f889ad00 'n' 'int'
