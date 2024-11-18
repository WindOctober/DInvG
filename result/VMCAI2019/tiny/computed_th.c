./Benchmark/PLDI/VMCAI2019/tiny/computed_th.c
[info] Using default compilation options.
TranslationUnitDecl 0x562e10358dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x562e10359660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x562e10359360 '__int128'
|-TypedefDecl 0x562e103596d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562e10359380 'unsigned __int128'
|-TypedefDecl 0x562e103599d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x562e103597b0 'struct __NSConstantString_tag'
|   `-Record 0x562e10359728 '__NSConstantString_tag'
|-TypedefDecl 0x562e10359a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562e10359a30 'char *'
|   `-BuiltinType 0x562e10358e60 'char'
|-TypedefDecl 0x562e10359d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562e10359d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562e10359b50 'struct __va_list_tag'
|     `-Record 0x562e10359ac8 '__va_list_tag'
|-FunctionDecl 0x562e103b8df0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/computed_th.c:1:1, col:18> col:12 used undet 'int ()' extern
|-FunctionDecl 0x562e103b9108 <line:29:1, line:51:1> line:29:6 used computed_th 'void (int *, int, int)'
| |-ParmVarDecl 0x562e103b8f20 <col:18, col:24> col:24 used r 'int *'
| |-ParmVarDecl 0x562e103b8fa0 <col:27, col:31> col:31 used n 'int'
| |-ParmVarDecl 0x562e103b9020 <col:34, col:38> col:38 used a 'int'
| `-CompoundStmt 0x562e103b98d0 <col:40, line:51:1>
|   |-DeclStmt 0x562e103b9240 <line:30:5, col:10>
|   | `-VarDecl 0x562e103b91d8 <col:5, col:9> col:9 used i 'int'
|   |-DeclStmt 0x562e103b92d8 <line:31:5, col:10>
|   | `-VarDecl 0x562e103b9270 <col:5, col:9> col:9 used j 'int'
|   |-DeclStmt 0x562e103b9370 <line:32:5, col:11>
|   | `-VarDecl 0x562e103b9308 <col:5, col:9> col:9 used th 'int'
|   |-IfStmt 0x562e103b94a8 <line:34:5, line:35:9>
|   | |-BinaryOperator 0x562e103b9478 <line:34:8, col:21> 'int' '||'
|   | | |-BinaryOperator 0x562e103b93e0 <col:8, col:12> 'int' '<'
|   | | | |-ImplicitCastExpr 0x562e103b93c8 <col:8> 'int' <LValueToRValue>
|   | | | | `-DeclRefExpr 0x562e103b9388 <col:8> 'int' lvalue ParmVar 0x562e103b8fa0 'n' 'int'
|   | | | `-IntegerLiteral 0x562e103b93a8 <col:12> 'int' 0
|   | | `-BinaryOperator 0x562e103b9458 <col:17, col:21> 'int' '<'
|   | |   |-ImplicitCastExpr 0x562e103b9440 <col:17> 'int' <LValueToRValue>
|   | |   | `-DeclRefExpr 0x562e103b9400 <col:17> 'int' lvalue ParmVar 0x562e103b9020 'a' 'int'
|   | |   `-IntegerLiteral 0x562e103b9420 <col:21> 'int' 0
|   | `-ReturnStmt 0x562e103b9498 <line:35:9>
|   |-BinaryOperator 0x562e103b9500 <line:37:5, col:10> 'int' '='
|   | |-DeclRefExpr 0x562e103b94c0 <col:5> 'int' lvalue Var 0x562e103b9308 'th' 'int'
|   | `-IntegerLiteral 0x562e103b94e0 <col:10> 'int' 0
|   |-BinaryOperator 0x562e103b9560 <line:38:5, col:9> 'int' '='
|   | |-DeclRefExpr 0x562e103b9520 <col:5> 'int' lvalue Var 0x562e103b91d8 'i' 'int'
|   | `-IntegerLiteral 0x562e103b9540 <col:9> 'int' 0
|   |-WhileStmt 0x562e103b96a0 <line:40:5, line:43:5>
|   | |-BinaryOperator 0x562e103b95f0 <line:40:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x562e103b95c0 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x562e103b9580 <col:11> 'int' lvalue Var 0x562e103b91d8 'i' 'int'
|   | | `-ImplicitCastExpr 0x562e103b95d8 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x562e103b95a0 <col:15> 'int' lvalue ParmVar 0x562e103b8fa0 'n' 'int'
|   | `-CompoundStmt 0x562e103b9680 <col:17, line:43:5>
|   |   |-UnaryOperator 0x562e103b9630 <line:41:9, col:11> 'int' postfix '++'
|   |   | `-DeclRefExpr 0x562e103b9610 <col:9> 'int' lvalue Var 0x562e103b9308 'th' 'int'
|   |   `-UnaryOperator 0x562e103b9668 <line:42:9, col:10> 'int' postfix '++'
|   |     `-DeclRefExpr 0x562e103b9648 <col:9> 'int' lvalue Var 0x562e103b91d8 'i' 'int'
|   |-BinaryOperator 0x562e103b9710 <line:45:5, col:9> 'int' '='
|   | |-DeclRefExpr 0x562e103b96b8 <col:5> 'int' lvalue Var 0x562e103b9270 'j' 'int'
|   | `-ImplicitCastExpr 0x562e103b96f8 <col:9> 'int' <LValueToRValue>
|   |   `-DeclRefExpr 0x562e103b96d8 <col:9> 'int' lvalue ParmVar 0x562e103b9020 'a' 'int'
|   |-WhileStmt 0x562e103b9810 <line:46:5, line:48:5>
|   | |-BinaryOperator 0x562e103b97a0 <line:46:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x562e103b9770 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x562e103b9730 <col:11> 'int' lvalue Var 0x562e103b9270 'j' 'int'
|   | | `-ImplicitCastExpr 0x562e103b9788 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x562e103b9750 <col:15> 'int' lvalue Var 0x562e103b9308 'th' 'int'
|   | `-CompoundStmt 0x562e103b97f8 <col:18, line:48:5>
|   |   `-UnaryOperator 0x562e103b97e0 <line:47:9, col:10> 'int' postfix '++'
|   |     `-DeclRefExpr 0x562e103b97c0 <col:9> 'int' lvalue Var 0x562e103b9270 'j' 'int'
|   `-BinaryOperator 0x562e103b98b0 <line:50:5, col:10> 'int' '='
|     |-UnaryOperator 0x562e103b9860 <col:5, col:6> 'int' lvalue prefix '*' cannot overflow
|     | `-ImplicitCastExpr 0x562e103b9848 <col:6> 'int *' <LValueToRValue>
|     |   `-DeclRefExpr 0x562e103b9828 <col:6> 'int *' lvalue ParmVar 0x562e103b8f20 'r' 'int *'
|     `-ImplicitCastExpr 0x562e103b9898 <col:10> 'int' <LValueToRValue>
|       `-DeclRefExpr 0x562e103b9878 <col:10> 'int' lvalue Var 0x562e103b9270 'j' 'int'
`-FunctionDecl 0x562e103b9978 <line:53:1, line:63:1> line:53:6 test 'void ()'
  `-CompoundStmt 0x562e103ba1f8 <line:54:1, line:63:1>
    |-DeclStmt 0x562e103b9a98 <line:55:5, col:10>
    | `-VarDecl 0x562e103b9a30 <col:5, col:9> col:9 used r 'int'
    |-DeclStmt 0x562e103b9b30 <line:56:5, col:10>
    | `-VarDecl 0x562e103b9ac8 <col:5, col:9> col:9 used n 'int'
    |-DeclStmt 0x562e103b9bc8 <line:57:5, col:10>
    | `-VarDecl 0x562e103b9b60 <col:5, col:9> col:9 used a 'int'
    |-BinaryOperator 0x562e103b9c80 <line:59:5, col:15> 'int' '='
    | |-DeclRefExpr 0x562e103b9be0 <col:5> 'int' lvalue Var 0x562e103b9ac8 'n' 'int'
    | `-CallExpr 0x562e103b9c60 <col:9, col:15> 'int'
    |   `-ImplicitCastExpr 0x562e103b9c48 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x562e103b9c00 <col:9> 'int ()' Function 0x562e103b8df0 'undet' 'int ()'
    |-BinaryOperator 0x562e103b9d18 <line:60:5, col:15> 'int' '='
    | |-DeclRefExpr 0x562e103b9ca0 <col:5> 'int' lvalue Var 0x562e103b9b60 'a' 'int'
    | `-CallExpr 0x562e103b9cf8 <col:9, col:15> 'int'
    |   `-ImplicitCastExpr 0x562e103b9ce0 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x562e103b9cc0 <col:9> 'int ()' Function 0x562e103b8df0 'undet' 'int ()'
    `-CallExpr 0x562e103ba190 <line:62:5, col:25> 'void'
      |-ImplicitCastExpr 0x562e103ba178 <col:5> 'void (*)(int *, int, int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x562e103b9d38 <col:5> 'void (int *, int, int)' Function 0x562e103b9108 'computed_th' 'void (int *, int, int)'
      |-UnaryOperator 0x562e103b9d78 <col:17, col:18> 'int *' prefix '&' cannot overflow
      | `-DeclRefExpr 0x562e103b9d58 <col:18> 'int' lvalue Var 0x562e103b9a30 'r' 'int'
      |-ImplicitCastExpr 0x562e103ba1c8 <col:21> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x562e103ba110 <col:21> 'int' lvalue Var 0x562e103b9ac8 'n' 'int'
      `-ImplicitCastExpr 0x562e103ba1e0 <col:24> 'int' <LValueToRValue>
        `-DeclRefExpr 0x562e103ba130 <col:24> 'int' lvalue Var 0x562e103b9b60 'a' 'int'
