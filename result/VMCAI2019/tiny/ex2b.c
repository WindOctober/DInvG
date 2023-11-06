./Benchmark/PLDI/VMCAI2019/tiny/ex2b.c
[info] Using default compilation options.
TranslationUnitDecl 0x55ea0227bd88 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55ea0227c620 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55ea0227c320 '__int128'
|-TypedefDecl 0x55ea0227c690 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55ea0227c340 'unsigned __int128'
|-TypedefDecl 0x55ea0227c998 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55ea0227c770 'struct __NSConstantString_tag'
|   `-Record 0x55ea0227c6e8 '__NSConstantString_tag'
|-TypedefDecl 0x55ea0227ca30 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55ea0227c9f0 'char *'
|   `-BuiltinType 0x55ea0227be20 'char'
|-TypedefDecl 0x55ea0227cd28 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55ea0227ccd0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55ea0227cb10 'struct __va_list_tag'
|     `-Record 0x55ea0227ca88 '__va_list_tag'
|-FunctionDecl 0x55ea022dbd40 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/ex2b.c:13:1, line:30:1> line:13:5 used ex2b 'int (int, int)'
| |-ParmVarDecl 0x55ea022dbbe8 <col:10, col:14> col:14 used a 'int'
| |-ParmVarDecl 0x55ea022dbc68 <col:17, col:21> col:21 used b 'int'
| `-CompoundStmt 0x55ea022dc518 <line:14:1, line:30:1>
|   |-DeclStmt 0x55ea022dbef0 <line:15:5, col:14>
|   | `-VarDecl 0x55ea022dbe50 <col:5, col:13> col:9 used x 'int' cinit
|   |   `-ImplicitCastExpr 0x55ea022dbed8 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x55ea022dbeb8 <col:13> 'int' lvalue ParmVar 0x55ea022dbbe8 'a' 'int'
|   |-DeclStmt 0x55ea022dbfc0 <line:16:5, col:14>
|   | `-VarDecl 0x55ea022dbf20 <col:5, col:13> col:9 used y 'int' cinit
|   |   `-ImplicitCastExpr 0x55ea022dbfa8 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x55ea022dbf88 <col:13> 'int' lvalue ParmVar 0x55ea022dbc68 'b' 'int'
|   |-DeclStmt 0x55ea022dc058 <line:17:5, col:10>
|   | `-VarDecl 0x55ea022dbff0 <col:5, col:9> col:9 used i 'int'
|   |-ForStmt 0x55ea022dc268 <line:19:5, line:22:5>
|   | |-BinaryOperator 0x55ea022dc0b0 <line:19:10, col:12> 'int' '='
|   | | |-DeclRefExpr 0x55ea022dc070 <col:10> 'int' lvalue Var 0x55ea022dbff0 'i' 'int'
|   | | `-IntegerLiteral 0x55ea022dc090 <col:12> 'int' 0
|   | |-<<<NULL>>>
|   | |-BinaryOperator 0x55ea022dc140 <col:15, col:19> 'int' '<'
|   | | |-ImplicitCastExpr 0x55ea022dc110 <col:15> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55ea022dc0d0 <col:15> 'int' lvalue Var 0x55ea022dbff0 'i' 'int'
|   | | `-ImplicitCastExpr 0x55ea022dc128 <col:19> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55ea022dc0f0 <col:19> 'int' lvalue Var 0x55ea022dbf20 'y' 'int'
|   | |-UnaryOperator 0x55ea022dc180 <col:22, col:23> 'int' postfix '++'
|   | | `-DeclRefExpr 0x55ea022dc160 <col:22> 'int' lvalue Var 0x55ea022dbff0 'i' 'int'
|   | `-CompoundStmt 0x55ea022dc250 <line:20:5, line:22:5>
|   |   `-BinaryOperator 0x55ea022dc230 <line:21:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x55ea022dc198 <col:9> 'int' lvalue Var 0x55ea022dbe50 'x' 'int'
|   |     `-BinaryOperator 0x55ea022dc210 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x55ea022dc1f8 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x55ea022dc1b8 <col:13> 'int' lvalue Var 0x55ea022dbe50 'x' 'int'
|   |       `-IntegerLiteral 0x55ea022dc1d8 <col:17> 'int' 2
|   |-ForStmt 0x55ea022dc498 <line:24:5, line:27:5>
|   | |-BinaryOperator 0x55ea022dc2e0 <line:24:10, col:12> 'int' '='
|   | | |-DeclRefExpr 0x55ea022dc2a0 <col:10> 'int' lvalue Var 0x55ea022dbff0 'i' 'int'
|   | | `-IntegerLiteral 0x55ea022dc2c0 <col:12> 'int' 0
|   | |-<<<NULL>>>
|   | |-BinaryOperator 0x55ea022dc370 <col:15, col:19> 'int' '<'
|   | | |-ImplicitCastExpr 0x55ea022dc340 <col:15> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55ea022dc300 <col:15> 'int' lvalue Var 0x55ea022dbff0 'i' 'int'
|   | | `-ImplicitCastExpr 0x55ea022dc358 <col:19> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55ea022dc320 <col:19> 'int' lvalue Var 0x55ea022dbf20 'y' 'int'
|   | |-UnaryOperator 0x55ea022dc3b0 <col:22, col:23> 'int' postfix '++'
|   | | `-DeclRefExpr 0x55ea022dc390 <col:22> 'int' lvalue Var 0x55ea022dbff0 'i' 'int'
|   | `-CompoundStmt 0x55ea022dc480 <line:25:5, line:27:5>
|   |   `-BinaryOperator 0x55ea022dc460 <line:26:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x55ea022dc3c8 <col:9> 'int' lvalue Var 0x55ea022dbe50 'x' 'int'
|   |     `-BinaryOperator 0x55ea022dc440 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x55ea022dc428 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x55ea022dc3e8 <col:13> 'int' lvalue Var 0x55ea022dbe50 'x' 'int'
|   |       `-IntegerLiteral 0x55ea022dc408 <col:17> 'int' 2
|   `-ReturnStmt 0x55ea022dc508 <line:29:5, col:12>
|     `-ImplicitCastExpr 0x55ea022dc4f0 <col:12> 'int' <LValueToRValue>
|       `-DeclRefExpr 0x55ea022dc4d0 <col:12> 'int' lvalue Var 0x55ea022dbe50 'x' 'int'
`-FunctionDecl 0x55ea022dc5a8 <line:32:1, line:38:1> line:32:6 test 'void ()'
  `-CompoundStmt 0x55ea022dc918 <line:33:1, line:38:1>
    |-DeclStmt 0x55ea022dc6c8 <line:34:5, col:10>
    | `-VarDecl 0x55ea022dc660 <col:5, col:9> col:9 used a 'int'
    |-DeclStmt 0x55ea022dc760 <line:35:5, col:10>
    | `-VarDecl 0x55ea022dc6f8 <col:5, col:9> col:9 used b 'int'
    `-DeclStmt 0x55ea022dc900 <line:37:5, col:23>
      `-VarDecl 0x55ea022dc790 <col:5, col:22> col:9 r 'int' cinit
        `-CallExpr 0x55ea022dc8a0 <col:13, col:22> 'int'
          |-ImplicitCastExpr 0x55ea022dc888 <col:13> 'int (*)(int, int)' <FunctionToPointerDecay>
          | `-DeclRefExpr 0x55ea022dc7f8 <col:13> 'int (int, int)' Function 0x55ea022dbd40 'ex2b' 'int (int, int)'
          |-ImplicitCastExpr 0x55ea022dc8d0 <col:18> 'int' <LValueToRValue>
          | `-DeclRefExpr 0x55ea022dc818 <col:18> 'int' lvalue Var 0x55ea022dc660 'a' 'int'
          `-ImplicitCastExpr 0x55ea022dc8e8 <col:21> 'int' <LValueToRValue>
            `-DeclRefExpr 0x55ea022dc838 <col:21> 'int' lvalue Var 0x55ea022dc6f8 'b' 'int'
