./Benchmark/PLDI/VMCAI2019/tiny/mul2.c
[info] Using default compilation options.
TranslationUnitDecl 0x5625cef1cd88 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5625cef1d620 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5625cef1d320 '__int128'
|-TypedefDecl 0x5625cef1d690 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5625cef1d340 'unsigned __int128'
|-TypedefDecl 0x5625cef1d998 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5625cef1d770 'struct __NSConstantString_tag'
|   `-Record 0x5625cef1d6e8 '__NSConstantString_tag'
|-TypedefDecl 0x5625cef1da30 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5625cef1d9f0 'char *'
|   `-BuiltinType 0x5625cef1ce20 'char'
|-TypedefDecl 0x5625cef1dd28 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5625cef1dcd0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5625cef1db10 'struct __va_list_tag'
|     `-Record 0x5625cef1da88 '__va_list_tag'
|-FunctionDecl 0x5625cef7ca60 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/mul2.c:13:1, line:24:1> line:13:5 used mul2 'int (int)'
| |-ParmVarDecl 0x5625cef7c998 <col:10, col:14> col:14 used a 'int'
| `-CompoundStmt 0x5625cef7cf30 <line:14:1, line:24:1>
|   |-DeclStmt 0x5625cef7cc08 <line:15:5, col:14>
|   | `-VarDecl 0x5625cef7cb68 <col:5, col:13> col:9 used x 'int' cinit
|   |   `-ImplicitCastExpr 0x5625cef7cbf0 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x5625cef7cbd0 <col:13> 'int' lvalue ParmVar 0x5625cef7c998 'a' 'int'
|   |-DeclStmt 0x5625cef7cca0 <line:16:5, col:10>
|   | `-VarDecl 0x5625cef7cc38 <col:5, col:9> col:9 used i 'int'
|   |-ForStmt 0x5625cef7ceb0 <line:18:5, line:21:5>
|   | |-BinaryOperator 0x5625cef7ccf8 <line:18:9, col:13> 'int' '='
|   | | |-DeclRefExpr 0x5625cef7ccb8 <col:9> 'int' lvalue Var 0x5625cef7cc38 'i' 'int'
|   | | `-IntegerLiteral 0x5625cef7ccd8 <col:13> 'int' 0
|   | |-<<<NULL>>>
|   | |-BinaryOperator 0x5625cef7cd88 <col:16, col:20> 'int' '<'
|   | | |-ImplicitCastExpr 0x5625cef7cd58 <col:16> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x5625cef7cd18 <col:16> 'int' lvalue Var 0x5625cef7cc38 'i' 'int'
|   | | `-ImplicitCastExpr 0x5625cef7cd70 <col:20> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x5625cef7cd38 <col:20> 'int' lvalue ParmVar 0x5625cef7c998 'a' 'int'
|   | |-UnaryOperator 0x5625cef7cdc8 <col:23, col:24> 'int' postfix '++'
|   | | `-DeclRefExpr 0x5625cef7cda8 <col:23> 'int' lvalue Var 0x5625cef7cc38 'i' 'int'
|   | `-CompoundStmt 0x5625cef7ce98 <line:19:5, line:21:5>
|   |   `-BinaryOperator 0x5625cef7ce78 <line:20:9, col:15> 'int' '='
|   |     |-DeclRefExpr 0x5625cef7cde0 <col:9> 'int' lvalue Var 0x5625cef7cb68 'x' 'int'
|   |     `-BinaryOperator 0x5625cef7ce58 <col:13, col:15> 'int' '+'
|   |       |-ImplicitCastExpr 0x5625cef7ce40 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x5625cef7ce00 <col:13> 'int' lvalue Var 0x5625cef7cb68 'x' 'int'
|   |       `-IntegerLiteral 0x5625cef7ce20 <col:15> 'int' 1
|   `-ReturnStmt 0x5625cef7cf20 <line:23:5, col:12>
|     `-ImplicitCastExpr 0x5625cef7cf08 <col:12> 'int' <LValueToRValue>
|       `-DeclRefExpr 0x5625cef7cee8 <col:12> 'int' lvalue Var 0x5625cef7cb68 'x' 'int'
`-FunctionDecl 0x5625cef7cfa8 <line:26:1, line:32:1> line:26:6 test 'void ()'
  `-CompoundStmt 0x5625cef7d280 <line:27:1, line:32:1>
    |-DeclStmt 0x5625cef7d0c8 <line:28:5, col:10>
    | `-VarDecl 0x5625cef7d060 <col:5, col:9> col:9 used r 'int'
    |-DeclStmt 0x5625cef7d160 <line:29:5, col:10>
    | `-VarDecl 0x5625cef7d0f8 <col:5, col:9> col:9 used a 'int'
    `-BinaryOperator 0x5625cef7d260 <line:31:5, col:15> 'int' '='
      |-DeclRefExpr 0x5625cef7d178 <col:5> 'int' lvalue Var 0x5625cef7d060 'r' 'int'
      `-CallExpr 0x5625cef7d220 <col:9, col:15> 'int'
        |-ImplicitCastExpr 0x5625cef7d208 <col:9> 'int (*)(int)' <FunctionToPointerDecay>
        | `-DeclRefExpr 0x5625cef7d198 <col:9> 'int (int)' Function 0x5625cef7ca60 'mul2' 'int (int)'
        `-ImplicitCastExpr 0x5625cef7d248 <col:14> 'int' <LValueToRValue>
          `-DeclRefExpr 0x5625cef7d1b8 <col:14> 'int' lvalue Var 0x5625cef7d0f8 'a' 'int'
