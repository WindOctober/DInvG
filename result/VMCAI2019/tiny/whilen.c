./Benchmark/PLDI/VMCAI2019/tiny/whilen.c
[info] Using default compilation options.
TranslationUnitDecl 0x55c5b1b1edc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55c5b1b1f660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55c5b1b1f360 '__int128'
|-TypedefDecl 0x55c5b1b1f6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55c5b1b1f380 'unsigned __int128'
|-TypedefDecl 0x55c5b1b1f9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55c5b1b1f7b0 'struct __NSConstantString_tag'
|   `-Record 0x55c5b1b1f728 '__NSConstantString_tag'
|-TypedefDecl 0x55c5b1b1fa70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55c5b1b1fa30 'char *'
|   `-BuiltinType 0x55c5b1b1ee60 'char'
|-TypedefDecl 0x55c5b1b1fd68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55c5b1b1fd10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55c5b1b1fb50 'struct __va_list_tag'
|     `-Record 0x55c5b1b1fac8 '__va_list_tag'
|-FunctionDecl 0x55c5b1b7ee10 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/whilen.c:17:1, line:40:1> line:17:5 used whilen 'int (int, int)'
| |-ParmVarDecl 0x55c5b1b7ecb8 <col:12, col:16> col:16 used n 'int'
| |-ParmVarDecl 0x55c5b1b7ed38 <col:19, col:23> col:23 used a 'int'
| `-CompoundStmt 0x55c5b1b7f4a0 <line:18:1, line:40:1>
|   |-DeclStmt 0x55c5b1b7ef88 <line:19:5, col:10>
|   | `-VarDecl 0x55c5b1b7ef20 <col:5, col:9> col:9 used i 'int'
|   |-DeclStmt 0x55c5b1b7f020 <line:20:5, col:10>
|   | `-VarDecl 0x55c5b1b7efb8 <col:5, col:9> col:9 used j 'int'
|   |-IfStmt 0x55c5b1b7f0f8 <line:22:5, line:23:17>
|   | |-BinaryOperator 0x55c5b1b7f090 <line:22:8, col:12> 'int' '<'
|   | | |-ImplicitCastExpr 0x55c5b1b7f078 <col:8> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55c5b1b7f038 <col:8> 'int' lvalue ParmVar 0x55c5b1b7ecb8 'n' 'int'
|   | | `-IntegerLiteral 0x55c5b1b7f058 <col:12> 'int' 1
|   | `-ReturnStmt 0x55c5b1b7f0e8 <line:23:9, col:17>
|   |   `-UnaryOperator 0x55c5b1b7f0d0 <col:16, col:17> 'int' prefix '-'
|   |     `-IntegerLiteral 0x55c5b1b7f0b0 <col:17> 'int' 1
|   |-BinaryOperator 0x55c5b1b7f150 <line:25:5, col:9> 'int' '='
|   | |-DeclRefExpr 0x55c5b1b7f110 <col:5> 'int' lvalue Var 0x55c5b1b7ef20 'i' 'int'
|   | `-IntegerLiteral 0x55c5b1b7f130 <col:9> 'int' 0
|   |-WhileStmt 0x55c5b1b7f250 <line:27:5, line:30:5>
|   | |-BinaryOperator 0x55c5b1b7f1e0 <line:27:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x55c5b1b7f1b0 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55c5b1b7f170 <col:11> 'int' lvalue Var 0x55c5b1b7ef20 'i' 'int'
|   | | `-ImplicitCastExpr 0x55c5b1b7f1c8 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55c5b1b7f190 <col:15> 'int' lvalue ParmVar 0x55c5b1b7ecb8 'n' 'int'
|   | `-CompoundStmt 0x55c5b1b7f238 <line:28:5, line:30:5>
|   |   `-UnaryOperator 0x55c5b1b7f220 <line:29:9, col:10> 'int' postfix '++'
|   |     `-DeclRefExpr 0x55c5b1b7f200 <col:9> 'int' lvalue Var 0x55c5b1b7ef20 'i' 'int'
|   |-BinaryOperator 0x55c5b1b7f2c0 <line:32:5, col:9> 'int' '='
|   | |-DeclRefExpr 0x55c5b1b7f268 <col:5> 'int' lvalue Var 0x55c5b1b7efb8 'j' 'int'
|   | `-ImplicitCastExpr 0x55c5b1b7f2a8 <col:9> 'int' <LValueToRValue>
|   |   `-DeclRefExpr 0x55c5b1b7f288 <col:9> 'int' lvalue ParmVar 0x55c5b1b7ed38 'a' 'int'
|   |-WhileStmt 0x55c5b1b7f440 <line:34:5, line:37:5>
|   | |-BinaryOperator 0x55c5b1b7f350 <line:34:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x55c5b1b7f320 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55c5b1b7f2e0 <col:11> 'int' lvalue Var 0x55c5b1b7efb8 'j' 'int'
|   | | `-ImplicitCastExpr 0x55c5b1b7f338 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55c5b1b7f300 <col:15> 'int' lvalue ParmVar 0x55c5b1b7ecb8 'n' 'int'
|   | `-CompoundStmt 0x55c5b1b7f428 <line:35:5, line:37:5>
|   |   `-BinaryOperator 0x55c5b1b7f408 <line:36:9, col:15> 'int' '='
|   |     |-DeclRefExpr 0x55c5b1b7f370 <col:9> 'int' lvalue Var 0x55c5b1b7efb8 'j' 'int'
|   |     `-BinaryOperator 0x55c5b1b7f3e8 <col:13, col:15> 'int' '+'
|   |       |-ImplicitCastExpr 0x55c5b1b7f3d0 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x55c5b1b7f390 <col:13> 'int' lvalue Var 0x55c5b1b7efb8 'j' 'int'
|   |       `-IntegerLiteral 0x55c5b1b7f3b0 <col:15> 'int' 1
|   `-ReturnStmt 0x55c5b1b7f490 <line:39:5, col:12>
|     `-ImplicitCastExpr 0x55c5b1b7f478 <col:12> 'int' <LValueToRValue>
|       `-DeclRefExpr 0x55c5b1b7f458 <col:12> 'int' lvalue Var 0x55c5b1b7efb8 'j' 'int'
`-FunctionDecl 0x55c5b1b7f538 <line:42:1, line:49:1> line:42:6 test 'void ()'
  `-CompoundStmt 0x55c5b1b7f8e0 <line:43:1, line:49:1>
    |-DeclStmt 0x55c5b1b7f658 <line:44:5, col:10>
    | `-VarDecl 0x55c5b1b7f5f0 <col:5, col:9> col:9 used n 'int'
    |-DeclStmt 0x55c5b1b7f6f0 <line:45:5, col:10>
    | `-VarDecl 0x55c5b1b7f688 <col:5, col:9> col:9 used a 'int'
    |-DeclStmt 0x55c5b1b7f788 <line:46:5, col:10>
    | `-VarDecl 0x55c5b1b7f720 <col:5, col:9> col:9 used r 'int'
    `-BinaryOperator 0x55c5b1b7f8c0 <line:48:5, col:20> 'int' '='
      |-DeclRefExpr 0x55c5b1b7f7a0 <col:5> 'int' lvalue Var 0x55c5b1b7f720 'r' 'int'
      `-CallExpr 0x55c5b1b7f860 <col:9, col:20> 'int'
        |-ImplicitCastExpr 0x55c5b1b7f848 <col:9> 'int (*)(int, int)' <FunctionToPointerDecay>
        | `-DeclRefExpr 0x55c5b1b7f7c0 <col:9> 'int (int, int)' Function 0x55c5b1b7ee10 'whilen' 'int (int, int)'
        |-ImplicitCastExpr 0x55c5b1b7f890 <col:16> 'int' <LValueToRValue>
        | `-DeclRefExpr 0x55c5b1b7f7e0 <col:16> 'int' lvalue Var 0x55c5b1b7f5f0 'n' 'int'
        `-ImplicitCastExpr 0x55c5b1b7f8a8 <col:19> 'int' <LValueToRValue>
          `-DeclRefExpr 0x55c5b1b7f800 <col:19> 'int' lvalue Var 0x55c5b1b7f688 'a' 'int'
