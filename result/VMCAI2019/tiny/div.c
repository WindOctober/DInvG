./Benchmark/PLDI/VMCAI2019/tiny/div.c
[info] Using default compilation options.
TranslationUnitDecl 0x557718714d88 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x557718715620 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x557718715320 '__int128'
|-TypedefDecl 0x557718715690 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x557718715340 'unsigned __int128'
|-TypedefDecl 0x557718715998 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x557718715770 'struct __NSConstantString_tag'
|   `-Record 0x5577187156e8 '__NSConstantString_tag'
|-TypedefDecl 0x557718715a30 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5577187159f0 'char *'
|   `-BuiltinType 0x557718714e20 'char'
|-TypedefDecl 0x557718715d28 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x557718715cd0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x557718715b10 'struct __va_list_tag'
|     `-Record 0x557718715a88 '__va_list_tag'
|-FunctionDecl 0x557718775028 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/div.c:29:1, line:49:1> line:29:6 used div 'void (int, int, int *, int *)'
| |-ParmVarDecl 0x557718774d88 <col:10, col:14> col:14 used a 'int'
| |-ParmVarDecl 0x557718774e08 <col:17, col:21> col:21 used b 'int'
| |-ParmVarDecl 0x557718774eb0 <col:24, col:30> col:30 used q 'int *'
| |-ParmVarDecl 0x557718774f30 <col:33, col:39> col:39 used r 'int *'
| `-CompoundStmt 0x5577187757e0 <line:30:1, line:49:1>
|   |-IfStmt 0x5577187751b8 <line:31:5, line:32:9>
|   | |-BinaryOperator 0x557718775188 <line:31:8, col:12> 'int' '<'
|   | | |-ImplicitCastExpr 0x557718775170 <col:8> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x557718775130 <col:8> 'int' lvalue ParmVar 0x557718774d88 'a' 'int'
|   | | `-IntegerLiteral 0x557718775150 <col:12> 'int' 0
|   | `-ReturnStmt 0x5577187751a8 <line:32:9>
|   |-IfStmt 0x557718775258 <line:34:5, line:35:9>
|   | |-BinaryOperator 0x557718775228 <line:34:8, col:12> 'int' '<'
|   | | |-ImplicitCastExpr 0x557718775210 <col:8> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x5577187751d0 <col:8> 'int' lvalue ParmVar 0x557718774e08 'b' 'int'
|   | | `-IntegerLiteral 0x5577187751f0 <col:12> 'int' 1
|   | `-ReturnStmt 0x557718775248 <line:35:9>
|   |-BinaryOperator 0x5577187752e0 <line:37:5, col:10> 'int' '='
|   | |-UnaryOperator 0x5577187752a8 <col:5, col:6> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x557718775290 <col:6> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x557718775270 <col:6> 'int *' lvalue ParmVar 0x557718774eb0 'q' 'int *'
|   | `-IntegerLiteral 0x5577187752c0 <col:10> 'int' 0
|   |-BinaryOperator 0x557718775388 <line:38:5, col:10> 'int' '='
|   | |-UnaryOperator 0x557718775338 <col:5, col:6> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x557718775320 <col:6> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x557718775300 <col:6> 'int *' lvalue ParmVar 0x557718774f30 'r' 'int *'
|   | `-ImplicitCastExpr 0x557718775370 <col:10> 'int' <LValueToRValue>
|   |   `-DeclRefExpr 0x557718775350 <col:10> 'int' lvalue ParmVar 0x557718774d88 'a' 'int'
|   `-IfStmt 0x5577187757c8 <line:40:5, line:48:5>
|     |-BinaryOperator 0x557718775448 <line:40:8, col:13> 'int' '>'
|     | |-ImplicitCastExpr 0x557718775418 <col:8, col:9> 'int' <LValueToRValue>
|     | | `-UnaryOperator 0x5577187753e0 <col:8, col:9> 'int' lvalue prefix '*' cannot overflow
|     | |   `-ImplicitCastExpr 0x5577187753c8 <col:9> 'int *' <LValueToRValue>
|     | |     `-DeclRefExpr 0x5577187753a8 <col:9> 'int *' lvalue ParmVar 0x557718774f30 'r' 'int *'
|     | `-ImplicitCastExpr 0x557718775430 <col:13> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5577187753f8 <col:13> 'int' lvalue ParmVar 0x557718774e08 'b' 'int'
|     `-CompoundStmt 0x5577187757b0 <line:41:5, line:48:5>
|       `-DoStmt 0x557718775790 <line:42:9, line:47:21>
|         |-CompoundStmt 0x5577187756b0 <line:43:9, line:46:9>
|         | |-BinaryOperator 0x557718775578 <line:44:13, col:23> 'int' '='
|         | | |-UnaryOperator 0x5577187754a0 <col:13, col:14> 'int' lvalue prefix '*' cannot overflow
|         | | | `-ImplicitCastExpr 0x557718775488 <col:14> 'int *' <LValueToRValue>
|         | | |   `-DeclRefExpr 0x557718775468 <col:14> 'int *' lvalue ParmVar 0x557718774f30 'r' 'int *'
|         | | `-BinaryOperator 0x557718775558 <col:18, col:23> 'int' '-'
|         | |   |-ImplicitCastExpr 0x557718775528 <col:18, col:19> 'int' <LValueToRValue>
|         | |   | `-UnaryOperator 0x5577187754f0 <col:18, col:19> 'int' lvalue prefix '*' cannot overflow
|         | |   |   `-ImplicitCastExpr 0x5577187754d8 <col:19> 'int *' <LValueToRValue>
|         | |   |     `-DeclRefExpr 0x5577187754b8 <col:19> 'int *' lvalue ParmVar 0x557718774f30 'r' 'int *'
|         | |   `-ImplicitCastExpr 0x557718775540 <col:23> 'int' <LValueToRValue>
|         | |     `-DeclRefExpr 0x557718775508 <col:23> 'int' lvalue ParmVar 0x557718774e08 'b' 'int'
|         | `-BinaryOperator 0x557718775690 <line:45:13, col:23> 'int' '='
|         |   |-UnaryOperator 0x5577187755d0 <col:13, col:14> 'int' lvalue prefix '*' cannot overflow
|         |   | `-ImplicitCastExpr 0x5577187755b8 <col:14> 'int *' <LValueToRValue>
|         |   |   `-DeclRefExpr 0x557718775598 <col:14> 'int *' lvalue ParmVar 0x557718774eb0 'q' 'int *'
|         |   `-BinaryOperator 0x557718775670 <col:18, col:23> 'int' '+'
|         |     |-ImplicitCastExpr 0x557718775658 <col:18, col:19> 'int' <LValueToRValue>
|         |     | `-UnaryOperator 0x557718775620 <col:18, col:19> 'int' lvalue prefix '*' cannot overflow
|         |     |   `-ImplicitCastExpr 0x557718775608 <col:19> 'int *' <LValueToRValue>
|         |     |     `-DeclRefExpr 0x5577187755e8 <col:19> 'int *' lvalue ParmVar 0x557718774eb0 'q' 'int *'
|         |     `-IntegerLiteral 0x557718775638 <col:23> 'int' 1
|         `-BinaryOperator 0x557718775770 <line:47:15, col:20> 'int' '>'
|           |-ImplicitCastExpr 0x557718775740 <col:15, col:16> 'int' <LValueToRValue>
|           | `-UnaryOperator 0x557718775708 <col:15, col:16> 'int' lvalue prefix '*' cannot overflow
|           |   `-ImplicitCastExpr 0x5577187756f0 <col:16> 'int *' <LValueToRValue>
|           |     `-DeclRefExpr 0x5577187756d0 <col:16> 'int *' lvalue ParmVar 0x557718774f30 'r' 'int *'
|           `-ImplicitCastExpr 0x557718775758 <col:20> 'int' <LValueToRValue>
|             `-DeclRefExpr 0x557718775720 <col:20> 'int' lvalue ParmVar 0x557718774e08 'b' 'int'
`-FunctionDecl 0x557718775868 <line:51:1, line:59:1> line:51:6 test 'void ()'
  `-CompoundStmt 0x557718775d30 <line:52:1, line:59:1>
    |-DeclStmt 0x5577187759a8 <line:53:5, col:14>
    | `-VarDecl 0x557718775920 <col:5, col:13> col:9 used a 'int' cinit
    |   `-IntegerLiteral 0x557718775988 <col:13> 'int' 6
    |-DeclStmt 0x557718775a60 <line:54:5, col:14>
    | `-VarDecl 0x5577187759d8 <col:5, col:13> col:9 used b 'int' cinit
    |   `-IntegerLiteral 0x557718775a40 <col:13> 'int' 2
    |-DeclStmt 0x557718775af8 <line:55:5, col:10>
    | `-VarDecl 0x557718775a90 <col:5, col:9> col:9 used q 'int'
    |-DeclStmt 0x557718775b90 <line:56:5, col:10>
    | `-VarDecl 0x557718775b28 <col:5, col:9> col:9 used r 'int'
    `-CallExpr 0x557718775cc0 <line:58:5, col:21> 'void'
      |-ImplicitCastExpr 0x557718775ca8 <col:5> 'void (*)(int, int, int *, int *)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x557718775ba8 <col:5> 'void (int, int, int *, int *)' Function 0x557718775028 'div' 'void (int, int, int *, int *)'
      |-ImplicitCastExpr 0x557718775d00 <col:9> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x557718775bc8 <col:9> 'int' lvalue Var 0x557718775920 'a' 'int'
      |-ImplicitCastExpr 0x557718775d18 <col:12> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x557718775be8 <col:12> 'int' lvalue Var 0x5577187759d8 'b' 'int'
      |-UnaryOperator 0x557718775c28 <col:15, col:16> 'int *' prefix '&' cannot overflow
      | `-DeclRefExpr 0x557718775c08 <col:16> 'int' lvalue Var 0x557718775a90 'q' 'int'
      `-UnaryOperator 0x557718775c60 <col:19, col:20> 'int *' prefix '&' cannot overflow
        `-DeclRefExpr 0x557718775c40 <col:20> 'int' lvalue Var 0x557718775b28 'r' 'int'
