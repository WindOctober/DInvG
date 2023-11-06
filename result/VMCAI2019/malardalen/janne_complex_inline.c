./Benchmark/PLDI/VMCAI2019/malardalen/janne_complex_inline.c
[info] Using default compilation options.
TranslationUnitDecl 0x5630b2010f28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5630b20117c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5630b20114c0 '__int128'
|-TypedefDecl 0x5630b2011830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5630b20114e0 'unsigned __int128'
|-TypedefDecl 0x5630b2011b38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5630b2011910 'struct __NSConstantString_tag'
|   `-Record 0x5630b2011888 '__NSConstantString_tag'
|-TypedefDecl 0x5630b2011bd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5630b2011b90 'char *'
|   `-BuiltinType 0x5630b2010fc0 'char'
|-TypedefDecl 0x5630b2011ec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5630b2011e70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5630b2011cb0 'struct __va_list_tag'
|     `-Record 0x5630b2011c28 '__va_list_tag'
|-FunctionDecl 0x5630b2071530 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/malardalen/janne_complex_inline.c:29:1, col:18> col:12 used undet 'int ()' extern
|-FunctionDecl 0x5630b20716f8 <line:30:1, col:30> col:13 used __assume 'void (int)' extern
| `-ParmVarDecl 0x5630b2071630 <col:22, col:26> col:26 cond 'int'
|-FunctionDecl 0x5630b2071a58 <line:32:1, line:59:1> line:32:6 janne_complex 'void (int *, int *, int, int)'
| |-ParmVarDecl 0x5630b20717e0 <col:20, col:26> col:26 used cnt1 'int *'
| |-ParmVarDecl 0x5630b2071860 <line:33:20, col:26> col:26 used cnt2 'int *'
| |-ParmVarDecl 0x5630b20718e0 <line:34:20, col:24> col:24 used a 'int'
| |-ParmVarDecl 0x5630b2071960 <line:35:20, col:24> col:24 used b 'int'
| `-CompoundStmt 0x5630b2073208 <line:36:1, line:59:1>
|   |-DeclStmt 0x5630b2071bd0 <line:37:5, col:14>
|   | `-VarDecl 0x5630b2071b30 <col:5, col:13> col:9 used x 'int' cinit
|   |   `-ImplicitCastExpr 0x5630b2071bb8 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x5630b2071b98 <col:13> 'int' lvalue ParmVar 0x5630b20718e0 'a' 'int'
|   |-DeclStmt 0x5630b2071ca0 <line:38:5, col:14>
|   | `-VarDecl 0x5630b2071c00 <col:5, col:13> col:9 used y 'int' cinit
|   |   `-ImplicitCastExpr 0x5630b2071c88 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x5630b2071c68 <col:13> 'int' lvalue ParmVar 0x5630b2071960 'b' 'int'
|   |-BinaryOperator 0x5630b2071d28 <line:39:5, col:13> 'int' '='
|   | |-UnaryOperator 0x5630b2071cf0 <col:5, col:6> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x5630b2071cd8 <col:6> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x5630b2071cb8 <col:6> 'int *' lvalue ParmVar 0x5630b20717e0 'cnt1' 'int *'
|   | `-IntegerLiteral 0x5630b2071d08 <col:13> 'int' 0
|   |-BinaryOperator 0x5630b2071db8 <col:16, col:24> 'int' '='
|   | |-UnaryOperator 0x5630b2071d80 <col:16, col:17> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x5630b2071d68 <col:17> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x5630b2071d48 <col:17> 'int *' lvalue ParmVar 0x5630b2071860 'cnt2' 'int *'
|   | `-IntegerLiteral 0x5630b2071d98 <col:24> 'int' 0
|   `-WhileStmt 0x5630b20731f0 <line:40:5, line:58:5>
|     |-BinaryOperator 0x5630b2071e30 <line:40:11, col:15> 'int' '<'
|     | |-ImplicitCastExpr 0x5630b2071e18 <col:11> 'int' <LValueToRValue>
|     | | `-DeclRefExpr 0x5630b2071dd8 <col:11> 'int' lvalue Var 0x5630b2071b30 'x' 'int'
|     | `-IntegerLiteral 0x5630b2071df8 <col:15> 'int' 30
|     `-CompoundStmt 0x5630b20731c0 <line:41:5, line:58:5>
|       |-BinaryOperator 0x5630b2071f48 <line:42:9, col:25> 'int' '='
|       | |-UnaryOperator 0x5630b2071e88 <col:9, col:10> 'int' lvalue prefix '*' cannot overflow
|       | | `-ImplicitCastExpr 0x5630b2071e70 <col:10> 'int *' <LValueToRValue>
|       | |   `-DeclRefExpr 0x5630b2071e50 <col:10> 'int *' lvalue ParmVar 0x5630b20717e0 'cnt1' 'int *'
|       | `-BinaryOperator 0x5630b2071f28 <col:17, col:25> 'int' '+'
|       |   |-ImplicitCastExpr 0x5630b2071f10 <col:17, col:18> 'int' <LValueToRValue>
|       |   | `-UnaryOperator 0x5630b2071ed8 <col:17, col:18> 'int' lvalue prefix '*' cannot overflow
|       |   |   `-ImplicitCastExpr 0x5630b2071ec0 <col:18> 'int *' <LValueToRValue>
|       |   |     `-DeclRefExpr 0x5630b2071ea0 <col:18> 'int *' lvalue ParmVar 0x5630b20717e0 'cnt1' 'int *'
|       |   `-IntegerLiteral 0x5630b2071ef0 <col:25> 'int' 1
|       |-WhileStmt 0x5630b2073038 <line:43:9, line:54:9>
|       | |-BinaryOperator 0x5630b2071fd8 <line:43:15, col:19> 'int' '<'
|       | | |-ImplicitCastExpr 0x5630b2071fa8 <col:15> 'int' <LValueToRValue>
|       | | | `-DeclRefExpr 0x5630b2071f68 <col:15> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|       | | `-ImplicitCastExpr 0x5630b2071fc0 <col:19> 'int' <LValueToRValue>
|       | |   `-DeclRefExpr 0x5630b2071f88 <col:19> 'int' lvalue Var 0x5630b2071b30 'x' 'int'
|       | `-CompoundStmt 0x5630b2073010 <line:44:9, line:54:9>
|       |   |-BinaryOperator 0x5630b20720f0 <line:45:13, col:29> 'int' '='
|       |   | |-UnaryOperator 0x5630b2072030 <col:13, col:14> 'int' lvalue prefix '*' cannot overflow
|       |   | | `-ImplicitCastExpr 0x5630b2072018 <col:14> 'int *' <LValueToRValue>
|       |   | |   `-DeclRefExpr 0x5630b2071ff8 <col:14> 'int *' lvalue ParmVar 0x5630b2071860 'cnt2' 'int *'
|       |   | `-BinaryOperator 0x5630b20720d0 <col:21, col:29> 'int' '+'
|       |   |   |-ImplicitCastExpr 0x5630b20720b8 <col:21, col:22> 'int' <LValueToRValue>
|       |   |   | `-UnaryOperator 0x5630b2072080 <col:21, col:22> 'int' lvalue prefix '*' cannot overflow
|       |   |   |   `-ImplicitCastExpr 0x5630b2072068 <col:22> 'int *' <LValueToRValue>
|       |   |   |     `-DeclRefExpr 0x5630b2072048 <col:22> 'int *' lvalue ParmVar 0x5630b2071860 'cnt2' 'int *'
|       |   |   `-IntegerLiteral 0x5630b2072098 <col:29> 'int' 1
|       |   |-IfStmt 0x5630b20722f8 <line:46:13, line:49:25> has_else
|       |   | |-BinaryOperator 0x5630b2072168 <line:46:16, col:20> 'int' '>'
|       |   | | |-ImplicitCastExpr 0x5630b2072150 <col:16> 'int' <LValueToRValue>
|       |   | | | `-DeclRefExpr 0x5630b2072110 <col:16> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|       |   | | `-IntegerLiteral 0x5630b2072130 <col:20> 'int' 5
|       |   | |-BinaryOperator 0x5630b2072220 <line:47:17, col:25> 'int' '='
|       |   | | |-DeclRefExpr 0x5630b2072188 <col:17> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|       |   | | `-BinaryOperator 0x5630b2072200 <col:21, col:25> 'int' '*'
|       |   | |   |-ImplicitCastExpr 0x5630b20721e8 <col:21> 'int' <LValueToRValue>
|       |   | |   | `-DeclRefExpr 0x5630b20721a8 <col:21> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|       |   | |   `-IntegerLiteral 0x5630b20721c8 <col:25> 'int' 3
|       |   | `-BinaryOperator 0x5630b20722d8 <line:49:17, col:25> 'int' '='
|       |   |   |-DeclRefExpr 0x5630b2072240 <col:17> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|       |   |   `-BinaryOperator 0x5630b20722b8 <col:21, col:25> 'int' '+'
|       |   |     |-ImplicitCastExpr 0x5630b20722a0 <col:21> 'int' <LValueToRValue>
|       |   |     | `-DeclRefExpr 0x5630b2072260 <col:21> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|       |   |     `-IntegerLiteral 0x5630b2072280 <col:25> 'int' 2
|       |   `-IfStmt 0x5630b2072fe8 <line:50:13, line:53:25> has_else
|       |     |-BinaryOperator 0x5630b2072410 <line:50:16, col:32> 'int' '&&'
|       |     | |-BinaryOperator 0x5630b2072378 <col:16, col:21> 'int' '>='
|       |     | | |-ImplicitCastExpr 0x5630b2072360 <col:16> 'int' <LValueToRValue>
|       |     | | | `-DeclRefExpr 0x5630b2072320 <col:16> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|       |     | | `-IntegerLiteral 0x5630b2072340 <col:21> 'int' 10
|       |     | `-BinaryOperator 0x5630b20723f0 <col:27, col:32> 'int' '<='
|       |     |   |-ImplicitCastExpr 0x5630b20723d8 <col:27> 'int' <LValueToRValue>
|       |     |   | `-DeclRefExpr 0x5630b2072398 <col:27> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|       |     |   `-IntegerLiteral 0x5630b20723b8 <col:32> 'int' 12
|       |     |-BinaryOperator 0x5630b2072f10 <line:51:17, col:25> 'int' '='
|       |     | |-DeclRefExpr 0x5630b2072430 <col:17> 'int' lvalue Var 0x5630b2071b30 'x' 'int'
|       |     | `-BinaryOperator 0x5630b20724a8 <col:21, col:25> 'int' '+'
|       |     |   |-ImplicitCastExpr 0x5630b2072490 <col:21> 'int' <LValueToRValue>
|       |     |   | `-DeclRefExpr 0x5630b2072450 <col:21> 'int' lvalue Var 0x5630b2071b30 'x' 'int'
|       |     |   `-IntegerLiteral 0x5630b2072470 <col:25> 'int' 10
|       |     `-BinaryOperator 0x5630b2072fc8 <line:53:17, col:25> 'int' '='
|       |       |-DeclRefExpr 0x5630b2072f30 <col:17> 'int' lvalue Var 0x5630b2071b30 'x' 'int'
|       |       `-BinaryOperator 0x5630b2072fa8 <col:21, col:25> 'int' '+'
|       |         |-ImplicitCastExpr 0x5630b2072f90 <col:21> 'int' <LValueToRValue>
|       |         | `-DeclRefExpr 0x5630b2072f50 <col:21> 'int' lvalue Var 0x5630b2071b30 'x' 'int'
|       |         `-IntegerLiteral 0x5630b2072f70 <col:25> 'int' 1
|       |-BinaryOperator 0x5630b20730e8 <line:56:9, col:17> 'int' '='
|       | |-DeclRefExpr 0x5630b2073050 <col:9> 'int' lvalue Var 0x5630b2071b30 'x' 'int'
|       | `-BinaryOperator 0x5630b20730c8 <col:13, col:17> 'int' '+'
|       |   |-ImplicitCastExpr 0x5630b20730b0 <col:13> 'int' <LValueToRValue>
|       |   | `-DeclRefExpr 0x5630b2073070 <col:13> 'int' lvalue Var 0x5630b2071b30 'x' 'int'
|       |   `-IntegerLiteral 0x5630b2073090 <col:17> 'int' 2
|       `-BinaryOperator 0x5630b20731a0 <line:57:9, col:17> 'int' '='
|         |-DeclRefExpr 0x5630b2073108 <col:9> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|         `-BinaryOperator 0x5630b2073180 <col:13, col:17> 'int' '-'
|           |-ImplicitCastExpr 0x5630b2073168 <col:13> 'int' <LValueToRValue>
|           | `-DeclRefExpr 0x5630b2073128 <col:13> 'int' lvalue Var 0x5630b2071c00 'y' 'int'
|           `-IntegerLiteral 0x5630b2073148 <col:17> 'int' 10
`-FunctionDecl 0x5630b2073268 <line:61:1, line:92:1> line:61:5 main 'int ()'
  `-CompoundStmt 0x5630b20745b8 <line:62:1, line:92:1>
    |-DeclStmt 0x5630b2073610 <line:63:5, col:47>
    | |-VarDecl 0x5630b2073320 <col:5, col:20> col:9 used a1 'int' cinit
    | | `-CallExpr 0x5630b20733f0 <col:14, col:20> 'int'
    | |   `-ImplicitCastExpr 0x5630b20733d8 <col:14> 'int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x5630b2073388 <col:14> 'int ()' Function 0x5630b2071530 'undet' 'int ()'
    | |-VarDecl 0x5630b2073428 <col:5, col:34> col:23 used b1 'int' cinit
    | | `-CallExpr 0x5630b20734c8 <col:28, col:34> 'int'
    | |   `-ImplicitCastExpr 0x5630b20734b0 <col:28> 'int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x5630b2073490 <col:28> 'int ()' Function 0x5630b2071530 'undet' 'int ()'
    | |-VarDecl 0x5630b2073500 <col:5, col:37> col:37 used cnt1 'int'
    | `-VarDecl 0x5630b2073580 <col:5, col:43> col:43 used cnt2 'int'
    |-CallExpr 0x5630b2073700 <line:64:5, col:21> 'void'
    | |-ImplicitCastExpr 0x5630b20736e8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5630b2073628 <col:5> 'void (int)' Function 0x5630b20716f8 '__assume' 'void (int)'
    | `-BinaryOperator 0x5630b20736a0 <col:14, col:20> 'int' '>='
    |   |-ImplicitCastExpr 0x5630b2073688 <col:14> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5630b2073648 <col:14> 'int' lvalue Var 0x5630b2073320 'a1' 'int'
    |   `-IntegerLiteral 0x5630b2073668 <col:20> 'int' 0
    |-CallExpr 0x5630b20737d8 <col:24, col:40> 'void'
    | |-ImplicitCastExpr 0x5630b20737c0 <col:24> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5630b2073728 <col:24> 'void (int)' Function 0x5630b20716f8 '__assume' 'void (int)'
    | `-BinaryOperator 0x5630b20737a0 <col:33, col:39> 'int' '>='
    |   |-ImplicitCastExpr 0x5630b2073788 <col:33> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5630b2073748 <col:33> 'int' lvalue Var 0x5630b2073428 'b1' 'int'
    |   `-IntegerLiteral 0x5630b2073768 <col:39> 'int' 0
    |-CompoundStmt 0x5630b2074550 <line:66:5, line:89:5>
    | |-DeclStmt 0x5630b20738b8 <line:67:9, col:20>
    | | `-VarDecl 0x5630b2073818 <col:9, col:18> col:13 used x1 'int' cinit
    | |   `-ImplicitCastExpr 0x5630b20738a0 <col:18> 'int' <LValueToRValue>
    | |     `-DeclRefExpr 0x5630b2073880 <col:18> 'int' lvalue Var 0x5630b2073320 'a1' 'int'
    | |-DeclStmt 0x5630b2073988 <line:68:9, col:20>
    | | `-VarDecl 0x5630b20738e8 <col:9, col:18> col:13 used y1 'int' cinit
    | |   `-ImplicitCastExpr 0x5630b2073970 <col:18> 'int' <LValueToRValue>
    | |     `-DeclRefExpr 0x5630b2073950 <col:18> 'int' lvalue Var 0x5630b2073428 'b1' 'int'
    | |-BinaryOperator 0x5630b20739e0 <line:69:9, col:16> 'int' '='
    | | |-DeclRefExpr 0x5630b20739a0 <col:9> 'int' lvalue Var 0x5630b2073500 'cnt1' 'int'
    | | `-IntegerLiteral 0x5630b20739c0 <col:16> 'int' 0
    | |-BinaryOperator 0x5630b2073a40 <col:19, col:26> 'int' '='
    | | |-DeclRefExpr 0x5630b2073a00 <col:19> 'int' lvalue Var 0x5630b2073580 'cnt2' 'int'
    | | `-IntegerLiteral 0x5630b2073a20 <col:26> 'int' 0
    | `-WhileStmt 0x5630b2074538 <line:70:9, line:88:9>
    |   |-BinaryOperator 0x5630b2073ab8 <line:70:15, col:20> 'int' '<'
    |   | |-ImplicitCastExpr 0x5630b2073aa0 <col:15> 'int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x5630b2073a60 <col:15> 'int' lvalue Var 0x5630b2073818 'x1' 'int'
    |   | `-IntegerLiteral 0x5630b2073a80 <col:20> 'int' 30
    |   `-CompoundStmt 0x5630b2074508 <line:71:9, line:88:9>
    |     |-BinaryOperator 0x5630b2073b70 <line:72:13, col:27> 'int' '='
    |     | |-DeclRefExpr 0x5630b2073ad8 <col:13> 'int' lvalue Var 0x5630b2073500 'cnt1' 'int'
    |     | `-BinaryOperator 0x5630b2073b50 <col:20, col:27> 'int' '+'
    |     |   |-ImplicitCastExpr 0x5630b2073b38 <col:20> 'int' <LValueToRValue>
    |     |   | `-DeclRefExpr 0x5630b2073af8 <col:20> 'int' lvalue Var 0x5630b2073500 'cnt1' 'int'
    |     |   `-IntegerLiteral 0x5630b2073b18 <col:27> 'int' 1
    |     |-WhileStmt 0x5630b2074380 <line:73:13, line:84:13>
    |     | |-BinaryOperator 0x5630b2073c00 <line:73:19, col:24> 'int' '<'
    |     | | |-ImplicitCastExpr 0x5630b2073bd0 <col:19> 'int' <LValueToRValue>
    |     | | | `-DeclRefExpr 0x5630b2073b90 <col:19> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |     | | `-ImplicitCastExpr 0x5630b2073be8 <col:24> 'int' <LValueToRValue>
    |     | |   `-DeclRefExpr 0x5630b2073bb0 <col:24> 'int' lvalue Var 0x5630b2073818 'x1' 'int'
    |     | `-CompoundStmt 0x5630b2074358 <line:74:13, line:84:13>
    |     |   |-BinaryOperator 0x5630b2073cb8 <line:75:17, col:31> 'int' '='
    |     |   | |-DeclRefExpr 0x5630b2073c20 <col:17> 'int' lvalue Var 0x5630b2073580 'cnt2' 'int'
    |     |   | `-BinaryOperator 0x5630b2073c98 <col:24, col:31> 'int' '+'
    |     |   |   |-ImplicitCastExpr 0x5630b2073c80 <col:24> 'int' <LValueToRValue>
    |     |   |   | `-DeclRefExpr 0x5630b2073c40 <col:24> 'int' lvalue Var 0x5630b2073580 'cnt2' 'int'
    |     |   |   `-IntegerLiteral 0x5630b2073c60 <col:31> 'int' 1
    |     |   |-IfStmt 0x5630b2073ec0 <line:76:17, line:79:31> has_else
    |     |   | |-BinaryOperator 0x5630b2073d30 <line:76:20, col:25> 'int' '>'
    |     |   | | |-ImplicitCastExpr 0x5630b2073d18 <col:20> 'int' <LValueToRValue>
    |     |   | | | `-DeclRefExpr 0x5630b2073cd8 <col:20> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |     |   | | `-IntegerLiteral 0x5630b2073cf8 <col:25> 'int' 5
    |     |   | |-BinaryOperator 0x5630b2073de8 <line:77:21, col:31> 'int' '='
    |     |   | | |-DeclRefExpr 0x5630b2073d50 <col:21> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |     |   | | `-BinaryOperator 0x5630b2073dc8 <col:26, col:31> 'int' '*'
    |     |   | |   |-ImplicitCastExpr 0x5630b2073db0 <col:26> 'int' <LValueToRValue>
    |     |   | |   | `-DeclRefExpr 0x5630b2073d70 <col:26> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |     |   | |   `-IntegerLiteral 0x5630b2073d90 <col:31> 'int' 3
    |     |   | `-BinaryOperator 0x5630b2073ea0 <line:79:21, col:31> 'int' '='
    |     |   |   |-DeclRefExpr 0x5630b2073e08 <col:21> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |     |   |   `-BinaryOperator 0x5630b2073e80 <col:26, col:31> 'int' '+'
    |     |   |     |-ImplicitCastExpr 0x5630b2073e68 <col:26> 'int' <LValueToRValue>
    |     |   |     | `-DeclRefExpr 0x5630b2073e28 <col:26> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |     |   |     `-IntegerLiteral 0x5630b2073e48 <col:31> 'int' 2
    |     |   `-IfStmt 0x5630b2074330 <line:80:17, line:83:31> has_else
    |     |     |-BinaryOperator 0x5630b20741a0 <line:80:20, col:38> 'int' '&&'
    |     |     | |-BinaryOperator 0x5630b2074108 <col:20, col:26> 'int' '>='
    |     |     | | |-ImplicitCastExpr 0x5630b20740f0 <col:20> 'int' <LValueToRValue>
    |     |     | | | `-DeclRefExpr 0x5630b2073ee8 <col:20> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |     |     | | `-IntegerLiteral 0x5630b20740d0 <col:26> 'int' 10
    |     |     | `-BinaryOperator 0x5630b2074180 <col:32, col:38> 'int' '<='
    |     |     |   |-ImplicitCastExpr 0x5630b2074168 <col:32> 'int' <LValueToRValue>
    |     |     |   | `-DeclRefExpr 0x5630b2074128 <col:32> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |     |     |   `-IntegerLiteral 0x5630b2074148 <col:38> 'int' 12
    |     |     |-BinaryOperator 0x5630b2074258 <line:81:21, col:31> 'int' '='
    |     |     | |-DeclRefExpr 0x5630b20741c0 <col:21> 'int' lvalue Var 0x5630b2073818 'x1' 'int'
    |     |     | `-BinaryOperator 0x5630b2074238 <col:26, col:31> 'int' '+'
    |     |     |   |-ImplicitCastExpr 0x5630b2074220 <col:26> 'int' <LValueToRValue>
    |     |     |   | `-DeclRefExpr 0x5630b20741e0 <col:26> 'int' lvalue Var 0x5630b2073818 'x1' 'int'
    |     |     |   `-IntegerLiteral 0x5630b2074200 <col:31> 'int' 10
    |     |     `-BinaryOperator 0x5630b2074310 <line:83:21, col:31> 'int' '='
    |     |       |-DeclRefExpr 0x5630b2074278 <col:21> 'int' lvalue Var 0x5630b2073818 'x1' 'int'
    |     |       `-BinaryOperator 0x5630b20742f0 <col:26, col:31> 'int' '+'
    |     |         |-ImplicitCastExpr 0x5630b20742d8 <col:26> 'int' <LValueToRValue>
    |     |         | `-DeclRefExpr 0x5630b2074298 <col:26> 'int' lvalue Var 0x5630b2073818 'x1' 'int'
    |     |         `-IntegerLiteral 0x5630b20742b8 <col:31> 'int' 1
    |     |-BinaryOperator 0x5630b2074430 <line:86:13, col:23> 'int' '='
    |     | |-DeclRefExpr 0x5630b2074398 <col:13> 'int' lvalue Var 0x5630b2073818 'x1' 'int'
    |     | `-BinaryOperator 0x5630b2074410 <col:18, col:23> 'int' '+'
    |     |   |-ImplicitCastExpr 0x5630b20743f8 <col:18> 'int' <LValueToRValue>
    |     |   | `-DeclRefExpr 0x5630b20743b8 <col:18> 'int' lvalue Var 0x5630b2073818 'x1' 'int'
    |     |   `-IntegerLiteral 0x5630b20743d8 <col:23> 'int' 2
    |     `-BinaryOperator 0x5630b20744e8 <line:87:13, col:23> 'int' '='
    |       |-DeclRefExpr 0x5630b2074450 <col:13> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |       `-BinaryOperator 0x5630b20744c8 <col:18, col:23> 'int' '-'
    |         |-ImplicitCastExpr 0x5630b20744b0 <col:18> 'int' <LValueToRValue>
    |         | `-DeclRefExpr 0x5630b2074470 <col:18> 'int' lvalue Var 0x5630b20738e8 'y1' 'int'
    |         `-IntegerLiteral 0x5630b2074490 <col:23> 'int' 10
    `-ReturnStmt 0x5630b20745a8 <line:91:3, col:10>
      `-IntegerLiteral 0x5630b2074588 <col:10> 'int' 0
