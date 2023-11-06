./Benchmark/PLDI/VMCAI2019/malardalen/janne_complex.c
[info] Using default compilation options.
TranslationUnitDecl 0x55ceadf6eeb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55ceadf6f750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55ceadf6f450 '__int128'
|-TypedefDecl 0x55ceadf6f7c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55ceadf6f470 'unsigned __int128'
|-TypedefDecl 0x55ceadf6fac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55ceadf6f8a0 'struct __NSConstantString_tag'
|   `-Record 0x55ceadf6f818 '__NSConstantString_tag'
|-TypedefDecl 0x55ceadf6fb60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55ceadf6fb20 'char *'
|   `-BuiltinType 0x55ceadf6ef50 'char'
|-TypedefDecl 0x55ceadf6fe58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55ceadf6fe00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55ceadf6fc40 'struct __va_list_tag'
|     `-Record 0x55ceadf6fbb8 '__va_list_tag'
|-FunctionDecl 0x55ceadfcf338 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/malardalen/janne_complex.c:29:1, col:30> col:13 used __assume 'void (int)' extern
| `-ParmVarDecl 0x55ceadfcf278 <col:22, col:26> col:26 cond 'int'
|-FunctionDecl 0x55ceadfcf480 <line:30:1, col:18> col:12 used undet 'int ()' extern
|-FunctionDecl 0x55ceadfcf7d8 <line:32:1, line:59:1> line:32:6 used janne_complex 'void (int *, int *, int, int)'
| |-ParmVarDecl 0x55ceadfcf560 <col:20, col:26> col:26 used cnt1 'int *'
| |-ParmVarDecl 0x55ceadfcf5e0 <line:33:20, col:26> col:26 used cnt2 'int *'
| |-ParmVarDecl 0x55ceadfcf660 <line:34:20, col:24> col:24 used a 'int'
| |-ParmVarDecl 0x55ceadfcf6e0 <line:35:20, col:24> col:24 used b 'int'
| `-CompoundStmt 0x55ceadfd0f88 <line:36:1, line:59:1>
|   |-DeclStmt 0x55ceadfcf950 <line:37:5, col:14>
|   | `-VarDecl 0x55ceadfcf8b0 <col:5, col:13> col:9 used x 'int' cinit
|   |   `-ImplicitCastExpr 0x55ceadfcf938 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x55ceadfcf918 <col:13> 'int' lvalue ParmVar 0x55ceadfcf660 'a' 'int'
|   |-DeclStmt 0x55ceadfcfa20 <line:38:5, col:14>
|   | `-VarDecl 0x55ceadfcf980 <col:5, col:13> col:9 used y 'int' cinit
|   |   `-ImplicitCastExpr 0x55ceadfcfa08 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x55ceadfcf9e8 <col:13> 'int' lvalue ParmVar 0x55ceadfcf6e0 'b' 'int'
|   |-BinaryOperator 0x55ceadfcfaa8 <line:39:5, col:13> 'int' '='
|   | |-UnaryOperator 0x55ceadfcfa70 <col:5, col:6> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x55ceadfcfa58 <col:6> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55ceadfcfa38 <col:6> 'int *' lvalue ParmVar 0x55ceadfcf560 'cnt1' 'int *'
|   | `-IntegerLiteral 0x55ceadfcfa88 <col:13> 'int' 0
|   |-BinaryOperator 0x55ceadfcfb38 <col:16, col:24> 'int' '='
|   | |-UnaryOperator 0x55ceadfcfb00 <col:16, col:17> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x55ceadfcfae8 <col:17> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55ceadfcfac8 <col:17> 'int *' lvalue ParmVar 0x55ceadfcf5e0 'cnt2' 'int *'
|   | `-IntegerLiteral 0x55ceadfcfb18 <col:24> 'int' 0
|   `-WhileStmt 0x55ceadfd0f70 <line:40:5, line:58:5>
|     |-BinaryOperator 0x55ceadfcfbb0 <line:40:11, col:15> 'int' '<'
|     | |-ImplicitCastExpr 0x55ceadfcfb98 <col:11> 'int' <LValueToRValue>
|     | | `-DeclRefExpr 0x55ceadfcfb58 <col:11> 'int' lvalue Var 0x55ceadfcf8b0 'x' 'int'
|     | `-IntegerLiteral 0x55ceadfcfb78 <col:15> 'int' 30
|     `-CompoundStmt 0x55ceadfd0f40 <line:41:5, line:58:5>
|       |-BinaryOperator 0x55ceadfcfcc8 <line:42:9, col:25> 'int' '='
|       | |-UnaryOperator 0x55ceadfcfc08 <col:9, col:10> 'int' lvalue prefix '*' cannot overflow
|       | | `-ImplicitCastExpr 0x55ceadfcfbf0 <col:10> 'int *' <LValueToRValue>
|       | |   `-DeclRefExpr 0x55ceadfcfbd0 <col:10> 'int *' lvalue ParmVar 0x55ceadfcf560 'cnt1' 'int *'
|       | `-BinaryOperator 0x55ceadfcfca8 <col:17, col:25> 'int' '+'
|       |   |-ImplicitCastExpr 0x55ceadfcfc90 <col:17, col:18> 'int' <LValueToRValue>
|       |   | `-UnaryOperator 0x55ceadfcfc58 <col:17, col:18> 'int' lvalue prefix '*' cannot overflow
|       |   |   `-ImplicitCastExpr 0x55ceadfcfc40 <col:18> 'int *' <LValueToRValue>
|       |   |     `-DeclRefExpr 0x55ceadfcfc20 <col:18> 'int *' lvalue ParmVar 0x55ceadfcf560 'cnt1' 'int *'
|       |   `-IntegerLiteral 0x55ceadfcfc70 <col:25> 'int' 1
|       |-WhileStmt 0x55ceadfd0db8 <line:43:9, line:54:9>
|       | |-BinaryOperator 0x55ceadfcfd58 <line:43:15, col:19> 'int' '<'
|       | | |-ImplicitCastExpr 0x55ceadfcfd28 <col:15> 'int' <LValueToRValue>
|       | | | `-DeclRefExpr 0x55ceadfcfce8 <col:15> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|       | | `-ImplicitCastExpr 0x55ceadfcfd40 <col:19> 'int' <LValueToRValue>
|       | |   `-DeclRefExpr 0x55ceadfcfd08 <col:19> 'int' lvalue Var 0x55ceadfcf8b0 'x' 'int'
|       | `-CompoundStmt 0x55ceadfd0d90 <line:44:9, line:54:9>
|       |   |-BinaryOperator 0x55ceadfcfe70 <line:45:13, col:29> 'int' '='
|       |   | |-UnaryOperator 0x55ceadfcfdb0 <col:13, col:14> 'int' lvalue prefix '*' cannot overflow
|       |   | | `-ImplicitCastExpr 0x55ceadfcfd98 <col:14> 'int *' <LValueToRValue>
|       |   | |   `-DeclRefExpr 0x55ceadfcfd78 <col:14> 'int *' lvalue ParmVar 0x55ceadfcf5e0 'cnt2' 'int *'
|       |   | `-BinaryOperator 0x55ceadfcfe50 <col:21, col:29> 'int' '+'
|       |   |   |-ImplicitCastExpr 0x55ceadfcfe38 <col:21, col:22> 'int' <LValueToRValue>
|       |   |   | `-UnaryOperator 0x55ceadfcfe00 <col:21, col:22> 'int' lvalue prefix '*' cannot overflow
|       |   |   |   `-ImplicitCastExpr 0x55ceadfcfde8 <col:22> 'int *' <LValueToRValue>
|       |   |   |     `-DeclRefExpr 0x55ceadfcfdc8 <col:22> 'int *' lvalue ParmVar 0x55ceadfcf5e0 'cnt2' 'int *'
|       |   |   `-IntegerLiteral 0x55ceadfcfe18 <col:29> 'int' 1
|       |   |-IfStmt 0x55ceadfd0078 <line:46:13, line:49:25> has_else
|       |   | |-BinaryOperator 0x55ceadfcfee8 <line:46:16, col:20> 'int' '>'
|       |   | | |-ImplicitCastExpr 0x55ceadfcfed0 <col:16> 'int' <LValueToRValue>
|       |   | | | `-DeclRefExpr 0x55ceadfcfe90 <col:16> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|       |   | | `-IntegerLiteral 0x55ceadfcfeb0 <col:20> 'int' 5
|       |   | |-BinaryOperator 0x55ceadfcffa0 <line:47:17, col:25> 'int' '='
|       |   | | |-DeclRefExpr 0x55ceadfcff08 <col:17> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|       |   | | `-BinaryOperator 0x55ceadfcff80 <col:21, col:25> 'int' '*'
|       |   | |   |-ImplicitCastExpr 0x55ceadfcff68 <col:21> 'int' <LValueToRValue>
|       |   | |   | `-DeclRefExpr 0x55ceadfcff28 <col:21> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|       |   | |   `-IntegerLiteral 0x55ceadfcff48 <col:25> 'int' 3
|       |   | `-BinaryOperator 0x55ceadfd0058 <line:49:17, col:25> 'int' '='
|       |   |   |-DeclRefExpr 0x55ceadfcffc0 <col:17> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|       |   |   `-BinaryOperator 0x55ceadfd0038 <col:21, col:25> 'int' '+'
|       |   |     |-ImplicitCastExpr 0x55ceadfd0020 <col:21> 'int' <LValueToRValue>
|       |   |     | `-DeclRefExpr 0x55ceadfcffe0 <col:21> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|       |   |     `-IntegerLiteral 0x55ceadfd0000 <col:25> 'int' 2
|       |   `-IfStmt 0x55ceadfd0d68 <line:50:13, line:53:25> has_else
|       |     |-BinaryOperator 0x55ceadfd0190 <line:50:16, col:32> 'int' '&&'
|       |     | |-BinaryOperator 0x55ceadfd00f8 <col:16, col:21> 'int' '>='
|       |     | | |-ImplicitCastExpr 0x55ceadfd00e0 <col:16> 'int' <LValueToRValue>
|       |     | | | `-DeclRefExpr 0x55ceadfd00a0 <col:16> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|       |     | | `-IntegerLiteral 0x55ceadfd00c0 <col:21> 'int' 10
|       |     | `-BinaryOperator 0x55ceadfd0170 <col:27, col:32> 'int' '<='
|       |     |   |-ImplicitCastExpr 0x55ceadfd0158 <col:27> 'int' <LValueToRValue>
|       |     |   | `-DeclRefExpr 0x55ceadfd0118 <col:27> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|       |     |   `-IntegerLiteral 0x55ceadfd0138 <col:32> 'int' 12
|       |     |-BinaryOperator 0x55ceadfd0c90 <line:51:17, col:25> 'int' '='
|       |     | |-DeclRefExpr 0x55ceadfd01b0 <col:17> 'int' lvalue Var 0x55ceadfcf8b0 'x' 'int'
|       |     | `-BinaryOperator 0x55ceadfd0228 <col:21, col:25> 'int' '+'
|       |     |   |-ImplicitCastExpr 0x55ceadfd0210 <col:21> 'int' <LValueToRValue>
|       |     |   | `-DeclRefExpr 0x55ceadfd01d0 <col:21> 'int' lvalue Var 0x55ceadfcf8b0 'x' 'int'
|       |     |   `-IntegerLiteral 0x55ceadfd01f0 <col:25> 'int' 10
|       |     `-BinaryOperator 0x55ceadfd0d48 <line:53:17, col:25> 'int' '='
|       |       |-DeclRefExpr 0x55ceadfd0cb0 <col:17> 'int' lvalue Var 0x55ceadfcf8b0 'x' 'int'
|       |       `-BinaryOperator 0x55ceadfd0d28 <col:21, col:25> 'int' '+'
|       |         |-ImplicitCastExpr 0x55ceadfd0d10 <col:21> 'int' <LValueToRValue>
|       |         | `-DeclRefExpr 0x55ceadfd0cd0 <col:21> 'int' lvalue Var 0x55ceadfcf8b0 'x' 'int'
|       |         `-IntegerLiteral 0x55ceadfd0cf0 <col:25> 'int' 1
|       |-BinaryOperator 0x55ceadfd0e68 <line:56:9, col:17> 'int' '='
|       | |-DeclRefExpr 0x55ceadfd0dd0 <col:9> 'int' lvalue Var 0x55ceadfcf8b0 'x' 'int'
|       | `-BinaryOperator 0x55ceadfd0e48 <col:13, col:17> 'int' '+'
|       |   |-ImplicitCastExpr 0x55ceadfd0e30 <col:13> 'int' <LValueToRValue>
|       |   | `-DeclRefExpr 0x55ceadfd0df0 <col:13> 'int' lvalue Var 0x55ceadfcf8b0 'x' 'int'
|       |   `-IntegerLiteral 0x55ceadfd0e10 <col:17> 'int' 2
|       `-BinaryOperator 0x55ceadfd0f20 <line:57:9, col:17> 'int' '='
|         |-DeclRefExpr 0x55ceadfd0e88 <col:9> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|         `-BinaryOperator 0x55ceadfd0f00 <col:13, col:17> 'int' '-'
|           |-ImplicitCastExpr 0x55ceadfd0ee8 <col:13> 'int' <LValueToRValue>
|           | `-DeclRefExpr 0x55ceadfd0ea8 <col:13> 'int' lvalue Var 0x55ceadfcf980 'y' 'int'
|           `-IntegerLiteral 0x55ceadfd0ec8 <col:17> 'int' 10
`-FunctionDecl 0x55ceadfd0fe8 <line:61:1, line:69:1> line:61:5 main 'int ()'
  `-CompoundStmt 0x55ceadfd1730 <line:62:1, line:69:1>
    |-DeclStmt 0x55ceadfd1390 <line:63:3, col:45>
    | |-VarDecl 0x55ceadfd10a0 <col:3, col:18> col:7 used a1 'int' cinit
    | | `-CallExpr 0x55ceadfd1170 <col:12, col:18> 'int'
    | |   `-ImplicitCastExpr 0x55ceadfd1158 <col:12> 'int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55ceadfd1108 <col:12> 'int ()' Function 0x55ceadfcf480 'undet' 'int ()'
    | |-VarDecl 0x55ceadfd11a8 <col:3, col:32> col:21 used b1 'int' cinit
    | | `-CallExpr 0x55ceadfd1248 <col:26, col:32> 'int'
    | |   `-ImplicitCastExpr 0x55ceadfd1230 <col:26> 'int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55ceadfd1210 <col:26> 'int ()' Function 0x55ceadfcf480 'undet' 'int ()'
    | |-VarDecl 0x55ceadfd1280 <col:3, col:35> col:35 used cnt1 'int'
    | `-VarDecl 0x55ceadfd1300 <col:3, col:41> col:41 used cnt2 'int'
    |-CallExpr 0x55ceadfd1480 <line:64:3, col:19> 'void'
    | |-ImplicitCastExpr 0x55ceadfd1468 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55ceadfd13a8 <col:3> 'void (int)' Function 0x55ceadfcf338 '__assume' 'void (int)'
    | `-BinaryOperator 0x55ceadfd1420 <col:12, col:18> 'int' '>='
    |   |-ImplicitCastExpr 0x55ceadfd1408 <col:12> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55ceadfd13c8 <col:12> 'int' lvalue Var 0x55ceadfd10a0 'a1' 'int'
    |   `-IntegerLiteral 0x55ceadfd13e8 <col:18> 'int' 0
    |-CallExpr 0x55ceadfd1558 <col:22, col:38> 'void'
    | |-ImplicitCastExpr 0x55ceadfd1540 <col:22> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55ceadfd14a8 <col:22> 'void (int)' Function 0x55ceadfcf338 '__assume' 'void (int)'
    | `-BinaryOperator 0x55ceadfd1520 <col:31, col:37> 'int' '>='
    |   |-ImplicitCastExpr 0x55ceadfd1508 <col:31> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55ceadfd14c8 <col:31> 'int' lvalue Var 0x55ceadfd11a8 'b1' 'int'
    |   `-IntegerLiteral 0x55ceadfd14e8 <col:37> 'int' 0
    |-CallExpr 0x55ceadfd1690 <line:66:3, col:37> 'void'
    | |-ImplicitCastExpr 0x55ceadfd1678 <col:3> 'void (*)(int *, int *, int, int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55ceadfd1580 <col:3> 'void (int *, int *, int, int)' Function 0x55ceadfcf7d8 'janne_complex' 'void (int *, int *, int, int)'
    | |-UnaryOperator 0x55ceadfd15c0 <col:17, col:18> 'int *' prefix '&' cannot overflow
    | | `-DeclRefExpr 0x55ceadfd15a0 <col:18> 'int' lvalue Var 0x55ceadfd1280 'cnt1' 'int'
    | |-UnaryOperator 0x55ceadfd15f8 <col:24, col:25> 'int *' prefix '&' cannot overflow
    | | `-DeclRefExpr 0x55ceadfd15d8 <col:25> 'int' lvalue Var 0x55ceadfd1300 'cnt2' 'int'
    | |-ImplicitCastExpr 0x55ceadfd16d0 <col:31> 'int' <LValueToRValue>
    | | `-DeclRefExpr 0x55ceadfd1610 <col:31> 'int' lvalue Var 0x55ceadfd10a0 'a1' 'int'
    | `-ImplicitCastExpr 0x55ceadfd16e8 <col:35> 'int' <LValueToRValue>
    |   `-DeclRefExpr 0x55ceadfd1630 <col:35> 'int' lvalue Var 0x55ceadfd11a8 'b1' 'int'
    `-ReturnStmt 0x55ceadfd1720 <line:68:3, col:10>
      `-IntegerLiteral 0x55ceadfd1700 <col:10> 'int' 0
