./Benchmark/PLDI/VMCAI2019/tiny/correct1.c
[info] Using default compilation options.
TranslationUnitDecl 0x562075052dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x562075053660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x562075053360 '__int128'
|-TypedefDecl 0x5620750536d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562075053380 'unsigned __int128'
|-TypedefDecl 0x5620750539d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5620750537b0 'struct __NSConstantString_tag'
|   `-Record 0x562075053728 '__NSConstantString_tag'
|-TypedefDecl 0x562075053a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562075053a30 'char *'
|   `-BuiltinType 0x562075052e60 'char'
|-TypedefDecl 0x562075053d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562075053d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562075053b50 'struct __va_list_tag'
|     `-Record 0x562075053ac8 '__va_list_tag'
|-FunctionDecl 0x5620750b30a8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/correct1.c:26:1, line:42:1> line:26:6 used correct1 'void (int *, int, int, int)'
| |-ParmVarDecl 0x5620750b2e30 <col:15, col:21> col:21 used x 'int *'
| |-ParmVarDecl 0x5620750b2eb0 <col:24, col:28> col:28 used obj 'int'
| |-ParmVarDecl 0x5620750b2f30 <col:33, col:37> col:37 used tol 'int'
| |-ParmVarDecl 0x5620750b2fb0 <col:42, col:46> col:46 used step 'int'
| `-CompoundStmt 0x5620750b39e0 <line:27:1, line:42:1>
|   |-IfStmt 0x5620750b32d0 <line:28:5, line:29:9>
|   | |-BinaryOperator 0x5620750b32a0 <line:28:8, col:26> 'int' '||'
|   | | |-BinaryOperator 0x5620750b3208 <col:8, col:14> 'int' '<'
|   | | | |-ImplicitCastExpr 0x5620750b31f0 <col:8> 'int' <LValueToRValue>
|   | | | | `-DeclRefExpr 0x5620750b31b0 <col:8> 'int' lvalue ParmVar 0x5620750b2f30 'tol' 'int'
|   | | | `-IntegerLiteral 0x5620750b31d0 <col:14> 'int' 0
|   | | `-BinaryOperator 0x5620750b3280 <col:19, col:26> 'int' '<'
|   | |   |-ImplicitCastExpr 0x5620750b3268 <col:19> 'int' <LValueToRValue>
|   | |   | `-DeclRefExpr 0x5620750b3228 <col:19> 'int' lvalue ParmVar 0x5620750b2fb0 'step' 'int'
|   | |   `-IntegerLiteral 0x5620750b3248 <col:26> 'int' 0
|   | `-ReturnStmt 0x5620750b32c0 <line:29:9>
|   |-DeclStmt 0x5620750b3428 <line:31:5, col:23>
|   | `-VarDecl 0x5620750b3300 <col:5, col:20> col:9 used err 'int' cinit
|   |   `-BinaryOperator 0x5620750b3408 <col:15, col:20> 'int' '-'
|   |     |-ImplicitCastExpr 0x5620750b33d8 <col:15, col:16> 'int' <LValueToRValue>
|   |     | `-UnaryOperator 0x5620750b33a0 <col:15, col:16> 'int' lvalue prefix '*' cannot overflow
|   |     |   `-ImplicitCastExpr 0x5620750b3388 <col:16> 'int *' <LValueToRValue>
|   |     |     `-DeclRefExpr 0x5620750b3368 <col:16> 'int *' lvalue ParmVar 0x5620750b2e30 'x' 'int *'
|   |     `-ImplicitCastExpr 0x5620750b33f0 <col:20> 'int' <LValueToRValue>
|   |       `-DeclRefExpr 0x5620750b33b8 <col:20> 'int' lvalue ParmVar 0x5620750b2eb0 'obj' 'int'
|   `-WhileStmt 0x5620750b39c8 <line:33:5, line:41:5>
|     |-BinaryOperator 0x5620750b34b0 <line:33:11, col:17> 'int' '>'
|     | |-ImplicitCastExpr 0x5620750b3480 <col:11> 'int' <LValueToRValue>
|     | | `-DeclRefExpr 0x5620750b3440 <col:11> 'int' lvalue Var 0x5620750b3300 'err' 'int'
|     | `-ImplicitCastExpr 0x5620750b3498 <col:17> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5620750b3460 <col:17> 'int' lvalue ParmVar 0x5620750b2f30 'tol' 'int'
|     `-CompoundStmt 0x5620750b39a8 <line:34:5, line:41:5>
|       |-IfStmt 0x5620750b3880 <line:35:9, line:38:23> has_else
|       | |-BinaryOperator 0x5620750b3540 <line:35:12, col:18> 'int' '>'
|       | | |-ImplicitCastExpr 0x5620750b3510 <col:12> 'int' <LValueToRValue>
|       | | | `-DeclRefExpr 0x5620750b34d0 <col:12> 'int' lvalue Var 0x5620750b3300 'err' 'int'
|       | | `-ImplicitCastExpr 0x5620750b3528 <col:18> 'int' <LValueToRValue>
|       | |   `-DeclRefExpr 0x5620750b34f0 <col:18> 'int' lvalue ParmVar 0x5620750b2f30 'tol' 'int'
|       | |-BinaryOperator 0x5620750b3670 <line:36:13, col:23> 'int' '='
|       | | |-UnaryOperator 0x5620750b3598 <col:13, col:14> 'int' lvalue prefix '*' cannot overflow
|       | | | `-ImplicitCastExpr 0x5620750b3580 <col:14> 'int *' <LValueToRValue>
|       | | |   `-DeclRefExpr 0x5620750b3560 <col:14> 'int *' lvalue ParmVar 0x5620750b2e30 'x' 'int *'
|       | | `-BinaryOperator 0x5620750b3650 <col:18, col:23> 'int' '-'
|       | |   |-ImplicitCastExpr 0x5620750b3620 <col:18, col:19> 'int' <LValueToRValue>
|       | |   | `-UnaryOperator 0x5620750b35e8 <col:18, col:19> 'int' lvalue prefix '*' cannot overflow
|       | |   |   `-ImplicitCastExpr 0x5620750b35d0 <col:19> 'int *' <LValueToRValue>
|       | |   |     `-DeclRefExpr 0x5620750b35b0 <col:19> 'int *' lvalue ParmVar 0x5620750b2e30 'x' 'int *'
|       | |   `-ImplicitCastExpr 0x5620750b3638 <col:23> 'int' <LValueToRValue>
|       | |     `-DeclRefExpr 0x5620750b3600 <col:23> 'int' lvalue ParmVar 0x5620750b2fb0 'step' 'int'
|       | `-IfStmt 0x5620750b3868 <line:37:14, line:38:23>
|       |   |-BinaryOperator 0x5620750b3718 <line:37:17, col:24> 'int' '<'
|       |   | |-ImplicitCastExpr 0x5620750b3700 <col:17> 'int' <LValueToRValue>
|       |   | | `-DeclRefExpr 0x5620750b3690 <col:17> 'int' lvalue Var 0x5620750b3300 'err' 'int'
|       |   | `-UnaryOperator 0x5620750b36e8 <col:23, col:24> 'int' prefix '-'
|       |   |   `-ImplicitCastExpr 0x5620750b36d0 <col:24> 'int' <LValueToRValue>
|       |   |     `-DeclRefExpr 0x5620750b36b0 <col:24> 'int' lvalue ParmVar 0x5620750b2f30 'tol' 'int'
|       |   `-BinaryOperator 0x5620750b3848 <line:38:13, col:23> 'int' '='
|       |     |-UnaryOperator 0x5620750b3770 <col:13, col:14> 'int' lvalue prefix '*' cannot overflow
|       |     | `-ImplicitCastExpr 0x5620750b3758 <col:14> 'int *' <LValueToRValue>
|       |     |   `-DeclRefExpr 0x5620750b3738 <col:14> 'int *' lvalue ParmVar 0x5620750b2e30 'x' 'int *'
|       |     `-BinaryOperator 0x5620750b3828 <col:18, col:23> 'int' '+'
|       |       |-ImplicitCastExpr 0x5620750b37f8 <col:18, col:19> 'int' <LValueToRValue>
|       |       | `-UnaryOperator 0x5620750b37c0 <col:18, col:19> 'int' lvalue prefix '*' cannot overflow
|       |       |   `-ImplicitCastExpr 0x5620750b37a8 <col:19> 'int *' <LValueToRValue>
|       |       |     `-DeclRefExpr 0x5620750b3788 <col:19> 'int *' lvalue ParmVar 0x5620750b2e30 'x' 'int *'
|       |       `-ImplicitCastExpr 0x5620750b3810 <col:23> 'int' <LValueToRValue>
|       |         `-DeclRefExpr 0x5620750b37d8 <col:23> 'int' lvalue ParmVar 0x5620750b2fb0 'step' 'int'
|       `-BinaryOperator 0x5620750b3988 <line:40:9, col:20> 'int' '='
|         |-DeclRefExpr 0x5620750b38a8 <col:9> 'int' lvalue Var 0x5620750b3300 'err' 'int'
|         `-BinaryOperator 0x5620750b3968 <col:15, col:20> 'int' '-'
|           |-ImplicitCastExpr 0x5620750b3938 <col:15, col:16> 'int' <LValueToRValue>
|           | `-UnaryOperator 0x5620750b3900 <col:15, col:16> 'int' lvalue prefix '*' cannot overflow
|           |   `-ImplicitCastExpr 0x5620750b38e8 <col:16> 'int *' <LValueToRValue>
|           |     `-DeclRefExpr 0x5620750b38c8 <col:16> 'int *' lvalue ParmVar 0x5620750b2e30 'x' 'int *'
|           `-ImplicitCastExpr 0x5620750b3950 <col:20> 'int' <LValueToRValue>
|             `-DeclRefExpr 0x5620750b3918 <col:20> 'int' lvalue ParmVar 0x5620750b2eb0 'obj' 'int'
`-FunctionDecl 0x5620750b3a58 <line:44:1, line:52:1> line:44:6 test 'void ()'
  `-CompoundStmt 0x5620750b4908 <line:45:1, line:52:1>
    |-DeclStmt 0x5620750b3b78 <line:46:5, col:10>
    | `-VarDecl 0x5620750b3b10 <col:5, col:9> col:9 used x 'int'
    |-DeclStmt 0x5620750b3c10 <line:47:5, col:12>
    | `-VarDecl 0x5620750b3ba8 <col:5, col:9> col:9 used obj 'int'
    |-DeclStmt 0x5620750b3ca8 <line:48:5, col:12>
    | `-VarDecl 0x5620750b3c40 <col:5, col:9> col:9 used tol 'int'
    |-DeclStmt 0x5620750b3d40 <line:49:5, col:13>
    | `-VarDecl 0x5620750b3cd8 <col:5, col:9> col:9 used step 'int'
    `-CallExpr 0x5620750b4880 <line:51:5, col:32> 'void'
      |-ImplicitCastExpr 0x5620750b4868 <col:5> 'void (*)(int *, int, int, int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x5620750b3d58 <col:5> 'void (int *, int, int, int)' Function 0x5620750b30a8 'correct1' 'void (int *, int, int, int)'
      |-UnaryOperator 0x5620750b3d98 <col:14, col:15> 'int *' prefix '&' cannot overflow
      | `-DeclRefExpr 0x5620750b3d78 <col:15> 'int' lvalue Var 0x5620750b3b10 'x' 'int'
      |-ImplicitCastExpr 0x5620750b48c0 <col:18> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x5620750b3db0 <col:18> 'int' lvalue Var 0x5620750b3ba8 'obj' 'int'
      |-ImplicitCastExpr 0x5620750b48d8 <col:23> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x5620750b3dd0 <col:23> 'int' lvalue Var 0x5620750b3c40 'tol' 'int'
      `-ImplicitCastExpr 0x5620750b48f0 <col:28> 'int' <LValueToRValue>
        `-DeclRefExpr 0x5620750b4820 <col:28> 'int' lvalue Var 0x5620750b3cd8 'step' 'int'
