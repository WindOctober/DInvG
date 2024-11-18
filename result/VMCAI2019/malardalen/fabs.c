./Benchmark/PLDI/VMCAI2019/malardalen/fabs.c
[info] Using default compilation options.
TranslationUnitDecl 0x555d2fe10dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x555d2fe11660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x555d2fe11360 '__int128'
|-TypedefDecl 0x555d2fe116d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x555d2fe11380 'unsigned __int128'
|-TypedefDecl 0x555d2fe119d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x555d2fe117b0 'struct __NSConstantString_tag'
|   `-Record 0x555d2fe11728 '__NSConstantString_tag'
|-TypedefDecl 0x555d2fe11a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x555d2fe11a30 'char *'
|   `-BuiltinType 0x555d2fe10e60 'char'
|-TypedefDecl 0x555d2fe11d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x555d2fe11d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x555d2fe11b50 'struct __va_list_tag'
|     `-Record 0x555d2fe11ac8 '__va_list_tag'
|-FunctionDecl 0x555d2fe70e20 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/malardalen/fabs.c:2:1, line:19:1> line:2:15 used fabs 'double (double, int *, int *)' static
| |-ParmVarDecl 0x555d2fe70c08 <col:20, col:27> col:27 used n 'double'
| |-ParmVarDecl 0x555d2fe70cb0 <line:3:9, col:15> col:15 used cptr_fabs_1 'int *'
| |-ParmVarDecl 0x555d2fe70d30 <line:4:9, col:15> col:15 used cptr_fabs_2 'int *'
| `-CompoundStmt 0x555d2fe71498 <line:5:1, line:19:1>
|   |-DeclStmt 0x555d2fe70fa0 <line:6:3, col:12>
|   | `-VarDecl 0x555d2fe70f38 <col:3, col:10> col:10 used f 'double'
|   |-BinaryOperator 0x555d2fe71028 <line:7:3, col:18> 'int' '='
|   | |-UnaryOperator 0x555d2fe70ff0 <col:3, col:4> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x555d2fe70fd8 <col:4> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x555d2fe70fb8 <col:4> 'int *' lvalue ParmVar 0x555d2fe70cb0 'cptr_fabs_1' 'int *'
|   | `-IntegerLiteral 0x555d2fe71008 <col:18> 'int' 0
|   |-BinaryOperator 0x555d2fe710b8 <line:8:3, col:18> 'int' '='
|   | |-UnaryOperator 0x555d2fe71080 <col:3, col:4> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x555d2fe71068 <col:4> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x555d2fe71048 <col:4> 'int *' lvalue ParmVar 0x555d2fe70d30 'cptr_fabs_2' 'int *'
|   | `-IntegerLiteral 0x555d2fe71098 <col:18> 'int' 0
|   `-CompoundStmt 0x555d2fe71478 <line:9:3, line:18:1>
|     |-IfStmt 0x555d2fe713e8 <line:10:3, line:16:3> has_else
|     | |-BinaryOperator 0x555d2fe71170 <line:10:7, col:21> 'int' '>='
|     | | |-ImplicitCastExpr 0x555d2fe71158 <col:7> 'double' <LValueToRValue>
|     | | | `-DeclRefExpr 0x555d2fe710d8 <col:7> 'double' lvalue ParmVar 0x555d2fe70c08 'n' 'double'
|     | | `-CStyleCastExpr 0x555d2fe71130 <col:12, col:21> 'double' <IntegralToFloating>
|     | |   `-IntegerLiteral 0x555d2fe710f8 <col:21> 'int' 0
|     | |-CompoundStmt 0x555d2fe71290 <col:24, line:13:3>
|     | | |-UnaryOperator 0x555d2fe71200 <line:11:5, col:20> 'int' postfix '++'
|     | | | `-ParenExpr 0x555d2fe711e0 <col:5, col:18> 'int' lvalue
|     | | |   `-UnaryOperator 0x555d2fe711c8 <col:6, col:7> 'int' lvalue prefix '*' cannot overflow
|     | | |     `-ImplicitCastExpr 0x555d2fe711b0 <col:7> 'int *' <LValueToRValue>
|     | | |       `-DeclRefExpr 0x555d2fe71190 <col:7> 'int *' lvalue ParmVar 0x555d2fe70cb0 'cptr_fabs_1' 'int *'
|     | | `-BinaryOperator 0x555d2fe71270 <line:12:5, col:9> 'double' '='
|     | |   |-DeclRefExpr 0x555d2fe71218 <col:5> 'double' lvalue Var 0x555d2fe70f38 'f' 'double'
|     | |   `-ImplicitCastExpr 0x555d2fe71258 <col:9> 'double' <LValueToRValue>
|     | |     `-DeclRefExpr 0x555d2fe71238 <col:9> 'double' lvalue ParmVar 0x555d2fe70c08 'n' 'double'
|     | `-CompoundStmt 0x555d2fe713c8 <line:13:10, line:16:3>
|     |   |-UnaryOperator 0x555d2fe71320 <line:14:5, col:20> 'int' postfix '++'
|     |   | `-ParenExpr 0x555d2fe71300 <col:5, col:18> 'int' lvalue
|     |   |   `-UnaryOperator 0x555d2fe712e8 <col:6, col:7> 'int' lvalue prefix '*' cannot overflow
|     |   |     `-ImplicitCastExpr 0x555d2fe712d0 <col:7> 'int *' <LValueToRValue>
|     |   |       `-DeclRefExpr 0x555d2fe712b0 <col:7> 'int *' lvalue ParmVar 0x555d2fe70d30 'cptr_fabs_2' 'int *'
|     |   `-BinaryOperator 0x555d2fe713a8 <line:15:5, col:11> 'double' '='
|     |     |-DeclRefExpr 0x555d2fe71338 <col:5> 'double' lvalue Var 0x555d2fe70f38 'f' 'double'
|     |     `-UnaryOperator 0x555d2fe71390 <col:9, col:11> 'double' prefix '-'
|     |       `-ImplicitCastExpr 0x555d2fe71378 <col:11> 'double' <LValueToRValue>
|     |         `-DeclRefExpr 0x555d2fe71358 <col:11> 'double' lvalue ParmVar 0x555d2fe70c08 'n' 'double'
|     `-ReturnStmt 0x555d2fe71468 <line:17:3, col:12>
|       `-ImplicitCastExpr 0x555d2fe71450 <col:10, col:12> 'double' <LValueToRValue>
|         `-ParenExpr 0x555d2fe71430 <col:10, col:12> 'double' lvalue
|           `-DeclRefExpr 0x555d2fe71410 <col:11> 'double' lvalue Var 0x555d2fe70f38 'f' 'double'
`-FunctionDecl 0x555d2fe71520 <line:21:1, line:30:1> line:21:5 main 'int ()'
  `-CompoundStmt 0x555d2fe71998 <line:22:1, line:30:1>
    |-DeclStmt 0x555d2fe71640 <line:23:5, col:13>
    | `-VarDecl 0x555d2fe715d8 <col:5, col:12> col:12 used n 'double'
    |-DeclStmt 0x555d2fe716d8 <line:24:5, col:20>
    | `-VarDecl 0x555d2fe71670 <col:5, col:9> col:9 used cptr_fabs_1 'int'
    |-DeclStmt 0x555d2fe71770 <line:25:5, col:20>
    | `-VarDecl 0x555d2fe71708 <col:5, col:9> col:9 used cptr_fabs_2 'int'
    |-DeclStmt 0x555d2fe71950 <line:27:5, col:51>
    | `-VarDecl 0x555d2fe717a0 <col:5, col:50> col:12 r 'double' cinit
    |   `-CallExpr 0x555d2fe71900 <col:16, col:50> 'double'
    |     |-ImplicitCastExpr 0x555d2fe718e8 <col:16> 'double (*)(double, int *, int *)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x555d2fe71808 <col:16> 'double (double, int *, int *)' Function 0x555d2fe70e20 'fabs' 'double (double, int *, int *)'
    |     |-ImplicitCastExpr 0x555d2fe71938 <col:21> 'double' <LValueToRValue>
    |     | `-DeclRefExpr 0x555d2fe71828 <col:21> 'double' lvalue Var 0x555d2fe715d8 'n' 'double'
    |     |-UnaryOperator 0x555d2fe71868 <col:24, col:25> 'int *' prefix '&' cannot overflow
    |     | `-DeclRefExpr 0x555d2fe71848 <col:25> 'int' lvalue Var 0x555d2fe71670 'cptr_fabs_1' 'int'
    |     `-UnaryOperator 0x555d2fe718a0 <col:38, col:39> 'int *' prefix '&' cannot overflow
    |       `-DeclRefExpr 0x555d2fe71880 <col:39> 'int' lvalue Var 0x555d2fe71708 'cptr_fabs_2' 'int'
    `-ReturnStmt 0x555d2fe71988 <line:29:5, col:12>
      `-IntegerLiteral 0x555d2fe71968 <col:12> 'int' 0
