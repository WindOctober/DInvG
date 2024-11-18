./Benchmark/PLDI/VMCAI2019/tiny/loop_seq.c
[info] Using default compilation options.
TranslationUnitDecl 0x55c698cc2dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55c698cc3660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55c698cc3360 '__int128'
|-TypedefDecl 0x55c698cc36d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55c698cc3380 'unsigned __int128'
|-TypedefDecl 0x55c698cc39d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55c698cc37b0 'struct __NSConstantString_tag'
|   `-Record 0x55c698cc3728 '__NSConstantString_tag'
|-TypedefDecl 0x55c698cc3a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55c698cc3a30 'char *'
|   `-BuiltinType 0x55c698cc2e60 'char'
|-TypedefDecl 0x55c698cc3d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55c698cc3d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55c698cc3b50 'struct __va_list_tag'
|     `-Record 0x55c698cc3ac8 '__va_list_tag'
|-FunctionDecl 0x55c698d22fa8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/loop_seq.c:33:1, line:53:1> line:33:6 used loop_seq 'void (int *, int, int)'
| |-ParmVarDecl 0x55c698d22dc0 <col:15, col:21> col:21 used r 'int *'
| |-ParmVarDecl 0x55c698d22e40 <col:24, col:28> col:28 used n 'int'
| |-ParmVarDecl 0x55c698d22ec0 <col:31, col:35> col:35 used m 'int'
| `-CompoundStmt 0x55c698d238a8 <col:38, line:53:1>
|   |-DeclStmt 0x55c698d23128 <line:34:5, col:10>
|   | `-VarDecl 0x55c698d230c0 <col:5, col:9> col:9 used i 'int'
|   |-DeclStmt 0x55c698d231c0 <line:35:5, col:10>
|   | `-VarDecl 0x55c698d23158 <col:5, col:9> col:9 used j 'int'
|   |-IfStmt 0x55c698d232f8 <line:37:5, line:38:9>
|   | |-BinaryOperator 0x55c698d232c8 <line:37:8, col:21> 'int' '||'
|   | | |-BinaryOperator 0x55c698d23230 <col:8, col:12> 'int' '<'
|   | | | |-ImplicitCastExpr 0x55c698d23218 <col:8> 'int' <LValueToRValue>
|   | | | | `-DeclRefExpr 0x55c698d231d8 <col:8> 'int' lvalue ParmVar 0x55c698d22e40 'n' 'int'
|   | | | `-IntegerLiteral 0x55c698d231f8 <col:12> 'int' 0
|   | | `-BinaryOperator 0x55c698d232a8 <col:17, col:21> 'int' '<'
|   | |   |-ImplicitCastExpr 0x55c698d23290 <col:17> 'int' <LValueToRValue>
|   | |   | `-DeclRefExpr 0x55c698d23250 <col:17> 'int' lvalue ParmVar 0x55c698d22ec0 'm' 'int'
|   | |   `-IntegerLiteral 0x55c698d23270 <col:21> 'int' 0
|   | `-ReturnStmt 0x55c698d232e8 <line:38:9>
|   |-BinaryOperator 0x55c698d23380 <line:40:5, col:10> 'int' '='
|   | |-UnaryOperator 0x55c698d23348 <col:5, col:6> 'int' lvalue prefix '*' cannot overflow
|   | | `-ImplicitCastExpr 0x55c698d23330 <col:6> 'int *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55c698d23310 <col:6> 'int *' lvalue ParmVar 0x55c698d22dc0 'r' 'int *'
|   | `-IntegerLiteral 0x55c698d23360 <col:10> 'int' 0
|   |-BinaryOperator 0x55c698d233e0 <line:41:5, col:9> 'int' '='
|   | |-DeclRefExpr 0x55c698d233a0 <col:5> 'int' lvalue Var 0x55c698d230c0 'i' 'int'
|   | `-IntegerLiteral 0x55c698d233c0 <col:9> 'int' 0
|   |-WhileStmt 0x55c698d23600 <line:43:5, line:46:5>
|   | |-BinaryOperator 0x55c698d23470 <line:43:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x55c698d23440 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55c698d23400 <col:11> 'int' lvalue Var 0x55c698d230c0 'i' 'int'
|   | | `-ImplicitCastExpr 0x55c698d23458 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55c698d23420 <col:15> 'int' lvalue ParmVar 0x55c698d22e40 'n' 'int'
|   | `-CompoundStmt 0x55c698d235e0 <col:17, line:46:5>
|   |   |-BinaryOperator 0x55c698d23588 <line:44:9, col:19> 'int' '='
|   |   | |-UnaryOperator 0x55c698d234c8 <col:9, col:10> 'int' lvalue prefix '*' cannot overflow
|   |   | | `-ImplicitCastExpr 0x55c698d234b0 <col:10> 'int *' <LValueToRValue>
|   |   | |   `-DeclRefExpr 0x55c698d23490 <col:10> 'int *' lvalue ParmVar 0x55c698d22dc0 'r' 'int *'
|   |   | `-BinaryOperator 0x55c698d23568 <col:14, col:19> 'int' '+'
|   |   |   |-ImplicitCastExpr 0x55c698d23550 <col:14, col:15> 'int' <LValueToRValue>
|   |   |   | `-UnaryOperator 0x55c698d23518 <col:14, col:15> 'int' lvalue prefix '*' cannot overflow
|   |   |   |   `-ImplicitCastExpr 0x55c698d23500 <col:15> 'int *' <LValueToRValue>
|   |   |   |     `-DeclRefExpr 0x55c698d234e0 <col:15> 'int *' lvalue ParmVar 0x55c698d22dc0 'r' 'int *'
|   |   |   `-IntegerLiteral 0x55c698d23530 <col:19> 'int' 1
|   |   `-UnaryOperator 0x55c698d235c8 <line:45:9, col:10> 'int' postfix '++'
|   |     `-DeclRefExpr 0x55c698d235a8 <col:9> 'int' lvalue Var 0x55c698d230c0 'i' 'int'
|   |-BinaryOperator 0x55c698d23670 <line:48:5, col:9> 'int' '='
|   | |-DeclRefExpr 0x55c698d23618 <col:5> 'int' lvalue Var 0x55c698d23158 'j' 'int'
|   | `-ImplicitCastExpr 0x55c698d23658 <col:9> 'int' <LValueToRValue>
|   |   `-DeclRefExpr 0x55c698d23638 <col:9> 'int' lvalue Var 0x55c698d230c0 'i' 'int'
|   `-WhileStmt 0x55c698d23890 <line:49:5, line:52:5>
|     |-BinaryOperator 0x55c698d23700 <line:49:11, col:15> 'int' '<'
|     | |-ImplicitCastExpr 0x55c698d236d0 <col:11> 'int' <LValueToRValue>
|     | | `-DeclRefExpr 0x55c698d23690 <col:11> 'int' lvalue Var 0x55c698d23158 'j' 'int'
|     | `-ImplicitCastExpr 0x55c698d236e8 <col:15> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55c698d236b0 <col:15> 'int' lvalue ParmVar 0x55c698d22ec0 'm' 'int'
|     `-CompoundStmt 0x55c698d23870 <col:17, line:52:5>
|       |-BinaryOperator 0x55c698d23818 <line:50:9, col:19> 'int' '='
|       | |-UnaryOperator 0x55c698d23758 <col:9, col:10> 'int' lvalue prefix '*' cannot overflow
|       | | `-ImplicitCastExpr 0x55c698d23740 <col:10> 'int *' <LValueToRValue>
|       | |   `-DeclRefExpr 0x55c698d23720 <col:10> 'int *' lvalue ParmVar 0x55c698d22dc0 'r' 'int *'
|       | `-BinaryOperator 0x55c698d237f8 <col:14, col:19> 'int' '+'
|       |   |-ImplicitCastExpr 0x55c698d237e0 <col:14, col:15> 'int' <LValueToRValue>
|       |   | `-UnaryOperator 0x55c698d237a8 <col:14, col:15> 'int' lvalue prefix '*' cannot overflow
|       |   |   `-ImplicitCastExpr 0x55c698d23790 <col:15> 'int *' <LValueToRValue>
|       |   |     `-DeclRefExpr 0x55c698d23770 <col:15> 'int *' lvalue ParmVar 0x55c698d22dc0 'r' 'int *'
|       |   `-IntegerLiteral 0x55c698d237c0 <col:19> 'int' 1
|       `-UnaryOperator 0x55c698d23858 <line:51:9, col:10> 'int' postfix '++'
|         `-DeclRefExpr 0x55c698d23838 <col:9> 'int' lvalue Var 0x55c698d23158 'j' 'int'
`-FunctionDecl 0x55c698d23948 <line:55:1, line:61:1> line:55:6 test 'void ()'
  `-CompoundStmt 0x55c698d23cf8 <line:56:1, line:61:1>
    |-DeclStmt 0x55c698d23a68 <line:57:5, col:10>
    | `-VarDecl 0x55c698d23a00 <col:5, col:9> col:9 used r 'int'
    |-DeclStmt 0x55c698d23b00 <line:58:5, col:10>
    | `-VarDecl 0x55c698d23a98 <col:5, col:9> col:9 used n 'int'
    |-DeclStmt 0x55c698d23b98 <line:59:5, col:10>
    | `-VarDecl 0x55c698d23b30 <col:5, col:9> col:9 used m 'int'
    `-CallExpr 0x55c698d23c90 <line:60:5, col:22> 'void'
      |-ImplicitCastExpr 0x55c698d23c78 <col:5> 'void (*)(int *, int, int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55c698d23bb0 <col:5> 'void (int *, int, int)' Function 0x55c698d22fa8 'loop_seq' 'void (int *, int, int)'
      |-UnaryOperator 0x55c698d23bf0 <col:14, col:15> 'int *' prefix '&' cannot overflow
      | `-DeclRefExpr 0x55c698d23bd0 <col:15> 'int' lvalue Var 0x55c698d23a00 'r' 'int'
      |-ImplicitCastExpr 0x55c698d23cc8 <col:18> 'int' <LValueToRValue>
      | `-DeclRefExpr 0x55c698d23c08 <col:18> 'int' lvalue Var 0x55c698d23a98 'n' 'int'
      `-ImplicitCastExpr 0x55c698d23ce0 <col:21> 'int' <LValueToRValue>
        `-DeclRefExpr 0x55c698d23c28 <col:21> 'int' lvalue Var 0x55c698d23b30 'm' 'int'
