./Benchmark/PLDI/SVComp/loops-crafted-1/theatreSquare.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/theatreSquare.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x556ca6878eb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x556ca6879750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x556ca6879450 '__int128'
|-TypedefDecl 0x556ca68797c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x556ca6879470 'unsigned __int128'
|-TypedefDecl 0x556ca6879ac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x556ca68798a0 'struct __NSConstantString_tag'
|   `-Record 0x556ca6879818 '__NSConstantString_tag'
|-TypedefDecl 0x556ca6879b60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x556ca6879b20 'char *'
|   `-BuiltinType 0x556ca6878f50 'char'
|-TypedefDecl 0x556ca6879e58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x556ca6879e00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x556ca6879c40 'struct __va_list_tag'
|     `-Record 0x556ca6879bb8 '__va_list_tag'
|-FunctionDecl 0x556ca68d95e8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/theatreSquare.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556ca68d9688 prev 0x556ca68d95e8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556ca68d9a08 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556ca68d9740 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x556ca68d97c0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x556ca68d9840 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x556ca68d98c0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x556ca68d9ac8 <col:99>
|-FunctionDecl 0x556ca68d9bb8 <line:3:1, col:79> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x556ca68d9ee8 <col:20, col:79>
|   `-CallExpr 0x556ca68d9e00 <col:22, col:76> 'void'
|     |-ImplicitCastExpr 0x556ca68d9de8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x556ca68d9c58 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x556ca68d9a08 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x556ca68d9e58 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x556ca68d9e40 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x556ca68d9cb8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x556ca68d9e88 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x556ca68d9e70 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x556ca68d9d18 <col:41> 'char [16]' lvalue "theatreSquare.c"
|     |-ImplicitCastExpr 0x556ca68d9ea0 <col:60> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x556ca68d9d40 <col:60> 'int' 3
|     `-ImplicitCastExpr 0x556ca68d9ed0 <col:63> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x556ca68d9eb8 <col:63> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x556ca68d9d98 <col:63> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x556ca68d9fd0 <line:4:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x556ca68da148 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x556ca68da088 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x556ca68da428 <col:34, line:10:1>
|   |-IfStmt 0x556ca68da400 <line:6:5, line:8:5>
|   | |-UnaryOperator 0x556ca68da248 <line:6:9, col:15> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x556ca68da230 <col:10, col:15> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x556ca68da210 <col:10, col:15> 'int' lvalue
|   | |     `-DeclRefExpr 0x556ca68da1f0 <col:11> 'int' lvalue ParmVar 0x556ca68da088 'cond' 'int'
|   | `-CompoundStmt 0x556ca68da3e8 <col:18, line:8:5>
|   |   `-LabelStmt 0x556ca68da3d0 <line:7:9, col:39> 'ERROR'
|   |     `-CompoundStmt 0x556ca68da360 <col:16, col:39>
|   |       |-CallExpr 0x556ca68da2c0 <col:17, col:29> 'void'
|   |       | `-ImplicitCastExpr 0x556ca68da2a8 <col:17> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x556ca68da260 <col:17> 'void ()' Function 0x556ca68d9bb8 'reach_error' 'void ()'
|   |       `-CallExpr 0x556ca68da340 <col:31, col:37> 'void'
|   |         `-ImplicitCastExpr 0x556ca68da328 <col:31> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x556ca68da2e0 <col:31> 'void (void) __attribute__((noreturn))' Function 0x556ca68d9688 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x556ca68da418 <line:9:5>
|-FunctionDecl 0x556ca68dc060 <line:34:1, line:59:1> line:34:5 used correct_version 'int (int, int, int)'
| |-ParmVarDecl 0x556ca68da460 <col:21, col:25> col:25 used n 'int'
| |-ParmVarDecl 0x556ca68dbef0 <col:28, col:32> col:32 used m 'int'
| |-ParmVarDecl 0x556ca68dbf70 <col:35, col:39> col:39 used a 'int'
| `-CompoundStmt 0x556ca68dcc80 <line:35:1, line:59:1>
|   |-DeclStmt 0x556ca68dc3c0 <line:36:5, col:35>
|   | |-VarDecl 0x556ca68dc130 <col:5, col:13> col:9 used i 'int' cinit
|   | | `-IntegerLiteral 0x556ca68dc198 <col:13> 'int' 0
|   | |-VarDecl 0x556ca68dc1d0 <col:5, col:20> col:16 used j 'int' cinit
|   | | `-IntegerLiteral 0x556ca68dc238 <col:20> 'int' 0
|   | |-VarDecl 0x556ca68dc270 <col:5, col:27> col:23 used b 'int' cinit
|   | | `-IntegerLiteral 0x556ca68dc2d8 <col:27> 'int' 0
|   | `-VarDecl 0x556ca68dc310 <col:5, col:34> col:30 used l 'int' cinit
|   |   `-IntegerLiteral 0x556ca68dc378 <col:34> 'int' 0
|   |-WhileStmt 0x556ca68dc610 <line:38:5, line:42:5>
|   | |-BinaryOperator 0x556ca68dc448 <line:38:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x556ca68dc418 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x556ca68dc3d8 <col:11> 'int' lvalue Var 0x556ca68dc270 'b' 'int'
|   | | `-ImplicitCastExpr 0x556ca68dc430 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x556ca68dc3f8 <col:15> 'int' lvalue ParmVar 0x556ca68da460 'n' 'int'
|   | `-CompoundStmt 0x556ca68dc5f0 <line:39:5, line:42:5>
|   |   |-BinaryOperator 0x556ca68dc518 <line:40:9, col:17> 'int' '='
|   |   | |-DeclRefExpr 0x556ca68dc468 <col:9> 'int' lvalue Var 0x556ca68dc270 'b' 'int'
|   |   | `-BinaryOperator 0x556ca68dc4f8 <col:13, col:17> 'int' '+'
|   |   |   |-ImplicitCastExpr 0x556ca68dc4c8 <col:13> 'int' <LValueToRValue>
|   |   |   | `-DeclRefExpr 0x556ca68dc488 <col:13> 'int' lvalue Var 0x556ca68dc270 'b' 'int'
|   |   |   `-ImplicitCastExpr 0x556ca68dc4e0 <col:17> 'int' <LValueToRValue>
|   |   |     `-DeclRefExpr 0x556ca68dc4a8 <col:17> 'int' lvalue ParmVar 0x556ca68dbf70 'a' 'int'
|   |   `-BinaryOperator 0x556ca68dc5d0 <line:41:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x556ca68dc538 <col:9> 'int' lvalue Var 0x556ca68dc130 'i' 'int'
|   |     `-BinaryOperator 0x556ca68dc5b0 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x556ca68dc598 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x556ca68dc558 <col:13> 'int' lvalue Var 0x556ca68dc130 'i' 'int'
|   |       `-IntegerLiteral 0x556ca68dc578 <col:17> 'int' 1
|   |-WhileStmt 0x556ca68dc860 <line:44:5, line:48:5>
|   | |-BinaryOperator 0x556ca68dc698 <line:44:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x556ca68dc668 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x556ca68dc628 <col:11> 'int' lvalue Var 0x556ca68dc310 'l' 'int'
|   | | `-ImplicitCastExpr 0x556ca68dc680 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x556ca68dc648 <col:15> 'int' lvalue ParmVar 0x556ca68dbef0 'm' 'int'
|   | `-CompoundStmt 0x556ca68dc840 <line:45:5, line:48:5>
|   |   |-BinaryOperator 0x556ca68dc768 <line:46:9, col:17> 'int' '='
|   |   | |-DeclRefExpr 0x556ca68dc6b8 <col:9> 'int' lvalue Var 0x556ca68dc310 'l' 'int'
|   |   | `-BinaryOperator 0x556ca68dc748 <col:13, col:17> 'int' '+'
|   |   |   |-ImplicitCastExpr 0x556ca68dc718 <col:13> 'int' <LValueToRValue>
|   |   |   | `-DeclRefExpr 0x556ca68dc6d8 <col:13> 'int' lvalue Var 0x556ca68dc310 'l' 'int'
|   |   |   `-ImplicitCastExpr 0x556ca68dc730 <col:17> 'int' <LValueToRValue>
|   |   |     `-DeclRefExpr 0x556ca68dc6f8 <col:17> 'int' lvalue ParmVar 0x556ca68dbf70 'a' 'int'
|   |   `-BinaryOperator 0x556ca68dc820 <line:47:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x556ca68dc788 <col:9> 'int' lvalue Var 0x556ca68dc1d0 'j' 'int'
|   |     `-BinaryOperator 0x556ca68dc800 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x556ca68dc7e8 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x556ca68dc7a8 <col:13> 'int' lvalue Var 0x556ca68dc1d0 'j' 'int'
|   |       `-IntegerLiteral 0x556ca68dc7c8 <col:17> 'int' 1
|   |-DeclStmt 0x556ca68dc9d0 <line:50:5, col:21>
|   | |-VarDecl 0x556ca68dc890 <col:5, col:13> col:9 used x 'int' cinit
|   | | `-IntegerLiteral 0x556ca68dc8f8 <col:13> 'int' 0
|   | `-VarDecl 0x556ca68dc930 <col:5, col:20> col:16 used y 'int' cinit
|   |   `-IntegerLiteral 0x556ca68dc998 <col:20> 'int' 0
|   |-WhileStmt 0x556ca68dcc20 <line:52:5, line:56:5>
|   | |-BinaryOperator 0x556ca68dca58 <line:52:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x556ca68dca28 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x556ca68dc9e8 <col:11> 'int' lvalue Var 0x556ca68dc890 'x' 'int'
|   | | `-ImplicitCastExpr 0x556ca68dca40 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x556ca68dca08 <col:15> 'int' lvalue Var 0x556ca68dc130 'i' 'int'
|   | `-CompoundStmt 0x556ca68dcc00 <line:53:5, line:56:5>
|   |   |-BinaryOperator 0x556ca68dcb28 <line:54:9, col:17> 'int' '='
|   |   | |-DeclRefExpr 0x556ca68dca78 <col:9> 'int' lvalue Var 0x556ca68dc930 'y' 'int'
|   |   | `-BinaryOperator 0x556ca68dcb08 <col:13, col:17> 'int' '+'
|   |   |   |-ImplicitCastExpr 0x556ca68dcad8 <col:13> 'int' <LValueToRValue>
|   |   |   | `-DeclRefExpr 0x556ca68dca98 <col:13> 'int' lvalue Var 0x556ca68dc930 'y' 'int'
|   |   |   `-ImplicitCastExpr 0x556ca68dcaf0 <col:17> 'int' <LValueToRValue>
|   |   |     `-DeclRefExpr 0x556ca68dcab8 <col:17> 'int' lvalue Var 0x556ca68dc1d0 'j' 'int'
|   |   `-BinaryOperator 0x556ca68dcbe0 <line:55:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x556ca68dcb48 <col:9> 'int' lvalue Var 0x556ca68dc890 'x' 'int'
|   |     `-BinaryOperator 0x556ca68dcbc0 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x556ca68dcba8 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x556ca68dcb68 <col:13> 'int' lvalue Var 0x556ca68dc890 'x' 'int'
|   |       `-IntegerLiteral 0x556ca68dcb88 <col:17> 'int' 1
|   `-ReturnStmt 0x556ca68dcc70 <line:58:5, col:12>
|     `-ImplicitCastExpr 0x556ca68dcc58 <col:12> 'int' <LValueToRValue>
|       `-DeclRefExpr 0x556ca68dcc38 <col:12> 'int' lvalue Var 0x556ca68dc930 'y' 'int'
|-FunctionDecl 0x556ca68dcf40 <line:61:1, line:86:1> line:61:5 used student_version 'int (int, int, int)'
| |-ParmVarDecl 0x556ca68dcd68 <col:21, col:25> col:25 used n 'int'
| |-ParmVarDecl 0x556ca68dcde8 <col:28, col:32> col:32 used m 'int'
| |-ParmVarDecl 0x556ca68dce68 <col:35, col:39> col:39 used a 'int'
| `-CompoundStmt 0x556ca68ddb60 <line:62:1, line:86:1>
|   |-DeclStmt 0x556ca68dd2a0 <line:63:5, col:35>
|   | |-VarDecl 0x556ca68dd010 <col:5, col:13> col:9 used i 'int' cinit
|   | | `-IntegerLiteral 0x556ca68dd078 <col:13> 'int' 0
|   | |-VarDecl 0x556ca68dd0b0 <col:5, col:20> col:16 used j 'int' cinit
|   | | `-IntegerLiteral 0x556ca68dd118 <col:20> 'int' 0
|   | |-VarDecl 0x556ca68dd150 <col:5, col:27> col:23 used b 'int' cinit
|   | | `-IntegerLiteral 0x556ca68dd1b8 <col:27> 'int' 0
|   | `-VarDecl 0x556ca68dd1f0 <col:5, col:34> col:30 used l 'int' cinit
|   |   `-IntegerLiteral 0x556ca68dd258 <col:34> 'int' 0
|   |-WhileStmt 0x556ca68dd4f0 <line:65:5, line:69:5>
|   | |-BinaryOperator 0x556ca68dd328 <line:65:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x556ca68dd2f8 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x556ca68dd2b8 <col:11> 'int' lvalue Var 0x556ca68dd150 'b' 'int'
|   | | `-ImplicitCastExpr 0x556ca68dd310 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x556ca68dd2d8 <col:15> 'int' lvalue ParmVar 0x556ca68dcd68 'n' 'int'
|   | `-CompoundStmt 0x556ca68dd4d0 <line:66:5, line:69:5>
|   |   |-BinaryOperator 0x556ca68dd3f8 <line:67:9, col:17> 'int' '='
|   |   | |-DeclRefExpr 0x556ca68dd348 <col:9> 'int' lvalue Var 0x556ca68dd150 'b' 'int'
|   |   | `-BinaryOperator 0x556ca68dd3d8 <col:13, col:17> 'int' '+'
|   |   |   |-ImplicitCastExpr 0x556ca68dd3a8 <col:13> 'int' <LValueToRValue>
|   |   |   | `-DeclRefExpr 0x556ca68dd368 <col:13> 'int' lvalue Var 0x556ca68dd150 'b' 'int'
|   |   |   `-ImplicitCastExpr 0x556ca68dd3c0 <col:17> 'int' <LValueToRValue>
|   |   |     `-DeclRefExpr 0x556ca68dd388 <col:17> 'int' lvalue ParmVar 0x556ca68dce68 'a' 'int'
|   |   `-BinaryOperator 0x556ca68dd4b0 <line:68:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x556ca68dd418 <col:9> 'int' lvalue Var 0x556ca68dd010 'i' 'int'
|   |     `-BinaryOperator 0x556ca68dd490 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x556ca68dd478 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x556ca68dd438 <col:13> 'int' lvalue Var 0x556ca68dd010 'i' 'int'
|   |       `-IntegerLiteral 0x556ca68dd458 <col:17> 'int' 1
|   |-WhileStmt 0x556ca68dd740 <line:71:5, line:75:5>
|   | |-BinaryOperator 0x556ca68dd578 <line:71:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x556ca68dd548 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x556ca68dd508 <col:11> 'int' lvalue Var 0x556ca68dd1f0 'l' 'int'
|   | | `-ImplicitCastExpr 0x556ca68dd560 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x556ca68dd528 <col:15> 'int' lvalue ParmVar 0x556ca68dcde8 'm' 'int'
|   | `-CompoundStmt 0x556ca68dd720 <line:72:5, line:75:5>
|   |   |-BinaryOperator 0x556ca68dd648 <line:73:9, col:17> 'int' '='
|   |   | |-DeclRefExpr 0x556ca68dd598 <col:9> 'int' lvalue Var 0x556ca68dd1f0 'l' 'int'
|   |   | `-BinaryOperator 0x556ca68dd628 <col:13, col:17> 'int' '+'
|   |   |   |-ImplicitCastExpr 0x556ca68dd5f8 <col:13> 'int' <LValueToRValue>
|   |   |   | `-DeclRefExpr 0x556ca68dd5b8 <col:13> 'int' lvalue Var 0x556ca68dd1f0 'l' 'int'
|   |   |   `-ImplicitCastExpr 0x556ca68dd610 <col:17> 'int' <LValueToRValue>
|   |   |     `-DeclRefExpr 0x556ca68dd5d8 <col:17> 'int' lvalue ParmVar 0x556ca68dce68 'a' 'int'
|   |   `-BinaryOperator 0x556ca68dd700 <line:74:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x556ca68dd668 <col:9> 'int' lvalue Var 0x556ca68dd0b0 'j' 'int'
|   |     `-BinaryOperator 0x556ca68dd6e0 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x556ca68dd6c8 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x556ca68dd688 <col:13> 'int' lvalue Var 0x556ca68dd0b0 'j' 'int'
|   |       `-IntegerLiteral 0x556ca68dd6a8 <col:17> 'int' 1
|   |-DeclStmt 0x556ca68dd8b0 <line:77:5, col:21>
|   | |-VarDecl 0x556ca68dd770 <col:5, col:13> col:9 used x 'int' cinit
|   | | `-IntegerLiteral 0x556ca68dd7d8 <col:13> 'int' 0
|   | `-VarDecl 0x556ca68dd810 <col:5, col:20> col:16 used y 'int' cinit
|   |   `-IntegerLiteral 0x556ca68dd878 <col:20> 'int' 0
|   |-WhileStmt 0x556ca68ddb00 <line:79:5, line:83:5>
|   | |-BinaryOperator 0x556ca68dd938 <line:79:11, col:15> 'int' '<'
|   | | |-ImplicitCastExpr 0x556ca68dd908 <col:11> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x556ca68dd8c8 <col:11> 'int' lvalue Var 0x556ca68dd770 'x' 'int'
|   | | `-ImplicitCastExpr 0x556ca68dd920 <col:15> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x556ca68dd8e8 <col:15> 'int' lvalue Var 0x556ca68dd010 'i' 'int'
|   | `-CompoundStmt 0x556ca68ddae0 <line:80:5, line:83:5>
|   |   |-BinaryOperator 0x556ca68dda08 <line:81:9, col:17> 'int' '='
|   |   | |-DeclRefExpr 0x556ca68dd958 <col:9> 'int' lvalue Var 0x556ca68dd810 'y' 'int'
|   |   | `-BinaryOperator 0x556ca68dd9e8 <col:13, col:17> 'int' '+'
|   |   |   |-ImplicitCastExpr 0x556ca68dd9b8 <col:13> 'int' <LValueToRValue>
|   |   |   | `-DeclRefExpr 0x556ca68dd978 <col:13> 'int' lvalue Var 0x556ca68dd810 'y' 'int'
|   |   |   `-ImplicitCastExpr 0x556ca68dd9d0 <col:17> 'int' <LValueToRValue>
|   |   |     `-DeclRefExpr 0x556ca68dd998 <col:17> 'int' lvalue Var 0x556ca68dd0b0 'j' 'int'
|   |   `-BinaryOperator 0x556ca68ddac0 <line:82:9, col:17> 'int' '='
|   |     |-DeclRefExpr 0x556ca68dda28 <col:9> 'int' lvalue Var 0x556ca68dd770 'x' 'int'
|   |     `-BinaryOperator 0x556ca68ddaa0 <col:13, col:17> 'int' '+'
|   |       |-ImplicitCastExpr 0x556ca68dda88 <col:13> 'int' <LValueToRValue>
|   |       | `-DeclRefExpr 0x556ca68dda48 <col:13> 'int' lvalue Var 0x556ca68dd770 'x' 'int'
|   |       `-IntegerLiteral 0x556ca68dda68 <col:17> 'int' 1
|   `-ReturnStmt 0x556ca68ddb50 <line:85:5, col:12>
|     `-ImplicitCastExpr 0x556ca68ddb38 <col:12> 'int' <LValueToRValue>
|       `-DeclRefExpr 0x556ca68ddb18 <col:12> 'int' lvalue Var 0x556ca68dd810 'y' 'int'
`-FunctionDecl 0x556ca68ddc80 <line:88:1, line:109:1> line:88:5 main 'int ()'
  `-CompoundStmt 0x556ca68deaa8 <line:89:1, line:109:1>
    |-DeclStmt 0x556ca68de008 <line:91:5, col:88>
    | |-VarDecl 0x556ca68ddd38 <col:5, col:33> col:9 used a 'int' cinit
    | | `-CallExpr 0x556ca68dde00 <col:11, col:33> 'int'
    | |   `-ImplicitCastExpr 0x556ca68ddde8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x556ca68ddda0 <col:11> 'int (void)' Function 0x556ca68d9fd0 '__VERIFIER_nondet_int' 'int (void)'
    | |-VarDecl 0x556ca68dde38 <col:5, col:60> col:36 used n 'int' cinit
    | | `-CallExpr 0x556ca68dded8 <col:38, col:60> 'int'
    | |   `-ImplicitCastExpr 0x556ca68ddec0 <col:38> 'int (*)(void)' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x556ca68ddea0 <col:38> 'int (void)' Function 0x556ca68d9fd0 '__VERIFIER_nondet_int' 'int (void)'
    | `-VarDecl 0x556ca68ddf28 <col:5, col:87> col:63 used m 'int' cinit
    |   `-CallExpr 0x556ca68ddfc8 <col:65, col:87> 'int'
    |     `-ImplicitCastExpr 0x556ca68ddfb0 <col:65> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x556ca68ddf90 <col:65> 'int (void)' Function 0x556ca68d9fd0 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x556ca68de190 <line:93:5, col:53>
    | |-VarDecl 0x556ca68de038 <col:5, col:9> col:9 used n_stones1 'int'
    | `-VarDecl 0x556ca68de0b8 <col:5, col:52> col:20 used n_stones2 'int' cinit
    |   `-CallExpr 0x556ca68de158 <col:30, col:52> 'int'
    |     `-ImplicitCastExpr 0x556ca68de140 <col:30> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x556ca68de120 <col:30> 'int (void)' Function 0x556ca68d9fd0 '__VERIFIER_nondet_int' 'int (void)'
    |-BinaryOperator 0x556ca68de200 <line:95:5, col:17> 'int' '='
    | |-DeclRefExpr 0x556ca68de1a8 <col:5> 'int' lvalue Var 0x556ca68de038 'n_stones1' 'int'
    | `-ImplicitCastExpr 0x556ca68de1e8 <col:17> 'int' <LValueToRValue>
    |   `-DeclRefExpr 0x556ca68de1c8 <col:17> 'int' lvalue Var 0x556ca68de0b8 'n_stones2' 'int'
    |-IfStmt 0x556ca68de948 <line:97:5, line:106:5>
    | |-BinaryOperator 0x556ca68de630 <line:97:8, line:102:17> 'int' '&&'
    | | |-BinaryOperator 0x556ca68de578 <line:97:8, line:101:17> 'int' '&&'
    | | | |-BinaryOperator 0x556ca68de4c0 <line:97:8, line:100:17> 'int' '&&'
    | | | | |-BinaryOperator 0x556ca68de408 <line:97:8, line:99:15> 'int' '&&'
    | | | | | |-BinaryOperator 0x556ca68de350 <line:97:8, line:98:15> 'int' '&&'
    | | | | | | |-ParenExpr 0x556ca68de298 <line:97:8, col:15> 'int'
    | | | | | | | `-BinaryOperator 0x556ca68de278 <col:9, col:14> 'int' '<='
    | | | | | | |   |-IntegerLiteral 0x556ca68de220 <col:9> 'int' 1
    | | | | | | |   `-ImplicitCastExpr 0x556ca68de260 <col:14> 'int' <LValueToRValue>
    | | | | | | |     `-DeclRefExpr 0x556ca68de240 <col:14> 'int' lvalue Var 0x556ca68dde38 'n' 'int'
    | | | | | | `-ParenExpr 0x556ca68de330 <line:98:8, col:15> 'int'
    | | | | | |   `-BinaryOperator 0x556ca68de310 <col:9, col:14> 'int' '<='
    | | | | | |     |-IntegerLiteral 0x556ca68de2b8 <col:9> 'int' 1
    | | | | | |     `-ImplicitCastExpr 0x556ca68de2f8 <col:14> 'int' <LValueToRValue>
    | | | | | |       `-DeclRefExpr 0x556ca68de2d8 <col:14> 'int' lvalue Var 0x556ca68ddf28 'm' 'int'
    | | | | | `-ParenExpr 0x556ca68de3e8 <line:99:8, col:15> 'int'
    | | | | |   `-BinaryOperator 0x556ca68de3c8 <col:9, col:14> 'int' '<='
    | | | | |     |-IntegerLiteral 0x556ca68de370 <col:9> 'int' 1
    | | | | |     `-ImplicitCastExpr 0x556ca68de3b0 <col:14> 'int' <LValueToRValue>
    | | | | |       `-DeclRefExpr 0x556ca68de390 <col:14> 'int' lvalue Var 0x556ca68ddd38 'a' 'int'
    | | | | `-ParenExpr 0x556ca68de4a0 <line:100:8, col:17> 'int'
    | | | |   `-BinaryOperator 0x556ca68de480 <col:9, col:14> 'int' '<='
    | | | |     |-ImplicitCastExpr 0x556ca68de468 <col:9> 'int' <LValueToRValue>
    | | | |     | `-DeclRefExpr 0x556ca68de428 <col:9> 'int' lvalue Var 0x556ca68dde38 'n' 'int'
    | | | |     `-IntegerLiteral 0x556ca68de448 <col:14> 'int' 109
    | | | `-ParenExpr 0x556ca68de558 <line:101:8, col:17> 'int'
    | | |   `-BinaryOperator 0x556ca68de538 <col:9, col:14> 'int' '<='
    | | |     |-ImplicitCastExpr 0x556ca68de520 <col:9> 'int' <LValueToRValue>
    | | |     | `-DeclRefExpr 0x556ca68de4e0 <col:9> 'int' lvalue Var 0x556ca68ddf28 'm' 'int'
    | | |     `-IntegerLiteral 0x556ca68de500 <col:14> 'int' 109
    | | `-ParenExpr 0x556ca68de610 <line:102:8, col:17> 'int'
    | |   `-BinaryOperator 0x556ca68de5f0 <col:9, col:14> 'int' '<='
    | |     |-ImplicitCastExpr 0x556ca68de5d8 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x556ca68de598 <col:9> 'int' lvalue Var 0x556ca68ddd38 'a' 'int'
    | |     `-IntegerLiteral 0x556ca68de5b8 <col:14> 'int' 109
    | `-CompoundStmt 0x556ca68de928 <line:103:5, line:106:5>
    |   |-BinaryOperator 0x556ca68de7b0 <line:104:9, col:44> 'int' '='
    |   | |-DeclRefExpr 0x556ca68de650 <col:9> 'int' lvalue Var 0x556ca68de038 'n_stones1' 'int'
    |   | `-CallExpr 0x556ca68de730 <col:21, col:44> 'int'
    |   |   |-ImplicitCastExpr 0x556ca68de718 <col:21> 'int (*)(int, int, int)' <FunctionToPointerDecay>
    |   |   | `-DeclRefExpr 0x556ca68de670 <col:21> 'int (int, int, int)' Function 0x556ca68dc060 'correct_version' 'int (int, int, int)'
    |   |   |-ImplicitCastExpr 0x556ca68de768 <col:37> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x556ca68de690 <col:37> 'int' lvalue Var 0x556ca68dde38 'n' 'int'
    |   |   |-ImplicitCastExpr 0x556ca68de780 <col:40> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x556ca68de6b0 <col:40> 'int' lvalue Var 0x556ca68ddf28 'm' 'int'
    |   |   `-ImplicitCastExpr 0x556ca68de798 <col:43> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x556ca68de6d0 <col:43> 'int' lvalue Var 0x556ca68ddd38 'a' 'int'
    |   `-BinaryOperator 0x556ca68de908 <line:105:9, col:44> 'int' '='
    |     |-DeclRefExpr 0x556ca68de7d0 <col:9> 'int' lvalue Var 0x556ca68de0b8 'n_stones2' 'int'
    |     `-CallExpr 0x556ca68de888 <col:21, col:44> 'int'
    |       |-ImplicitCastExpr 0x556ca68de870 <col:21> 'int (*)(int, int, int)' <FunctionToPointerDecay>
    |       | `-DeclRefExpr 0x556ca68de7f0 <col:21> 'int (int, int, int)' Function 0x556ca68dcf40 'student_version' 'int (int, int, int)'
    |       |-ImplicitCastExpr 0x556ca68de8c0 <col:37> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x556ca68de810 <col:37> 'int' lvalue Var 0x556ca68dde38 'n' 'int'
    |       |-ImplicitCastExpr 0x556ca68de8d8 <col:40> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x556ca68de830 <col:40> 'int' lvalue Var 0x556ca68ddf28 'm' 'int'
    |       `-ImplicitCastExpr 0x556ca68de8f0 <col:43> 'int' <LValueToRValue>
    |         `-DeclRefExpr 0x556ca68de850 <col:43> 'int' lvalue Var 0x556ca68ddd38 'a' 'int'
    |-CallExpr 0x556ca68dea50 <line:107:5, col:45> 'void'
    | |-ImplicitCastExpr 0x556ca68dea38 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x556ca68de960 <col:5> 'void (int)' Function 0x556ca68da148 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x556ca68de9f0 <col:23, col:36> 'int' '=='
    |   |-ImplicitCastExpr 0x556ca68de9c0 <col:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x556ca68de980 <col:23> 'int' lvalue Var 0x556ca68de038 'n_stones1' 'int'
    |   `-ImplicitCastExpr 0x556ca68de9d8 <col:36> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x556ca68de9a0 <col:36> 'int' lvalue Var 0x556ca68de0b8 'n_stones2' 'int'
    `-ReturnStmt 0x556ca68dea98 <line:108:5, col:12>
      `-IntegerLiteral 0x556ca68dea78 <col:12> 'int' 0
1 warning generated.
