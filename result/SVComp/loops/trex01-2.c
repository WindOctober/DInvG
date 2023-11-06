./Benchmark/PLDI/SVComp/loops/trex01-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex01-2.c:2:22: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error() { assert(0); }
                     ^
TranslationUnitDecl 0x557fe6e16dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x557fe6e17660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x557fe6e17360 '__int128'
|-TypedefDecl 0x557fe6e176d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x557fe6e17380 'unsigned __int128'
|-TypedefDecl 0x557fe6e179d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x557fe6e177b0 'struct __NSConstantString_tag'
|   `-Record 0x557fe6e17728 '__NSConstantString_tag'
|-TypedefDecl 0x557fe6e17a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x557fe6e17a30 'char *'
|   `-BuiltinType 0x557fe6e16e60 'char'
|-TypedefDecl 0x557fe6e17d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x557fe6e17d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x557fe6e17b50 'struct __va_list_tag'
|     `-Record 0x557fe6e17ac8 '__va_list_tag'
|-FunctionDecl 0x557fe6e76f58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex01-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557fe6e76ff8 prev 0x557fe6e76f58 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557fe6e770e8 <line:2:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x557fe6e77378 <col:20, col:33>
|   `-CallExpr 0x557fe6e77350 <col:22, col:30> 'int'
|     |-ImplicitCastExpr 0x557fe6e77338 <col:22> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x557fe6e772d0 <col:22> 'int ()' Function 0x557fe6e77220 'assert' 'int ()'
|     `-IntegerLiteral 0x557fe6e772f0 <col:29> 'int' 0
|-FunctionDecl 0x557fe6e77428 prev 0x557fe6e76ff8 <line:3:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557fe6e775a8 <line:4:1, line:6:1> line:4:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x557fe6e774e0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x557fe6e77750 <col:36, line:6:1>
|   `-IfStmt 0x557fe6e77738 <line:5:3, col:22>
|     |-UnaryOperator 0x557fe6e77688 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x557fe6e77670 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x557fe6e77650 <col:7> 'int' lvalue ParmVar 0x557fe6e774e0 'cond' 'int'
|     `-CompoundStmt 0x557fe6e77720 <col:13, col:22>
|       `-CallExpr 0x557fe6e77700 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x557fe6e776e8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x557fe6e776a0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x557fe6e77428 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x557fe6e77810 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x557fe6e77780 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x557fe6e77ad0 <col:34, line:13:1>
|   |-IfStmt 0x557fe6e77aa8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x557fe6e77910 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x557fe6e778f8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x557fe6e778d8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x557fe6e778b8 <col:9> 'int' lvalue ParmVar 0x557fe6e77780 'cond' 'int'
|   | `-CompoundStmt 0x557fe6e77a90 <col:16, line:11:3>
|   |   `-LabelStmt 0x557fe6e77a78 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x557fe6e77a08 <col:12, col:35>
|   |       |-CallExpr 0x557fe6e77990 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x557fe6e77978 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x557fe6e77928 <col:13> 'void ()' Function 0x557fe6e770e8 'reach_error' 'void ()'
|   |       `-CallExpr 0x557fe6e779e8 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x557fe6e779d0 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x557fe6e779b0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x557fe6e77428 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x557fe6e77ac0 <line:12:3>
|-FunctionDecl 0x557fe6e77b38 <line:14:1, col:30> col:7 used __VERIFIER_nondet_bool '_Bool ()'
|-FunctionDecl 0x557fe6e77c00 <line:15:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x557fe6e77d48 <line:19:1, line:41:1> line:19:6 used f 'void (int)'
| |-ParmVarDecl 0x557fe6e77cb8 <col:8, col:12> col:12 used d 'int'
| `-CompoundStmt 0x557fe6e79ac0 <col:15, line:41:1>
|   |-DeclStmt 0x557fe6e78748 <line:20:3, col:99>
|   | |-VarDecl 0x557fe6e78410 <col:3, col:33> col:7 used x 'int' cinit
|   | | `-CallExpr 0x557fe6e784b0 <col:11, col:33> 'int'
|   | |   `-ImplicitCastExpr 0x557fe6e78498 <col:11> 'int (*)()' <FunctionToPointerDecay>
|   | |     `-DeclRefExpr 0x557fe6e78478 <col:11> 'int ()' Function 0x557fe6e77c00 '__VERIFIER_nondet_int' 'int ()'
|   | |-VarDecl 0x557fe6e784e8 <col:3, col:62> col:36 used y 'int' cinit
|   | | `-CallExpr 0x557fe6e78588 <col:40, col:62> 'int'
|   | |   `-ImplicitCastExpr 0x557fe6e78570 <col:40> 'int (*)()' <FunctionToPointerDecay>
|   | |     `-DeclRefExpr 0x557fe6e78550 <col:40> 'int ()' Function 0x557fe6e77c00 '__VERIFIER_nondet_int' 'int ()'
|   | |-VarDecl 0x557fe6e785c0 <col:3, col:91> col:65 used k 'int' cinit
|   | | `-CallExpr 0x557fe6e78660 <col:69, col:91> 'int'
|   | |   `-ImplicitCastExpr 0x557fe6e78648 <col:69> 'int (*)()' <FunctionToPointerDecay>
|   | |     `-DeclRefExpr 0x557fe6e78628 <col:69> 'int ()' Function 0x557fe6e77c00 '__VERIFIER_nondet_int' 'int ()'
|   | `-VarDecl 0x557fe6e78698 <col:3, col:98> col:94 used z 'int' cinit
|   |   `-IntegerLiteral 0x557fe6e78700 <col:98> 'int' 1
|   |-LabelStmt 0x557fe6e78888 <line:21:3, line:23:5> 'L1'
|   | `-IfStmt 0x557fe6e78820 <line:22:3, line:23:5>
|   |   |-UnaryOperator 0x557fe6e787f8 <line:22:7, col:24> 'int' prefix '!' cannot overflow
|   |   | `-ParenExpr 0x557fe6e787d8 <col:8, col:24> 'int'
|   |   |   `-BinaryOperator 0x557fe6e787b8 <col:9, col:14> 'int' '<='
|   |   |     |-ImplicitCastExpr 0x557fe6e787a0 <col:9> 'int' <LValueToRValue>
|   |   |     | `-DeclRefExpr 0x557fe6e78760 <col:9> 'int' lvalue Var 0x557fe6e785c0 'k' 'int'
|   |   |     `-IntegerLiteral 0x557fe6e78780 <col:14> 'int' 1073741823
|   |   `-ReturnStmt 0x557fe6e78810 <line:23:5>
|   |-WhileStmt 0x557fe6e78a00 <line:24:3, col:30>
|   | |-BinaryOperator 0x557fe6e78910 <col:10, col:14> 'int' '<'
|   | | |-ImplicitCastExpr 0x557fe6e788e0 <col:10> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x557fe6e788a0 <col:10> 'int' lvalue Var 0x557fe6e78698 'z' 'int'
|   | | `-ImplicitCastExpr 0x557fe6e788f8 <col:14> 'int' <LValueToRValue>
|   | |   `-DeclRefExpr 0x557fe6e788c0 <col:14> 'int' lvalue Var 0x557fe6e785c0 'k' 'int'
|   | `-CompoundStmt 0x557fe6e789e8 <col:17, col:30>
|   |   `-BinaryOperator 0x557fe6e789c8 <col:19, col:27> 'int' '='
|   |     |-DeclRefExpr 0x557fe6e78930 <col:19> 'int' lvalue Var 0x557fe6e78698 'z' 'int'
|   |     `-BinaryOperator 0x557fe6e789a8 <col:23, col:27> 'int' '*'
|   |       |-IntegerLiteral 0x557fe6e78950 <col:23> 'int' 2
|   |       `-ImplicitCastExpr 0x557fe6e78990 <col:27> 'int' <LValueToRValue>
|   |         `-DeclRefExpr 0x557fe6e78970 <col:27> 'int' lvalue Var 0x557fe6e78698 'z' 'int'
|   |-CallExpr 0x557fe6e78af0 <line:25:3, col:25> 'void'
|   | |-ImplicitCastExpr 0x557fe6e78ad8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
|   | | `-DeclRefExpr 0x557fe6e78a18 <col:3> 'void (int)' Function 0x557fe6e77810 '__VERIFIER_assert' 'void (int)'
|   | `-BinaryOperator 0x557fe6e78a90 <col:21, col:24> 'int' '>='
|   |   |-ImplicitCastExpr 0x557fe6e78a78 <col:21> 'int' <LValueToRValue>
|   |   | `-DeclRefExpr 0x557fe6e78a38 <col:21> 'int' lvalue Var 0x557fe6e78698 'z' 'int'
|   |   `-IntegerLiteral 0x557fe6e78a58 <col:24> 'int' 1
|   |-LabelStmt 0x557fe6e78cf0 <line:26:3, line:27:45> 'L2'
|   | `-IfStmt 0x557fe6e78c88 <col:3, col:45>
|   |   |-UnaryOperator 0x557fe6e78c60 <col:7, col:42> 'int' prefix '!' cannot overflow
|   |   | `-ParenExpr 0x557fe6e78c40 <col:8, col:42> 'int'
|   |   |   `-BinaryOperator 0x557fe6e78c20 <col:9, line:17:19> 'int' '&&'
|   |   |     |-BinaryOperator 0x557fe6e78b70 <line:27:9, line:17:19> 'int' '<='
|   |   |     | |-ImplicitCastExpr 0x557fe6e78b58 <line:27:9> 'int' <LValueToRValue>
|   |   |     | | `-DeclRefExpr 0x557fe6e78b18 <col:9> 'int' lvalue Var 0x557fe6e78410 'x' 'int'
|   |   |     | `-IntegerLiteral 0x557fe6e78b38 <line:17:19> 'int' 1000000
|   |   |     `-BinaryOperator 0x557fe6e78c00 <line:27:27, line:17:19> 'int' '>='
|   |   |       |-ImplicitCastExpr 0x557fe6e78be8 <line:27:27> 'int' <LValueToRValue>
|   |   |       | `-DeclRefExpr 0x557fe6e78b90 <col:27> 'int' lvalue Var 0x557fe6e78410 'x' 'int'
|   |   |       `-UnaryOperator 0x557fe6e78bd0 <col:32, line:17:19> 'int' prefix '-'
|   |   |         `-IntegerLiteral 0x557fe6e78bb0 <col:19> 'int' 1000000
|   |   `-ReturnStmt 0x557fe6e78c78 <line:27:45>
|   |-IfStmt 0x557fe6e78e78 <line:28:3, col:45>
|   | |-UnaryOperator 0x557fe6e78e50 <col:7, col:42> 'int' prefix '!' cannot overflow
|   | | `-ParenExpr 0x557fe6e78e30 <col:8, col:42> 'int'
|   | |   `-BinaryOperator 0x557fe6e78e10 <col:9, line:17:19> 'int' '&&'
|   | |     |-BinaryOperator 0x557fe6e78d60 <line:28:9, line:17:19> 'int' '<='
|   | |     | |-ImplicitCastExpr 0x557fe6e78d48 <line:28:9> 'int' <LValueToRValue>
|   | |     | | `-DeclRefExpr 0x557fe6e78d08 <col:9> 'int' lvalue Var 0x557fe6e784e8 'y' 'int'
|   | |     | `-IntegerLiteral 0x557fe6e78d28 <line:17:19> 'int' 1000000
|   | |     `-BinaryOperator 0x557fe6e78df0 <line:28:27, line:17:19> 'int' '>='
|   | |       |-ImplicitCastExpr 0x557fe6e78dd8 <line:28:27> 'int' <LValueToRValue>
|   | |       | `-DeclRefExpr 0x557fe6e78d80 <col:27> 'int' lvalue Var 0x557fe6e784e8 'y' 'int'
|   | |       `-UnaryOperator 0x557fe6e78dc0 <col:32, line:17:19> 'int' prefix '-'
|   | |         `-IntegerLiteral 0x557fe6e78da0 <col:19> 'int' 1000000
|   | `-ReturnStmt 0x557fe6e78e68 <line:28:45>
|   |-IfStmt 0x557fe6e79000 <line:29:3, col:45>
|   | |-UnaryOperator 0x557fe6e78fd8 <col:7, col:42> 'int' prefix '!' cannot overflow
|   | | `-ParenExpr 0x557fe6e78fb8 <col:8, col:42> 'int'
|   | |   `-BinaryOperator 0x557fe6e78f98 <col:9, line:17:19> 'int' '&&'
|   | |     |-BinaryOperator 0x557fe6e78ee8 <line:29:9, line:17:19> 'int' '<='
|   | |     | |-ImplicitCastExpr 0x557fe6e78ed0 <line:29:9> 'int' <LValueToRValue>
|   | |     | | `-DeclRefExpr 0x557fe6e78e90 <col:9> 'int' lvalue Var 0x557fe6e785c0 'k' 'int'
|   | |     | `-IntegerLiteral 0x557fe6e78eb0 <line:17:19> 'int' 1000000
|   | |     `-BinaryOperator 0x557fe6e78f78 <line:29:27, line:17:19> 'int' '>='
|   | |       |-ImplicitCastExpr 0x557fe6e78f60 <line:29:27> 'int' <LValueToRValue>
|   | |       | `-DeclRefExpr 0x557fe6e78f08 <col:27> 'int' lvalue Var 0x557fe6e785c0 'k' 'int'
|   | |       `-UnaryOperator 0x557fe6e78f48 <col:32, line:17:19> 'int' prefix '-'
|   | |         `-IntegerLiteral 0x557fe6e78f28 <col:19> 'int' 1000000
|   | `-ReturnStmt 0x557fe6e78ff0 <line:29:45>
|   `-WhileStmt 0x557fe6e79aa8 <line:30:3, line:40:3>
|     |-BinaryOperator 0x557fe6e79108 <line:30:10, col:23> 'int' '&&'
|     | |-BinaryOperator 0x557fe6e79070 <col:10, col:14> 'int' '>'
|     | | |-ImplicitCastExpr 0x557fe6e79058 <col:10> 'int' <LValueToRValue>
|     | | | `-DeclRefExpr 0x557fe6e79018 <col:10> 'int' lvalue Var 0x557fe6e78410 'x' 'int'
|     | | `-IntegerLiteral 0x557fe6e79038 <col:14> 'int' 0
|     | `-BinaryOperator 0x557fe6e790e8 <col:19, col:23> 'int' '>'
|     |   |-ImplicitCastExpr 0x557fe6e790d0 <col:19> 'int' <LValueToRValue>
|     |   | `-DeclRefExpr 0x557fe6e79090 <col:19> 'int' lvalue Var 0x557fe6e784e8 'y' 'int'
|     |   `-IntegerLiteral 0x557fe6e790b0 <col:23> 'int' 0
|     `-CompoundStmt 0x557fe6e79a88 <col:26, line:40:3>
|       |-DeclStmt 0x557fe6e79220 <line:31:5, col:39>
|       | `-VarDecl 0x557fe6e79138 <col:5, col:38> col:11 used c '_Bool' cinit
|       |   `-CallExpr 0x557fe6e79200 <col:15, col:38> '_Bool'
|       |     `-ImplicitCastExpr 0x557fe6e791e8 <col:15> '_Bool (*)()' <FunctionToPointerDecay>
|       |       `-DeclRefExpr 0x557fe6e791a0 <col:15> '_Bool ()' Function 0x557fe6e77b38 '__VERIFIER_nondet_bool' '_Bool ()'
|       `-IfStmt 0x557fe6e79a60 <line:32:5, line:39:5> has_else
|         |-ImplicitCastExpr 0x557fe6e79258 <line:32:9> '_Bool' <LValueToRValue>
|         | `-DeclRefExpr 0x557fe6e79238 <col:9> '_Bool' lvalue Var 0x557fe6e79138 'c' '_Bool'
|         |-CompoundStmt 0x557fe6e79948 <col:12, line:37:5>
|         | |-LabelStmt 0x557fe6e79390 <line:33:7, line:34:15> 'P1'
|         | | `-BinaryOperator 0x557fe6e79320 <col:7, col:15> 'int' '='
|         | |   |-DeclRefExpr 0x557fe6e79270 <col:7> 'int' lvalue Var 0x557fe6e78410 'x' 'int'
|         | |   `-BinaryOperator 0x557fe6e79300 <col:11, col:15> 'int' '-'
|         | |     |-ImplicitCastExpr 0x557fe6e792d0 <col:11> 'int' <LValueToRValue>
|         | |     | `-DeclRefExpr 0x557fe6e79290 <col:11> 'int' lvalue Var 0x557fe6e78410 'x' 'int'
|         | |     `-ImplicitCastExpr 0x557fe6e792e8 <col:15> 'int' <LValueToRValue>
|         | |       `-DeclRefExpr 0x557fe6e792b0 <col:15> 'int' lvalue ParmVar 0x557fe6e77cb8 'd' 'int'
|         | |-BinaryOperator 0x557fe6e79868 <line:35:7, col:34> 'int' '='
|         | | |-DeclRefExpr 0x557fe6e793a8 <col:7> 'int' lvalue Var 0x557fe6e784e8 'y' 'int'
|         | | `-ImplicitCastExpr 0x557fe6e79850 <col:11, col:34> 'int' <IntegralCast>
|         | |   `-CallExpr 0x557fe6e79830 <col:11, col:34> '_Bool'
|         | |     `-ImplicitCastExpr 0x557fe6e793e8 <col:11> '_Bool (*)()' <FunctionToPointerDecay>
|         | |       `-DeclRefExpr 0x557fe6e793c8 <col:11> '_Bool ()' Function 0x557fe6e77b38 '__VERIFIER_nondet_bool' '_Bool ()'
|         | |-NullStmt 0x557fe6e79888 <col:36>
|         | `-BinaryOperator 0x557fe6e79928 <line:36:7, col:15> 'int' '='
|         |   |-DeclRefExpr 0x557fe6e79890 <col:7> 'int' lvalue Var 0x557fe6e78698 'z' 'int'
|         |   `-BinaryOperator 0x557fe6e79908 <col:11, col:15> 'int' '-'
|         |     |-ImplicitCastExpr 0x557fe6e798f0 <col:11> 'int' <LValueToRValue>
|         |     | `-DeclRefExpr 0x557fe6e798b0 <col:11> 'int' lvalue Var 0x557fe6e78698 'z' 'int'
|         |     `-IntegerLiteral 0x557fe6e798d0 <col:15> 'int' 1
|         `-CompoundStmt 0x557fe6e79a48 <line:37:12, line:39:5>
|           `-BinaryOperator 0x557fe6e79a28 <line:38:7, col:15> 'int' '='
|             |-DeclRefExpr 0x557fe6e79978 <col:7> 'int' lvalue Var 0x557fe6e784e8 'y' 'int'
|             `-BinaryOperator 0x557fe6e79a08 <col:11, col:15> 'int' '-'
|               |-ImplicitCastExpr 0x557fe6e799d8 <col:11> 'int' <LValueToRValue>
|               | `-DeclRefExpr 0x557fe6e79998 <col:11> 'int' lvalue Var 0x557fe6e784e8 'y' 'int'
|               `-ImplicitCastExpr 0x557fe6e799f0 <col:15> 'int' <LValueToRValue>
|                 `-DeclRefExpr 0x557fe6e799b8 <col:15> 'int' lvalue ParmVar 0x557fe6e77cb8 'd' 'int'
`-FunctionDecl 0x557fe6e79b38 <line:43:1, line:52:1> line:43:5 main 'int ()'
  `-CompoundStmt 0x557fe6e79e80 <col:12, line:52:1>
    |-DeclStmt 0x557fe6e79ca8 <line:44:3, col:37>
    | `-VarDecl 0x557fe6e79be8 <col:3, col:36> col:9 used c '_Bool' cinit
    |   `-CallExpr 0x557fe6e79c88 <col:13, col:36> '_Bool'
    |     `-ImplicitCastExpr 0x557fe6e79c70 <col:13> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x557fe6e79c50 <col:13> '_Bool ()' Function 0x557fe6e77b38 '__VERIFIER_nondet_bool' '_Bool ()'
    |-IfStmt 0x557fe6e79e28 <line:45:3, line:49:3> has_else
    | |-ImplicitCastExpr 0x557fe6e79ce0 <line:45:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x557fe6e79cc0 <col:7> '_Bool' lvalue Var 0x557fe6e79be8 'c' '_Bool'
    | |-CompoundStmt 0x557fe6e79d78 <col:10, line:47:3>
    | | `-CallExpr 0x557fe6e79d50 <line:46:5, col:8> 'void'
    | |   |-ImplicitCastExpr 0x557fe6e79d38 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | |   | `-DeclRefExpr 0x557fe6e79cf8 <col:5> 'void (int)' Function 0x557fe6e77d48 'f' 'void (int)'
    | |   `-IntegerLiteral 0x557fe6e79d18 <col:7> 'int' 1
    | `-CompoundStmt 0x557fe6e79e10 <line:47:10, line:49:3>
    |   `-CallExpr 0x557fe6e79de8 <line:48:5, col:8> 'void'
    |     |-ImplicitCastExpr 0x557fe6e79dd0 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x557fe6e79d90 <col:5> 'void (int)' Function 0x557fe6e77d48 'f' 'void (int)'
    |     `-IntegerLiteral 0x557fe6e79db0 <col:7> 'int' 2
    `-ReturnStmt 0x557fe6e79e70 <line:51:3, col:10>
      `-IntegerLiteral 0x557fe6e79e50 <col:10> 'int' 0
1 warning generated.
