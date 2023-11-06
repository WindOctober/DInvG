./Benchmark/PLDI/SVComp/loops/trex01-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex01-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x558aa513fdc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x558aa5140660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x558aa5140360 '__int128'
|-TypedefDecl 0x558aa51406d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x558aa5140380 'unsigned __int128'
|-TypedefDecl 0x558aa51409d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x558aa51407b0 'struct __NSConstantString_tag'
|   `-Record 0x558aa5140728 '__NSConstantString_tag'
|-TypedefDecl 0x558aa5140a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x558aa5140a30 'char *'
|   `-BuiltinType 0x558aa513fe60 'char'
|-TypedefDecl 0x558aa5140d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x558aa5140d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x558aa5140b50 'struct __va_list_tag'
|     `-Record 0x558aa5140ac8 '__va_list_tag'
|-FunctionDecl 0x558aa519ff08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex01-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558aa519ffa8 prev 0x558aa519ff08 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558aa51a0328 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x558aa51a0060 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x558aa51a00e0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x558aa51a0160 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x558aa51a01e0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x558aa51a03e8 <col:99>
|-FunctionDecl 0x558aa51a04d8 <line:3:1, col:74> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x558aa51a0808 <col:20, col:74>
|   `-CallExpr 0x558aa51a0720 <col:22, col:71> 'void'
|     |-ImplicitCastExpr 0x558aa51a0708 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x558aa51a0578 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x558aa51a0328 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x558aa51a0778 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x558aa51a0760 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x558aa51a05d8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x558aa51a07a8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x558aa51a0790 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x558aa51a0638 <col:41> 'char [11]' lvalue "trex01-1.c"
|     |-ImplicitCastExpr 0x558aa51a07c0 <col:55> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x558aa51a0660 <col:55> 'int' 3
|     `-ImplicitCastExpr 0x558aa51a07f0 <col:58> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x558aa51a07d8 <col:58> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x558aa51a06b8 <col:58> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x558aa51a08f8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x558aa51a0838 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x558aa51a0bd8 <col:34, line:10:1>
|   |-IfStmt 0x558aa51a0bb0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x558aa51a09f8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x558aa51a09e0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x558aa51a09c0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x558aa51a09a0 <col:9> 'int' lvalue ParmVar 0x558aa51a0838 'cond' 'int'
|   | `-CompoundStmt 0x558aa51a0b98 <col:16, line:8:3>
|   |   `-LabelStmt 0x558aa51a0b80 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x558aa51a0b10 <col:12, col:35>
|   |       |-CallExpr 0x558aa51a0a70 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x558aa51a0a58 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x558aa51a0a10 <col:13> 'void ()' Function 0x558aa51a04d8 'reach_error' 'void ()'
|   |       `-CallExpr 0x558aa51a0af0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x558aa51a0ad8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x558aa51a0a90 <col:27> 'void (void) __attribute__((noreturn))' Function 0x558aa519ffa8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x558aa51a0bc8 <line:9:3>
|-FunctionDecl 0x558aa51a0c48 <line:11:1, col:30> col:7 used __VERIFIER_nondet_bool '_Bool ()'
|-FunctionDecl 0x558aa51a0d40 <line:12:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x558aa51a28a0 <line:14:1, line:33:1> line:14:6 used f 'void (int)'
| |-ParmVarDecl 0x558aa51a2810 <col:8, col:12> col:12 used d 'int'
| `-CompoundStmt 0x558aa51a3768 <col:15, line:33:1>
|   |-DeclStmt 0x558aa51a2cc8 <line:15:3, col:99>
|   | |-VarDecl 0x558aa51a2960 <col:3, col:33> col:7 used x 'int' cinit
|   | | `-CallExpr 0x558aa51a2a30 <col:11, col:33> 'int'
|   | |   `-ImplicitCastExpr 0x558aa51a2a18 <col:11> 'int (*)()' <FunctionToPointerDecay>
|   | |     `-DeclRefExpr 0x558aa51a29c8 <col:11> 'int ()' Function 0x558aa51a0d40 '__VERIFIER_nondet_int' 'int ()'
|   | |-VarDecl 0x558aa51a2a68 <col:3, col:62> col:36 used y 'int' cinit
|   | | `-CallExpr 0x558aa51a2b08 <col:40, col:62> 'int'
|   | |   `-ImplicitCastExpr 0x558aa51a2af0 <col:40> 'int (*)()' <FunctionToPointerDecay>
|   | |     `-DeclRefExpr 0x558aa51a2ad0 <col:40> 'int ()' Function 0x558aa51a0d40 '__VERIFIER_nondet_int' 'int ()'
|   | |-VarDecl 0x558aa51a2b40 <col:3, col:91> col:65 used k 'int' cinit
|   | | `-CallExpr 0x558aa51a2be0 <col:69, col:91> 'int'
|   | |   `-ImplicitCastExpr 0x558aa51a2bc8 <col:69> 'int (*)()' <FunctionToPointerDecay>
|   | |     `-DeclRefExpr 0x558aa51a2ba8 <col:69> 'int ()' Function 0x558aa51a0d40 '__VERIFIER_nondet_int' 'int ()'
|   | `-VarDecl 0x558aa51a2c18 <col:3, col:98> col:94 used z 'int' cinit
|   |   `-IntegerLiteral 0x558aa51a2c80 <col:98> 'int' 1
|   |-IfStmt 0x558aa51a2da0 <line:16:3, line:17:5>
|   | |-UnaryOperator 0x558aa51a2d78 <line:16:7, col:24> 'int' prefix '!' cannot overflow
|   | | `-ParenExpr 0x558aa51a2d58 <col:8, col:24> 'int'
|   | |   `-BinaryOperator 0x558aa51a2d38 <col:9, col:14> 'int' '<='
|   | |     |-ImplicitCastExpr 0x558aa51a2d20 <col:9> 'int' <LValueToRValue>
|   | |     | `-DeclRefExpr 0x558aa51a2ce0 <col:9> 'int' lvalue Var 0x558aa51a2b40 'k' 'int'
|   | |     `-IntegerLiteral 0x558aa51a2d00 <col:14> 'int' 1073741823
|   | `-ReturnStmt 0x558aa51a2d90 <line:17:5>
|   |-LabelStmt 0x558aa51a2f80 <line:18:3, line:19:30> 'L1'
|   | `-WhileStmt 0x558aa51a2f18 <col:3, col:30>
|   |   |-BinaryOperator 0x558aa51a2e28 <col:10, col:14> 'int' '<'
|   |   | |-ImplicitCastExpr 0x558aa51a2df8 <col:10> 'int' <LValueToRValue>
|   |   | | `-DeclRefExpr 0x558aa51a2db8 <col:10> 'int' lvalue Var 0x558aa51a2c18 'z' 'int'
|   |   | `-ImplicitCastExpr 0x558aa51a2e10 <col:14> 'int' <LValueToRValue>
|   |   |   `-DeclRefExpr 0x558aa51a2dd8 <col:14> 'int' lvalue Var 0x558aa51a2b40 'k' 'int'
|   |   `-CompoundStmt 0x558aa51a2f00 <col:17, col:30>
|   |     `-BinaryOperator 0x558aa51a2ee0 <col:19, col:27> 'int' '='
|   |       |-DeclRefExpr 0x558aa51a2e48 <col:19> 'int' lvalue Var 0x558aa51a2c18 'z' 'int'
|   |       `-BinaryOperator 0x558aa51a2ec0 <col:23, col:27> 'int' '*'
|   |         |-IntegerLiteral 0x558aa51a2e68 <col:23> 'int' 2
|   |         `-ImplicitCastExpr 0x558aa51a2ea8 <col:27> 'int' <LValueToRValue>
|   |           `-DeclRefExpr 0x558aa51a2e88 <col:27> 'int' lvalue Var 0x558aa51a2c18 'z' 'int'
|   |-CallExpr 0x558aa51a3070 <line:20:3, col:25> 'void'
|   | |-ImplicitCastExpr 0x558aa51a3058 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
|   | | `-DeclRefExpr 0x558aa51a2f98 <col:3> 'void (int)' Function 0x558aa51a08f8 '__VERIFIER_assert' 'void (int)'
|   | `-BinaryOperator 0x558aa51a3010 <col:21, col:24> 'int' '>='
|   |   |-ImplicitCastExpr 0x558aa51a2ff8 <col:21> 'int' <LValueToRValue>
|   |   | `-DeclRefExpr 0x558aa51a2fb8 <col:21> 'int' lvalue Var 0x558aa51a2c18 'z' 'int'
|   |   `-IntegerLiteral 0x558aa51a2fd8 <col:24> 'int' 2
|   `-LabelStmt 0x558aa51a3750 <line:21:3, line:32:3> 'L2'
|     `-WhileStmt 0x558aa51a36e8 <line:22:3, line:32:3>
|       |-BinaryOperator 0x558aa51a3188 <line:22:10, col:23> 'int' '&&'
|       | |-BinaryOperator 0x558aa51a30f0 <col:10, col:14> 'int' '>'
|       | | |-ImplicitCastExpr 0x558aa51a30d8 <col:10> 'int' <LValueToRValue>
|       | | | `-DeclRefExpr 0x558aa51a3098 <col:10> 'int' lvalue Var 0x558aa51a2960 'x' 'int'
|       | | `-IntegerLiteral 0x558aa51a30b8 <col:14> 'int' 0
|       | `-BinaryOperator 0x558aa51a3168 <col:19, col:23> 'int' '>'
|       |   |-ImplicitCastExpr 0x558aa51a3150 <col:19> 'int' <LValueToRValue>
|       |   | `-DeclRefExpr 0x558aa51a3110 <col:19> 'int' lvalue Var 0x558aa51a2a68 'y' 'int'
|       |   `-IntegerLiteral 0x558aa51a3130 <col:23> 'int' 0
|       `-CompoundStmt 0x558aa51a36c8 <col:26, line:32:3>
|         |-DeclStmt 0x558aa51a32a0 <line:23:5, col:39>
|         | `-VarDecl 0x558aa51a31b8 <col:5, col:38> col:11 used c '_Bool' cinit
|         |   `-CallExpr 0x558aa51a3280 <col:15, col:38> '_Bool'
|         |     `-ImplicitCastExpr 0x558aa51a3268 <col:15> '_Bool (*)()' <FunctionToPointerDecay>
|         |       `-DeclRefExpr 0x558aa51a3220 <col:15> '_Bool ()' Function 0x558aa51a0c48 '__VERIFIER_nondet_bool' '_Bool ()'
|         `-IfStmt 0x558aa51a36a0 <line:24:5, line:31:5> has_else
|           |-ImplicitCastExpr 0x558aa51a32d8 <line:24:9> '_Bool' <LValueToRValue>
|           | `-DeclRefExpr 0x558aa51a32b8 <col:9> '_Bool' lvalue Var 0x558aa51a31b8 'c' '_Bool'
|           |-CompoundStmt 0x558aa51a3590 <col:12, line:29:5>
|           | |-LabelStmt 0x558aa51a3410 <line:25:7, line:26:15> 'P1'
|           | | `-BinaryOperator 0x558aa51a33a0 <col:7, col:15> 'int' '='
|           | |   |-DeclRefExpr 0x558aa51a32f0 <col:7> 'int' lvalue Var 0x558aa51a2960 'x' 'int'
|           | |   `-BinaryOperator 0x558aa51a3380 <col:11, col:15> 'int' '-'
|           | |     |-ImplicitCastExpr 0x558aa51a3350 <col:11> 'int' <LValueToRValue>
|           | |     | `-DeclRefExpr 0x558aa51a3310 <col:11> 'int' lvalue Var 0x558aa51a2960 'x' 'int'
|           | |     `-ImplicitCastExpr 0x558aa51a3368 <col:15> 'int' <LValueToRValue>
|           | |       `-DeclRefExpr 0x558aa51a3330 <col:15> 'int' lvalue ParmVar 0x558aa51a2810 'd' 'int'
|           | |-BinaryOperator 0x558aa51a34b8 <line:27:7, col:34> 'int' '='
|           | | |-DeclRefExpr 0x558aa51a3428 <col:7> 'int' lvalue Var 0x558aa51a2a68 'y' 'int'
|           | | `-ImplicitCastExpr 0x558aa51a34a0 <col:11, col:34> 'int' <IntegralCast>
|           | |   `-CallExpr 0x558aa51a3480 <col:11, col:34> '_Bool'
|           | |     `-ImplicitCastExpr 0x558aa51a3468 <col:11> '_Bool (*)()' <FunctionToPointerDecay>
|           | |       `-DeclRefExpr 0x558aa51a3448 <col:11> '_Bool ()' Function 0x558aa51a0c48 '__VERIFIER_nondet_bool' '_Bool ()'
|           | `-BinaryOperator 0x558aa51a3570 <line:28:7, col:15> 'int' '='
|           |   |-DeclRefExpr 0x558aa51a34d8 <col:7> 'int' lvalue Var 0x558aa51a2c18 'z' 'int'
|           |   `-BinaryOperator 0x558aa51a3550 <col:11, col:15> 'int' '-'
|           |     |-ImplicitCastExpr 0x558aa51a3538 <col:11> 'int' <LValueToRValue>
|           |     | `-DeclRefExpr 0x558aa51a34f8 <col:11> 'int' lvalue Var 0x558aa51a2c18 'z' 'int'
|           |     `-IntegerLiteral 0x558aa51a3518 <col:15> 'int' 1
|           `-CompoundStmt 0x558aa51a3688 <line:29:12, line:31:5>
|             `-BinaryOperator 0x558aa51a3668 <line:30:7, col:15> 'int' '='
|               |-DeclRefExpr 0x558aa51a35b8 <col:7> 'int' lvalue Var 0x558aa51a2a68 'y' 'int'
|               `-BinaryOperator 0x558aa51a3648 <col:11, col:15> 'int' '-'
|                 |-ImplicitCastExpr 0x558aa51a3618 <col:11> 'int' <LValueToRValue>
|                 | `-DeclRefExpr 0x558aa51a35d8 <col:11> 'int' lvalue Var 0x558aa51a2a68 'y' 'int'
|                 `-ImplicitCastExpr 0x558aa51a3630 <col:15> 'int' <LValueToRValue>
|                   `-DeclRefExpr 0x558aa51a35f8 <col:15> 'int' lvalue ParmVar 0x558aa51a2810 'd' 'int'
`-FunctionDecl 0x558aa51a39d0 <line:35:1, line:44:1> line:35:5 main 'int ()'
  `-CompoundStmt 0x558aa51a3d18 <col:12, line:44:1>
    |-DeclStmt 0x558aa51a3b40 <line:36:3, col:37>
    | `-VarDecl 0x558aa51a3a80 <col:3, col:36> col:9 used c '_Bool' cinit
    |   `-CallExpr 0x558aa51a3b20 <col:13, col:36> '_Bool'
    |     `-ImplicitCastExpr 0x558aa51a3b08 <col:13> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x558aa51a3ae8 <col:13> '_Bool ()' Function 0x558aa51a0c48 '__VERIFIER_nondet_bool' '_Bool ()'
    |-IfStmt 0x558aa51a3cc0 <line:37:3, line:41:3> has_else
    | |-ImplicitCastExpr 0x558aa51a3b78 <line:37:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x558aa51a3b58 <col:7> '_Bool' lvalue Var 0x558aa51a3a80 'c' '_Bool'
    | |-CompoundStmt 0x558aa51a3c10 <col:10, line:39:3>
    | | `-CallExpr 0x558aa51a3be8 <line:38:5, col:8> 'void'
    | |   |-ImplicitCastExpr 0x558aa51a3bd0 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | |   | `-DeclRefExpr 0x558aa51a3b90 <col:5> 'void (int)' Function 0x558aa51a28a0 'f' 'void (int)'
    | |   `-IntegerLiteral 0x558aa51a3bb0 <col:7> 'int' 1
    | `-CompoundStmt 0x558aa51a3ca8 <line:39:10, line:41:3>
    |   `-CallExpr 0x558aa51a3c80 <line:40:5, col:8> 'void'
    |     |-ImplicitCastExpr 0x558aa51a3c68 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x558aa51a3c28 <col:5> 'void (int)' Function 0x558aa51a28a0 'f' 'void (int)'
    |     `-IntegerLiteral 0x558aa51a3c48 <col:7> 'int' 2
    `-ReturnStmt 0x558aa51a3d08 <line:43:3, col:10>
      `-IntegerLiteral 0x558aa51a3ce8 <col:10> 'int' 0
1 warning generated.
