./Benchmark/PLDI/SVComp/loops/terminator_02-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/terminator_02-2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x557462c94e18 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x557462c956b0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x557462c953b0 '__int128'
|-TypedefDecl 0x557462c95720 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x557462c953d0 'unsigned __int128'
|-TypedefDecl 0x557462c95a28 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x557462c95800 'struct __NSConstantString_tag'
|   `-Record 0x557462c95778 '__NSConstantString_tag'
|-TypedefDecl 0x557462c95ac0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x557462c95a80 'char *'
|   `-BuiltinType 0x557462c94eb0 'char'
|-TypedefDecl 0x557462c95db8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x557462c95d60 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x557462c95ba0 'struct __va_list_tag'
|     `-Record 0x557462c95b18 '__va_list_tag'
|-FunctionDecl 0x557462cf4f68 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/terminator_02-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557462cf5008 prev 0x557462cf4f68 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557462cf5388 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x557462cf50c0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x557462cf5140 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x557462cf51c0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x557462cf5240 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x557462cf5448 <col:99>
|-FunctionDecl 0x557462cf5538 <line:3:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x557462cf5878 <col:20, col:81>
|   `-CallExpr 0x557462cf5790 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x557462cf5778 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x557462cf55d8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x557462cf5388 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x557462cf57e8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x557462cf57d0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x557462cf5638 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x557462cf5818 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x557462cf5800 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x557462cf5698 <col:41> 'char [18]' lvalue "terminator_02-2.c"
|     |-ImplicitCastExpr 0x557462cf5830 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x557462cf56c8 <col:62> 'int' 3
|     `-ImplicitCastExpr 0x557462cf5860 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x557462cf5848 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x557462cf5728 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x557462cf5928 prev 0x557462cf5008 <line:5:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557462cf5aa8 <line:6:1, line:8:1> line:6:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x557462cf59e0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x557462cf5c50 <col:36, line:8:1>
|   `-IfStmt 0x557462cf5c38 <line:7:3, col:22>
|     |-UnaryOperator 0x557462cf5b88 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x557462cf5b70 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x557462cf5b50 <col:7> 'int' lvalue ParmVar 0x557462cf59e0 'cond' 'int'
|     `-CompoundStmt 0x557462cf5c20 <col:13, col:22>
|       `-CallExpr 0x557462cf5c00 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x557462cf5be8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x557462cf5ba0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x557462cf5928 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x557462cf5d10 <line:9:1, line:14:1> line:9:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x557462cf5c80 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x557462cf79f0 <col:34, line:14:1>
|   |-IfStmt 0x557462cf79c8 <line:10:3, line:12:3>
|   | |-UnaryOperator 0x557462cf5e10 <line:10:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x557462cf5df8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x557462cf5dd8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x557462cf5db8 <col:9> 'int' lvalue ParmVar 0x557462cf5c80 'cond' 'int'
|   | `-CompoundStmt 0x557462cf79b0 <col:16, line:12:3>
|   |   `-LabelStmt 0x557462cf7998 <line:11:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x557462cf7928 <col:12, col:35>
|   |       |-CallExpr 0x557462cf78b0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x557462cf7898 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x557462cf5e28 <col:13> 'void ()' Function 0x557462cf5538 'reach_error' 'void ()'
|   |       `-CallExpr 0x557462cf7908 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x557462cf78f0 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x557462cf78d0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x557462cf5928 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x557462cf79e0 <line:13:3>
|-FunctionDecl 0x557462cf7a60 <line:15:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x557462cf7b48 <line:16:1, col:30> col:7 used __VERIFIER_nondet_bool '_Bool ()'
`-FunctionDecl 0x557462cf7c10 <line:18:1, line:40:1> line:18:5 main 'int ()'
  `-CompoundStmt 0x557462cf8818 <line:19:1, line:40:1>
    |-DeclStmt 0x557462cf7db0 <line:20:5, col:34>
    | `-VarDecl 0x557462cf7cc8 <col:5, col:33> col:9 used x 'int' cinit
    |   `-CallExpr 0x557462cf7d90 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x557462cf7d78 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x557462cf7d30 <col:11> 'int ()' Function 0x557462cf7a60 '__VERIFIER_nondet_int' 'int ()'
    |-DeclStmt 0x557462cf7ea0 <line:21:5, col:34>
    | `-VarDecl 0x557462cf7de0 <col:5, col:33> col:9 used z 'int' cinit
    |   `-CallExpr 0x557462cf7e80 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x557462cf7e68 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x557462cf7e48 <col:11> 'int ()' Function 0x557462cf7a60 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x557462cf7fb0 <line:22:5, col:27>
    | |-UnaryOperator 0x557462cf7f68 <col:9, col:17> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x557462cf7f48 <col:10, col:17> 'int'
    | |   `-BinaryOperator 0x557462cf7f28 <col:11, col:14> 'int' '>'
    | |     |-ImplicitCastExpr 0x557462cf7f10 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x557462cf7eb8 <col:11> 'int' lvalue Var 0x557462cf7cc8 'x' 'int'
    | |     `-UnaryOperator 0x557462cf7ef8 <col:13, col:14> 'int' prefix '-'
    | |       `-IntegerLiteral 0x557462cf7ed8 <col:14> 'int' 100
    | `-ReturnStmt 0x557462cf7fa0 <col:20, col:27>
    |   `-IntegerLiteral 0x557462cf7f80 <col:27> 'int' 0
    |-IfStmt 0x557462cf80a8 <line:23:5, col:26>
    | |-UnaryOperator 0x557462cf8060 <col:9, col:16> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x557462cf8040 <col:10, col:16> 'int'
    | |   `-BinaryOperator 0x557462cf8020 <col:11, col:13> 'int' '<'
    | |     |-ImplicitCastExpr 0x557462cf8008 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x557462cf7fc8 <col:11> 'int' lvalue Var 0x557462cf7cc8 'x' 'int'
    | |     `-IntegerLiteral 0x557462cf7fe8 <col:13> 'int' 200
    | `-ReturnStmt 0x557462cf8098 <col:19, col:26>
    |   `-IntegerLiteral 0x557462cf8078 <col:26> 'int' 0
    |-IfStmt 0x557462cf81a0 <line:24:5, col:26>
    | |-UnaryOperator 0x557462cf8158 <col:9, col:16> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x557462cf8138 <col:10, col:16> 'int'
    | |   `-BinaryOperator 0x557462cf8118 <col:11, col:13> 'int' '>'
    | |     |-ImplicitCastExpr 0x557462cf8100 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x557462cf80c0 <col:11> 'int' lvalue Var 0x557462cf7de0 'z' 'int'
    | |     `-IntegerLiteral 0x557462cf80e0 <col:13> 'int' 100
    | `-ReturnStmt 0x557462cf8190 <col:19, col:26>
    |   `-IntegerLiteral 0x557462cf8170 <col:26> 'int' 0
    |-IfStmt 0x557462cf8298 <line:25:5, col:26>
    | |-UnaryOperator 0x557462cf8250 <col:9, col:16> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x557462cf8230 <col:10, col:16> 'int'
    | |   `-BinaryOperator 0x557462cf8210 <col:11, col:13> 'int' '<'
    | |     |-ImplicitCastExpr 0x557462cf81f8 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x557462cf81b8 <col:11> 'int' lvalue Var 0x557462cf7de0 'z' 'int'
    | |     `-IntegerLiteral 0x557462cf81d8 <col:13> 'int' 200
    | `-ReturnStmt 0x557462cf8288 <col:19, col:26>
    |   `-IntegerLiteral 0x557462cf8268 <col:26> 'int' 0
    |-WhileStmt 0x557462cf8638 <line:26:5, line:35:5>
    | |-BinaryOperator 0x557462cf83a0 <line:26:11, col:22> 'int' '&&'
    | | |-BinaryOperator 0x557462cf8308 <col:11, col:13> 'int' '<'
    | | | |-ImplicitCastExpr 0x557462cf82f0 <col:11> 'int' <LValueToRValue>
    | | | | `-DeclRefExpr 0x557462cf82b0 <col:11> 'int' lvalue Var 0x557462cf7cc8 'x' 'int'
    | | | `-IntegerLiteral 0x557462cf82d0 <col:13> 'int' 100
    | | `-BinaryOperator 0x557462cf8380 <col:20, col:22> 'int' '>'
    | |   |-ImplicitCastExpr 0x557462cf8368 <col:20> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x557462cf8328 <col:20> 'int' lvalue Var 0x557462cf7de0 'z' 'int'
    | |   `-IntegerLiteral 0x557462cf8348 <col:22> 'int' 100
    | `-CompoundStmt 0x557462cf8618 <line:27:5, line:35:5>
    |   |-DeclStmt 0x557462cf84c0 <line:28:9, col:43>
    |   | `-VarDecl 0x557462cf83d0 <col:9, col:42> col:15 used tmp '_Bool' cinit
    |   |   `-CallExpr 0x557462cf84a0 <col:19, col:42> '_Bool'
    |   |     `-ImplicitCastExpr 0x557462cf8488 <col:19> '_Bool (*)()' <FunctionToPointerDecay>
    |   |       `-DeclRefExpr 0x557462cf8438 <col:19> '_Bool ()' Function 0x557462cf7b48 '__VERIFIER_nondet_bool' '_Bool ()'
    |   `-IfStmt 0x557462cf85f0 <line:29:9, line:34:9> has_else
    |     |-ImplicitCastExpr 0x557462cf84f8 <line:29:13> '_Bool' <LValueToRValue>
    |     | `-DeclRefExpr 0x557462cf84d8 <col:13> '_Bool' lvalue Var 0x557462cf83d0 'tmp' '_Bool'
    |     |-CompoundStmt 0x557462cf8548 <col:18, line:31:9>
    |     | `-UnaryOperator 0x557462cf8530 <line:30:13, col:14> 'int' postfix '++'
    |     |   `-DeclRefExpr 0x557462cf8510 <col:13> 'int' lvalue Var 0x557462cf7cc8 'x' 'int'
    |     `-CompoundStmt 0x557462cf85d0 <line:31:16, line:34:9>
    |       |-UnaryOperator 0x557462cf8580 <line:32:13, col:14> 'int' postfix '--'
    |       | `-DeclRefExpr 0x557462cf8560 <col:13> 'int' lvalue Var 0x557462cf7cc8 'x' 'int'
    |       `-UnaryOperator 0x557462cf85b8 <line:33:13, col:14> 'int' postfix '--'
    |         `-DeclRefExpr 0x557462cf8598 <col:13> 'int' lvalue Var 0x557462cf7de0 'z' 'int'
    |-CallExpr 0x557462cf87c0 <line:37:5, col:39> 'void'
    | |-ImplicitCastExpr 0x557462cf87a8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x557462cf8650 <col:5> 'void (int)' Function 0x557462cf5d10 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x557462cf8760 <col:23, col:36> 'int' '||'
    |   |-BinaryOperator 0x557462cf86c8 <col:23, col:26> 'int' '>='
    |   | |-ImplicitCastExpr 0x557462cf86b0 <col:23> 'int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x557462cf8670 <col:23> 'int' lvalue Var 0x557462cf7cc8 'x' 'int'
    |   | `-IntegerLiteral 0x557462cf8690 <col:26> 'int' 100
    |   `-BinaryOperator 0x557462cf8740 <col:33, col:36> 'int' '<='
    |     |-ImplicitCastExpr 0x557462cf8728 <col:33> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x557462cf86e8 <col:33> 'int' lvalue Var 0x557462cf7de0 'z' 'int'
    |     `-IntegerLiteral 0x557462cf8708 <col:36> 'int' 100
    `-ReturnStmt 0x557462cf8808 <line:39:5, col:12>
      `-IntegerLiteral 0x557462cf87e8 <col:12> 'int' 0
1 warning generated.
