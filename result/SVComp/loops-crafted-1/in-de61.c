./Benchmark/PLDI/SVComp/loops-crafted-1/in-de61.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de61.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55c4ce6c5e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55c4ce6c6730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55c4ce6c6430 '__int128'
|-TypedefDecl 0x55c4ce6c67a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55c4ce6c6450 'unsigned __int128'
|-TypedefDecl 0x55c4ce6c6aa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55c4ce6c6880 'struct __NSConstantString_tag'
|   `-Record 0x55c4ce6c67f8 '__NSConstantString_tag'
|-TypedefDecl 0x55c4ce6c6b40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55c4ce6c6b00 'char *'
|   `-BuiltinType 0x55c4ce6c5f30 'char'
|-TypedefDecl 0x55c4ce6c6e38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55c4ce6c6de0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55c4ce6c6c20 'struct __va_list_tag'
|     `-Record 0x55c4ce6c6b98 '__va_list_tag'
|-FunctionDecl 0x55c4ce725f38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de61.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55c4ce725fd8 prev 0x55c4ce725f38 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55c4ce726358 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55c4ce726090 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55c4ce726110 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55c4ce726190 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55c4ce726210 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55c4ce726418 <col:99>
|-FunctionDecl 0x55c4ce726508 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55c4ce726838 <col:20, col:73>
|   `-CallExpr 0x55c4ce726750 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x55c4ce726738 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55c4ce7265a8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55c4ce726358 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55c4ce7267a8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55c4ce726790 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55c4ce726608 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55c4ce7267d8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55c4ce7267c0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55c4ce726668 <col:41> 'char [10]' lvalue "in-de61.c"
|     |-ImplicitCastExpr 0x55c4ce7267f0 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55c4ce726690 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x55c4ce726820 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55c4ce726808 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55c4ce7266e8 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55c4ce726920 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55c4ce726a98 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55c4ce7269d8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55c4ce726d78 <col:34, line:10:1>
|   |-IfStmt 0x55c4ce726d50 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55c4ce726b98 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55c4ce726b80 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55c4ce726b60 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55c4ce726b40 <col:9> 'int' lvalue ParmVar 0x55c4ce7269d8 'cond' 'int'
|   | `-CompoundStmt 0x55c4ce726d38 <col:16, line:8:3>
|   |   `-LabelStmt 0x55c4ce726d20 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55c4ce726cb0 <col:12, col:35>
|   |       |-CallExpr 0x55c4ce726c10 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55c4ce726bf8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55c4ce726bb0 <col:13> 'void ()' Function 0x55c4ce726508 'reach_error' 'void ()'
|   |       `-CallExpr 0x55c4ce726c90 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55c4ce726c78 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55c4ce726c30 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55c4ce725fd8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55c4ce726d68 <line:9:3>
`-FunctionDecl 0x55c4ce728840 <line:12:1, line:55:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x55c4ce729538 <line:13:1, line:55:1>
    |-DeclStmt 0x55c4ce7289e0 <line:14:3, col:44>
    | `-VarDecl 0x55c4ce7288f8 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x55c4ce7289c0 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55c4ce7289a8 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55c4ce728960 <col:20> 'unsigned int (void)' Function 0x55c4ce726920 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x55c4ce728c08 <line:15:3, col:27>
    | |-VarDecl 0x55c4ce728a10 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55c4ce728a98 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55c4ce728a78 <col:18> 'unsigned int' lvalue Var 0x55c4ce7288f8 'n' 'unsigned int'
    | |-VarDecl 0x55c4ce728ac8 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55c4ce728b50 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55c4ce728b30 <col:23> 'int' 0
    | `-VarDecl 0x55c4ce728b80 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x55c4ce728d40 <line:16:3, line:20:3>
    | |-BinaryOperator 0x55c4ce728c90 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55c4ce728c60 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55c4ce728c20 <col:9> 'unsigned int' lvalue Var 0x55c4ce728a10 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55c4ce728c78 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55c4ce728c40 <col:11> 'int' 0
    | `-CompoundStmt 0x55c4ce728d20 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x55c4ce728cd0 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55c4ce728cb0 <col:5> 'unsigned int' lvalue Var 0x55c4ce728a10 'x' 'unsigned int'
    |   `-UnaryOperator 0x55c4ce728d08 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55c4ce728ce8 <col:5> 'unsigned int' lvalue Var 0x55c4ce728ac8 'y' 'unsigned int'
    |-BinaryOperator 0x55c4ce728db0 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x55c4ce728d58 <col:3> 'unsigned int' lvalue Var 0x55c4ce728b80 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x55c4ce728d98 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x55c4ce728d78 <col:7> 'unsigned int' lvalue Var 0x55c4ce728ac8 'y' 'unsigned int'
    |-WhileStmt 0x55c4ce728ef0 <line:23:3, line:27:3>
    | |-BinaryOperator 0x55c4ce728e40 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55c4ce728e10 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55c4ce728dd0 <col:9> 'unsigned int' lvalue Var 0x55c4ce728b80 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x55c4ce728e28 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55c4ce728df0 <col:11> 'int' 0
    | `-CompoundStmt 0x55c4ce728ed0 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x55c4ce728e80 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55c4ce728e60 <col:5> 'unsigned int' lvalue Var 0x55c4ce728a10 'x' 'unsigned int'
    |   `-UnaryOperator 0x55c4ce728eb8 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55c4ce728e98 <col:5> 'unsigned int' lvalue Var 0x55c4ce728b80 'z' 'unsigned int'
    |-WhileStmt 0x55c4ce729028 <line:29:3, line:33:3>
    | |-BinaryOperator 0x55c4ce728f78 <line:29:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55c4ce728f48 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55c4ce728f08 <col:9> 'unsigned int' lvalue Var 0x55c4ce728ac8 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x55c4ce728f60 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55c4ce728f28 <col:11> 'int' 0
    | `-CompoundStmt 0x55c4ce729008 <line:30:3, line:33:3>
    |   |-UnaryOperator 0x55c4ce728fb8 <line:31:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55c4ce728f98 <col:5> 'unsigned int' lvalue Var 0x55c4ce728ac8 'y' 'unsigned int'
    |   `-UnaryOperator 0x55c4ce728ff0 <line:32:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55c4ce728fd0 <col:5> 'unsigned int' lvalue Var 0x55c4ce728b80 'z' 'unsigned int'
    |-WhileStmt 0x55c4ce729160 <line:35:3, line:39:3>
    | |-BinaryOperator 0x55c4ce7290b0 <line:35:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55c4ce729080 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55c4ce729040 <col:9> 'unsigned int' lvalue Var 0x55c4ce728a10 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55c4ce729098 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55c4ce729060 <col:11> 'int' 0
    | `-CompoundStmt 0x55c4ce729140 <line:36:3, line:39:3>
    |   |-UnaryOperator 0x55c4ce7290f0 <line:37:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55c4ce7290d0 <col:5> 'unsigned int' lvalue Var 0x55c4ce728a10 'x' 'unsigned int'
    |   `-UnaryOperator 0x55c4ce729128 <line:38:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55c4ce729108 <col:5> 'unsigned int' lvalue Var 0x55c4ce728ac8 'y' 'unsigned int'
    |-WhileStmt 0x55c4ce729298 <line:41:3, line:45:3>
    | |-BinaryOperator 0x55c4ce7291e8 <line:41:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55c4ce7291b8 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55c4ce729178 <col:9> 'unsigned int' lvalue Var 0x55c4ce728b80 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x55c4ce7291d0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55c4ce729198 <col:11> 'int' 0
    | `-CompoundStmt 0x55c4ce729278 <line:42:3, line:45:3>
    |   |-UnaryOperator 0x55c4ce729228 <line:43:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55c4ce729208 <col:5> 'unsigned int' lvalue Var 0x55c4ce728a10 'x' 'unsigned int'
    |   `-UnaryOperator 0x55c4ce729260 <line:44:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55c4ce729240 <col:5> 'unsigned int' lvalue Var 0x55c4ce728b80 'z' 'unsigned int'
    |-WhileStmt 0x55c4ce7293d0 <line:47:3, line:51:3>
    | |-BinaryOperator 0x55c4ce729320 <line:47:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55c4ce7292f0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55c4ce7292b0 <col:9> 'unsigned int' lvalue Var 0x55c4ce728ac8 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x55c4ce729308 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55c4ce7292d0 <col:11> 'int' 0
    | `-CompoundStmt 0x55c4ce7293b0 <line:48:3, line:51:3>
    |   |-UnaryOperator 0x55c4ce729360 <line:49:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55c4ce729340 <col:5> 'unsigned int' lvalue Var 0x55c4ce728ac8 'y' 'unsigned int'
    |   `-UnaryOperator 0x55c4ce729398 <line:50:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55c4ce729378 <col:5> 'unsigned int' lvalue Var 0x55c4ce728b80 'z' 'unsigned int'
    |-CallExpr 0x55c4ce7294e0 <line:53:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55c4ce7294c8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55c4ce7293e8 <col:3> 'void (int)' Function 0x55c4ce726a98 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55c4ce729478 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55c4ce729448 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55c4ce729408 <col:21> 'unsigned int' lvalue Var 0x55c4ce728b80 'z' 'unsigned int'
    |   `-ImplicitCastExpr 0x55c4ce729460 <col:24> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55c4ce729428 <col:24> 'unsigned int' lvalue Var 0x55c4ce7288f8 'n' 'unsigned int'
    `-ReturnStmt 0x55c4ce729528 <line:54:3, col:10>
      `-IntegerLiteral 0x55c4ce729508 <col:10> 'int' 0
1 warning generated.
