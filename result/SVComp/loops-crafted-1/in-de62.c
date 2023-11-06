./Benchmark/PLDI/SVComp/loops-crafted-1/in-de62.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de62.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55acfd8a7e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55acfd8a8730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55acfd8a8430 '__int128'
|-TypedefDecl 0x55acfd8a87a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55acfd8a8450 'unsigned __int128'
|-TypedefDecl 0x55acfd8a8aa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55acfd8a8880 'struct __NSConstantString_tag'
|   `-Record 0x55acfd8a87f8 '__NSConstantString_tag'
|-TypedefDecl 0x55acfd8a8b40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55acfd8a8b00 'char *'
|   `-BuiltinType 0x55acfd8a7f30 'char'
|-TypedefDecl 0x55acfd8a8e38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55acfd8a8de0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55acfd8a8c20 'struct __va_list_tag'
|     `-Record 0x55acfd8a8b98 '__va_list_tag'
|-FunctionDecl 0x55acfd907f38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de62.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55acfd907fd8 prev 0x55acfd907f38 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55acfd908358 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55acfd908090 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55acfd908110 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55acfd908190 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55acfd908210 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55acfd908418 <col:99>
|-FunctionDecl 0x55acfd908508 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55acfd908838 <col:20, col:73>
|   `-CallExpr 0x55acfd908750 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x55acfd908738 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55acfd9085a8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55acfd908358 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55acfd9087a8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55acfd908790 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55acfd908608 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55acfd9087d8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55acfd9087c0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55acfd908668 <col:41> 'char [10]' lvalue "in-de62.c"
|     |-ImplicitCastExpr 0x55acfd9087f0 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55acfd908690 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x55acfd908820 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55acfd908808 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55acfd9086e8 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55acfd908920 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55acfd908a98 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55acfd9089d8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55acfd908d78 <col:34, line:10:1>
|   |-IfStmt 0x55acfd908d50 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55acfd908b98 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55acfd908b80 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55acfd908b60 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55acfd908b40 <col:9> 'int' lvalue ParmVar 0x55acfd9089d8 'cond' 'int'
|   | `-CompoundStmt 0x55acfd908d38 <col:16, line:8:3>
|   |   `-LabelStmt 0x55acfd908d20 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55acfd908cb0 <col:12, col:35>
|   |       |-CallExpr 0x55acfd908c10 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55acfd908bf8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55acfd908bb0 <col:13> 'void ()' Function 0x55acfd908508 'reach_error' 'void ()'
|   |       `-CallExpr 0x55acfd908c90 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55acfd908c78 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55acfd908c30 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55acfd907fd8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55acfd908d68 <line:9:3>
`-FunctionDecl 0x55acfd90a840 <line:12:1, line:55:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x55acfd90b538 <line:13:1, line:55:1>
    |-DeclStmt 0x55acfd90a9e0 <line:14:3, col:44>
    | `-VarDecl 0x55acfd90a8f8 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x55acfd90a9c0 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55acfd90a9a8 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55acfd90a960 <col:20> 'unsigned int (void)' Function 0x55acfd908920 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x55acfd90ac08 <line:15:3, col:27>
    | |-VarDecl 0x55acfd90aa10 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55acfd90aa98 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55acfd90aa78 <col:18> 'unsigned int' lvalue Var 0x55acfd90a8f8 'n' 'unsigned int'
    | |-VarDecl 0x55acfd90aac8 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55acfd90ab50 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55acfd90ab30 <col:23> 'int' 0
    | `-VarDecl 0x55acfd90ab80 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x55acfd90ad40 <line:16:3, line:20:3>
    | |-BinaryOperator 0x55acfd90ac90 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55acfd90ac60 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55acfd90ac20 <col:9> 'unsigned int' lvalue Var 0x55acfd90aa10 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55acfd90ac78 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55acfd90ac40 <col:11> 'int' 0
    | `-CompoundStmt 0x55acfd90ad20 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x55acfd90acd0 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55acfd90acb0 <col:5> 'unsigned int' lvalue Var 0x55acfd90aa10 'x' 'unsigned int'
    |   `-UnaryOperator 0x55acfd90ad08 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55acfd90ace8 <col:5> 'unsigned int' lvalue Var 0x55acfd90aac8 'y' 'unsigned int'
    |-BinaryOperator 0x55acfd90adb0 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x55acfd90ad58 <col:3> 'unsigned int' lvalue Var 0x55acfd90ab80 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x55acfd90ad98 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x55acfd90ad78 <col:7> 'unsigned int' lvalue Var 0x55acfd90aac8 'y' 'unsigned int'
    |-WhileStmt 0x55acfd90aef0 <line:23:3, line:27:3>
    | |-BinaryOperator 0x55acfd90ae40 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55acfd90ae10 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55acfd90add0 <col:9> 'unsigned int' lvalue Var 0x55acfd90ab80 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x55acfd90ae28 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55acfd90adf0 <col:11> 'int' 0
    | `-CompoundStmt 0x55acfd90aed0 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x55acfd90ae80 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55acfd90ae60 <col:5> 'unsigned int' lvalue Var 0x55acfd90aa10 'x' 'unsigned int'
    |   `-UnaryOperator 0x55acfd90aeb8 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55acfd90ae98 <col:5> 'unsigned int' lvalue Var 0x55acfd90ab80 'z' 'unsigned int'
    |-WhileStmt 0x55acfd90b028 <line:29:3, line:33:3>
    | |-BinaryOperator 0x55acfd90af78 <line:29:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55acfd90af48 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55acfd90af08 <col:9> 'unsigned int' lvalue Var 0x55acfd90aac8 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x55acfd90af60 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55acfd90af28 <col:11> 'int' 0
    | `-CompoundStmt 0x55acfd90b008 <line:30:3, line:33:3>
    |   |-UnaryOperator 0x55acfd90afb8 <line:31:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55acfd90af98 <col:5> 'unsigned int' lvalue Var 0x55acfd90aac8 'y' 'unsigned int'
    |   `-UnaryOperator 0x55acfd90aff0 <line:32:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55acfd90afd0 <col:5> 'unsigned int' lvalue Var 0x55acfd90ab80 'z' 'unsigned int'
    |-WhileStmt 0x55acfd90b160 <line:35:3, line:39:3>
    | |-BinaryOperator 0x55acfd90b0b0 <line:35:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55acfd90b080 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55acfd90b040 <col:9> 'unsigned int' lvalue Var 0x55acfd90aa10 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55acfd90b098 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55acfd90b060 <col:11> 'int' 0
    | `-CompoundStmt 0x55acfd90b140 <line:36:3, line:39:3>
    |   |-UnaryOperator 0x55acfd90b0f0 <line:37:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55acfd90b0d0 <col:5> 'unsigned int' lvalue Var 0x55acfd90aa10 'x' 'unsigned int'
    |   `-UnaryOperator 0x55acfd90b128 <line:38:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55acfd90b108 <col:5> 'unsigned int' lvalue Var 0x55acfd90aac8 'y' 'unsigned int'
    |-WhileStmt 0x55acfd90b298 <line:41:3, line:45:3>
    | |-BinaryOperator 0x55acfd90b1e8 <line:41:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55acfd90b1b8 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55acfd90b178 <col:9> 'unsigned int' lvalue Var 0x55acfd90ab80 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x55acfd90b1d0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55acfd90b198 <col:11> 'int' 0
    | `-CompoundStmt 0x55acfd90b278 <line:42:3, line:45:3>
    |   |-UnaryOperator 0x55acfd90b228 <line:43:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55acfd90b208 <col:5> 'unsigned int' lvalue Var 0x55acfd90aa10 'x' 'unsigned int'
    |   `-UnaryOperator 0x55acfd90b260 <line:44:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55acfd90b240 <col:5> 'unsigned int' lvalue Var 0x55acfd90ab80 'z' 'unsigned int'
    |-WhileStmt 0x55acfd90b3d0 <line:47:3, line:51:3>
    | |-BinaryOperator 0x55acfd90b320 <line:47:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55acfd90b2f0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55acfd90b2b0 <col:9> 'unsigned int' lvalue Var 0x55acfd90aac8 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x55acfd90b308 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55acfd90b2d0 <col:11> 'int' 0
    | `-CompoundStmt 0x55acfd90b3b0 <line:48:3, line:51:3>
    |   |-UnaryOperator 0x55acfd90b360 <line:49:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55acfd90b340 <col:5> 'unsigned int' lvalue Var 0x55acfd90aac8 'y' 'unsigned int'
    |   `-UnaryOperator 0x55acfd90b398 <line:50:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55acfd90b378 <col:5> 'unsigned int' lvalue Var 0x55acfd90aa10 'x' 'unsigned int'
    |-CallExpr 0x55acfd90b4e0 <line:53:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55acfd90b4c8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55acfd90b3e8 <col:3> 'void (int)' Function 0x55acfd908a98 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55acfd90b478 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55acfd90b448 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55acfd90b408 <col:21> 'unsigned int' lvalue Var 0x55acfd90aa10 'x' 'unsigned int'
    |   `-ImplicitCastExpr 0x55acfd90b460 <col:24> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55acfd90b428 <col:24> 'int' 0
    `-ReturnStmt 0x55acfd90b528 <line:54:3, col:10>
      `-IntegerLiteral 0x55acfd90b508 <col:10> 'int' 0
1 warning generated.
