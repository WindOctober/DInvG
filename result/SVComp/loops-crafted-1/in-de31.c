./Benchmark/PLDI/SVComp/loops-crafted-1/in-de31.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de31.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55f447829e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55f44782a730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55f44782a430 '__int128'
|-TypedefDecl 0x55f44782a7a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55f44782a450 'unsigned __int128'
|-TypedefDecl 0x55f44782aaa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55f44782a880 'struct __NSConstantString_tag'
|   `-Record 0x55f44782a7f8 '__NSConstantString_tag'
|-TypedefDecl 0x55f44782ab40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55f44782ab00 'char *'
|   `-BuiltinType 0x55f447829f30 'char'
|-TypedefDecl 0x55f44782ae38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55f44782ade0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55f44782ac20 'struct __va_list_tag'
|     `-Record 0x55f44782ab98 '__va_list_tag'
|-FunctionDecl 0x55f447889ec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de31.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f447889f68 prev 0x55f447889ec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f44788a2e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f44788a020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55f44788a0a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55f44788a120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55f44788a1a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55f44788a3a8 <col:99>
|-FunctionDecl 0x55f44788a498 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55f44788a7c8 <col:20, col:73>
|   `-CallExpr 0x55f44788a6e0 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x55f44788a6c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55f44788a538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55f44788a2e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55f44788a738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55f44788a720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55f44788a598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55f44788a768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55f44788a750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55f44788a5f8 <col:41> 'char [10]' lvalue "in-de31.c"
|     |-ImplicitCastExpr 0x55f44788a780 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55f44788a620 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x55f44788a7b0 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55f44788a798 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55f44788a678 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55f44788a8b0 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55f44788aa28 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55f44788a968 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55f44788ad08 <col:34, line:10:1>
|   |-IfStmt 0x55f44788ace0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55f44788ab28 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55f44788ab10 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55f44788aaf0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55f44788aad0 <col:9> 'int' lvalue ParmVar 0x55f44788a968 'cond' 'int'
|   | `-CompoundStmt 0x55f44788acc8 <col:16, line:8:3>
|   |   `-LabelStmt 0x55f44788acb0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55f44788ac40 <col:12, col:35>
|   |       |-CallExpr 0x55f44788aba0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55f44788ab88 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55f44788ab40 <col:13> 'void ()' Function 0x55f44788a498 'reach_error' 'void ()'
|   |       `-CallExpr 0x55f44788ac20 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55f44788ac08 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55f44788abc0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55f447889f68 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55f44788acf8 <line:9:3>
`-FunctionDecl 0x55f44788c7d0 <line:12:1, line:37:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x55f44788d118 <line:13:1, line:37:1>
    |-DeclStmt 0x55f44788c970 <line:14:3, col:44>
    | `-VarDecl 0x55f44788c888 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x55f44788c950 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55f44788c938 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55f44788c8f0 <col:20> 'unsigned int (void)' Function 0x55f44788a8b0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x55f44788cb98 <line:15:3, col:27>
    | |-VarDecl 0x55f44788c9a0 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55f44788ca28 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55f44788ca08 <col:18> 'unsigned int' lvalue Var 0x55f44788c888 'n' 'unsigned int'
    | |-VarDecl 0x55f44788ca58 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55f44788cae0 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55f44788cac0 <col:23> 'int' 0
    | `-VarDecl 0x55f44788cb10 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x55f44788ccd0 <line:16:3, line:20:3>
    | |-BinaryOperator 0x55f44788cc20 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55f44788cbf0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f44788cbb0 <col:9> 'unsigned int' lvalue Var 0x55f44788c9a0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55f44788cc08 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55f44788cbd0 <col:11> 'int' 0
    | `-CompoundStmt 0x55f44788ccb0 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x55f44788cc60 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55f44788cc40 <col:5> 'unsigned int' lvalue Var 0x55f44788c9a0 'x' 'unsigned int'
    |   `-UnaryOperator 0x55f44788cc98 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55f44788cc78 <col:5> 'unsigned int' lvalue Var 0x55f44788ca58 'y' 'unsigned int'
    |-BinaryOperator 0x55f44788cd40 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x55f44788cce8 <col:3> 'unsigned int' lvalue Var 0x55f44788cb10 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x55f44788cd28 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x55f44788cd08 <col:7> 'unsigned int' lvalue Var 0x55f44788ca58 'y' 'unsigned int'
    |-WhileStmt 0x55f44788ce80 <line:23:3, line:27:3>
    | |-BinaryOperator 0x55f44788cdd0 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55f44788cda0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f44788cd60 <col:9> 'unsigned int' lvalue Var 0x55f44788cb10 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x55f44788cdb8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55f44788cd80 <col:11> 'int' 0
    | `-CompoundStmt 0x55f44788ce60 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x55f44788ce10 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55f44788cdf0 <col:5> 'unsigned int' lvalue Var 0x55f44788c9a0 'x' 'unsigned int'
    |   `-UnaryOperator 0x55f44788ce48 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55f44788ce28 <col:5> 'unsigned int' lvalue Var 0x55f44788cb10 'z' 'unsigned int'
    |-WhileStmt 0x55f44788cfb8 <line:29:3, line:33:3>
    | |-BinaryOperator 0x55f44788cf08 <line:29:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55f44788ced8 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f44788ce98 <col:9> 'unsigned int' lvalue Var 0x55f44788ca58 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x55f44788cef0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55f44788ceb8 <col:11> 'int' 0
    | `-CompoundStmt 0x55f44788cf98 <line:30:3, line:33:3>
    |   |-UnaryOperator 0x55f44788cf48 <line:31:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55f44788cf28 <col:5> 'unsigned int' lvalue Var 0x55f44788ca58 'y' 'unsigned int'
    |   `-UnaryOperator 0x55f44788cf80 <line:32:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55f44788cf60 <col:5> 'unsigned int' lvalue Var 0x55f44788cb10 'z' 'unsigned int'
    |-CallExpr 0x55f44788d0c0 <line:35:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55f44788d0a8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55f44788cfd0 <col:3> 'void (int)' Function 0x55f44788aa28 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55f44788d060 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55f44788d030 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55f44788cff0 <col:21> 'unsigned int' lvalue Var 0x55f44788cb10 'z' 'unsigned int'
    |   `-ImplicitCastExpr 0x55f44788d048 <col:24> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55f44788d010 <col:24> 'unsigned int' lvalue Var 0x55f44788c888 'n' 'unsigned int'
    `-ReturnStmt 0x55f44788d108 <line:36:3, col:10>
      `-IntegerLiteral 0x55f44788d0e8 <col:10> 'int' 0
1 warning generated.
