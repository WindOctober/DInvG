./Benchmark/PLDI/SVComp/loops-crafted-1/in-de51.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de51.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55cbd1a4ce98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55cbd1a4d730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55cbd1a4d430 '__int128'
|-TypedefDecl 0x55cbd1a4d7a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55cbd1a4d450 'unsigned __int128'
|-TypedefDecl 0x55cbd1a4daa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55cbd1a4d880 'struct __NSConstantString_tag'
|   `-Record 0x55cbd1a4d7f8 '__NSConstantString_tag'
|-TypedefDecl 0x55cbd1a4db40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55cbd1a4db00 'char *'
|   `-BuiltinType 0x55cbd1a4cf30 'char'
|-TypedefDecl 0x55cbd1a4de38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55cbd1a4dde0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55cbd1a4dc20 'struct __va_list_tag'
|     `-Record 0x55cbd1a4db98 '__va_list_tag'
|-FunctionDecl 0x55cbd1aacb88 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de51.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55cbd1aacc28 prev 0x55cbd1aacb88 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55cbd1aacfa8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55cbd1aacce0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55cbd1aacd60 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55cbd1aacde0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55cbd1aace60 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55cbd1aad068 <col:99>
|-FunctionDecl 0x55cbd1aad158 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55cbd1aad488 <col:20, col:73>
|   `-CallExpr 0x55cbd1aad3a0 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x55cbd1aad388 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55cbd1aad1f8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55cbd1aacfa8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55cbd1aad3f8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55cbd1aad3e0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55cbd1aad258 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55cbd1aad428 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55cbd1aad410 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55cbd1aad2b8 <col:41> 'char [10]' lvalue "in-de51.c"
|     |-ImplicitCastExpr 0x55cbd1aad440 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55cbd1aad2e0 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x55cbd1aad470 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55cbd1aad458 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55cbd1aad338 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55cbd1aad570 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55cbd1aad6e8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55cbd1aad628 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55cbd1aad9c8 <col:34, line:10:1>
|   |-IfStmt 0x55cbd1aad9a0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55cbd1aad7e8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55cbd1aad7d0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55cbd1aad7b0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55cbd1aad790 <col:9> 'int' lvalue ParmVar 0x55cbd1aad628 'cond' 'int'
|   | `-CompoundStmt 0x55cbd1aad988 <col:16, line:8:3>
|   |   `-LabelStmt 0x55cbd1aad970 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55cbd1aad900 <col:12, col:35>
|   |       |-CallExpr 0x55cbd1aad860 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55cbd1aad848 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55cbd1aad800 <col:13> 'void ()' Function 0x55cbd1aad158 'reach_error' 'void ()'
|   |       `-CallExpr 0x55cbd1aad8e0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55cbd1aad8c8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55cbd1aad880 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55cbd1aacc28 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55cbd1aad9b8 <line:9:3>
`-FunctionDecl 0x55cbd1aaf490 <line:12:1, line:49:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x55cbd1ab0048 <line:13:1, line:49:1>
    |-DeclStmt 0x55cbd1aaf630 <line:14:3, col:44>
    | `-VarDecl 0x55cbd1aaf548 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x55cbd1aaf610 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55cbd1aaf5f8 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55cbd1aaf5b0 <col:20> 'unsigned int (void)' Function 0x55cbd1aad570 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x55cbd1aaf858 <line:15:3, col:27>
    | |-VarDecl 0x55cbd1aaf660 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55cbd1aaf6e8 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55cbd1aaf6c8 <col:18> 'unsigned int' lvalue Var 0x55cbd1aaf548 'n' 'unsigned int'
    | |-VarDecl 0x55cbd1aaf718 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55cbd1aaf7a0 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55cbd1aaf780 <col:23> 'int' 0
    | `-VarDecl 0x55cbd1aaf7d0 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x55cbd1aaf990 <line:16:3, line:20:3>
    | |-BinaryOperator 0x55cbd1aaf8e0 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55cbd1aaf8b0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55cbd1aaf870 <col:9> 'unsigned int' lvalue Var 0x55cbd1aaf660 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55cbd1aaf8c8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55cbd1aaf890 <col:11> 'int' 0
    | `-CompoundStmt 0x55cbd1aaf970 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x55cbd1aaf920 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55cbd1aaf900 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf660 'x' 'unsigned int'
    |   `-UnaryOperator 0x55cbd1aaf958 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55cbd1aaf938 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf718 'y' 'unsigned int'
    |-BinaryOperator 0x55cbd1aafa00 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x55cbd1aaf9a8 <col:3> 'unsigned int' lvalue Var 0x55cbd1aaf7d0 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x55cbd1aaf9e8 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x55cbd1aaf9c8 <col:7> 'unsigned int' lvalue Var 0x55cbd1aaf718 'y' 'unsigned int'
    |-WhileStmt 0x55cbd1aafb40 <line:23:3, line:27:3>
    | |-BinaryOperator 0x55cbd1aafa90 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55cbd1aafa60 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55cbd1aafa20 <col:9> 'unsigned int' lvalue Var 0x55cbd1aaf7d0 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x55cbd1aafa78 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55cbd1aafa40 <col:11> 'int' 0
    | `-CompoundStmt 0x55cbd1aafb20 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x55cbd1aafad0 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55cbd1aafab0 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf660 'x' 'unsigned int'
    |   `-UnaryOperator 0x55cbd1aafb08 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55cbd1aafae8 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf7d0 'z' 'unsigned int'
    |-WhileStmt 0x55cbd1aafc78 <line:29:3, line:33:3>
    | |-BinaryOperator 0x55cbd1aafbc8 <line:29:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55cbd1aafb98 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55cbd1aafb58 <col:9> 'unsigned int' lvalue Var 0x55cbd1aaf718 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x55cbd1aafbb0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55cbd1aafb78 <col:11> 'int' 0
    | `-CompoundStmt 0x55cbd1aafc58 <line:30:3, line:33:3>
    |   |-UnaryOperator 0x55cbd1aafc08 <line:31:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55cbd1aafbe8 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf718 'y' 'unsigned int'
    |   `-UnaryOperator 0x55cbd1aafc40 <line:32:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55cbd1aafc20 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf7d0 'z' 'unsigned int'
    |-WhileStmt 0x55cbd1aafdb0 <line:35:3, line:39:3>
    | |-BinaryOperator 0x55cbd1aafd00 <line:35:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55cbd1aafcd0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55cbd1aafc90 <col:9> 'unsigned int' lvalue Var 0x55cbd1aaf660 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55cbd1aafce8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55cbd1aafcb0 <col:11> 'int' 0
    | `-CompoundStmt 0x55cbd1aafd90 <line:36:3, line:39:3>
    |   |-UnaryOperator 0x55cbd1aafd40 <line:37:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55cbd1aafd20 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf660 'x' 'unsigned int'
    |   `-UnaryOperator 0x55cbd1aafd78 <line:38:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55cbd1aafd58 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf718 'y' 'unsigned int'
    |-WhileStmt 0x55cbd1aafee8 <line:41:3, line:45:3>
    | |-BinaryOperator 0x55cbd1aafe38 <line:41:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55cbd1aafe08 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55cbd1aafdc8 <col:9> 'unsigned int' lvalue Var 0x55cbd1aaf7d0 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x55cbd1aafe20 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55cbd1aafde8 <col:11> 'int' 0
    | `-CompoundStmt 0x55cbd1aafec8 <line:42:3, line:45:3>
    |   |-UnaryOperator 0x55cbd1aafe78 <line:43:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55cbd1aafe58 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf660 'x' 'unsigned int'
    |   `-UnaryOperator 0x55cbd1aafeb0 <line:44:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55cbd1aafe90 <col:5> 'unsigned int' lvalue Var 0x55cbd1aaf7d0 'z' 'unsigned int'
    |-CallExpr 0x55cbd1aafff0 <line:47:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55cbd1aaffd8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55cbd1aaff00 <col:3> 'void (int)' Function 0x55cbd1aad6e8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55cbd1aaff90 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55cbd1aaff60 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55cbd1aaff20 <col:21> 'unsigned int' lvalue Var 0x55cbd1aaf660 'x' 'unsigned int'
    |   `-ImplicitCastExpr 0x55cbd1aaff78 <col:24> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55cbd1aaff40 <col:24> 'unsigned int' lvalue Var 0x55cbd1aaf548 'n' 'unsigned int'
    `-ReturnStmt 0x55cbd1ab0038 <line:48:3, col:10>
      `-IntegerLiteral 0x55cbd1ab0018 <col:10> 'int' 0
1 warning generated.
