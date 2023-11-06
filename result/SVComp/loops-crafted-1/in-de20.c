./Benchmark/PLDI/SVComp/loops-crafted-1/in-de20.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de20.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55b6a0b4be98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55b6a0b4c730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55b6a0b4c430 '__int128'
|-TypedefDecl 0x55b6a0b4c7a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55b6a0b4c450 'unsigned __int128'
|-TypedefDecl 0x55b6a0b4caa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55b6a0b4c880 'struct __NSConstantString_tag'
|   `-Record 0x55b6a0b4c7f8 '__NSConstantString_tag'
|-TypedefDecl 0x55b6a0b4cb40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55b6a0b4cb00 'char *'
|   `-BuiltinType 0x55b6a0b4bf30 'char'
|-TypedefDecl 0x55b6a0b4ce38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55b6a0b4cde0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55b6a0b4cc20 'struct __va_list_tag'
|     `-Record 0x55b6a0b4cb98 '__va_list_tag'
|-FunctionDecl 0x55b6a0babb88 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de20.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b6a0babc28 prev 0x55b6a0babb88 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b6a0babfa8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55b6a0babce0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55b6a0babd60 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55b6a0babde0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55b6a0babe60 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55b6a0bac068 <col:99>
|-FunctionDecl 0x55b6a0bac158 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55b6a0bac488 <col:20, col:73>
|   `-CallExpr 0x55b6a0bac3a0 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x55b6a0bac388 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55b6a0bac1f8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55b6a0babfa8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55b6a0bac3f8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55b6a0bac3e0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55b6a0bac258 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55b6a0bac428 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55b6a0bac410 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55b6a0bac2b8 <col:41> 'char [10]' lvalue "in-de20.c"
|     |-ImplicitCastExpr 0x55b6a0bac440 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55b6a0bac2e0 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x55b6a0bac470 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55b6a0bac458 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55b6a0bac338 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55b6a0bac570 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55b6a0bac6e8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55b6a0bac628 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55b6a0bac9c8 <col:34, line:10:1>
|   |-IfStmt 0x55b6a0bac9a0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55b6a0bac7e8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55b6a0bac7d0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55b6a0bac7b0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55b6a0bac790 <col:9> 'int' lvalue ParmVar 0x55b6a0bac628 'cond' 'int'
|   | `-CompoundStmt 0x55b6a0bac988 <col:16, line:8:3>
|   |   `-LabelStmt 0x55b6a0bac970 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55b6a0bac900 <col:12, col:35>
|   |       |-CallExpr 0x55b6a0bac860 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55b6a0bac848 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55b6a0bac800 <col:13> 'void ()' Function 0x55b6a0bac158 'reach_error' 'void ()'
|   |       `-CallExpr 0x55b6a0bac8e0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55b6a0bac8c8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55b6a0bac880 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55b6a0babc28 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55b6a0bac9b8 <line:9:3>
`-FunctionDecl 0x55b6a0bae490 <line:12:1, line:31:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x55b6a0baeca8 <line:13:1, line:31:1>
    |-DeclStmt 0x55b6a0bae630 <line:14:3, col:44>
    | `-VarDecl 0x55b6a0bae548 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x55b6a0bae610 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55b6a0bae5f8 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55b6a0bae5b0 <col:20> 'unsigned int (void)' Function 0x55b6a0bac570 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x55b6a0bae858 <line:15:3, col:27>
    | |-VarDecl 0x55b6a0bae660 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55b6a0bae6e8 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55b6a0bae6c8 <col:18> 'unsigned int' lvalue Var 0x55b6a0bae548 'n' 'unsigned int'
    | |-VarDecl 0x55b6a0bae718 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55b6a0bae7a0 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55b6a0bae780 <col:23> 'int' 0
    | `-VarDecl 0x55b6a0bae7d0 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x55b6a0bae990 <line:16:3, line:20:3>
    | |-BinaryOperator 0x55b6a0bae8e0 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55b6a0bae8b0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55b6a0bae870 <col:9> 'unsigned int' lvalue Var 0x55b6a0bae660 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55b6a0bae8c8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55b6a0bae890 <col:11> 'int' 0
    | `-CompoundStmt 0x55b6a0bae970 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x55b6a0bae920 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55b6a0bae900 <col:5> 'unsigned int' lvalue Var 0x55b6a0bae660 'x' 'unsigned int'
    |   `-UnaryOperator 0x55b6a0bae958 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55b6a0bae938 <col:5> 'unsigned int' lvalue Var 0x55b6a0bae718 'y' 'unsigned int'
    |-BinaryOperator 0x55b6a0baea00 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x55b6a0bae9a8 <col:3> 'unsigned int' lvalue Var 0x55b6a0bae7d0 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x55b6a0bae9e8 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x55b6a0bae9c8 <col:7> 'unsigned int' lvalue Var 0x55b6a0bae718 'y' 'unsigned int'
    |-WhileStmt 0x55b6a0baeb40 <line:23:3, line:27:3>
    | |-BinaryOperator 0x55b6a0baea90 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55b6a0baea60 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55b6a0baea20 <col:9> 'unsigned int' lvalue Var 0x55b6a0bae7d0 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x55b6a0baea78 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55b6a0baea40 <col:11> 'int' 0
    | `-CompoundStmt 0x55b6a0baeb20 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x55b6a0baead0 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55b6a0baeab0 <col:5> 'unsigned int' lvalue Var 0x55b6a0bae660 'x' 'unsigned int'
    |   `-UnaryOperator 0x55b6a0baeb08 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x55b6a0baeae8 <col:5> 'unsigned int' lvalue Var 0x55b6a0bae7d0 'z' 'unsigned int'
    |-CallExpr 0x55b6a0baec50 <line:29:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55b6a0baec38 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55b6a0baeb58 <col:3> 'void (int)' Function 0x55b6a0bac6e8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55b6a0baebe8 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55b6a0baebb8 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55b6a0baeb78 <col:21> 'unsigned int' lvalue Var 0x55b6a0bae660 'x' 'unsigned int'
    |   `-ImplicitCastExpr 0x55b6a0baebd0 <col:24> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55b6a0baeb98 <col:24> 'unsigned int' lvalue Var 0x55b6a0bae548 'n' 'unsigned int'
    `-ReturnStmt 0x55b6a0baec98 <line:30:3, col:10>
      `-IntegerLiteral 0x55b6a0baec78 <col:10> 'int' 0
1 warning generated.
