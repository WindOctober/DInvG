./Benchmark/PLDI/SVComp/loops-crafted-1/in-de52.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de52.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5561ec4b3e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5561ec4b4730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5561ec4b4430 '__int128'
|-TypedefDecl 0x5561ec4b47a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5561ec4b4450 'unsigned __int128'
|-TypedefDecl 0x5561ec4b4aa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5561ec4b4880 'struct __NSConstantString_tag'
|   `-Record 0x5561ec4b47f8 '__NSConstantString_tag'
|-TypedefDecl 0x5561ec4b4b40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5561ec4b4b00 'char *'
|   `-BuiltinType 0x5561ec4b3f30 'char'
|-TypedefDecl 0x5561ec4b4e38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5561ec4b4de0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5561ec4b4c20 'struct __va_list_tag'
|     `-Record 0x5561ec4b4b98 '__va_list_tag'
|-FunctionDecl 0x5561ec513b88 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de52.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5561ec513c28 prev 0x5561ec513b88 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5561ec513fa8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5561ec513ce0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5561ec513d60 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5561ec513de0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5561ec513e60 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5561ec514068 <col:99>
|-FunctionDecl 0x5561ec514158 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5561ec514488 <col:20, col:73>
|   `-CallExpr 0x5561ec5143a0 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x5561ec514388 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5561ec5141f8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5561ec513fa8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5561ec5143f8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5561ec5143e0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5561ec514258 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5561ec514428 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5561ec514410 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5561ec5142b8 <col:41> 'char [10]' lvalue "in-de52.c"
|     |-ImplicitCastExpr 0x5561ec514440 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5561ec5142e0 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x5561ec514470 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5561ec514458 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5561ec514338 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5561ec514570 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x5561ec5146e8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5561ec514628 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5561ec5149c8 <col:34, line:10:1>
|   |-IfStmt 0x5561ec5149a0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x5561ec5147e8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5561ec5147d0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5561ec5147b0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5561ec514790 <col:9> 'int' lvalue ParmVar 0x5561ec514628 'cond' 'int'
|   | `-CompoundStmt 0x5561ec514988 <col:16, line:8:3>
|   |   `-LabelStmt 0x5561ec514970 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5561ec514900 <col:12, col:35>
|   |       |-CallExpr 0x5561ec514860 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5561ec514848 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5561ec514800 <col:13> 'void ()' Function 0x5561ec514158 'reach_error' 'void ()'
|   |       `-CallExpr 0x5561ec5148e0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5561ec5148c8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5561ec514880 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5561ec513c28 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5561ec5149b8 <line:9:3>
`-FunctionDecl 0x5561ec516490 <line:12:1, line:49:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x5561ec517048 <line:13:1, line:49:1>
    |-DeclStmt 0x5561ec516630 <line:14:3, col:44>
    | `-VarDecl 0x5561ec516548 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x5561ec516610 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x5561ec5165f8 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5561ec5165b0 <col:20> 'unsigned int (void)' Function 0x5561ec514570 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x5561ec516858 <line:15:3, col:27>
    | |-VarDecl 0x5561ec516660 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x5561ec5166e8 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x5561ec5166c8 <col:18> 'unsigned int' lvalue Var 0x5561ec516548 'n' 'unsigned int'
    | |-VarDecl 0x5561ec516718 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x5561ec5167a0 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5561ec516780 <col:23> 'int' 0
    | `-VarDecl 0x5561ec5167d0 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x5561ec516990 <line:16:3, line:20:3>
    | |-BinaryOperator 0x5561ec5168e0 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x5561ec5168b0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5561ec516870 <col:9> 'unsigned int' lvalue Var 0x5561ec516660 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x5561ec5168c8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5561ec516890 <col:11> 'int' 0
    | `-CompoundStmt 0x5561ec516970 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x5561ec516920 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x5561ec516900 <col:5> 'unsigned int' lvalue Var 0x5561ec516660 'x' 'unsigned int'
    |   `-UnaryOperator 0x5561ec516958 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x5561ec516938 <col:5> 'unsigned int' lvalue Var 0x5561ec516718 'y' 'unsigned int'
    |-BinaryOperator 0x5561ec516a00 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x5561ec5169a8 <col:3> 'unsigned int' lvalue Var 0x5561ec5167d0 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x5561ec5169e8 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x5561ec5169c8 <col:7> 'unsigned int' lvalue Var 0x5561ec516718 'y' 'unsigned int'
    |-WhileStmt 0x5561ec516b40 <line:23:3, line:27:3>
    | |-BinaryOperator 0x5561ec516a90 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x5561ec516a60 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5561ec516a20 <col:9> 'unsigned int' lvalue Var 0x5561ec5167d0 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x5561ec516a78 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5561ec516a40 <col:11> 'int' 0
    | `-CompoundStmt 0x5561ec516b20 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x5561ec516ad0 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x5561ec516ab0 <col:5> 'unsigned int' lvalue Var 0x5561ec516660 'x' 'unsigned int'
    |   `-UnaryOperator 0x5561ec516b08 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x5561ec516ae8 <col:5> 'unsigned int' lvalue Var 0x5561ec5167d0 'z' 'unsigned int'
    |-WhileStmt 0x5561ec516c78 <line:29:3, line:33:3>
    | |-BinaryOperator 0x5561ec516bc8 <line:29:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x5561ec516b98 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5561ec516b58 <col:9> 'unsigned int' lvalue Var 0x5561ec516718 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x5561ec516bb0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5561ec516b78 <col:11> 'int' 0
    | `-CompoundStmt 0x5561ec516c58 <line:30:3, line:33:3>
    |   |-UnaryOperator 0x5561ec516c08 <line:31:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x5561ec516be8 <col:5> 'unsigned int' lvalue Var 0x5561ec516718 'y' 'unsigned int'
    |   `-UnaryOperator 0x5561ec516c40 <line:32:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x5561ec516c20 <col:5> 'unsigned int' lvalue Var 0x5561ec5167d0 'z' 'unsigned int'
    |-WhileStmt 0x5561ec516db0 <line:35:3, line:39:3>
    | |-BinaryOperator 0x5561ec516d00 <line:35:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x5561ec516cd0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5561ec516c90 <col:9> 'unsigned int' lvalue Var 0x5561ec516660 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x5561ec516ce8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5561ec516cb0 <col:11> 'int' 0
    | `-CompoundStmt 0x5561ec516d90 <line:36:3, line:39:3>
    |   |-UnaryOperator 0x5561ec516d40 <line:37:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x5561ec516d20 <col:5> 'unsigned int' lvalue Var 0x5561ec516660 'x' 'unsigned int'
    |   `-UnaryOperator 0x5561ec516d78 <line:38:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x5561ec516d58 <col:5> 'unsigned int' lvalue Var 0x5561ec516718 'y' 'unsigned int'
    |-WhileStmt 0x5561ec516ee8 <line:41:3, line:45:3>
    | |-BinaryOperator 0x5561ec516e38 <line:41:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x5561ec516e08 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5561ec516dc8 <col:9> 'unsigned int' lvalue Var 0x5561ec5167d0 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x5561ec516e20 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5561ec516de8 <col:11> 'int' 0
    | `-CompoundStmt 0x5561ec516ec8 <line:42:3, line:45:3>
    |   |-UnaryOperator 0x5561ec516e78 <line:43:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x5561ec516e58 <col:5> 'unsigned int' lvalue Var 0x5561ec516718 'y' 'unsigned int'
    |   `-UnaryOperator 0x5561ec516eb0 <line:44:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x5561ec516e90 <col:5> 'unsigned int' lvalue Var 0x5561ec5167d0 'z' 'unsigned int'
    |-CallExpr 0x5561ec516ff0 <line:47:3, col:25> 'void'
    | |-ImplicitCastExpr 0x5561ec516fd8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5561ec516f00 <col:3> 'void (int)' Function 0x5561ec5146e8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5561ec516f90 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x5561ec516f60 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5561ec516f20 <col:21> 'unsigned int' lvalue Var 0x5561ec516718 'y' 'unsigned int'
    |   `-ImplicitCastExpr 0x5561ec516f78 <col:24> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5561ec516f40 <col:24> 'int' 0
    `-ReturnStmt 0x5561ec517038 <line:48:3, col:10>
      `-IntegerLiteral 0x5561ec517018 <col:10> 'int' 0
1 warning generated.
