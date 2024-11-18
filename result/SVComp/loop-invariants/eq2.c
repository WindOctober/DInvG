./Benchmark/PLDI/SVComp/loop-invariants/eq2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/eq2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55ea9751fdc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55ea97520660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55ea97520360 '__int128'
|-TypedefDecl 0x55ea975206d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55ea97520380 'unsigned __int128'
|-TypedefDecl 0x55ea975209d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55ea975207b0 'struct __NSConstantString_tag'
|   `-Record 0x55ea97520728 '__NSConstantString_tag'
|-TypedefDecl 0x55ea97520a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55ea97520a30 'char *'
|   `-BuiltinType 0x55ea9751fe60 'char'
|-TypedefDecl 0x55ea97520d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55ea97520d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55ea97520b50 'struct __va_list_tag'
|     `-Record 0x55ea97520ac8 '__va_list_tag'
|-FunctionDecl 0x55ea9757fab8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/eq2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ea9757fb58 prev 0x55ea9757fab8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ea9757fed8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55ea9757fc10 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55ea9757fc90 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55ea9757fd10 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55ea9757fd90 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55ea9757ff98 <col:99>
|-FunctionDecl 0x55ea97580088 <line:3:1, col:69> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55ea975803b8 <col:20, col:69>
|   `-CallExpr 0x55ea975802d0 <col:22, col:66> 'void'
|     |-ImplicitCastExpr 0x55ea975802b8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55ea97580128 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55ea9757fed8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55ea97580328 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55ea97580310 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55ea97580188 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55ea97580358 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55ea97580340 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55ea975801e8 <col:41> 'char [6]' lvalue "eq2.c"
|     |-ImplicitCastExpr 0x55ea97580370 <col:50> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55ea97580208 <col:50> 'int' 3
|     `-ImplicitCastExpr 0x55ea975803a0 <col:53> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55ea97580388 <col:53> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55ea97580268 <col:53> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55ea975804a0 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55ea97580618 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55ea97580558 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55ea975808f8 <col:34, line:10:1>
|   |-IfStmt 0x55ea975808d0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55ea97580718 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55ea97580700 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55ea975806e0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55ea975806c0 <col:9> 'int' lvalue ParmVar 0x55ea97580558 'cond' 'int'
|   | `-CompoundStmt 0x55ea975808b8 <col:16, line:8:3>
|   |   `-LabelStmt 0x55ea975808a0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55ea97580830 <col:12, col:35>
|   |       |-CallExpr 0x55ea97580790 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55ea97580778 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55ea97580730 <col:13> 'void ()' Function 0x55ea97580088 'reach_error' 'void ()'
|   |       `-CallExpr 0x55ea97580810 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55ea975807f8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55ea975807b0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55ea9757fb58 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55ea975808e8 <line:9:3>
`-FunctionDecl 0x55ea975823e8 <line:11:1, line:22:1> line:11:5 main 'int (void)'
  `-CompoundStmt 0x55ea97582b48 <col:16, line:22:1>
    |-DeclStmt 0x55ea975825c0 <line:12:3, col:44>
    | `-VarDecl 0x55ea975824d0 <col:3, col:43> col:16 used w 'unsigned int' cinit
    |   `-CallExpr 0x55ea975825a0 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55ea97582588 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55ea97582538 <col:20> 'unsigned int (void)' Function 0x55ea975804a0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x55ea97582690 <line:13:3, col:21>
    | `-VarDecl 0x55ea975825f0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55ea97582678 <col:20> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55ea97582658 <col:20> 'unsigned int' lvalue Var 0x55ea975824d0 'w' 'unsigned int'
    |-DeclStmt 0x55ea975827b8 <line:14:3, col:25>
    | `-VarDecl 0x55ea975826c0 <col:3, col:24> col:16 used y 'unsigned int' cinit
    |   `-BinaryOperator 0x55ea97582798 <col:20, col:24> 'unsigned int' '+'
    |     |-ImplicitCastExpr 0x55ea97582768 <col:20> 'unsigned int' <LValueToRValue>
    |     | `-DeclRefExpr 0x55ea97582728 <col:20> 'unsigned int' lvalue Var 0x55ea975824d0 'w' 'unsigned int'
    |     `-ImplicitCastExpr 0x55ea97582780 <col:24> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x55ea97582748 <col:24> 'int' 1
    |-DeclStmt 0x55ea975828e0 <line:15:3, col:25>
    | `-VarDecl 0x55ea975827e8 <col:3, col:24> col:16 used z 'unsigned int' cinit
    |   `-BinaryOperator 0x55ea975828c0 <col:20, col:24> 'unsigned int' '+'
    |     |-ImplicitCastExpr 0x55ea97582890 <col:20> 'unsigned int' <LValueToRValue>
    |     | `-DeclRefExpr 0x55ea97582850 <col:20> 'unsigned int' lvalue Var 0x55ea975825f0 'x' 'unsigned int'
    |     `-ImplicitCastExpr 0x55ea975828a8 <col:24> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x55ea97582870 <col:24> 'int' 1
    |-WhileStmt 0x55ea975829e0 <line:16:3, line:19:3>
    | |-CallExpr 0x55ea97582930 <line:16:10, col:33> 'unsigned int'
    | | `-ImplicitCastExpr 0x55ea97582918 <col:10> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    | |   `-DeclRefExpr 0x55ea975828f8 <col:10> 'unsigned int (void)' Function 0x55ea975804a0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    | `-CompoundStmt 0x55ea975829c0 <col:36, line:19:3>
    |   |-UnaryOperator 0x55ea97582970 <line:17:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55ea97582950 <col:5> 'unsigned int' lvalue Var 0x55ea975826c0 'y' 'unsigned int'
    |   `-UnaryOperator 0x55ea975829a8 <line:18:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55ea97582988 <col:5> 'unsigned int' lvalue Var 0x55ea975827e8 'z' 'unsigned int'
    |-CallExpr 0x55ea97582af0 <line:20:3, col:27> 'void'
    | |-ImplicitCastExpr 0x55ea97582ad8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55ea975829f8 <col:3> 'void (int)' Function 0x55ea97580618 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55ea97582a88 <col:21, col:26> 'int' '=='
    |   |-ImplicitCastExpr 0x55ea97582a58 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55ea97582a18 <col:21> 'unsigned int' lvalue Var 0x55ea975826c0 'y' 'unsigned int'
    |   `-ImplicitCastExpr 0x55ea97582a70 <col:26> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55ea97582a38 <col:26> 'unsigned int' lvalue Var 0x55ea975827e8 'z' 'unsigned int'
    `-ReturnStmt 0x55ea97582b38 <line:21:3, col:10>
      `-IntegerLiteral 0x55ea97582b18 <col:10> 'int' 0
1 warning generated.
