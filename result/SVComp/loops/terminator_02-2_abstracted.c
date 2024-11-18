./Benchmark/PLDI/SVComp/loops/terminator_02-2_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/terminator_02-2_abstracted.c:12:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x562725ca9f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x562725caa7e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x562725caa4e0 '__int128'
|-TypedefDecl 0x562725caa850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562725caa500 'unsigned __int128'
|-TypedefDecl 0x562725caab58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x562725caa930 'struct __NSConstantString_tag'
|   `-Record 0x562725caa8a8 '__NSConstantString_tag'
|-TypedefDecl 0x562725caabf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562725caabb0 'char *'
|   `-BuiltinType 0x562725ca9fe0 'char'
|-TypedefDecl 0x562725caaee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562725caae90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562725caacd0 'struct __va_list_tag'
|     `-Record 0x562725caac48 '__va_list_tag'
|-FunctionDecl 0x562725d0a258 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/terminator_02-2_abstracted.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562725d0a2f8 prev 0x562725d0a258 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562725d0a3f0 <line:2:1, col:34> col:12 used __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x562725d0a528 <line:3:1, col:37> col:14 __VERIFIER_nondet_bool '_Bool ()' extern
|-FunctionDecl 0x562725d0a618 <line:4:1, col:36> col:13 __VERIFIER_nondet_char 'char ()' extern
|-FunctionDecl 0x562725d0a710 <line:5:1, col:40> col:15 __VERIFIER_nondet_double 'double ()' extern
|-FunctionDecl 0x562725d0a800 <line:6:1, col:38> col:14 __VERIFIER_nondet_float 'float ()' extern
|-FunctionDecl 0x562725d0a8f0 <line:7:1, col:46> col:22 __VERIFIER_nondet_ulong 'unsigned long ()' extern
|-FunctionDecl 0x562725d0a9e0 <line:8:1, col:55> col:27 __VERIFIER_nondet_ulonglong 'unsigned long long ()' extern
|-FunctionDecl 0x562725d0aad0 <line:9:1, col:44> col:21 __VERIFIER_nondet_uint 'unsigned int ()' extern
|-FunctionDecl 0x562725d0ab98 prev 0x562725d0a3f0 <line:10:1, col:34> col:12 used __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x562725d0acd0 prev 0x562725d0a2f8 <line:11:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562725d0b048 <line:12:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x562725d0ad88 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x562725d0ae08 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x562725d0ae88 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x562725d0af08 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x562725d0b108 <col:99>
|-FunctionDecl 0x562725d0c1c8 <line:13:1, col:92> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x562725d0c508 <col:20, col:92>
|   `-CallExpr 0x562725d0c420 <col:22, col:89> 'void'
|     |-ImplicitCastExpr 0x562725d0c408 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x562725d0c268 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x562725d0b048 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x562725d0c478 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x562725d0c460 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x562725d0c2c8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x562725d0c4a8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x562725d0c490 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x562725d0c328 <col:41> 'char [29]' lvalue "terminator_02-2_abstracted.c"
|     |-ImplicitCastExpr 0x562725d0c4c0 <col:73> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x562725d0c360 <col:73> 'int' 3
|     `-ImplicitCastExpr 0x562725d0c4f0 <col:76> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x562725d0c4d8 <col:76> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x562725d0c3b8 <col:76> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x562725d0c5b8 prev 0x562725d0acd0 <line:15:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562725d0c738 <line:16:1, line:18:1> line:16:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x562725d0c670 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x562725d0c8e0 <col:36, line:18:1>
|   `-IfStmt 0x562725d0c8c8 <line:17:3, col:22>
|     |-UnaryOperator 0x562725d0c818 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x562725d0c800 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x562725d0c7e0 <col:7> 'int' lvalue ParmVar 0x562725d0c670 'cond' 'int'
|     `-CompoundStmt 0x562725d0c8b0 <col:13, col:22>
|       `-CallExpr 0x562725d0c890 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x562725d0c878 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x562725d0c830 <col:14> 'void (void) __attribute__((noreturn))' Function 0x562725d0c5b8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x562725d0c9a0 <line:19:1, line:24:1> line:19:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x562725d0c910 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x562725d0cc60 <col:34, line:24:1>
|   |-IfStmt 0x562725d0cc38 <line:20:3, line:22:3>
|   | |-UnaryOperator 0x562725d0caa0 <line:20:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x562725d0ca88 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x562725d0ca68 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x562725d0ca48 <col:9> 'int' lvalue ParmVar 0x562725d0c910 'cond' 'int'
|   | `-CompoundStmt 0x562725d0cc20 <col:16, line:22:3>
|   |   `-LabelStmt 0x562725d0cc08 <line:21:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x562725d0cb98 <col:12, col:35>
|   |       |-CallExpr 0x562725d0cb20 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x562725d0cb08 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x562725d0cab8 <col:13> 'void ()' Function 0x562725d0c1c8 'reach_error' 'void ()'
|   |       `-CallExpr 0x562725d0cb78 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x562725d0cb60 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x562725d0cb40 <col:27> 'void (void) __attribute__((noreturn))' Function 0x562725d0c5b8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x562725d0cc50 <line:23:3>
|-FunctionDecl 0x562725d0cca8 prev 0x562725d0ab98 <line:25:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x562725d0cd68 prev 0x562725d0a528 <line:26:1, col:30> col:7 __VERIFIER_nondet_bool '_Bool ()'
`-FunctionDecl 0x562725d0ce30 <line:28:1, line:47:1> line:28:5 main 'int ()'
  `-CompoundStmt 0x562725d0e3e8 <line:29:1, line:47:1>
    |-DeclStmt 0x562725d0cfd0 <line:30:5, col:34>
    | `-VarDecl 0x562725d0cee8 <col:5, col:33> col:9 used x 'int' cinit
    |   `-CallExpr 0x562725d0cfb0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x562725d0cf98 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562725d0cf50 <col:11> 'int ()' Function 0x562725d0cca8 '__VERIFIER_nondet_int' 'int ()'
    |-DeclStmt 0x562725d0d0c0 <line:31:5, col:34>
    | `-VarDecl 0x562725d0d000 <col:5, col:33> col:9 used z 'int' cinit
    |   `-CallExpr 0x562725d0d0a0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x562725d0d088 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562725d0d068 <col:11> 'int ()' Function 0x562725d0cca8 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x562725d0da28 <line:32:5, col:27>
    | |-UnaryOperator 0x562725d0d9e0 <col:9, col:17> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x562725d0d9c0 <col:10, col:17> 'int'
    | |   `-BinaryOperator 0x562725d0d148 <col:11, col:14> 'int' '>'
    | |     |-ImplicitCastExpr 0x562725d0d130 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x562725d0d0d8 <col:11> 'int' lvalue Var 0x562725d0cee8 'x' 'int'
    | |     `-UnaryOperator 0x562725d0d118 <col:13, col:14> 'int' prefix '-'
    | |       `-IntegerLiteral 0x562725d0d0f8 <col:14> 'int' 100
    | `-ReturnStmt 0x562725d0da18 <col:20, col:27>
    |   `-IntegerLiteral 0x562725d0d9f8 <col:27> 'int' 0
    |-IfStmt 0x562725d0db20 <line:33:5, col:26>
    | |-UnaryOperator 0x562725d0dad8 <col:9, col:16> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x562725d0dab8 <col:10, col:16> 'int'
    | |   `-BinaryOperator 0x562725d0da98 <col:11, col:13> 'int' '<'
    | |     |-ImplicitCastExpr 0x562725d0da80 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x562725d0da40 <col:11> 'int' lvalue Var 0x562725d0cee8 'x' 'int'
    | |     `-IntegerLiteral 0x562725d0da60 <col:13> 'int' 200
    | `-ReturnStmt 0x562725d0db10 <col:19, col:26>
    |   `-IntegerLiteral 0x562725d0daf0 <col:26> 'int' 0
    |-IfStmt 0x562725d0dc18 <line:34:5, col:26>
    | |-UnaryOperator 0x562725d0dbd0 <col:9, col:16> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x562725d0dbb0 <col:10, col:16> 'int'
    | |   `-BinaryOperator 0x562725d0db90 <col:11, col:13> 'int' '>'
    | |     |-ImplicitCastExpr 0x562725d0db78 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x562725d0db38 <col:11> 'int' lvalue Var 0x562725d0d000 'z' 'int'
    | |     `-IntegerLiteral 0x562725d0db58 <col:13> 'int' 100
    | `-ReturnStmt 0x562725d0dc08 <col:19, col:26>
    |   `-IntegerLiteral 0x562725d0dbe8 <col:26> 'int' 0
    |-IfStmt 0x562725d0dd10 <line:35:5, col:26>
    | |-UnaryOperator 0x562725d0dcc8 <col:9, col:16> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x562725d0dca8 <col:10, col:16> 'int'
    | |   `-BinaryOperator 0x562725d0dc88 <col:11, col:13> 'int' '<'
    | |     |-ImplicitCastExpr 0x562725d0dc70 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x562725d0dc30 <col:11> 'int' lvalue Var 0x562725d0d000 'z' 'int'
    | |     `-IntegerLiteral 0x562725d0dc50 <col:13> 'int' 200
    | `-ReturnStmt 0x562725d0dd00 <col:19, col:26>
    |   `-IntegerLiteral 0x562725d0dce0 <col:26> 'int' 0
    |-IfStmt 0x562725d0e008 <line:37:5, line:40:5>
    | |-BinaryOperator 0x562725d0de98 <line:37:9, col:33> 'int' '&'
    | | |-ParenExpr 0x562725d0ddc0 <col:9, col:19> 'int'
    | | | `-BinaryOperator 0x562725d0dda0 <col:10, col:18> 'int' '>'
    | | |   |-ImplicitCastExpr 0x562725d0dd88 <col:10> 'int' <LValueToRValue>
    | | |   | `-DeclRefExpr 0x562725d0dd28 <col:10> 'int' lvalue Var 0x562725d0d000 'z' 'int'
    | | |   `-ParenExpr 0x562725d0dd68 <col:14, col:18> 'int'
    | | |     `-IntegerLiteral 0x562725d0dd48 <col:15> 'int' 100
    | | `-ParenExpr 0x562725d0de78 <col:23, col:33> 'int'
    | |   `-BinaryOperator 0x562725d0de58 <col:24, col:32> 'int' '<'
    | |     |-ImplicitCastExpr 0x562725d0de40 <col:24> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x562725d0dde0 <col:24> 'int' lvalue Var 0x562725d0cee8 'x' 'int'
    | |     `-ParenExpr 0x562725d0de20 <col:28, col:32> 'int'
    | |       `-IntegerLiteral 0x562725d0de00 <col:29> 'int' 100
    | `-CompoundStmt 0x562725d0dfe8 <col:36, line:40:5>
    |   |-BinaryOperator 0x562725d0df30 <line:38:5, col:31> 'int' '='
    |   | |-DeclRefExpr 0x562725d0deb8 <col:5> 'int' lvalue Var 0x562725d0d000 'z' 'int'
    |   | `-CallExpr 0x562725d0df10 <col:9, col:31> 'int'
    |   |   `-ImplicitCastExpr 0x562725d0def8 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x562725d0ded8 <col:9> 'int ()' Function 0x562725d0cca8 '__VERIFIER_nondet_int' 'int ()'
    |   `-BinaryOperator 0x562725d0dfc8 <line:39:5, col:31> 'int' '='
    |     |-DeclRefExpr 0x562725d0df50 <col:5> 'int' lvalue Var 0x562725d0cee8 'x' 'int'
    |     `-CallExpr 0x562725d0dfa8 <col:9, col:31> 'int'
    |       `-ImplicitCastExpr 0x562725d0df90 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x562725d0df70 <col:9> 'int ()' Function 0x562725d0cca8 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x562725d0e208 <line:41:5, col:42>
    | |-BinaryOperator 0x562725d0e190 <col:9, col:33> 'int' '&'
    | | |-ParenExpr 0x562725d0e0b8 <col:9, col:19> 'int'
    | | | `-BinaryOperator 0x562725d0e098 <col:10, col:18> 'int' '>'
    | | |   |-ImplicitCastExpr 0x562725d0e080 <col:10> 'int' <LValueToRValue>
    | | |   | `-DeclRefExpr 0x562725d0e020 <col:10> 'int' lvalue Var 0x562725d0d000 'z' 'int'
    | | |   `-ParenExpr 0x562725d0e060 <col:14, col:18> 'int'
    | | |     `-IntegerLiteral 0x562725d0e040 <col:15> 'int' 100
    | | `-ParenExpr 0x562725d0e170 <col:23, col:33> 'int'
    | |   `-BinaryOperator 0x562725d0e150 <col:24, col:32> 'int' '<'
    | |     |-ImplicitCastExpr 0x562725d0e138 <col:24> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x562725d0e0d8 <col:24> 'int' lvalue Var 0x562725d0cee8 'x' 'int'
    | |     `-ParenExpr 0x562725d0e118 <col:28, col:32> 'int'
    | |       `-IntegerLiteral 0x562725d0e0f8 <col:29> 'int' 100
    | `-CallExpr 0x562725d0e1e8 <col:36, col:42> 'void'
    |   `-ImplicitCastExpr 0x562725d0e1d0 <col:36> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x562725d0e1b0 <col:36> 'void (void) __attribute__((noreturn))' Function 0x562725d0c5b8 'abort' 'void (void) __attribute__((noreturn))'
    |-CallExpr 0x562725d0e390 <line:44:5, col:39> 'void'
    | |-ImplicitCastExpr 0x562725d0e378 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x562725d0e220 <col:5> 'void (int)' Function 0x562725d0c9a0 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x562725d0e330 <col:23, col:36> 'int' '||'
    |   |-BinaryOperator 0x562725d0e298 <col:23, col:26> 'int' '>='
    |   | |-ImplicitCastExpr 0x562725d0e280 <col:23> 'int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x562725d0e240 <col:23> 'int' lvalue Var 0x562725d0cee8 'x' 'int'
    |   | `-IntegerLiteral 0x562725d0e260 <col:26> 'int' 100
    |   `-BinaryOperator 0x562725d0e310 <col:33, col:36> 'int' '<='
    |     |-ImplicitCastExpr 0x562725d0e2f8 <col:33> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x562725d0e2b8 <col:33> 'int' lvalue Var 0x562725d0d000 'z' 'int'
    |     `-IntegerLiteral 0x562725d0e2d8 <col:36> 'int' 100
    `-ReturnStmt 0x562725d0e3d8 <line:46:5, col:12>
      `-IntegerLiteral 0x562725d0e3b8 <col:12> 'int' 0
1 warning generated.
