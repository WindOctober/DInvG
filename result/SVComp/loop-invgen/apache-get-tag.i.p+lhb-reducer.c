./Benchmark/PLDI/SVComp/loop-invgen/apache-get-tag.i.p+lhb-reducer.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/apache-get-tag.i.p+lhb-reducer.c:3:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5556a3668028 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5556a36688c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5556a36685c0 '__int128'
|-TypedefDecl 0x5556a3668930 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5556a36685e0 'unsigned __int128'
|-TypedefDecl 0x5556a3668c38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5556a3668a10 'struct __NSConstantString_tag'
|   `-Record 0x5556a3668988 '__NSConstantString_tag'
|-TypedefDecl 0x5556a3668cd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5556a3668c90 'char *'
|   `-BuiltinType 0x5556a36680c0 'char'
|-TypedefDecl 0x5556a3668fc8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5556a3668f70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5556a3668db0 'struct __va_list_tag'
|     `-Record 0x5556a3668d28 '__va_list_tag'
|-VarDecl 0x5556a36c7c38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/apache-get-tag.i.p+lhb-reducer.c:1:1, col:5> col:5 used __return_main 'int'
|-FunctionDecl 0x5556a36c7dd8 <line:2:6> col:6 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5556a36c7e78 prev 0x5556a36c7dd8 <col:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5556a36c81f8 <line:3:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5556a36c7f30 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5556a36c7fb0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5556a36c8030 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5556a36c80b0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5556a36c82b8 <col:99>
|-FunctionDecl 0x5556a36c8358 <line:4:1, col:96> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5556a36c8698 <col:20, col:96>
|   `-CallExpr 0x5556a36c85b0 <col:22, col:93> 'void'
|     |-ImplicitCastExpr 0x5556a36c8598 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5556a36c83f8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5556a36c81f8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5556a36c8608 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5556a36c85f0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5556a36c8458 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5556a36c8638 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5556a36c8620 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5556a36c84b8 <col:41> 'char [33]' lvalue "apache-get-tag.i.p+lhb-reducer.c"
|     |-ImplicitCastExpr 0x5556a36c8650 <col:77> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5556a36c84f0 <col:77> 'int' 4
|     `-ImplicitCastExpr 0x5556a36c8680 <col:80> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5556a36c8668 <col:80> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5556a36c8548 <col:80> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5556a36c8748 prev 0x5556a36c7e78 <line:5:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5556a36c88c8 <line:6:1, line:8:1> line:6:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x5556a36c8800 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x5556a36c8a70 <col:36, line:8:1>
|   `-IfStmt 0x5556a36c8a58 <line:7:3, col:22>
|     |-UnaryOperator 0x5556a36c89a8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5556a36c8990 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5556a36c8970 <col:7> 'int' lvalue ParmVar 0x5556a36c8800 'cond' 'int'
|     `-CompoundStmt 0x5556a36c8a40 <col:13, col:22>
|       `-CallExpr 0x5556a36c8a20 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x5556a36c8a08 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5556a36c89c0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x5556a36c8748 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5556a36c8b30 <line:9:1, col:32> col:6 __VERIFIER_assert 'void (int)'
| `-ParmVarDecl 0x5556a36c8aa0 <col:24, col:28> col:28 cond 'int'
|-FunctionDecl 0x5556a36cbc98 <line:10:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x5556a36cbd60 <line:11:1, col:10> col:5 main 'int ()'
|-VarDecl 0x5556a36cbe18 <line:12:1, col:5> col:5 used __return_2598 'int'
|-VarDecl 0x5556a36cbe98 <line:13:1, col:5> col:5 used __tmp_2624_0 'int'
|-VarDecl 0x5556a36cbf18 <line:14:1, col:5> col:5 used __tmp_2624_1 'int'
|-VarDecl 0x5556a36cbf98 <line:15:1, col:5> col:5 used __tmp_3137_0 'int'
|-VarDecl 0x5556a36cc018 <line:16:1, col:5> col:5 used __tmp_3137_1 'int'
`-FunctionDecl 0x5556a36cc0a8 prev 0x5556a36cbd60 <line:17:2, line:1006:2> line:17:6 main 'int ()'
  `-CompoundStmt 0x5556a36e0040 <line:18:2, line:1006:2>
    |-DeclStmt 0x5556a36cc1c8 <line:19:2, col:22>
    | `-VarDecl 0x5556a36cc160 <col:2, col:6> col:6 used main__tagbuf_len 'int'
    |-DeclStmt 0x5556a36cc260 <line:20:2, col:13>
    | `-VarDecl 0x5556a36cc1f8 <col:2, col:6> col:6 used main__t 'int'
    |-BinaryOperator 0x5556a36cc320 <line:21:2, col:43> 'int' '='
    | |-DeclRefExpr 0x5556a36cc278 <col:2> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
    | `-CallExpr 0x5556a36cc300 <col:21, col:43> 'int'
    |   `-ImplicitCastExpr 0x5556a36cc2e8 <col:21> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x5556a36cc298 <col:21> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
    `-IfStmt 0x5556a36e0018 <line:22:2, line:1005:2> has_else
      |-BinaryOperator 0x5556a36cc398 <line:22:6, col:26> 'int' '>='
      | |-ImplicitCastExpr 0x5556a36cc380 <col:6> 'int' <LValueToRValue>
      | | `-DeclRefExpr 0x5556a36cc340 <col:6> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      | `-IntegerLiteral 0x5556a36cc360 <col:26> 'int' 1
      |-CompoundStmt 0x5556a36dffc0 <line:23:2, line:1001:2>
      | |-BinaryOperator 0x5556a36cc3f8 <line:24:2, col:12> 'int' '='
      | | |-DeclRefExpr 0x5556a36cc3b8 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      | | `-IntegerLiteral 0x5556a36cc3d8 <col:12> 'int' 0
      | |-BinaryOperator 0x5556a36cc4b0 <line:25:2, col:40> 'int' '='
      | | |-DeclRefExpr 0x5556a36cc418 <col:2> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      | | `-BinaryOperator 0x5556a36cc490 <col:21, col:40> 'int' '-'
      | |   |-ImplicitCastExpr 0x5556a36cc478 <col:21> 'int' <LValueToRValue>
      | |   | `-DeclRefExpr 0x5556a36cc438 <col:21> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      | |   `-IntegerLiteral 0x5556a36cc458 <col:40> 'int' 1
      | `-IfStmt 0x5556a36dff98 <line:26:2, line:1000:2> has_else
      |   |-BinaryOperator 0x5556a36cc540 <line:26:6, col:17> 'int' '=='
      |   | |-ImplicitCastExpr 0x5556a36cc510 <col:6> 'int' <LValueToRValue>
      |   | | `-DeclRefExpr 0x5556a36cc4d0 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |   | `-ImplicitCastExpr 0x5556a36cc528 <col:17> 'int' <LValueToRValue>
      |   |   `-DeclRefExpr 0x5556a36cc4f0 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |   |-CompoundStmt 0x5556a36d14c8 <line:27:2, line:60:2>
      |   | |-LabelStmt 0x5556a36cc5b8 <line:28:2, col:13> 'label_2604'
      |   | | `-NullStmt 0x5556a36cc560 <col:13>
      |   | `-CompoundStmt 0x5556a36d1490 <line:29:2, line:59:2>
      |   |   |-DeclStmt 0x5556a36cc650 <line:30:2, col:13>
      |   |   | `-VarDecl 0x5556a36cc5e8 <col:2, col:6> col:6 used __tmp_1 'int'
      |   |   |-BinaryOperator 0x5556a36cc700 <line:31:2, col:17> 'int' '='
      |   |   | |-DeclRefExpr 0x5556a36cc668 <col:2> 'int' lvalue Var 0x5556a36cc5e8 '__tmp_1' 'int'
      |   |   | `-BinaryOperator 0x5556a36cc6e0 <col:12, col:17> 'int' '<='
      |   |   |   |-IntegerLiteral 0x5556a36cc688 <col:12> 'int' 0
      |   |   |   `-ImplicitCastExpr 0x5556a36cc6c8 <col:17> 'int' <LValueToRValue>
      |   |   |     `-DeclRefExpr 0x5556a36cc6a8 <col:17> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |   |   |-DeclStmt 0x5556a36cc7a0 <line:32:2, col:29>
      |   |   | `-VarDecl 0x5556a36cc738 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |   |   |-BinaryOperator 0x5556a36cc810 <line:33:2, col:28> 'int' '='
      |   |   | |-DeclRefExpr 0x5556a36cc7b8 <col:2> 'int' lvalue Var 0x5556a36cc738 '__VERIFIER_assert__cond' 'int'
      |   |   | `-ImplicitCastExpr 0x5556a36cc7f8 <col:28> 'int' <LValueToRValue>
      |   |   |   `-DeclRefExpr 0x5556a36cc7d8 <col:28> 'int' lvalue Var 0x5556a36cc5e8 '__tmp_1' 'int'
      |   |   `-IfStmt 0x5556a36d1468 <line:34:2, line:58:2> has_else
      |   |     |-BinaryOperator 0x5556a36cc888 <line:34:6, col:33> 'int' '=='
      |   |     | |-ImplicitCastExpr 0x5556a36cc870 <col:6> 'int' <LValueToRValue>
      |   |     | | `-DeclRefExpr 0x5556a36cc830 <col:6> 'int' lvalue Var 0x5556a36cc738 '__VERIFIER_assert__cond' 'int'
      |   |     | `-IntegerLiteral 0x5556a36cc850 <col:33> 'int' 0
      |   |     |-CompoundStmt 0x5556a36cc990 <line:35:2, line:38:2>
      |   |     | |-CompoundStmt 0x5556a36cc930 <line:36:2, col:17>
      |   |     | | `-CallExpr 0x5556a36cc910 <col:3, col:15> 'void'
      |   |     | |   `-ImplicitCastExpr 0x5556a36cc8f8 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |   |     | |     `-DeclRefExpr 0x5556a36cc8a8 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |   |     | `-ReturnStmt 0x5556a36cc980 <line:37:2, col:9>
      |   |     |   `-ImplicitCastExpr 0x5556a36cc968 <col:9> 'int' <LValueToRValue>
      |   |     |     `-DeclRefExpr 0x5556a36cc948 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |   |     `-CompoundStmt 0x5556a36d1450 <line:40:2, line:58:2>
      |   |       `-CompoundStmt 0x5556a36d1418 <line:41:2, line:57:2>
      |   |         |-DeclStmt 0x5556a36cca30 <line:42:2, col:13>
      |   |         | `-VarDecl 0x5556a36cc9c8 <col:2, col:6> col:6 used __tmp_2 'int'
      |   |         |-BinaryOperator 0x5556a36ccaf8 <line:43:2, col:23> 'int' '='
      |   |         | |-DeclRefExpr 0x5556a36cca48 <col:2> 'int' lvalue Var 0x5556a36cc9c8 '__tmp_2' 'int'
      |   |         | `-BinaryOperator 0x5556a36ccad8 <col:12, col:23> 'int' '<='
      |   |         |   |-ImplicitCastExpr 0x5556a36ccaa8 <col:12> 'int' <LValueToRValue>
      |   |         |   | `-DeclRefExpr 0x5556a36cca68 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |   |         |   `-ImplicitCastExpr 0x5556a36ccac0 <col:23> 'int' <LValueToRValue>
      |   |         |     `-DeclRefExpr 0x5556a36cca88 <col:23> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |   |         |-DeclStmt 0x5556a36ccb98 <line:44:2, col:29>
      |   |         | `-VarDecl 0x5556a36ccb30 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |   |         |-BinaryOperator 0x5556a36ccc08 <line:45:2, col:28> 'int' '='
      |   |         | |-DeclRefExpr 0x5556a36ccbb0 <col:2> 'int' lvalue Var 0x5556a36ccb30 '__VERIFIER_assert__cond' 'int'
      |   |         | `-ImplicitCastExpr 0x5556a36ccbf0 <col:28> 'int' <LValueToRValue>
      |   |         |   `-DeclRefExpr 0x5556a36ccbd0 <col:28> 'int' lvalue Var 0x5556a36cc9c8 '__tmp_2' 'int'
      |   |         `-IfStmt 0x5556a36d13f0 <line:46:2, line:56:2> has_else
      |   |           |-BinaryOperator 0x5556a36d11b8 <line:46:6, col:33> 'int' '=='
      |   |           | |-ImplicitCastExpr 0x5556a36d11a0 <col:6> 'int' <LValueToRValue>
      |   |           | | `-DeclRefExpr 0x5556a36ccc28 <col:6> 'int' lvalue Var 0x5556a36ccb30 '__VERIFIER_assert__cond' 'int'
      |   |           | `-IntegerLiteral 0x5556a36ccc48 <col:33> 'int' 0
      |   |           |-CompoundStmt 0x5556a36d1290 <line:47:2, line:50:2>
      |   |           | |-CompoundStmt 0x5556a36d1230 <line:48:2, col:17>
      |   |           | | `-CallExpr 0x5556a36d1210 <col:3, col:15> 'void'
      |   |           | |   `-ImplicitCastExpr 0x5556a36d11f8 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |   |           | |     `-DeclRefExpr 0x5556a36d11d8 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |   |           | `-ReturnStmt 0x5556a36d1280 <line:49:2, col:9>
      |   |           |   `-ImplicitCastExpr 0x5556a36d1268 <col:9> 'int' <LValueToRValue>
      |   |           |     `-DeclRefExpr 0x5556a36d1248 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |   |           `-CompoundStmt 0x5556a36d13c8 <line:52:2, line:56:2>
      |   |             |-LabelStmt 0x5556a36d1308 <line:53:2, col:13> 'label_2597'
      |   |             | `-NullStmt 0x5556a36d12b0 <col:13>
      |   |             |-BinaryOperator 0x5556a36d1360 <line:54:3, col:19> 'int' '='
      |   |             | |-DeclRefExpr 0x5556a36d1320 <col:3> 'int' lvalue Var 0x5556a36cbe18 '__return_2598' 'int'
      |   |             | `-IntegerLiteral 0x5556a36d1340 <col:19> 'int' 0
      |   |             `-ReturnStmt 0x5556a36d13b8 <line:55:2, col:9>
      |   |               `-ImplicitCastExpr 0x5556a36d13a0 <col:9> 'int' <LValueToRValue>
      |   |                 `-DeclRefExpr 0x5556a36d1380 <col:9> 'int' lvalue Var 0x5556a36cbe18 '__return_2598' 'int'
      |   `-CompoundStmt 0x5556a36dff70 <line:62:2, line:1000:2>
      |     |-DeclStmt 0x5556a36d1568 <line:63:2, col:30>
      |     | `-VarDecl 0x5556a36d1500 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |     |-BinaryOperator 0x5556a36d15f8 <line:64:2, col:51> 'int' '='
      |     | |-DeclRefExpr 0x5556a36d1580 <col:2> 'int' lvalue Var 0x5556a36d1500 'main____CPAchecker_TMP_0' 'int'
      |     | `-CallExpr 0x5556a36d15d8 <col:29, col:51> 'int'
      |     |   `-ImplicitCastExpr 0x5556a36d15c0 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |     |     `-DeclRefExpr 0x5556a36d15a0 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |     `-IfStmt 0x5556a36dff48 <line:65:2, line:999:2> has_else
      |       |-UnaryOperator 0x5556a36d16b0 <line:65:6, col:37> 'int' prefix '!' cannot overflow
      |       | `-ParenExpr 0x5556a36d1690 <col:7, col:37> 'int'
      |       |   `-BinaryOperator 0x5556a36d1670 <col:8, col:36> 'int' '=='
      |       |     |-ImplicitCastExpr 0x5556a36d1658 <col:8> 'int' <LValueToRValue>
      |       |     | `-DeclRefExpr 0x5556a36d1618 <col:8> 'int' lvalue Var 0x5556a36d1500 'main____CPAchecker_TMP_0' 'int'
      |       |     `-IntegerLiteral 0x5556a36d1638 <col:36> 'int' 0
      |       |-CompoundStmt 0x5556a36d93f8 <line:66:2, line:290:2>
      |       | `-CompoundStmt 0x5556a36d93c0 <line:67:2, line:289:2>
      |       |   |-DeclStmt 0x5556a36d1748 <line:68:2, col:13>
      |       |   | `-VarDecl 0x5556a36d16e0 <col:2, col:6> col:6 used __tmp_3 'int'
      |       |   |-BinaryOperator 0x5556a36d17f8 <line:69:2, col:17> 'int' '='
      |       |   | |-DeclRefExpr 0x5556a36d1760 <col:2> 'int' lvalue Var 0x5556a36d16e0 '__tmp_3' 'int'
      |       |   | `-BinaryOperator 0x5556a36d17d8 <col:12, col:17> 'int' '<='
      |       |   |   |-IntegerLiteral 0x5556a36d1780 <col:12> 'int' 0
      |       |   |   `-ImplicitCastExpr 0x5556a36d17c0 <col:17> 'int' <LValueToRValue>
      |       |   |     `-DeclRefExpr 0x5556a36d17a0 <col:17> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |   |-DeclStmt 0x5556a36d1898 <line:70:2, col:29>
      |       |   | `-VarDecl 0x5556a36d1830 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |   |-BinaryOperator 0x5556a36d1908 <line:71:2, col:28> 'int' '='
      |       |   | |-DeclRefExpr 0x5556a36d18b0 <col:2> 'int' lvalue Var 0x5556a36d1830 '__VERIFIER_assert__cond' 'int'
      |       |   | `-ImplicitCastExpr 0x5556a36d18f0 <col:28> 'int' <LValueToRValue>
      |       |   |   `-DeclRefExpr 0x5556a36d18d0 <col:28> 'int' lvalue Var 0x5556a36d16e0 '__tmp_3' 'int'
      |       |   `-IfStmt 0x5556a36d9398 <line:72:2, line:288:2> has_else
      |       |     |-BinaryOperator 0x5556a36d1980 <line:72:6, col:33> 'int' '=='
      |       |     | |-ImplicitCastExpr 0x5556a36d1968 <col:6> 'int' <LValueToRValue>
      |       |     | | `-DeclRefExpr 0x5556a36d1928 <col:6> 'int' lvalue Var 0x5556a36d1830 '__VERIFIER_assert__cond' 'int'
      |       |     | `-IntegerLiteral 0x5556a36d1948 <col:33> 'int' 0
      |       |     |-CompoundStmt 0x5556a36d19e8 <line:73:2, line:75:2>
      |       |     | `-ReturnStmt 0x5556a36d19d8 <line:74:2, col:9>
      |       |     |   `-ImplicitCastExpr 0x5556a36d19c0 <col:9> 'int' <LValueToRValue>
      |       |     |     `-DeclRefExpr 0x5556a36d19a0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |     `-CompoundStmt 0x5556a36d9380 <line:77:2, line:288:2>
      |       |       `-CompoundStmt 0x5556a36d9348 <line:78:2, line:287:2>
      |       |         |-DeclStmt 0x5556a36d1a80 <line:79:2, col:13>
      |       |         | `-VarDecl 0x5556a36d1a18 <col:2, col:6> col:6 used __tmp_4 'int'
      |       |         |-BinaryOperator 0x5556a36d1b48 <line:80:2, col:23> 'int' '='
      |       |         | |-DeclRefExpr 0x5556a36d1a98 <col:2> 'int' lvalue Var 0x5556a36d1a18 '__tmp_4' 'int'
      |       |         | `-BinaryOperator 0x5556a36d1b28 <col:12, col:23> 'int' '<='
      |       |         |   |-ImplicitCastExpr 0x5556a36d1af8 <col:12> 'int' <LValueToRValue>
      |       |         |   | `-DeclRefExpr 0x5556a36d1ab8 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |         |   `-ImplicitCastExpr 0x5556a36d1b10 <col:23> 'int' <LValueToRValue>
      |       |         |     `-DeclRefExpr 0x5556a36d1ad8 <col:23> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |       |         |-DeclStmt 0x5556a36d1be8 <line:81:2, col:29>
      |       |         | `-VarDecl 0x5556a36d1b80 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |         |-BinaryOperator 0x5556a36d1c58 <line:82:2, col:28> 'int' '='
      |       |         | |-DeclRefExpr 0x5556a36d1c00 <col:2> 'int' lvalue Var 0x5556a36d1b80 '__VERIFIER_assert__cond' 'int'
      |       |         | `-ImplicitCastExpr 0x5556a36d1c40 <col:28> 'int' <LValueToRValue>
      |       |         |   `-DeclRefExpr 0x5556a36d1c20 <col:28> 'int' lvalue Var 0x5556a36d1a18 '__tmp_4' 'int'
      |       |         `-IfStmt 0x5556a36d9320 <line:83:2, line:286:2> has_else
      |       |           |-BinaryOperator 0x5556a36d1cd0 <line:83:6, col:33> 'int' '=='
      |       |           | |-ImplicitCastExpr 0x5556a36d1cb8 <col:6> 'int' <LValueToRValue>
      |       |           | | `-DeclRefExpr 0x5556a36d1c78 <col:6> 'int' lvalue Var 0x5556a36d1b80 '__VERIFIER_assert__cond' 'int'
      |       |           | `-IntegerLiteral 0x5556a36d1c98 <col:33> 'int' 0
      |       |           |-CompoundStmt 0x5556a36d1d38 <line:84:2, line:86:2>
      |       |           | `-ReturnStmt 0x5556a36d1d28 <line:85:2, col:9>
      |       |           |   `-ImplicitCastExpr 0x5556a36d1d10 <col:9> 'int' <LValueToRValue>
      |       |           |     `-DeclRefExpr 0x5556a36d1cf0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |           `-CompoundStmt 0x5556a36d92d0 <line:88:2, line:286:2>
      |       |             |-DeclStmt 0x5556a36d1e08 <line:89:2, col:40>
      |       |             | `-VarDecl 0x5556a36d1d68 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |       |             |   `-ImplicitCastExpr 0x5556a36d1df0 <col:33> 'int' <LValueToRValue>
      |       |             |     `-DeclRefExpr 0x5556a36d1dd0 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |             |-BinaryOperator 0x5556a36d1eb8 <line:90:2, col:22> 'int' '='
      |       |             | |-DeclRefExpr 0x5556a36d1e20 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |             | `-BinaryOperator 0x5556a36d1e98 <col:12, col:22> 'int' '+'
      |       |             |   |-ImplicitCastExpr 0x5556a36d1e80 <col:12> 'int' <LValueToRValue>
      |       |             |   | `-DeclRefExpr 0x5556a36d1e40 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |             |   `-IntegerLiteral 0x5556a36d1e60 <col:22> 'int' 1
      |       |             |-BinaryOperator 0x5556a36d1f30 <line:91:2, col:17> 'int' '='
      |       |             | |-DeclRefExpr 0x5556a36d1ed8 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |       |             | `-ImplicitCastExpr 0x5556a36d1f18 <col:17> 'int' <LValueToRValue>
      |       |             |   `-DeclRefExpr 0x5556a36d1ef8 <col:17> 'int' lvalue Var 0x5556a36d1500 'main____CPAchecker_TMP_0' 'int'
      |       |             |-BinaryOperator 0x5556a36d1fa8 <line:92:2, col:17> 'int' '='
      |       |             | |-DeclRefExpr 0x5556a36d1f50 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |       |             | `-ImplicitCastExpr 0x5556a36d1f90 <col:17> 'int' <LValueToRValue>
      |       |             |   `-DeclRefExpr 0x5556a36d1f70 <col:17> 'int' lvalue Var 0x5556a36d1d68 'main____CPAchecker_TMP_2' 'int'
      |       |             |-LabelStmt 0x5556a36d2020 <line:93:2, col:13> 'label_2624'
      |       |             | `-NullStmt 0x5556a36d1fc8 <col:13>
      |       |             |-BinaryOperator 0x5556a36d2090 <line:94:2, col:29> 'int' '='
      |       |             | |-DeclRefExpr 0x5556a36d2038 <col:2> 'int' lvalue Var 0x5556a36d1500 'main____CPAchecker_TMP_0' 'int'
      |       |             | `-ImplicitCastExpr 0x5556a36d2078 <col:29> 'int' <LValueToRValue>
      |       |             |   `-DeclRefExpr 0x5556a36d2058 <col:29> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |       |             |-BinaryOperator 0x5556a36d2108 <line:95:2, col:29> 'int' '='
      |       |             | |-DeclRefExpr 0x5556a36d20b0 <col:2> 'int' lvalue Var 0x5556a36d1d68 'main____CPAchecker_TMP_2' 'int'
      |       |             | `-ImplicitCastExpr 0x5556a36d20f0 <col:29> 'int' <LValueToRValue>
      |       |             |   `-DeclRefExpr 0x5556a36d20d0 <col:29> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |       |             `-IfStmt 0x5556a36d92a8 <line:96:2, line:285:2> has_else
      |       |               |-BinaryOperator 0x5556a36d3880 <line:96:6, col:17> 'int' '=='
      |       |               | |-ImplicitCastExpr 0x5556a36d2168 <col:6> 'int' <LValueToRValue>
      |       |               | | `-DeclRefExpr 0x5556a36d2128 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |               | `-ImplicitCastExpr 0x5556a36d2180 <col:17> 'int' <LValueToRValue>
      |       |               |   `-DeclRefExpr 0x5556a36d2148 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |       |               |-CompoundStmt 0x5556a36d4120 <line:97:2, line:127:2>
      |       |               | `-CompoundStmt 0x5556a36d40e8 <line:98:2, line:126:2>
      |       |               |   |-DeclStmt 0x5556a36d3920 <line:99:2, col:13>
      |       |               |   | `-VarDecl 0x5556a36d38b8 <col:2, col:6> col:6 used __tmp_5 'int'
      |       |               |   |-BinaryOperator 0x5556a36d39d0 <line:100:2, col:17> 'int' '='
      |       |               |   | |-DeclRefExpr 0x5556a36d3938 <col:2> 'int' lvalue Var 0x5556a36d38b8 '__tmp_5' 'int'
      |       |               |   | `-BinaryOperator 0x5556a36d39b0 <col:12, col:17> 'int' '<='
      |       |               |   |   |-IntegerLiteral 0x5556a36d3958 <col:12> 'int' 0
      |       |               |   |   `-ImplicitCastExpr 0x5556a36d3998 <col:17> 'int' <LValueToRValue>
      |       |               |   |     `-DeclRefExpr 0x5556a36d3978 <col:17> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |               |   |-DeclStmt 0x5556a36d3a70 <line:101:2, col:29>
      |       |               |   | `-VarDecl 0x5556a36d3a08 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |               |   |-BinaryOperator 0x5556a36d3ae0 <line:102:2, col:28> 'int' '='
      |       |               |   | |-DeclRefExpr 0x5556a36d3a88 <col:2> 'int' lvalue Var 0x5556a36d3a08 '__VERIFIER_assert__cond' 'int'
      |       |               |   | `-ImplicitCastExpr 0x5556a36d3ac8 <col:28> 'int' <LValueToRValue>
      |       |               |   |   `-DeclRefExpr 0x5556a36d3aa8 <col:28> 'int' lvalue Var 0x5556a36d38b8 '__tmp_5' 'int'
      |       |               |   `-IfStmt 0x5556a36d40c0 <line:103:2, line:125:2> has_else
      |       |               |     |-BinaryOperator 0x5556a36d3b58 <line:103:6, col:33> 'int' '=='
      |       |               |     | |-ImplicitCastExpr 0x5556a36d3b40 <col:6> 'int' <LValueToRValue>
      |       |               |     | | `-DeclRefExpr 0x5556a36d3b00 <col:6> 'int' lvalue Var 0x5556a36d3a08 '__VERIFIER_assert__cond' 'int'
      |       |               |     | `-IntegerLiteral 0x5556a36d3b20 <col:33> 'int' 0
      |       |               |     |-CompoundStmt 0x5556a36d3c30 <line:104:2, line:107:2>
      |       |               |     | |-CompoundStmt 0x5556a36d3bd0 <line:105:2, col:17>
      |       |               |     | | `-CallExpr 0x5556a36d3bb0 <col:3, col:15> 'void'
      |       |               |     | |   `-ImplicitCastExpr 0x5556a36d3b98 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |               |     | |     `-DeclRefExpr 0x5556a36d3b78 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |               |     | `-ReturnStmt 0x5556a36d3c20 <line:106:2, col:9>
      |       |               |     |   `-ImplicitCastExpr 0x5556a36d3c08 <col:9> 'int' <LValueToRValue>
      |       |               |     |     `-DeclRefExpr 0x5556a36d3be8 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |               |     `-CompoundStmt 0x5556a36d40a8 <line:109:2, line:125:2>
      |       |               |       `-CompoundStmt 0x5556a36d4070 <line:110:2, line:124:2>
      |       |               |         |-DeclStmt 0x5556a36d3cd0 <line:111:2, col:13>
      |       |               |         | `-VarDecl 0x5556a36d3c68 <col:2, col:6> col:6 used __tmp_6 'int'
      |       |               |         |-BinaryOperator 0x5556a36d3d98 <line:112:2, col:23> 'int' '='
      |       |               |         | |-DeclRefExpr 0x5556a36d3ce8 <col:2> 'int' lvalue Var 0x5556a36d3c68 '__tmp_6' 'int'
      |       |               |         | `-BinaryOperator 0x5556a36d3d78 <col:12, col:23> 'int' '<='
      |       |               |         |   |-ImplicitCastExpr 0x5556a36d3d48 <col:12> 'int' <LValueToRValue>
      |       |               |         |   | `-DeclRefExpr 0x5556a36d3d08 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |               |         |   `-ImplicitCastExpr 0x5556a36d3d60 <col:23> 'int' <LValueToRValue>
      |       |               |         |     `-DeclRefExpr 0x5556a36d3d28 <col:23> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |       |               |         |-DeclStmt 0x5556a36d3e38 <line:113:2, col:29>
      |       |               |         | `-VarDecl 0x5556a36d3dd0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |               |         |-BinaryOperator 0x5556a36d3ea8 <line:114:2, col:28> 'int' '='
      |       |               |         | |-DeclRefExpr 0x5556a36d3e50 <col:2> 'int' lvalue Var 0x5556a36d3dd0 '__VERIFIER_assert__cond' 'int'
      |       |               |         | `-ImplicitCastExpr 0x5556a36d3e90 <col:28> 'int' <LValueToRValue>
      |       |               |         |   `-DeclRefExpr 0x5556a36d3e70 <col:28> 'int' lvalue Var 0x5556a36d3c68 '__tmp_6' 'int'
      |       |               |         `-IfStmt 0x5556a36d4048 <line:115:2, line:123:2> has_else
      |       |               |           |-BinaryOperator 0x5556a36d3f20 <line:115:6, col:33> 'int' '=='
      |       |               |           | |-ImplicitCastExpr 0x5556a36d3f08 <col:6> 'int' <LValueToRValue>
      |       |               |           | | `-DeclRefExpr 0x5556a36d3ec8 <col:6> 'int' lvalue Var 0x5556a36d3dd0 '__VERIFIER_assert__cond' 'int'
      |       |               |           | `-IntegerLiteral 0x5556a36d3ee8 <col:33> 'int' 0
      |       |               |           |-CompoundStmt 0x5556a36d3ff8 <line:116:2, line:119:2>
      |       |               |           | |-CompoundStmt 0x5556a36d3f98 <line:117:2, col:17>
      |       |               |           | | `-CallExpr 0x5556a36d3f78 <col:3, col:15> 'void'
      |       |               |           | |   `-ImplicitCastExpr 0x5556a36d3f60 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |               |           | |     `-DeclRefExpr 0x5556a36d3f40 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |               |           | `-ReturnStmt 0x5556a36d3fe8 <line:118:2, col:9>
      |       |               |           |   `-ImplicitCastExpr 0x5556a36d3fd0 <col:9> 'int' <LValueToRValue>
      |       |               |           |     `-DeclRefExpr 0x5556a36d3fb0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |               |           `-CompoundStmt 0x5556a36d4030 <line:121:2, line:123:2>
      |       |               |             `-GotoStmt 0x5556a36d4018 <line:122:2, col:7> 'label_2597' 0x5556a36d12b8
      |       |               `-CompoundStmt 0x5556a36d9280 <line:129:2, line:285:2>
      |       |                 |-DeclStmt 0x5556a36d41b8 <line:130:2, col:30>
      |       |                 | `-VarDecl 0x5556a36d4150 <col:2, col:6> col:6 used main____CPAchecker_TMP_3 'int'
      |       |                 |-BinaryOperator 0x5556a36d4248 <line:131:2, col:51> 'int' '='
      |       |                 | |-DeclRefExpr 0x5556a36d41d0 <col:2> 'int' lvalue Var 0x5556a36d4150 'main____CPAchecker_TMP_3' 'int'
      |       |                 | `-CallExpr 0x5556a36d4228 <col:29, col:51> 'int'
      |       |                 |   `-ImplicitCastExpr 0x5556a36d4210 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |       |                 |     `-DeclRefExpr 0x5556a36d41f0 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |       |                 `-IfStmt 0x5556a36d9258 <line:132:2, line:284:2> has_else
      |       |                   |-UnaryOperator 0x5556a36d4300 <line:132:6, col:37> 'int' prefix '!' cannot overflow
      |       |                   | `-ParenExpr 0x5556a36d42e0 <col:7, col:37> 'int'
      |       |                   |   `-BinaryOperator 0x5556a36d42c0 <col:8, col:36> 'int' '=='
      |       |                   |     |-ImplicitCastExpr 0x5556a36d42a8 <col:8> 'int' <LValueToRValue>
      |       |                   |     | `-DeclRefExpr 0x5556a36d4268 <col:8> 'int' lvalue Var 0x5556a36d4150 'main____CPAchecker_TMP_3' 'int'
      |       |                   |     `-IntegerLiteral 0x5556a36d4288 <col:36> 'int' 0
      |       |                   |-CompoundStmt 0x5556a36d8720 <line:133:2, line:243:2>
      |       |                   | |-DeclStmt 0x5556a36d4398 <line:134:2, col:30>
      |       |                   | | `-VarDecl 0x5556a36d4330 <col:2, col:6> col:6 used main____CPAchecker_TMP_4 'int'
      |       |                   | |-BinaryOperator 0x5556a36d4428 <line:135:2, col:51> 'int' '='
      |       |                   | | |-DeclRefExpr 0x5556a36d43b0 <col:2> 'int' lvalue Var 0x5556a36d4330 'main____CPAchecker_TMP_4' 'int'
      |       |                   | | `-CallExpr 0x5556a36d4408 <col:29, col:51> 'int'
      |       |                   | |   `-ImplicitCastExpr 0x5556a36d43f0 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |       |                   | |     `-DeclRefExpr 0x5556a36d43d0 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |       |                   | `-IfStmt 0x5556a36d86f8 <line:136:2, line:242:2> has_else
      |       |                   |   |-UnaryOperator 0x5556a36d44e0 <line:136:6, col:37> 'int' prefix '!' cannot overflow
      |       |                   |   | `-ParenExpr 0x5556a36d44c0 <col:7, col:37> 'int'
      |       |                   |   |   `-BinaryOperator 0x5556a36d44a0 <col:8, col:36> 'int' '=='
      |       |                   |   |     |-ImplicitCastExpr 0x5556a36d4488 <col:8> 'int' <LValueToRValue>
      |       |                   |   |     | `-DeclRefExpr 0x5556a36d4448 <col:8> 'int' lvalue Var 0x5556a36d4330 'main____CPAchecker_TMP_4' 'int'
      |       |                   |   |     `-IntegerLiteral 0x5556a36d4468 <col:36> 'int' 0
      |       |                   |   |-CompoundStmt 0x5556a36d86b0 <line:137:2, line:238:2>
      |       |                   |   | `-CompoundStmt 0x5556a36d8678 <line:138:2, line:237:2>
      |       |                   |   |   |-DeclStmt 0x5556a36d4578 <line:139:2, col:13>
      |       |                   |   |   | `-VarDecl 0x5556a36d4510 <col:2, col:6> col:6 used __tmp_7 'int'
      |       |                   |   |   |-BinaryOperator 0x5556a36d4628 <line:140:2, col:17> 'int' '='
      |       |                   |   |   | |-DeclRefExpr 0x5556a36d4590 <col:2> 'int' lvalue Var 0x5556a36d4510 '__tmp_7' 'int'
      |       |                   |   |   | `-BinaryOperator 0x5556a36d4608 <col:12, col:17> 'int' '<='
      |       |                   |   |   |   |-IntegerLiteral 0x5556a36d45b0 <col:12> 'int' 0
      |       |                   |   |   |   `-ImplicitCastExpr 0x5556a36d45f0 <col:17> 'int' <LValueToRValue>
      |       |                   |   |   |     `-DeclRefExpr 0x5556a36d45d0 <col:17> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |   |-DeclStmt 0x5556a36d46c8 <line:141:2, col:29>
      |       |                   |   |   | `-VarDecl 0x5556a36d4660 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |                   |   |   |-BinaryOperator 0x5556a36d4738 <line:142:2, col:28> 'int' '='
      |       |                   |   |   | |-DeclRefExpr 0x5556a36d46e0 <col:2> 'int' lvalue Var 0x5556a36d4660 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |   | `-ImplicitCastExpr 0x5556a36d4720 <col:28> 'int' <LValueToRValue>
      |       |                   |   |   |   `-DeclRefExpr 0x5556a36d4700 <col:28> 'int' lvalue Var 0x5556a36d4510 '__tmp_7' 'int'
      |       |                   |   |   `-IfStmt 0x5556a36d8650 <line:143:2, line:236:2> has_else
      |       |                   |   |     |-BinaryOperator 0x5556a36d47b0 <line:143:6, col:33> 'int' '=='
      |       |                   |   |     | |-ImplicitCastExpr 0x5556a36d4798 <col:6> 'int' <LValueToRValue>
      |       |                   |   |     | | `-DeclRefExpr 0x5556a36d4758 <col:6> 'int' lvalue Var 0x5556a36d4660 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |     | `-IntegerLiteral 0x5556a36d4778 <col:33> 'int' 0
      |       |                   |   |     |-CompoundStmt 0x5556a36d57d0 <line:144:2, line:147:2>
      |       |                   |   |     | |-CompoundStmt 0x5556a36d4828 <line:145:2, col:17>
      |       |                   |   |     | | `-CallExpr 0x5556a36d4808 <col:3, col:15> 'void'
      |       |                   |   |     | |   `-ImplicitCastExpr 0x5556a36d47f0 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |                   |   |     | |     `-DeclRefExpr 0x5556a36d47d0 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |                   |   |     | `-ReturnStmt 0x5556a36d57c0 <line:146:2, col:9>
      |       |                   |   |     |   `-ImplicitCastExpr 0x5556a36d4860 <col:9> 'int' <LValueToRValue>
      |       |                   |   |     |     `-DeclRefExpr 0x5556a36d4840 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |                   |   |     `-CompoundStmt 0x5556a36d8638 <line:149:2, line:236:2>
      |       |                   |   |       `-CompoundStmt 0x5556a36d8600 <line:150:2, line:235:2>
      |       |                   |   |         |-DeclStmt 0x5556a36d5870 <line:151:2, col:13>
      |       |                   |   |         | `-VarDecl 0x5556a36d5808 <col:2, col:6> col:6 used __tmp_8 'int'
      |       |                   |   |         |-BinaryOperator 0x5556a36d5938 <line:152:2, col:23> 'int' '='
      |       |                   |   |         | |-DeclRefExpr 0x5556a36d5888 <col:2> 'int' lvalue Var 0x5556a36d5808 '__tmp_8' 'int'
      |       |                   |   |         | `-BinaryOperator 0x5556a36d5918 <col:12, col:23> 'int' '<='
      |       |                   |   |         |   |-ImplicitCastExpr 0x5556a36d58e8 <col:12> 'int' <LValueToRValue>
      |       |                   |   |         |   | `-DeclRefExpr 0x5556a36d58a8 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |         |   `-ImplicitCastExpr 0x5556a36d5900 <col:23> 'int' <LValueToRValue>
      |       |                   |   |         |     `-DeclRefExpr 0x5556a36d58c8 <col:23> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |       |                   |   |         |-DeclStmt 0x5556a36d59d8 <line:153:2, col:29>
      |       |                   |   |         | `-VarDecl 0x5556a36d5970 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |                   |   |         |-BinaryOperator 0x5556a36d5a48 <line:154:2, col:28> 'int' '='
      |       |                   |   |         | |-DeclRefExpr 0x5556a36d59f0 <col:2> 'int' lvalue Var 0x5556a36d5970 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |         | `-ImplicitCastExpr 0x5556a36d5a30 <col:28> 'int' <LValueToRValue>
      |       |                   |   |         |   `-DeclRefExpr 0x5556a36d5a10 <col:28> 'int' lvalue Var 0x5556a36d5808 '__tmp_8' 'int'
      |       |                   |   |         `-IfStmt 0x5556a36d85d8 <line:155:2, line:234:2> has_else
      |       |                   |   |           |-BinaryOperator 0x5556a36d5ac0 <line:155:6, col:33> 'int' '=='
      |       |                   |   |           | |-ImplicitCastExpr 0x5556a36d5aa8 <col:6> 'int' <LValueToRValue>
      |       |                   |   |           | | `-DeclRefExpr 0x5556a36d5a68 <col:6> 'int' lvalue Var 0x5556a36d5970 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |           | `-IntegerLiteral 0x5556a36d5a88 <col:33> 'int' 0
      |       |                   |   |           |-CompoundStmt 0x5556a36d5b98 <line:156:2, line:159:2>
      |       |                   |   |           | |-CompoundStmt 0x5556a36d5b38 <line:157:2, col:17>
      |       |                   |   |           | | `-CallExpr 0x5556a36d5b18 <col:3, col:15> 'void'
      |       |                   |   |           | |   `-ImplicitCastExpr 0x5556a36d5b00 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |                   |   |           | |     `-DeclRefExpr 0x5556a36d5ae0 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |                   |   |           | `-ReturnStmt 0x5556a36d5b88 <line:158:2, col:9>
      |       |                   |   |           |   `-ImplicitCastExpr 0x5556a36d5b70 <col:9> 'int' <LValueToRValue>
      |       |                   |   |           |     `-DeclRefExpr 0x5556a36d5b50 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |                   |   |           `-CompoundStmt 0x5556a36d85b0 <line:161:2, line:234:2>
      |       |                   |   |             |-DeclStmt 0x5556a36d5c70 <line:162:2, col:40>
      |       |                   |   |             | `-VarDecl 0x5556a36d5bd0 <col:2, col:33> col:6 main____CPAchecker_TMP_5 'int' cinit
      |       |                   |   |             |   `-ImplicitCastExpr 0x5556a36d5c58 <col:33> 'int' <LValueToRValue>
      |       |                   |   |             |     `-DeclRefExpr 0x5556a36d5c38 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |             |-BinaryOperator 0x5556a36d5d20 <line:163:2, col:22> 'int' '='
      |       |                   |   |             | |-DeclRefExpr 0x5556a36d5c88 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |             | `-BinaryOperator 0x5556a36d5d00 <col:12, col:22> 'int' '+'
      |       |                   |   |             |   |-ImplicitCastExpr 0x5556a36d5ce8 <col:12> 'int' <LValueToRValue>
      |       |                   |   |             |   | `-DeclRefExpr 0x5556a36d5ca8 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |             |   `-IntegerLiteral 0x5556a36d5cc8 <col:22> 'int' 1
      |       |                   |   |             `-IfStmt 0x5556a36d8588 <line:164:2, line:233:2> has_else
      |       |                   |   |               |-BinaryOperator 0x5556a36d5db0 <line:164:6, col:17> 'int' '=='
      |       |                   |   |               | |-ImplicitCastExpr 0x5556a36d5d80 <col:6> 'int' <LValueToRValue>
      |       |                   |   |               | | `-DeclRefExpr 0x5556a36d5d40 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |               | `-ImplicitCastExpr 0x5556a36d5d98 <col:17> 'int' <LValueToRValue>
      |       |                   |   |               |   `-DeclRefExpr 0x5556a36d5d60 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |       |                   |   |               |-CompoundStmt 0x5556a36d6650 <line:165:2, line:195:2>
      |       |                   |   |               | `-CompoundStmt 0x5556a36d6618 <line:166:2, line:194:2>
      |       |                   |   |               |   |-DeclStmt 0x5556a36d5e50 <line:167:2, col:13>
      |       |                   |   |               |   | `-VarDecl 0x5556a36d5de8 <col:2, col:6> col:6 used __tmp_9 'int'
      |       |                   |   |               |   |-BinaryOperator 0x5556a36d5f00 <line:168:2, col:17> 'int' '='
      |       |                   |   |               |   | |-DeclRefExpr 0x5556a36d5e68 <col:2> 'int' lvalue Var 0x5556a36d5de8 '__tmp_9' 'int'
      |       |                   |   |               |   | `-BinaryOperator 0x5556a36d5ee0 <col:12, col:17> 'int' '<='
      |       |                   |   |               |   |   |-IntegerLiteral 0x5556a36d5e88 <col:12> 'int' 0
      |       |                   |   |               |   |   `-ImplicitCastExpr 0x5556a36d5ec8 <col:17> 'int' <LValueToRValue>
      |       |                   |   |               |   |     `-DeclRefExpr 0x5556a36d5ea8 <col:17> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |               |   |-DeclStmt 0x5556a36d5fa0 <line:169:2, col:29>
      |       |                   |   |               |   | `-VarDecl 0x5556a36d5f38 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |                   |   |               |   |-BinaryOperator 0x5556a36d6010 <line:170:2, col:28> 'int' '='
      |       |                   |   |               |   | |-DeclRefExpr 0x5556a36d5fb8 <col:2> 'int' lvalue Var 0x5556a36d5f38 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |               |   | `-ImplicitCastExpr 0x5556a36d5ff8 <col:28> 'int' <LValueToRValue>
      |       |                   |   |               |   |   `-DeclRefExpr 0x5556a36d5fd8 <col:28> 'int' lvalue Var 0x5556a36d5de8 '__tmp_9' 'int'
      |       |                   |   |               |   `-IfStmt 0x5556a36d65f0 <line:171:2, line:193:2> has_else
      |       |                   |   |               |     |-BinaryOperator 0x5556a36d6088 <line:171:6, col:33> 'int' '=='
      |       |                   |   |               |     | |-ImplicitCastExpr 0x5556a36d6070 <col:6> 'int' <LValueToRValue>
      |       |                   |   |               |     | | `-DeclRefExpr 0x5556a36d6030 <col:6> 'int' lvalue Var 0x5556a36d5f38 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |               |     | `-IntegerLiteral 0x5556a36d6050 <col:33> 'int' 0
      |       |                   |   |               |     |-CompoundStmt 0x5556a36d6160 <line:172:2, line:175:2>
      |       |                   |   |               |     | |-CompoundStmt 0x5556a36d6100 <line:173:2, col:17>
      |       |                   |   |               |     | | `-CallExpr 0x5556a36d60e0 <col:3, col:15> 'void'
      |       |                   |   |               |     | |   `-ImplicitCastExpr 0x5556a36d60c8 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |                   |   |               |     | |     `-DeclRefExpr 0x5556a36d60a8 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |                   |   |               |     | `-ReturnStmt 0x5556a36d6150 <line:174:2, col:9>
      |       |                   |   |               |     |   `-ImplicitCastExpr 0x5556a36d6138 <col:9> 'int' <LValueToRValue>
      |       |                   |   |               |     |     `-DeclRefExpr 0x5556a36d6118 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |                   |   |               |     `-CompoundStmt 0x5556a36d65d8 <line:177:2, line:193:2>
      |       |                   |   |               |       `-CompoundStmt 0x5556a36d65a0 <line:178:2, line:192:2>
      |       |                   |   |               |         |-DeclStmt 0x5556a36d6200 <line:179:2, col:14>
      |       |                   |   |               |         | `-VarDecl 0x5556a36d6198 <col:2, col:6> col:6 used __tmp_10 'int'
      |       |                   |   |               |         |-BinaryOperator 0x5556a36d62c8 <line:180:2, col:24> 'int' '='
      |       |                   |   |               |         | |-DeclRefExpr 0x5556a36d6218 <col:2> 'int' lvalue Var 0x5556a36d6198 '__tmp_10' 'int'
      |       |                   |   |               |         | `-BinaryOperator 0x5556a36d62a8 <col:13, col:24> 'int' '<='
      |       |                   |   |               |         |   |-ImplicitCastExpr 0x5556a36d6278 <col:13> 'int' <LValueToRValue>
      |       |                   |   |               |         |   | `-DeclRefExpr 0x5556a36d6238 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |               |         |   `-ImplicitCastExpr 0x5556a36d6290 <col:24> 'int' <LValueToRValue>
      |       |                   |   |               |         |     `-DeclRefExpr 0x5556a36d6258 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |       |                   |   |               |         |-DeclStmt 0x5556a36d6368 <line:181:2, col:29>
      |       |                   |   |               |         | `-VarDecl 0x5556a36d6300 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |                   |   |               |         |-BinaryOperator 0x5556a36d63d8 <line:182:2, col:28> 'int' '='
      |       |                   |   |               |         | |-DeclRefExpr 0x5556a36d6380 <col:2> 'int' lvalue Var 0x5556a36d6300 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |               |         | `-ImplicitCastExpr 0x5556a36d63c0 <col:28> 'int' <LValueToRValue>
      |       |                   |   |               |         |   `-DeclRefExpr 0x5556a36d63a0 <col:28> 'int' lvalue Var 0x5556a36d6198 '__tmp_10' 'int'
      |       |                   |   |               |         `-IfStmt 0x5556a36d6578 <line:183:2, line:191:2> has_else
      |       |                   |   |               |           |-BinaryOperator 0x5556a36d6450 <line:183:6, col:33> 'int' '=='
      |       |                   |   |               |           | |-ImplicitCastExpr 0x5556a36d6438 <col:6> 'int' <LValueToRValue>
      |       |                   |   |               |           | | `-DeclRefExpr 0x5556a36d63f8 <col:6> 'int' lvalue Var 0x5556a36d6300 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |               |           | `-IntegerLiteral 0x5556a36d6418 <col:33> 'int' 0
      |       |                   |   |               |           |-CompoundStmt 0x5556a36d6528 <line:184:2, line:187:2>
      |       |                   |   |               |           | |-CompoundStmt 0x5556a36d64c8 <line:185:2, col:17>
      |       |                   |   |               |           | | `-CallExpr 0x5556a36d64a8 <col:3, col:15> 'void'
      |       |                   |   |               |           | |   `-ImplicitCastExpr 0x5556a36d6490 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |                   |   |               |           | |     `-DeclRefExpr 0x5556a36d6470 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |                   |   |               |           | `-ReturnStmt 0x5556a36d6518 <line:186:2, col:9>
      |       |                   |   |               |           |   `-ImplicitCastExpr 0x5556a36d6500 <col:9> 'int' <LValueToRValue>
      |       |                   |   |               |           |     `-DeclRefExpr 0x5556a36d64e0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |                   |   |               |           `-CompoundStmt 0x5556a36d6560 <line:189:2, line:191:2>
      |       |                   |   |               |             `-GotoStmt 0x5556a36d6548 <line:190:2, col:7> 'label_2597' 0x5556a36d12b8
      |       |                   |   |               `-CompoundStmt 0x5556a36d8560 <line:197:2, line:233:2>
      |       |                   |   |                 |-LabelStmt 0x5556a36d66c0 <line:198:2, col:13> 'label_2634'
      |       |                   |   |                 | `-NullStmt 0x5556a36d6668 <col:13>
      |       |                   |   |                 |-LabelStmt 0x5556a36d6730 <line:199:2, col:13> 'label_2661'
      |       |                   |   |                 | `-NullStmt 0x5556a36d66d8 <col:13>
      |       |                   |   |                 `-CompoundStmt 0x5556a36d8528 <line:200:2, line:232:2>
      |       |                   |   |                   |-DeclStmt 0x5556a36d7ac8 <line:201:2, col:14>
      |       |                   |   |                   | `-VarDecl 0x5556a36d7a60 <col:2, col:6> col:6 used __tmp_11 'int'
      |       |                   |   |                   |-BinaryOperator 0x5556a36d7b78 <line:202:2, col:18> 'int' '='
      |       |                   |   |                   | |-DeclRefExpr 0x5556a36d7ae0 <col:2> 'int' lvalue Var 0x5556a36d7a60 '__tmp_11' 'int'
      |       |                   |   |                   | `-BinaryOperator 0x5556a36d7b58 <col:13, col:18> 'int' '<='
      |       |                   |   |                   |   |-IntegerLiteral 0x5556a36d7b00 <col:13> 'int' 0
      |       |                   |   |                   |   `-ImplicitCastExpr 0x5556a36d7b40 <col:18> 'int' <LValueToRValue>
      |       |                   |   |                   |     `-DeclRefExpr 0x5556a36d7b20 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |                   |-DeclStmt 0x5556a36d7c18 <line:203:2, col:29>
      |       |                   |   |                   | `-VarDecl 0x5556a36d7bb0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |                   |   |                   |-BinaryOperator 0x5556a36d7c88 <line:204:2, col:28> 'int' '='
      |       |                   |   |                   | |-DeclRefExpr 0x5556a36d7c30 <col:2> 'int' lvalue Var 0x5556a36d7bb0 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |                   | `-ImplicitCastExpr 0x5556a36d7c70 <col:28> 'int' <LValueToRValue>
      |       |                   |   |                   |   `-DeclRefExpr 0x5556a36d7c50 <col:28> 'int' lvalue Var 0x5556a36d7a60 '__tmp_11' 'int'
      |       |                   |   |                   `-IfStmt 0x5556a36d8500 <line:205:2, line:231:2> has_else
      |       |                   |   |                     |-BinaryOperator 0x5556a36d7d00 <line:205:6, col:33> 'int' '=='
      |       |                   |   |                     | |-ImplicitCastExpr 0x5556a36d7ce8 <col:6> 'int' <LValueToRValue>
      |       |                   |   |                     | | `-DeclRefExpr 0x5556a36d7ca8 <col:6> 'int' lvalue Var 0x5556a36d7bb0 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |                     | `-IntegerLiteral 0x5556a36d7cc8 <col:33> 'int' 0
      |       |                   |   |                     |-CompoundStmt 0x5556a36d7dd8 <line:206:2, line:209:2>
      |       |                   |   |                     | |-CompoundStmt 0x5556a36d7d78 <line:207:2, col:17>
      |       |                   |   |                     | | `-CallExpr 0x5556a36d7d58 <col:3, col:15> 'void'
      |       |                   |   |                     | |   `-ImplicitCastExpr 0x5556a36d7d40 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |                   |   |                     | |     `-DeclRefExpr 0x5556a36d7d20 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |                   |   |                     | `-ReturnStmt 0x5556a36d7dc8 <line:208:2, col:9>
      |       |                   |   |                     |   `-ImplicitCastExpr 0x5556a36d7db0 <col:9> 'int' <LValueToRValue>
      |       |                   |   |                     |     `-DeclRefExpr 0x5556a36d7d90 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |                   |   |                     `-CompoundStmt 0x5556a36d84e8 <line:211:2, line:231:2>
      |       |                   |   |                       `-CompoundStmt 0x5556a36d84b0 <line:212:2, line:230:2>
      |       |                   |   |                         |-DeclStmt 0x5556a36d7e78 <line:213:2, col:14>
      |       |                   |   |                         | `-VarDecl 0x5556a36d7e10 <col:2, col:6> col:6 used __tmp_12 'int'
      |       |                   |   |                         |-BinaryOperator 0x5556a36d7f40 <line:214:2, col:24> 'int' '='
      |       |                   |   |                         | |-DeclRefExpr 0x5556a36d7e90 <col:2> 'int' lvalue Var 0x5556a36d7e10 '__tmp_12' 'int'
      |       |                   |   |                         | `-BinaryOperator 0x5556a36d7f20 <col:13, col:24> 'int' '<='
      |       |                   |   |                         |   |-ImplicitCastExpr 0x5556a36d7ef0 <col:13> 'int' <LValueToRValue>
      |       |                   |   |                         |   | `-DeclRefExpr 0x5556a36d7eb0 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |                         |   `-ImplicitCastExpr 0x5556a36d7f08 <col:24> 'int' <LValueToRValue>
      |       |                   |   |                         |     `-DeclRefExpr 0x5556a36d7ed0 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |       |                   |   |                         |-DeclStmt 0x5556a36d7fe0 <line:215:2, col:29>
      |       |                   |   |                         | `-VarDecl 0x5556a36d7f78 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |                   |   |                         |-BinaryOperator 0x5556a36d8050 <line:216:2, col:28> 'int' '='
      |       |                   |   |                         | |-DeclRefExpr 0x5556a36d7ff8 <col:2> 'int' lvalue Var 0x5556a36d7f78 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |                         | `-ImplicitCastExpr 0x5556a36d8038 <col:28> 'int' <LValueToRValue>
      |       |                   |   |                         |   `-DeclRefExpr 0x5556a36d8018 <col:28> 'int' lvalue Var 0x5556a36d7e10 '__tmp_12' 'int'
      |       |                   |   |                         `-IfStmt 0x5556a36d8488 <line:217:2, line:229:2> has_else
      |       |                   |   |                           |-BinaryOperator 0x5556a36d80c8 <line:217:6, col:33> 'int' '=='
      |       |                   |   |                           | |-ImplicitCastExpr 0x5556a36d80b0 <col:6> 'int' <LValueToRValue>
      |       |                   |   |                           | | `-DeclRefExpr 0x5556a36d8070 <col:6> 'int' lvalue Var 0x5556a36d7f78 '__VERIFIER_assert__cond' 'int'
      |       |                   |   |                           | `-IntegerLiteral 0x5556a36d8090 <col:33> 'int' 0
      |       |                   |   |                           |-CompoundStmt 0x5556a36d81a0 <line:218:2, line:221:2>
      |       |                   |   |                           | |-CompoundStmt 0x5556a36d8140 <line:219:2, col:17>
      |       |                   |   |                           | | `-CallExpr 0x5556a36d8120 <col:3, col:15> 'void'
      |       |                   |   |                           | |   `-ImplicitCastExpr 0x5556a36d8108 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |                   |   |                           | |     `-DeclRefExpr 0x5556a36d80e8 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |                   |   |                           | `-ReturnStmt 0x5556a36d8190 <line:220:2, col:9>
      |       |                   |   |                           |   `-ImplicitCastExpr 0x5556a36d8178 <col:9> 'int' <LValueToRValue>
      |       |                   |   |                           |     `-DeclRefExpr 0x5556a36d8158 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |                   |   |                           `-CompoundStmt 0x5556a36d8450 <line:223:2, line:229:2>
      |       |                   |   |                             |-DeclStmt 0x5556a36d8278 <line:224:2, col:40>
      |       |                   |   |                             | `-VarDecl 0x5556a36d81d8 <col:2, col:33> col:6 main____CPAchecker_TMP_7 'int' cinit
      |       |                   |   |                             |   `-ImplicitCastExpr 0x5556a36d8260 <col:33> 'int' <LValueToRValue>
      |       |                   |   |                             |     `-DeclRefExpr 0x5556a36d8240 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |                             |-BinaryOperator 0x5556a36d8328 <line:225:2, col:22> 'int' '='
      |       |                   |   |                             | |-DeclRefExpr 0x5556a36d8290 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |                             | `-BinaryOperator 0x5556a36d8308 <col:12, col:22> 'int' '+'
      |       |                   |   |                             |   |-ImplicitCastExpr 0x5556a36d82f0 <col:12> 'int' <LValueToRValue>
      |       |                   |   |                             |   | `-DeclRefExpr 0x5556a36d82b0 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                   |   |                             |   `-IntegerLiteral 0x5556a36d82d0 <col:22> 'int' 1
      |       |                   |   |                             |-BinaryOperator 0x5556a36d83a0 <line:226:2, col:17> 'int' '='
      |       |                   |   |                             | |-DeclRefExpr 0x5556a36d8348 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |       |                   |   |                             | `-ImplicitCastExpr 0x5556a36d8388 <col:17> 'int' <LValueToRValue>
      |       |                   |   |                             |   `-DeclRefExpr 0x5556a36d8368 <col:17> 'int' lvalue Var 0x5556a36d1500 'main____CPAchecker_TMP_0' 'int'
      |       |                   |   |                             |-BinaryOperator 0x5556a36d8418 <line:227:2, col:17> 'int' '='
      |       |                   |   |                             | |-DeclRefExpr 0x5556a36d83c0 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |       |                   |   |                             | `-ImplicitCastExpr 0x5556a36d8400 <col:17> 'int' <LValueToRValue>
      |       |                   |   |                             |   `-DeclRefExpr 0x5556a36d83e0 <col:17> 'int' lvalue Var 0x5556a36d1d68 'main____CPAchecker_TMP_2' 'int'
      |       |                   |   |                             `-GotoStmt 0x5556a36d8438 <line:228:2, col:7> 'label_2624' 0x5556a36d1fd0
      |       |                   |   `-CompoundStmt 0x5556a36d86e0 <line:240:2, line:242:2>
      |       |                   |     `-GotoStmt 0x5556a36d86c8 <line:241:2, col:7> 'label_2634' 0x5556a36d6670
      |       |                   `-CompoundStmt 0x5556a36d9230 <line:245:2, line:284:2>
      |       |                     |-DeclStmt 0x5556a36d87c8 <line:246:2, col:30>
      |       |                     | `-VarDecl 0x5556a36d8760 <col:2, col:6> col:6 used main____CPAchecker_TMP_6 'int'
      |       |                     |-BinaryOperator 0x5556a36d8858 <line:247:2, col:51> 'int' '='
      |       |                     | |-DeclRefExpr 0x5556a36d87e0 <col:2> 'int' lvalue Var 0x5556a36d8760 'main____CPAchecker_TMP_6' 'int'
      |       |                     | `-CallExpr 0x5556a36d8838 <col:29, col:51> 'int'
      |       |                     |   `-ImplicitCastExpr 0x5556a36d8820 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |       |                     |     `-DeclRefExpr 0x5556a36d8800 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |       |                     `-IfStmt 0x5556a36d9208 <line:248:2, line:283:2> has_else
      |       |                       |-UnaryOperator 0x5556a36d8910 <line:248:6, col:37> 'int' prefix '!' cannot overflow
      |       |                       | `-ParenExpr 0x5556a36d88f0 <col:7, col:37> 'int'
      |       |                       |   `-BinaryOperator 0x5556a36d88d0 <col:8, col:36> 'int' '=='
      |       |                       |     |-ImplicitCastExpr 0x5556a36d88b8 <col:8> 'int' <LValueToRValue>
      |       |                       |     | `-DeclRefExpr 0x5556a36d8878 <col:8> 'int' lvalue Var 0x5556a36d8760 'main____CPAchecker_TMP_6' 'int'
      |       |                       |     `-IntegerLiteral 0x5556a36d8898 <col:36> 'int' 0
      |       |                       |-CompoundStmt 0x5556a36d91c0 <line:249:2, line:279:2>
      |       |                       | `-CompoundStmt 0x5556a36d9188 <line:250:2, line:278:2>
      |       |                       |   |-DeclStmt 0x5556a36d89a8 <line:251:2, col:14>
      |       |                       |   | `-VarDecl 0x5556a36d8940 <col:2, col:6> col:6 used __tmp_13 'int'
      |       |                       |   |-BinaryOperator 0x5556a36d8a70 <line:252:2, col:18> 'int' '='
      |       |                       |   | |-DeclRefExpr 0x5556a36d89c0 <col:2> 'int' lvalue Var 0x5556a36d8940 '__tmp_13' 'int'
      |       |                       |   | `-BinaryOperator 0x5556a36d8a38 <col:13, col:18> 'int' '<='
      |       |                       |   |   |-IntegerLiteral 0x5556a36d89e0 <col:13> 'int' 0
      |       |                       |   |   `-ImplicitCastExpr 0x5556a36d8a20 <col:18> 'int' <LValueToRValue>
      |       |                       |   |     `-DeclRefExpr 0x5556a36d8a00 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                       |   |-DeclStmt 0x5556a36d8b10 <line:253:2, col:29>
      |       |                       |   | `-VarDecl 0x5556a36d8aa8 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |                       |   |-BinaryOperator 0x5556a36d8b80 <line:254:2, col:28> 'int' '='
      |       |                       |   | |-DeclRefExpr 0x5556a36d8b28 <col:2> 'int' lvalue Var 0x5556a36d8aa8 '__VERIFIER_assert__cond' 'int'
      |       |                       |   | `-ImplicitCastExpr 0x5556a36d8b68 <col:28> 'int' <LValueToRValue>
      |       |                       |   |   `-DeclRefExpr 0x5556a36d8b48 <col:28> 'int' lvalue Var 0x5556a36d8940 '__tmp_13' 'int'
      |       |                       |   `-IfStmt 0x5556a36d9160 <line:255:2, line:277:2> has_else
      |       |                       |     |-BinaryOperator 0x5556a36d8bf8 <line:255:6, col:33> 'int' '=='
      |       |                       |     | |-ImplicitCastExpr 0x5556a36d8be0 <col:6> 'int' <LValueToRValue>
      |       |                       |     | | `-DeclRefExpr 0x5556a36d8ba0 <col:6> 'int' lvalue Var 0x5556a36d8aa8 '__VERIFIER_assert__cond' 'int'
      |       |                       |     | `-IntegerLiteral 0x5556a36d8bc0 <col:33> 'int' 0
      |       |                       |     |-CompoundStmt 0x5556a36d8cd0 <line:256:2, line:259:2>
      |       |                       |     | |-CompoundStmt 0x5556a36d8c70 <line:257:2, col:17>
      |       |                       |     | | `-CallExpr 0x5556a36d8c50 <col:3, col:15> 'void'
      |       |                       |     | |   `-ImplicitCastExpr 0x5556a36d8c38 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |                       |     | |     `-DeclRefExpr 0x5556a36d8c18 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |                       |     | `-ReturnStmt 0x5556a36d8cc0 <line:258:2, col:9>
      |       |                       |     |   `-ImplicitCastExpr 0x5556a36d8ca8 <col:9> 'int' <LValueToRValue>
      |       |                       |     |     `-DeclRefExpr 0x5556a36d8c88 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |                       |     `-CompoundStmt 0x5556a36d9148 <line:261:2, line:277:2>
      |       |                       |       `-CompoundStmt 0x5556a36d9110 <line:262:2, line:276:2>
      |       |                       |         |-DeclStmt 0x5556a36d8d70 <line:263:2, col:14>
      |       |                       |         | `-VarDecl 0x5556a36d8d08 <col:2, col:6> col:6 used __tmp_14 'int'
      |       |                       |         |-BinaryOperator 0x5556a36d8e38 <line:264:2, col:24> 'int' '='
      |       |                       |         | |-DeclRefExpr 0x5556a36d8d88 <col:2> 'int' lvalue Var 0x5556a36d8d08 '__tmp_14' 'int'
      |       |                       |         | `-BinaryOperator 0x5556a36d8e18 <col:13, col:24> 'int' '<='
      |       |                       |         |   |-ImplicitCastExpr 0x5556a36d8de8 <col:13> 'int' <LValueToRValue>
      |       |                       |         |   | `-DeclRefExpr 0x5556a36d8da8 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |       |                       |         |   `-ImplicitCastExpr 0x5556a36d8e00 <col:24> 'int' <LValueToRValue>
      |       |                       |         |     `-DeclRefExpr 0x5556a36d8dc8 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |       |                       |         |-DeclStmt 0x5556a36d8ed8 <line:265:2, col:29>
      |       |                       |         | `-VarDecl 0x5556a36d8e70 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |       |                       |         |-BinaryOperator 0x5556a36d8f48 <line:266:2, col:28> 'int' '='
      |       |                       |         | |-DeclRefExpr 0x5556a36d8ef0 <col:2> 'int' lvalue Var 0x5556a36d8e70 '__VERIFIER_assert__cond' 'int'
      |       |                       |         | `-ImplicitCastExpr 0x5556a36d8f30 <col:28> 'int' <LValueToRValue>
      |       |                       |         |   `-DeclRefExpr 0x5556a36d8f10 <col:28> 'int' lvalue Var 0x5556a36d8d08 '__tmp_14' 'int'
      |       |                       |         `-IfStmt 0x5556a36d90e8 <line:267:2, line:275:2> has_else
      |       |                       |           |-BinaryOperator 0x5556a36d8fc0 <line:267:6, col:33> 'int' '=='
      |       |                       |           | |-ImplicitCastExpr 0x5556a36d8fa8 <col:6> 'int' <LValueToRValue>
      |       |                       |           | | `-DeclRefExpr 0x5556a36d8f68 <col:6> 'int' lvalue Var 0x5556a36d8e70 '__VERIFIER_assert__cond' 'int'
      |       |                       |           | `-IntegerLiteral 0x5556a36d8f88 <col:33> 'int' 0
      |       |                       |           |-CompoundStmt 0x5556a36d9098 <line:268:2, line:271:2>
      |       |                       |           | |-CompoundStmt 0x5556a36d9038 <line:269:2, col:17>
      |       |                       |           | | `-CallExpr 0x5556a36d9018 <col:3, col:15> 'void'
      |       |                       |           | |   `-ImplicitCastExpr 0x5556a36d9000 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |       |                       |           | |     `-DeclRefExpr 0x5556a36d8fe0 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |       |                       |           | `-ReturnStmt 0x5556a36d9088 <line:270:2, col:9>
      |       |                       |           |   `-ImplicitCastExpr 0x5556a36d9070 <col:9> 'int' <LValueToRValue>
      |       |                       |           |     `-DeclRefExpr 0x5556a36d9050 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |       |                       |           `-CompoundStmt 0x5556a36d90d0 <line:273:2, line:275:2>
      |       |                       |             `-GotoStmt 0x5556a36d90b8 <line:274:2, col:7> 'label_2597' 0x5556a36d12b8
      |       |                       `-CompoundStmt 0x5556a36d91f0 <line:281:2, line:283:2>
      |       |                         `-GotoStmt 0x5556a36d91d8 <line:282:2, col:7> 'label_2661' 0x5556a36d66e0
      |       `-CompoundStmt 0x5556a36dff30 <line:292:2, line:999:2>
      |         `-CompoundStmt 0x5556a36dfef8 <line:293:2, line:998:2>
      |           |-DeclStmt 0x5556a36d9490 <line:294:2, col:14>
      |           | `-VarDecl 0x5556a36d9428 <col:2, col:6> col:6 used __tmp_15 'int'
      |           |-BinaryOperator 0x5556a36d9540 <line:295:2, col:18> 'int' '='
      |           | |-DeclRefExpr 0x5556a36d94a8 <col:2> 'int' lvalue Var 0x5556a36d9428 '__tmp_15' 'int'
      |           | `-BinaryOperator 0x5556a36d9520 <col:13, col:18> 'int' '<='
      |           |   |-IntegerLiteral 0x5556a36d94c8 <col:13> 'int' 0
      |           |   `-ImplicitCastExpr 0x5556a36d9508 <col:18> 'int' <LValueToRValue>
      |           |     `-DeclRefExpr 0x5556a36d94e8 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |           |-DeclStmt 0x5556a36d95e0 <line:296:2, col:29>
      |           | `-VarDecl 0x5556a36d9578 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |           |-BinaryOperator 0x5556a36d9650 <line:297:2, col:28> 'int' '='
      |           | |-DeclRefExpr 0x5556a36d95f8 <col:2> 'int' lvalue Var 0x5556a36d9578 '__VERIFIER_assert__cond' 'int'
      |           | `-ImplicitCastExpr 0x5556a36d9638 <col:28> 'int' <LValueToRValue>
      |           |   `-DeclRefExpr 0x5556a36d9618 <col:28> 'int' lvalue Var 0x5556a36d9428 '__tmp_15' 'int'
      |           `-IfStmt 0x5556a36dfed0 <line:298:2, line:997:2> has_else
      |             |-BinaryOperator 0x5556a36d96c8 <line:298:6, col:33> 'int' '=='
      |             | |-ImplicitCastExpr 0x5556a36d96b0 <col:6> 'int' <LValueToRValue>
      |             | | `-DeclRefExpr 0x5556a36d9670 <col:6> 'int' lvalue Var 0x5556a36d9578 '__VERIFIER_assert__cond' 'int'
      |             | `-IntegerLiteral 0x5556a36d9690 <col:33> 'int' 0
      |             |-CompoundStmt 0x5556a36d9730 <line:299:2, line:301:2>
      |             | `-ReturnStmt 0x5556a36d9720 <line:300:2, col:9>
      |             |   `-ImplicitCastExpr 0x5556a36d9708 <col:9> 'int' <LValueToRValue>
      |             |     `-DeclRefExpr 0x5556a36d96e8 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |             `-CompoundStmt 0x5556a36dfeb8 <line:303:2, line:997:2>
      |               `-CompoundStmt 0x5556a36dfe80 <line:304:2, line:996:2>
      |                 |-DeclStmt 0x5556a36d97c8 <line:305:2, col:14>
      |                 | `-VarDecl 0x5556a36d9760 <col:2, col:6> col:6 used __tmp_16 'int'
      |                 |-BinaryOperator 0x5556a36d9890 <line:306:2, col:24> 'int' '='
      |                 | |-DeclRefExpr 0x5556a36d97e0 <col:2> 'int' lvalue Var 0x5556a36d9760 '__tmp_16' 'int'
      |                 | `-BinaryOperator 0x5556a36d9870 <col:13, col:24> 'int' '<='
      |                 |   |-ImplicitCastExpr 0x5556a36d9840 <col:13> 'int' <LValueToRValue>
      |                 |   | `-DeclRefExpr 0x5556a36d9800 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                 |   `-ImplicitCastExpr 0x5556a36d9858 <col:24> 'int' <LValueToRValue>
      |                 |     `-DeclRefExpr 0x5556a36d9820 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                 |-DeclStmt 0x5556a36d9930 <line:307:2, col:29>
      |                 | `-VarDecl 0x5556a36d98c8 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                 |-BinaryOperator 0x5556a36d99a0 <line:308:2, col:28> 'int' '='
      |                 | |-DeclRefExpr 0x5556a36d9948 <col:2> 'int' lvalue Var 0x5556a36d98c8 '__VERIFIER_assert__cond' 'int'
      |                 | `-ImplicitCastExpr 0x5556a36d9988 <col:28> 'int' <LValueToRValue>
      |                 |   `-DeclRefExpr 0x5556a36d9968 <col:28> 'int' lvalue Var 0x5556a36d9760 '__tmp_16' 'int'
      |                 `-IfStmt 0x5556a36dfe58 <line:309:2, line:995:2> has_else
      |                   |-BinaryOperator 0x5556a36d9a18 <line:309:6, col:33> 'int' '=='
      |                   | |-ImplicitCastExpr 0x5556a36d9a00 <col:6> 'int' <LValueToRValue>
      |                   | | `-DeclRefExpr 0x5556a36d99c0 <col:6> 'int' lvalue Var 0x5556a36d98c8 '__VERIFIER_assert__cond' 'int'
      |                   | `-IntegerLiteral 0x5556a36d99e0 <col:33> 'int' 0
      |                   |-CompoundStmt 0x5556a36d9a90 <line:310:2, line:312:2>
      |                   | `-ReturnStmt 0x5556a36d9a80 <line:311:2, col:9>
      |                   |   `-ImplicitCastExpr 0x5556a36d9a58 <col:9> 'int' <LValueToRValue>
      |                   |     `-DeclRefExpr 0x5556a36d9a38 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                   `-CompoundStmt 0x5556a36dfe30 <line:314:2, line:995:2>
      |                     |-DeclStmt 0x5556a36d9b60 <line:315:2, col:40>
      |                     | `-VarDecl 0x5556a36d9ac0 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
      |                     |   `-ImplicitCastExpr 0x5556a36d9b48 <col:33> 'int' <LValueToRValue>
      |                     |     `-DeclRefExpr 0x5556a36d9b28 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                     |-BinaryOperator 0x5556a36d9c10 <line:316:2, col:22> 'int' '='
      |                     | |-DeclRefExpr 0x5556a36d9b78 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                     | `-BinaryOperator 0x5556a36d9bf0 <col:12, col:22> 'int' '+'
      |                     |   |-ImplicitCastExpr 0x5556a36d9bd8 <col:12> 'int' <LValueToRValue>
      |                     |   | `-DeclRefExpr 0x5556a36d9b98 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                     |   `-IntegerLiteral 0x5556a36d9bb8 <col:22> 'int' 1
      |                     `-IfStmt 0x5556a36dfe08 <line:317:2, line:994:2> has_else
      |                       |-BinaryOperator 0x5556a36d9ca0 <line:317:6, col:17> 'int' '=='
      |                       | |-ImplicitCastExpr 0x5556a36d9c70 <col:6> 'int' <LValueToRValue>
      |                       | | `-DeclRefExpr 0x5556a36d9c30 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                       | `-ImplicitCastExpr 0x5556a36d9c88 <col:17> 'int' <LValueToRValue>
      |                       |   `-DeclRefExpr 0x5556a36d9c50 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                       |-CompoundStmt 0x5556a36d9cd8 <line:318:2, line:320:2>
      |                       | `-GotoStmt 0x5556a36d9cc0 <line:319:2, col:7> 'label_2604' 0x5556a36cc568
      |                       `-CompoundStmt 0x5556a36dfde0 <line:322:2, line:994:2>
      |                         |-DeclStmt 0x5556a36d9d70 <line:323:2, col:30>
      |                         | `-VarDecl 0x5556a36d9d08 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                         |-BinaryOperator 0x5556a36d9e00 <line:324:2, col:51> 'int' '='
      |                         | |-DeclRefExpr 0x5556a36d9d88 <col:2> 'int' lvalue Var 0x5556a36d9d08 'main____CPAchecker_TMP_0' 'int'
      |                         | `-CallExpr 0x5556a36d9de0 <col:29, col:51> 'int'
      |                         |   `-ImplicitCastExpr 0x5556a36d9dc8 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                         |     `-DeclRefExpr 0x5556a36d9da8 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                         `-IfStmt 0x5556a36dfdb8 <line:325:2, line:993:2> has_else
      |                           |-UnaryOperator 0x5556a36d9eb8 <line:325:6, col:37> 'int' prefix '!' cannot overflow
      |                           | `-ParenExpr 0x5556a36d9e98 <col:7, col:37> 'int'
      |                           |   `-BinaryOperator 0x5556a36d9e78 <col:8, col:36> 'int' '=='
      |                           |     |-ImplicitCastExpr 0x5556a36d9e60 <col:8> 'int' <LValueToRValue>
      |                           |     | `-DeclRefExpr 0x5556a36d9e20 <col:8> 'int' lvalue Var 0x5556a36d9d08 'main____CPAchecker_TMP_0' 'int'
      |                           |     `-IntegerLiteral 0x5556a36d9e40 <col:36> 'int' 0
      |                           |-CompoundStmt 0x5556a36da8f8 <line:326:2, line:358:2>
      |                           | `-CompoundStmt 0x5556a36da8c0 <line:327:2, line:357:2>
      |                           |   |-DeclStmt 0x5556a36d9f50 <line:328:2, col:14>
      |                           |   | `-VarDecl 0x5556a36d9ee8 <col:2, col:6> col:6 used __tmp_17 'int'
      |                           |   |-BinaryOperator 0x5556a36da000 <line:329:2, col:18> 'int' '='
      |                           |   | |-DeclRefExpr 0x5556a36d9f68 <col:2> 'int' lvalue Var 0x5556a36d9ee8 '__tmp_17' 'int'
      |                           |   | `-BinaryOperator 0x5556a36d9fe0 <col:13, col:18> 'int' '<='
      |                           |   |   |-IntegerLiteral 0x5556a36d9f88 <col:13> 'int' 0
      |                           |   |   `-ImplicitCastExpr 0x5556a36d9fc8 <col:18> 'int' <LValueToRValue>
      |                           |   |     `-DeclRefExpr 0x5556a36d9fa8 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                           |   |-DeclStmt 0x5556a36da0a0 <line:330:2, col:29>
      |                           |   | `-VarDecl 0x5556a36da038 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                           |   |-BinaryOperator 0x5556a36da110 <line:331:2, col:28> 'int' '='
      |                           |   | |-DeclRefExpr 0x5556a36da0b8 <col:2> 'int' lvalue Var 0x5556a36da038 '__VERIFIER_assert__cond' 'int'
      |                           |   | `-ImplicitCastExpr 0x5556a36da0f8 <col:28> 'int' <LValueToRValue>
      |                           |   |   `-DeclRefExpr 0x5556a36da0d8 <col:28> 'int' lvalue Var 0x5556a36d9ee8 '__tmp_17' 'int'
      |                           |   `-IfStmt 0x5556a36da898 <line:332:2, line:356:2> has_else
      |                           |     |-BinaryOperator 0x5556a36da188 <line:332:6, col:33> 'int' '=='
      |                           |     | |-ImplicitCastExpr 0x5556a36da170 <col:6> 'int' <LValueToRValue>
      |                           |     | | `-DeclRefExpr 0x5556a36da130 <col:6> 'int' lvalue Var 0x5556a36da038 '__VERIFIER_assert__cond' 'int'
      |                           |     | `-IntegerLiteral 0x5556a36da150 <col:33> 'int' 0
      |                           |     |-CompoundStmt 0x5556a36da1f0 <line:333:2, line:335:2>
      |                           |     | `-ReturnStmt 0x5556a36da1e0 <line:334:2, col:9>
      |                           |     |   `-ImplicitCastExpr 0x5556a36da1c8 <col:9> 'int' <LValueToRValue>
      |                           |     |     `-DeclRefExpr 0x5556a36da1a8 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                           |     `-CompoundStmt 0x5556a36da880 <line:337:2, line:356:2>
      |                           |       `-CompoundStmt 0x5556a36da848 <line:338:2, line:355:2>
      |                           |         |-DeclStmt 0x5556a36da288 <line:339:2, col:14>
      |                           |         | `-VarDecl 0x5556a36da220 <col:2, col:6> col:6 used __tmp_18 'int'
      |                           |         |-BinaryOperator 0x5556a36da350 <line:340:2, col:24> 'int' '='
      |                           |         | |-DeclRefExpr 0x5556a36da2a0 <col:2> 'int' lvalue Var 0x5556a36da220 '__tmp_18' 'int'
      |                           |         | `-BinaryOperator 0x5556a36da330 <col:13, col:24> 'int' '<='
      |                           |         |   |-ImplicitCastExpr 0x5556a36da300 <col:13> 'int' <LValueToRValue>
      |                           |         |   | `-DeclRefExpr 0x5556a36da2c0 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                           |         |   `-ImplicitCastExpr 0x5556a36da318 <col:24> 'int' <LValueToRValue>
      |                           |         |     `-DeclRefExpr 0x5556a36da2e0 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                           |         |-DeclStmt 0x5556a36da3f0 <line:341:2, col:29>
      |                           |         | `-VarDecl 0x5556a36da388 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                           |         |-BinaryOperator 0x5556a36da460 <line:342:2, col:28> 'int' '='
      |                           |         | |-DeclRefExpr 0x5556a36da408 <col:2> 'int' lvalue Var 0x5556a36da388 '__VERIFIER_assert__cond' 'int'
      |                           |         | `-ImplicitCastExpr 0x5556a36da448 <col:28> 'int' <LValueToRValue>
      |                           |         |   `-DeclRefExpr 0x5556a36da428 <col:28> 'int' lvalue Var 0x5556a36da220 '__tmp_18' 'int'
      |                           |         `-IfStmt 0x5556a36da820 <line:343:2, line:354:2> has_else
      |                           |           |-BinaryOperator 0x5556a36da4d8 <line:343:6, col:33> 'int' '=='
      |                           |           | |-ImplicitCastExpr 0x5556a36da4c0 <col:6> 'int' <LValueToRValue>
      |                           |           | | `-DeclRefExpr 0x5556a36da480 <col:6> 'int' lvalue Var 0x5556a36da388 '__VERIFIER_assert__cond' 'int'
      |                           |           | `-IntegerLiteral 0x5556a36da4a0 <col:33> 'int' 0
      |                           |           |-CompoundStmt 0x5556a36da540 <line:344:2, line:346:2>
      |                           |           | `-ReturnStmt 0x5556a36da530 <line:345:2, col:9>
      |                           |           |   `-ImplicitCastExpr 0x5556a36da518 <col:9> 'int' <LValueToRValue>
      |                           |           |     `-DeclRefExpr 0x5556a36da4f8 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                           |           `-CompoundStmt 0x5556a36da7e8 <line:348:2, line:354:2>
      |                           |             |-DeclStmt 0x5556a36da610 <line:349:2, col:40>
      |                           |             | `-VarDecl 0x5556a36da570 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                           |             |   `-ImplicitCastExpr 0x5556a36da5f8 <col:33> 'int' <LValueToRValue>
      |                           |             |     `-DeclRefExpr 0x5556a36da5d8 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                           |             |-BinaryOperator 0x5556a36da6c0 <line:350:2, col:22> 'int' '='
      |                           |             | |-DeclRefExpr 0x5556a36da628 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                           |             | `-BinaryOperator 0x5556a36da6a0 <col:12, col:22> 'int' '+'
      |                           |             |   |-ImplicitCastExpr 0x5556a36da688 <col:12> 'int' <LValueToRValue>
      |                           |             |   | `-DeclRefExpr 0x5556a36da648 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                           |             |   `-IntegerLiteral 0x5556a36da668 <col:22> 'int' 1
      |                           |             |-BinaryOperator 0x5556a36da738 <line:351:2, col:17> 'int' '='
      |                           |             | |-DeclRefExpr 0x5556a36da6e0 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                           |             | `-ImplicitCastExpr 0x5556a36da720 <col:17> 'int' <LValueToRValue>
      |                           |             |   `-DeclRefExpr 0x5556a36da700 <col:17> 'int' lvalue Var 0x5556a36d9d08 'main____CPAchecker_TMP_0' 'int'
      |                           |             |-BinaryOperator 0x5556a36da7b0 <line:352:2, col:17> 'int' '='
      |                           |             | |-DeclRefExpr 0x5556a36da758 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                           |             | `-ImplicitCastExpr 0x5556a36da798 <col:17> 'int' <LValueToRValue>
      |                           |             |   `-DeclRefExpr 0x5556a36da778 <col:17> 'int' lvalue Var 0x5556a36da570 'main____CPAchecker_TMP_2' 'int'
      |                           |             `-GotoStmt 0x5556a36da7d0 <line:353:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                           `-CompoundStmt 0x5556a36dfda0 <line:360:2, line:993:2>
      |                             `-CompoundStmt 0x5556a36dfd68 <line:361:2, line:992:2>
      |                               |-DeclStmt 0x5556a36da990 <line:362:2, col:14>
      |                               | `-VarDecl 0x5556a36da928 <col:2, col:6> col:6 used __tmp_19 'int'
      |                               |-BinaryOperator 0x5556a36daa40 <line:363:2, col:18> 'int' '='
      |                               | |-DeclRefExpr 0x5556a36da9a8 <col:2> 'int' lvalue Var 0x5556a36da928 '__tmp_19' 'int'
      |                               | `-BinaryOperator 0x5556a36daa20 <col:13, col:18> 'int' '<='
      |                               |   |-IntegerLiteral 0x5556a36da9c8 <col:13> 'int' 0
      |                               |   `-ImplicitCastExpr 0x5556a36daa08 <col:18> 'int' <LValueToRValue>
      |                               |     `-DeclRefExpr 0x5556a36da9e8 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                               |-DeclStmt 0x5556a36daaf8 <line:364:2, col:29>
      |                               | `-VarDecl 0x5556a36daa90 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                               |-BinaryOperator 0x5556a36dab68 <line:365:2, col:28> 'int' '='
      |                               | |-DeclRefExpr 0x5556a36dab10 <col:2> 'int' lvalue Var 0x5556a36daa90 '__VERIFIER_assert__cond' 'int'
      |                               | `-ImplicitCastExpr 0x5556a36dab50 <col:28> 'int' <LValueToRValue>
      |                               |   `-DeclRefExpr 0x5556a36dab30 <col:28> 'int' lvalue Var 0x5556a36da928 '__tmp_19' 'int'
      |                               `-IfStmt 0x5556a36dfd40 <line:366:2, line:991:2> has_else
      |                                 |-BinaryOperator 0x5556a36dabe0 <line:366:6, col:33> 'int' '=='
      |                                 | |-ImplicitCastExpr 0x5556a36dabc8 <col:6> 'int' <LValueToRValue>
      |                                 | | `-DeclRefExpr 0x5556a36dab88 <col:6> 'int' lvalue Var 0x5556a36daa90 '__VERIFIER_assert__cond' 'int'
      |                                 | `-IntegerLiteral 0x5556a36daba8 <col:33> 'int' 0
      |                                 |-CompoundStmt 0x5556a36dac48 <line:367:2, line:369:2>
      |                                 | `-ReturnStmt 0x5556a36dac38 <line:368:2, col:9>
      |                                 |   `-ImplicitCastExpr 0x5556a36dac20 <col:9> 'int' <LValueToRValue>
      |                                 |     `-DeclRefExpr 0x5556a36dac00 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                 `-CompoundStmt 0x5556a36dfd28 <line:371:2, line:991:2>
      |                                   `-CompoundStmt 0x5556a36dfcf0 <line:372:2, line:990:2>
      |                                     |-DeclStmt 0x5556a36dace0 <line:373:2, col:14>
      |                                     | `-VarDecl 0x5556a36dac78 <col:2, col:6> col:6 used __tmp_20 'int'
      |                                     |-BinaryOperator 0x5556a36dada8 <line:374:2, col:24> 'int' '='
      |                                     | |-DeclRefExpr 0x5556a36dacf8 <col:2> 'int' lvalue Var 0x5556a36dac78 '__tmp_20' 'int'
      |                                     | `-BinaryOperator 0x5556a36dad88 <col:13, col:24> 'int' '<='
      |                                     |   |-ImplicitCastExpr 0x5556a36dad58 <col:13> 'int' <LValueToRValue>
      |                                     |   | `-DeclRefExpr 0x5556a36dad18 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                     |   `-ImplicitCastExpr 0x5556a36dad70 <col:24> 'int' <LValueToRValue>
      |                                     |     `-DeclRefExpr 0x5556a36dad38 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                     |-DeclStmt 0x5556a36dae48 <line:375:2, col:29>
      |                                     | `-VarDecl 0x5556a36dade0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                     |-BinaryOperator 0x5556a36daeb8 <line:376:2, col:28> 'int' '='
      |                                     | |-DeclRefExpr 0x5556a36dae60 <col:2> 'int' lvalue Var 0x5556a36dade0 '__VERIFIER_assert__cond' 'int'
      |                                     | `-ImplicitCastExpr 0x5556a36daea0 <col:28> 'int' <LValueToRValue>
      |                                     |   `-DeclRefExpr 0x5556a36dae80 <col:28> 'int' lvalue Var 0x5556a36dac78 '__tmp_20' 'int'
      |                                     `-IfStmt 0x5556a36dfcc8 <line:377:2, line:989:2> has_else
      |                                       |-BinaryOperator 0x5556a36daf30 <line:377:6, col:33> 'int' '=='
      |                                       | |-ImplicitCastExpr 0x5556a36daf18 <col:6> 'int' <LValueToRValue>
      |                                       | | `-DeclRefExpr 0x5556a36daed8 <col:6> 'int' lvalue Var 0x5556a36dade0 '__VERIFIER_assert__cond' 'int'
      |                                       | `-IntegerLiteral 0x5556a36daef8 <col:33> 'int' 0
      |                                       |-CompoundStmt 0x5556a36daf98 <line:378:2, line:380:2>
      |                                       | `-ReturnStmt 0x5556a36daf88 <line:379:2, col:9>
      |                                       |   `-ImplicitCastExpr 0x5556a36daf70 <col:9> 'int' <LValueToRValue>
      |                                       |     `-DeclRefExpr 0x5556a36daf50 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                       `-CompoundStmt 0x5556a36dfca0 <line:382:2, line:989:2>
      |                                         |-DeclStmt 0x5556a36db068 <line:383:2, col:40>
      |                                         | `-VarDecl 0x5556a36dafc8 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
      |                                         |   `-ImplicitCastExpr 0x5556a36db050 <col:33> 'int' <LValueToRValue>
      |                                         |     `-DeclRefExpr 0x5556a36db030 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                         |-BinaryOperator 0x5556a36db118 <line:384:2, col:22> 'int' '='
      |                                         | |-DeclRefExpr 0x5556a36db080 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                         | `-BinaryOperator 0x5556a36db0f8 <col:12, col:22> 'int' '+'
      |                                         |   |-ImplicitCastExpr 0x5556a36db0e0 <col:12> 'int' <LValueToRValue>
      |                                         |   | `-DeclRefExpr 0x5556a36db0a0 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                         |   `-IntegerLiteral 0x5556a36db0c0 <col:22> 'int' 1
      |                                         `-IfStmt 0x5556a36dfc78 <line:385:2, line:988:2> has_else
      |                                           |-BinaryOperator 0x5556a36db1a8 <line:385:6, col:17> 'int' '=='
      |                                           | |-ImplicitCastExpr 0x5556a36db178 <col:6> 'int' <LValueToRValue>
      |                                           | | `-DeclRefExpr 0x5556a36db138 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                           | `-ImplicitCastExpr 0x5556a36db190 <col:17> 'int' <LValueToRValue>
      |                                           |   `-DeclRefExpr 0x5556a36db158 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                           |-CompoundStmt 0x5556a36db1e0 <line:386:2, line:388:2>
      |                                           | `-GotoStmt 0x5556a36db1c8 <line:387:2, col:7> 'label_2604' 0x5556a36cc568
      |                                           `-CompoundStmt 0x5556a36dfc50 <line:390:2, line:988:2>
      |                                             |-DeclStmt 0x5556a36db278 <line:391:2, col:30>
      |                                             | `-VarDecl 0x5556a36db210 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                                             |-BinaryOperator 0x5556a36db308 <line:392:2, col:51> 'int' '='
      |                                             | |-DeclRefExpr 0x5556a36db290 <col:2> 'int' lvalue Var 0x5556a36db210 'main____CPAchecker_TMP_0' 'int'
      |                                             | `-CallExpr 0x5556a36db2e8 <col:29, col:51> 'int'
      |                                             |   `-ImplicitCastExpr 0x5556a36db2d0 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                                             |     `-DeclRefExpr 0x5556a36db2b0 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                                             `-IfStmt 0x5556a36dfc28 <line:393:2, line:987:2> has_else
      |                                               |-UnaryOperator 0x5556a36db3c0 <line:393:6, col:37> 'int' prefix '!' cannot overflow
      |                                               | `-ParenExpr 0x5556a36db3a0 <col:7, col:37> 'int'
      |                                               |   `-BinaryOperator 0x5556a36db380 <col:8, col:36> 'int' '=='
      |                                               |     |-ImplicitCastExpr 0x5556a36db368 <col:8> 'int' <LValueToRValue>
      |                                               |     | `-DeclRefExpr 0x5556a36db328 <col:8> 'int' lvalue Var 0x5556a36db210 'main____CPAchecker_TMP_0' 'int'
      |                                               |     `-IntegerLiteral 0x5556a36db348 <col:36> 'int' 0
      |                                               |-CompoundStmt 0x5556a36dbe28 <line:394:2, line:426:2>
      |                                               | `-CompoundStmt 0x5556a36dbdf0 <line:395:2, line:425:2>
      |                                               |   |-DeclStmt 0x5556a36db458 <line:396:2, col:14>
      |                                               |   | `-VarDecl 0x5556a36db3f0 <col:2, col:6> col:6 used __tmp_21 'int'
      |                                               |   |-BinaryOperator 0x5556a36db508 <line:397:2, col:18> 'int' '='
      |                                               |   | |-DeclRefExpr 0x5556a36db470 <col:2> 'int' lvalue Var 0x5556a36db3f0 '__tmp_21' 'int'
      |                                               |   | `-BinaryOperator 0x5556a36db4e8 <col:13, col:18> 'int' '<='
      |                                               |   |   |-IntegerLiteral 0x5556a36db490 <col:13> 'int' 0
      |                                               |   |   `-ImplicitCastExpr 0x5556a36db4d0 <col:18> 'int' <LValueToRValue>
      |                                               |   |     `-DeclRefExpr 0x5556a36db4b0 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                               |   |-DeclStmt 0x5556a36db5a8 <line:398:2, col:29>
      |                                               |   | `-VarDecl 0x5556a36db540 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                               |   |-BinaryOperator 0x5556a36db618 <line:399:2, col:28> 'int' '='
      |                                               |   | |-DeclRefExpr 0x5556a36db5c0 <col:2> 'int' lvalue Var 0x5556a36db540 '__VERIFIER_assert__cond' 'int'
      |                                               |   | `-ImplicitCastExpr 0x5556a36db600 <col:28> 'int' <LValueToRValue>
      |                                               |   |   `-DeclRefExpr 0x5556a36db5e0 <col:28> 'int' lvalue Var 0x5556a36db3f0 '__tmp_21' 'int'
      |                                               |   `-IfStmt 0x5556a36dbdc8 <line:400:2, line:424:2> has_else
      |                                               |     |-BinaryOperator 0x5556a36db690 <line:400:6, col:33> 'int' '=='
      |                                               |     | |-ImplicitCastExpr 0x5556a36db678 <col:6> 'int' <LValueToRValue>
      |                                               |     | | `-DeclRefExpr 0x5556a36db638 <col:6> 'int' lvalue Var 0x5556a36db540 '__VERIFIER_assert__cond' 'int'
      |                                               |     | `-IntegerLiteral 0x5556a36db658 <col:33> 'int' 0
      |                                               |     |-CompoundStmt 0x5556a36db6f8 <line:401:2, line:403:2>
      |                                               |     | `-ReturnStmt 0x5556a36db6e8 <line:402:2, col:9>
      |                                               |     |   `-ImplicitCastExpr 0x5556a36db6d0 <col:9> 'int' <LValueToRValue>
      |                                               |     |     `-DeclRefExpr 0x5556a36db6b0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                               |     `-CompoundStmt 0x5556a36dbdb0 <line:405:2, line:424:2>
      |                                               |       `-CompoundStmt 0x5556a36dbd78 <line:406:2, line:423:2>
      |                                               |         |-DeclStmt 0x5556a36db790 <line:407:2, col:14>
      |                                               |         | `-VarDecl 0x5556a36db728 <col:2, col:6> col:6 used __tmp_22 'int'
      |                                               |         |-BinaryOperator 0x5556a36db858 <line:408:2, col:24> 'int' '='
      |                                               |         | |-DeclRefExpr 0x5556a36db7a8 <col:2> 'int' lvalue Var 0x5556a36db728 '__tmp_22' 'int'
      |                                               |         | `-BinaryOperator 0x5556a36db838 <col:13, col:24> 'int' '<='
      |                                               |         |   |-ImplicitCastExpr 0x5556a36db808 <col:13> 'int' <LValueToRValue>
      |                                               |         |   | `-DeclRefExpr 0x5556a36db7c8 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                               |         |   `-ImplicitCastExpr 0x5556a36db820 <col:24> 'int' <LValueToRValue>
      |                                               |         |     `-DeclRefExpr 0x5556a36db7e8 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                               |         |-DeclStmt 0x5556a36db8f8 <line:409:2, col:29>
      |                                               |         | `-VarDecl 0x5556a36db890 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                               |         |-BinaryOperator 0x5556a36db968 <line:410:2, col:28> 'int' '='
      |                                               |         | |-DeclRefExpr 0x5556a36db910 <col:2> 'int' lvalue Var 0x5556a36db890 '__VERIFIER_assert__cond' 'int'
      |                                               |         | `-ImplicitCastExpr 0x5556a36db950 <col:28> 'int' <LValueToRValue>
      |                                               |         |   `-DeclRefExpr 0x5556a36db930 <col:28> 'int' lvalue Var 0x5556a36db728 '__tmp_22' 'int'
      |                                               |         `-IfStmt 0x5556a36dbd50 <line:411:2, line:422:2> has_else
      |                                               |           |-BinaryOperator 0x5556a36db9e0 <line:411:6, col:33> 'int' '=='
      |                                               |           | |-ImplicitCastExpr 0x5556a36db9c8 <col:6> 'int' <LValueToRValue>
      |                                               |           | | `-DeclRefExpr 0x5556a36db988 <col:6> 'int' lvalue Var 0x5556a36db890 '__VERIFIER_assert__cond' 'int'
      |                                               |           | `-IntegerLiteral 0x5556a36db9a8 <col:33> 'int' 0
      |                                               |           |-CompoundStmt 0x5556a36dba48 <line:412:2, line:414:2>
      |                                               |           | `-ReturnStmt 0x5556a36dba38 <line:413:2, col:9>
      |                                               |           |   `-ImplicitCastExpr 0x5556a36dba20 <col:9> 'int' <LValueToRValue>
      |                                               |           |     `-DeclRefExpr 0x5556a36dba00 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                               |           `-CompoundStmt 0x5556a36dbd18 <line:416:2, line:422:2>
      |                                               |             |-DeclStmt 0x5556a36dbb40 <line:417:2, col:40>
      |                                               |             | `-VarDecl 0x5556a36dbaa0 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                                               |             |   `-ImplicitCastExpr 0x5556a36dbb28 <col:33> 'int' <LValueToRValue>
      |                                               |             |     `-DeclRefExpr 0x5556a36dbb08 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                               |             |-BinaryOperator 0x5556a36dbbf0 <line:418:2, col:22> 'int' '='
      |                                               |             | |-DeclRefExpr 0x5556a36dbb58 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                               |             | `-BinaryOperator 0x5556a36dbbd0 <col:12, col:22> 'int' '+'
      |                                               |             |   |-ImplicitCastExpr 0x5556a36dbbb8 <col:12> 'int' <LValueToRValue>
      |                                               |             |   | `-DeclRefExpr 0x5556a36dbb78 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                               |             |   `-IntegerLiteral 0x5556a36dbb98 <col:22> 'int' 1
      |                                               |             |-BinaryOperator 0x5556a36dbc68 <line:419:2, col:17> 'int' '='
      |                                               |             | |-DeclRefExpr 0x5556a36dbc10 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                                               |             | `-ImplicitCastExpr 0x5556a36dbc50 <col:17> 'int' <LValueToRValue>
      |                                               |             |   `-DeclRefExpr 0x5556a36dbc30 <col:17> 'int' lvalue Var 0x5556a36db210 'main____CPAchecker_TMP_0' 'int'
      |                                               |             |-BinaryOperator 0x5556a36dbce0 <line:420:2, col:17> 'int' '='
      |                                               |             | |-DeclRefExpr 0x5556a36dbc88 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                                               |             | `-ImplicitCastExpr 0x5556a36dbcc8 <col:17> 'int' <LValueToRValue>
      |                                               |             |   `-DeclRefExpr 0x5556a36dbca8 <col:17> 'int' lvalue Var 0x5556a36dbaa0 'main____CPAchecker_TMP_2' 'int'
      |                                               |             `-GotoStmt 0x5556a36dbd00 <line:421:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                                               `-CompoundStmt 0x5556a36dfc10 <line:428:2, line:987:2>
      |                                                 `-CompoundStmt 0x5556a36dfbd8 <line:429:2, line:986:2>
      |                                                   |-DeclStmt 0x5556a36dbec0 <line:430:2, col:14>
      |                                                   | `-VarDecl 0x5556a36dbe58 <col:2, col:6> col:6 used __tmp_23 'int'
      |                                                   |-BinaryOperator 0x5556a36dbf70 <line:431:2, col:18> 'int' '='
      |                                                   | |-DeclRefExpr 0x5556a36dbed8 <col:2> 'int' lvalue Var 0x5556a36dbe58 '__tmp_23' 'int'
      |                                                   | `-BinaryOperator 0x5556a36dbf50 <col:13, col:18> 'int' '<='
      |                                                   |   |-IntegerLiteral 0x5556a36dbef8 <col:13> 'int' 0
      |                                                   |   `-ImplicitCastExpr 0x5556a36dbf38 <col:18> 'int' <LValueToRValue>
      |                                                   |     `-DeclRefExpr 0x5556a36dbf18 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                   |-DeclStmt 0x5556a36dc010 <line:432:2, col:29>
      |                                                   | `-VarDecl 0x5556a36dbfa8 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                   |-BinaryOperator 0x5556a36dc080 <line:433:2, col:28> 'int' '='
      |                                                   | |-DeclRefExpr 0x5556a36dc028 <col:2> 'int' lvalue Var 0x5556a36dbfa8 '__VERIFIER_assert__cond' 'int'
      |                                                   | `-ImplicitCastExpr 0x5556a36dc068 <col:28> 'int' <LValueToRValue>
      |                                                   |   `-DeclRefExpr 0x5556a36dc048 <col:28> 'int' lvalue Var 0x5556a36dbe58 '__tmp_23' 'int'
      |                                                   `-IfStmt 0x5556a36dfbb0 <line:434:2, line:985:2> has_else
      |                                                     |-BinaryOperator 0x5556a36dc0f8 <line:434:6, col:33> 'int' '=='
      |                                                     | |-ImplicitCastExpr 0x5556a36dc0e0 <col:6> 'int' <LValueToRValue>
      |                                                     | | `-DeclRefExpr 0x5556a36dc0a0 <col:6> 'int' lvalue Var 0x5556a36dbfa8 '__VERIFIER_assert__cond' 'int'
      |                                                     | `-IntegerLiteral 0x5556a36dc0c0 <col:33> 'int' 0
      |                                                     |-CompoundStmt 0x5556a36dc160 <line:435:2, line:437:2>
      |                                                     | `-ReturnStmt 0x5556a36dc150 <line:436:2, col:9>
      |                                                     |   `-ImplicitCastExpr 0x5556a36dc138 <col:9> 'int' <LValueToRValue>
      |                                                     |     `-DeclRefExpr 0x5556a36dc118 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                     `-CompoundStmt 0x5556a36ee418 <line:439:2, line:985:2>
      |                                                       `-CompoundStmt 0x5556a36ee3e0 <line:440:2, line:984:2>
      |                                                         |-DeclStmt 0x5556a36dc1f8 <line:441:2, col:14>
      |                                                         | `-VarDecl 0x5556a36dc190 <col:2, col:6> col:6 used __tmp_24 'int'
      |                                                         |-BinaryOperator 0x5556a36dc2c0 <line:442:2, col:24> 'int' '='
      |                                                         | |-DeclRefExpr 0x5556a36dc210 <col:2> 'int' lvalue Var 0x5556a36dc190 '__tmp_24' 'int'
      |                                                         | `-BinaryOperator 0x5556a36dc2a0 <col:13, col:24> 'int' '<='
      |                                                         |   |-ImplicitCastExpr 0x5556a36dc270 <col:13> 'int' <LValueToRValue>
      |                                                         |   | `-DeclRefExpr 0x5556a36dc230 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                         |   `-ImplicitCastExpr 0x5556a36dc288 <col:24> 'int' <LValueToRValue>
      |                                                         |     `-DeclRefExpr 0x5556a36dc250 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                         |-DeclStmt 0x5556a36dc360 <line:443:2, col:29>
      |                                                         | `-VarDecl 0x5556a36dc2f8 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                         |-BinaryOperator 0x5556a36dc3d0 <line:444:2, col:28> 'int' '='
      |                                                         | |-DeclRefExpr 0x5556a36dc378 <col:2> 'int' lvalue Var 0x5556a36dc2f8 '__VERIFIER_assert__cond' 'int'
      |                                                         | `-ImplicitCastExpr 0x5556a36dc3b8 <col:28> 'int' <LValueToRValue>
      |                                                         |   `-DeclRefExpr 0x5556a36dc398 <col:28> 'int' lvalue Var 0x5556a36dc190 '__tmp_24' 'int'
      |                                                         `-IfStmt 0x5556a36ee3b8 <line:445:2, line:983:2> has_else
      |                                                           |-BinaryOperator 0x5556a36dc448 <line:445:6, col:33> 'int' '=='
      |                                                           | |-ImplicitCastExpr 0x5556a36dc430 <col:6> 'int' <LValueToRValue>
      |                                                           | | `-DeclRefExpr 0x5556a36dc3f0 <col:6> 'int' lvalue Var 0x5556a36dc2f8 '__VERIFIER_assert__cond' 'int'
      |                                                           | `-IntegerLiteral 0x5556a36dc410 <col:33> 'int' 0
      |                                                           |-CompoundStmt 0x5556a36dc4b0 <line:446:2, line:448:2>
      |                                                           | `-ReturnStmt 0x5556a36dc4a0 <line:447:2, col:9>
      |                                                           |   `-ImplicitCastExpr 0x5556a36dc488 <col:9> 'int' <LValueToRValue>
      |                                                           |     `-DeclRefExpr 0x5556a36dc468 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                           `-CompoundStmt 0x5556a36ee390 <line:450:2, line:983:2>
      |                                                             |-DeclStmt 0x5556a36dc580 <line:451:2, col:40>
      |                                                             | `-VarDecl 0x5556a36dc4e0 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
      |                                                             |   `-ImplicitCastExpr 0x5556a36dc568 <col:33> 'int' <LValueToRValue>
      |                                                             |     `-DeclRefExpr 0x5556a36dc548 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                             |-BinaryOperator 0x5556a36dc630 <line:452:2, col:22> 'int' '='
      |                                                             | |-DeclRefExpr 0x5556a36dc598 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                             | `-BinaryOperator 0x5556a36dc610 <col:12, col:22> 'int' '+'
      |                                                             |   |-ImplicitCastExpr 0x5556a36dc5f8 <col:12> 'int' <LValueToRValue>
      |                                                             |   | `-DeclRefExpr 0x5556a36dc5b8 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                             |   `-IntegerLiteral 0x5556a36dc5d8 <col:22> 'int' 1
      |                                                             `-IfStmt 0x5556a36ee368 <line:453:2, line:982:2> has_else
      |                                                               |-BinaryOperator 0x5556a36dc6c0 <line:453:6, col:17> 'int' '=='
      |                                                               | |-ImplicitCastExpr 0x5556a36dc690 <col:6> 'int' <LValueToRValue>
      |                                                               | | `-DeclRefExpr 0x5556a36dc650 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                               | `-ImplicitCastExpr 0x5556a36dc6a8 <col:17> 'int' <LValueToRValue>
      |                                                               |   `-DeclRefExpr 0x5556a36dc670 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                               |-CompoundStmt 0x5556a36dc6f8 <line:454:2, line:456:2>
      |                                                               | `-GotoStmt 0x5556a36dc6e0 <line:455:2, col:7> 'label_2604' 0x5556a36cc568
      |                                                               `-CompoundStmt 0x5556a36ee340 <line:458:2, line:982:2>
      |                                                                 |-DeclStmt 0x5556a36dc790 <line:459:2, col:30>
      |                                                                 | `-VarDecl 0x5556a36dc728 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                                                                 |-BinaryOperator 0x5556a36dc820 <line:460:2, col:51> 'int' '='
      |                                                                 | |-DeclRefExpr 0x5556a36dc7a8 <col:2> 'int' lvalue Var 0x5556a36dc728 'main____CPAchecker_TMP_0' 'int'
      |                                                                 | `-CallExpr 0x5556a36dc800 <col:29, col:51> 'int'
      |                                                                 |   `-ImplicitCastExpr 0x5556a36dc7e8 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                                                                 |     `-DeclRefExpr 0x5556a36dc7c8 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                                                                 `-IfStmt 0x5556a36ee318 <line:461:2, line:981:2> has_else
      |                                                                   |-UnaryOperator 0x5556a36dc8d8 <line:461:6, col:37> 'int' prefix '!' cannot overflow
      |                                                                   | `-ParenExpr 0x5556a36dc8b8 <col:7, col:37> 'int'
      |                                                                   |   `-BinaryOperator 0x5556a36dc898 <col:8, col:36> 'int' '=='
      |                                                                   |     |-ImplicitCastExpr 0x5556a36dc880 <col:8> 'int' <LValueToRValue>
      |                                                                   |     | `-DeclRefExpr 0x5556a36dc840 <col:8> 'int' lvalue Var 0x5556a36dc728 'main____CPAchecker_TMP_0' 'int'
      |                                                                   |     `-IntegerLiteral 0x5556a36dc860 <col:36> 'int' 0
      |                                                                   |-CompoundStmt 0x5556a36ddbe0 <line:462:2, line:494:2>
      |                                                                   | `-CompoundStmt 0x5556a36ddba8 <line:463:2, line:493:2>
      |                                                                   |   |-DeclStmt 0x5556a36dc970 <line:464:2, col:14>
      |                                                                   |   | `-VarDecl 0x5556a36dc908 <col:2, col:6> col:6 used __tmp_25 'int'
      |                                                                   |   |-BinaryOperator 0x5556a36dca20 <line:465:2, col:18> 'int' '='
      |                                                                   |   | |-DeclRefExpr 0x5556a36dc988 <col:2> 'int' lvalue Var 0x5556a36dc908 '__tmp_25' 'int'
      |                                                                   |   | `-BinaryOperator 0x5556a36dca00 <col:13, col:18> 'int' '<='
      |                                                                   |   |   |-IntegerLiteral 0x5556a36dc9a8 <col:13> 'int' 0
      |                                                                   |   |   `-ImplicitCastExpr 0x5556a36dc9e8 <col:18> 'int' <LValueToRValue>
      |                                                                   |   |     `-DeclRefExpr 0x5556a36dc9c8 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                   |   |-DeclStmt 0x5556a36dd388 <line:466:2, col:29>
      |                                                                   |   | `-VarDecl 0x5556a36dd320 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                   |   |-BinaryOperator 0x5556a36dd3f8 <line:467:2, col:28> 'int' '='
      |                                                                   |   | |-DeclRefExpr 0x5556a36dd3a0 <col:2> 'int' lvalue Var 0x5556a36dd320 '__VERIFIER_assert__cond' 'int'
      |                                                                   |   | `-ImplicitCastExpr 0x5556a36dd3e0 <col:28> 'int' <LValueToRValue>
      |                                                                   |   |   `-DeclRefExpr 0x5556a36dd3c0 <col:28> 'int' lvalue Var 0x5556a36dc908 '__tmp_25' 'int'
      |                                                                   |   `-IfStmt 0x5556a36ddb80 <line:468:2, line:492:2> has_else
      |                                                                   |     |-BinaryOperator 0x5556a36dd470 <line:468:6, col:33> 'int' '=='
      |                                                                   |     | |-ImplicitCastExpr 0x5556a36dd458 <col:6> 'int' <LValueToRValue>
      |                                                                   |     | | `-DeclRefExpr 0x5556a36dd418 <col:6> 'int' lvalue Var 0x5556a36dd320 '__VERIFIER_assert__cond' 'int'
      |                                                                   |     | `-IntegerLiteral 0x5556a36dd438 <col:33> 'int' 0
      |                                                                   |     |-CompoundStmt 0x5556a36dd4d8 <line:469:2, line:471:2>
      |                                                                   |     | `-ReturnStmt 0x5556a36dd4c8 <line:470:2, col:9>
      |                                                                   |     |   `-ImplicitCastExpr 0x5556a36dd4b0 <col:9> 'int' <LValueToRValue>
      |                                                                   |     |     `-DeclRefExpr 0x5556a36dd490 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                   |     `-CompoundStmt 0x5556a36ddb68 <line:473:2, line:492:2>
      |                                                                   |       `-CompoundStmt 0x5556a36ddb30 <line:474:2, line:491:2>
      |                                                                   |         |-DeclStmt 0x5556a36dd570 <line:475:2, col:14>
      |                                                                   |         | `-VarDecl 0x5556a36dd508 <col:2, col:6> col:6 used __tmp_26 'int'
      |                                                                   |         |-BinaryOperator 0x5556a36dd638 <line:476:2, col:24> 'int' '='
      |                                                                   |         | |-DeclRefExpr 0x5556a36dd588 <col:2> 'int' lvalue Var 0x5556a36dd508 '__tmp_26' 'int'
      |                                                                   |         | `-BinaryOperator 0x5556a36dd618 <col:13, col:24> 'int' '<='
      |                                                                   |         |   |-ImplicitCastExpr 0x5556a36dd5e8 <col:13> 'int' <LValueToRValue>
      |                                                                   |         |   | `-DeclRefExpr 0x5556a36dd5a8 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                   |         |   `-ImplicitCastExpr 0x5556a36dd600 <col:24> 'int' <LValueToRValue>
      |                                                                   |         |     `-DeclRefExpr 0x5556a36dd5c8 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                   |         |-DeclStmt 0x5556a36dd6d8 <line:477:2, col:29>
      |                                                                   |         | `-VarDecl 0x5556a36dd670 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                   |         |-BinaryOperator 0x5556a36dd748 <line:478:2, col:28> 'int' '='
      |                                                                   |         | |-DeclRefExpr 0x5556a36dd6f0 <col:2> 'int' lvalue Var 0x5556a36dd670 '__VERIFIER_assert__cond' 'int'
      |                                                                   |         | `-ImplicitCastExpr 0x5556a36dd730 <col:28> 'int' <LValueToRValue>
      |                                                                   |         |   `-DeclRefExpr 0x5556a36dd710 <col:28> 'int' lvalue Var 0x5556a36dd508 '__tmp_26' 'int'
      |                                                                   |         `-IfStmt 0x5556a36ddb08 <line:479:2, line:490:2> has_else
      |                                                                   |           |-BinaryOperator 0x5556a36dd7c0 <line:479:6, col:33> 'int' '=='
      |                                                                   |           | |-ImplicitCastExpr 0x5556a36dd7a8 <col:6> 'int' <LValueToRValue>
      |                                                                   |           | | `-DeclRefExpr 0x5556a36dd768 <col:6> 'int' lvalue Var 0x5556a36dd670 '__VERIFIER_assert__cond' 'int'
      |                                                                   |           | `-IntegerLiteral 0x5556a36dd788 <col:33> 'int' 0
      |                                                                   |           |-CompoundStmt 0x5556a36dd828 <line:480:2, line:482:2>
      |                                                                   |           | `-ReturnStmt 0x5556a36dd818 <line:481:2, col:9>
      |                                                                   |           |   `-ImplicitCastExpr 0x5556a36dd800 <col:9> 'int' <LValueToRValue>
      |                                                                   |           |     `-DeclRefExpr 0x5556a36dd7e0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                   |           `-CompoundStmt 0x5556a36ddad0 <line:484:2, line:490:2>
      |                                                                   |             |-DeclStmt 0x5556a36dd8f8 <line:485:2, col:40>
      |                                                                   |             | `-VarDecl 0x5556a36dd858 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                                                                   |             |   `-ImplicitCastExpr 0x5556a36dd8e0 <col:33> 'int' <LValueToRValue>
      |                                                                   |             |     `-DeclRefExpr 0x5556a36dd8c0 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                   |             |-BinaryOperator 0x5556a36dd9a8 <line:486:2, col:22> 'int' '='
      |                                                                   |             | |-DeclRefExpr 0x5556a36dd910 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                   |             | `-BinaryOperator 0x5556a36dd988 <col:12, col:22> 'int' '+'
      |                                                                   |             |   |-ImplicitCastExpr 0x5556a36dd970 <col:12> 'int' <LValueToRValue>
      |                                                                   |             |   | `-DeclRefExpr 0x5556a36dd930 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                   |             |   `-IntegerLiteral 0x5556a36dd950 <col:22> 'int' 1
      |                                                                   |             |-BinaryOperator 0x5556a36dda20 <line:487:2, col:17> 'int' '='
      |                                                                   |             | |-DeclRefExpr 0x5556a36dd9c8 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                                                                   |             | `-ImplicitCastExpr 0x5556a36dda08 <col:17> 'int' <LValueToRValue>
      |                                                                   |             |   `-DeclRefExpr 0x5556a36dd9e8 <col:17> 'int' lvalue Var 0x5556a36dc728 'main____CPAchecker_TMP_0' 'int'
      |                                                                   |             |-BinaryOperator 0x5556a36dda98 <line:488:2, col:17> 'int' '='
      |                                                                   |             | |-DeclRefExpr 0x5556a36dda40 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                                                                   |             | `-ImplicitCastExpr 0x5556a36dda80 <col:17> 'int' <LValueToRValue>
      |                                                                   |             |   `-DeclRefExpr 0x5556a36dda60 <col:17> 'int' lvalue Var 0x5556a36dd858 'main____CPAchecker_TMP_2' 'int'
      |                                                                   |             `-GotoStmt 0x5556a36ddab8 <line:489:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                                                                   `-CompoundStmt 0x5556a36ee300 <line:496:2, line:981:2>
      |                                                                     `-CompoundStmt 0x5556a36ee2c8 <line:497:2, line:980:2>
      |                                                                       |-DeclStmt 0x5556a36ddc78 <line:498:2, col:14>
      |                                                                       | `-VarDecl 0x5556a36ddc10 <col:2, col:6> col:6 used __tmp_27 'int'
      |                                                                       |-BinaryOperator 0x5556a36ddd28 <line:499:2, col:18> 'int' '='
      |                                                                       | |-DeclRefExpr 0x5556a36ddc90 <col:2> 'int' lvalue Var 0x5556a36ddc10 '__tmp_27' 'int'
      |                                                                       | `-BinaryOperator 0x5556a36ddd08 <col:13, col:18> 'int' '<='
      |                                                                       |   |-IntegerLiteral 0x5556a36ddcb0 <col:13> 'int' 0
      |                                                                       |   `-ImplicitCastExpr 0x5556a36ddcf0 <col:18> 'int' <LValueToRValue>
      |                                                                       |     `-DeclRefExpr 0x5556a36ddcd0 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                       |-DeclStmt 0x5556a36dddc8 <line:500:2, col:29>
      |                                                                       | `-VarDecl 0x5556a36ddd60 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                       |-BinaryOperator 0x5556a36dde38 <line:501:2, col:28> 'int' '='
      |                                                                       | |-DeclRefExpr 0x5556a36ddde0 <col:2> 'int' lvalue Var 0x5556a36ddd60 '__VERIFIER_assert__cond' 'int'
      |                                                                       | `-ImplicitCastExpr 0x5556a36dde20 <col:28> 'int' <LValueToRValue>
      |                                                                       |   `-DeclRefExpr 0x5556a36dde00 <col:28> 'int' lvalue Var 0x5556a36ddc10 '__tmp_27' 'int'
      |                                                                       `-IfStmt 0x5556a36ee2a0 <line:502:2, line:979:2> has_else
      |                                                                         |-BinaryOperator 0x5556a36ddeb0 <line:502:6, col:33> 'int' '=='
      |                                                                         | |-ImplicitCastExpr 0x5556a36dde98 <col:6> 'int' <LValueToRValue>
      |                                                                         | | `-DeclRefExpr 0x5556a36dde58 <col:6> 'int' lvalue Var 0x5556a36ddd60 '__VERIFIER_assert__cond' 'int'
      |                                                                         | `-IntegerLiteral 0x5556a36dde78 <col:33> 'int' 0
      |                                                                         |-CompoundStmt 0x5556a36ddf18 <line:503:2, line:505:2>
      |                                                                         | `-ReturnStmt 0x5556a36ddf08 <line:504:2, col:9>
      |                                                                         |   `-ImplicitCastExpr 0x5556a36ddef0 <col:9> 'int' <LValueToRValue>
      |                                                                         |     `-DeclRefExpr 0x5556a36dded0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                         `-CompoundStmt 0x5556a36ee288 <line:507:2, line:979:2>
      |                                                                           `-CompoundStmt 0x5556a36ee250 <line:508:2, line:978:2>
      |                                                                             |-DeclStmt 0x5556a36ddfb0 <line:509:2, col:14>
      |                                                                             | `-VarDecl 0x5556a36ddf48 <col:2, col:6> col:6 used __tmp_28 'int'
      |                                                                             |-BinaryOperator 0x5556a36de078 <line:510:2, col:24> 'int' '='
      |                                                                             | |-DeclRefExpr 0x5556a36ddfc8 <col:2> 'int' lvalue Var 0x5556a36ddf48 '__tmp_28' 'int'
      |                                                                             | `-BinaryOperator 0x5556a36de058 <col:13, col:24> 'int' '<='
      |                                                                             |   |-ImplicitCastExpr 0x5556a36de028 <col:13> 'int' <LValueToRValue>
      |                                                                             |   | `-DeclRefExpr 0x5556a36ddfe8 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                             |   `-ImplicitCastExpr 0x5556a36de040 <col:24> 'int' <LValueToRValue>
      |                                                                             |     `-DeclRefExpr 0x5556a36de008 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                             |-DeclStmt 0x5556a36de118 <line:511:2, col:29>
      |                                                                             | `-VarDecl 0x5556a36de0b0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                             |-BinaryOperator 0x5556a36de188 <line:512:2, col:28> 'int' '='
      |                                                                             | |-DeclRefExpr 0x5556a36de130 <col:2> 'int' lvalue Var 0x5556a36de0b0 '__VERIFIER_assert__cond' 'int'
      |                                                                             | `-ImplicitCastExpr 0x5556a36de170 <col:28> 'int' <LValueToRValue>
      |                                                                             |   `-DeclRefExpr 0x5556a36de150 <col:28> 'int' lvalue Var 0x5556a36ddf48 '__tmp_28' 'int'
      |                                                                             `-IfStmt 0x5556a36ee228 <line:513:2, line:977:2> has_else
      |                                                                               |-BinaryOperator 0x5556a36de200 <line:513:6, col:33> 'int' '=='
      |                                                                               | |-ImplicitCastExpr 0x5556a36de1e8 <col:6> 'int' <LValueToRValue>
      |                                                                               | | `-DeclRefExpr 0x5556a36de1a8 <col:6> 'int' lvalue Var 0x5556a36de0b0 '__VERIFIER_assert__cond' 'int'
      |                                                                               | `-IntegerLiteral 0x5556a36de1c8 <col:33> 'int' 0
      |                                                                               |-CompoundStmt 0x5556a36de268 <line:514:2, line:516:2>
      |                                                                               | `-ReturnStmt 0x5556a36de258 <line:515:2, col:9>
      |                                                                               |   `-ImplicitCastExpr 0x5556a36de240 <col:9> 'int' <LValueToRValue>
      |                                                                               |     `-DeclRefExpr 0x5556a36de220 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                               `-CompoundStmt 0x5556a36ee200 <line:518:2, line:977:2>
      |                                                                                 |-DeclStmt 0x5556a36debb8 <line:519:2, col:40>
      |                                                                                 | `-VarDecl 0x5556a36de298 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
      |                                                                                 |   `-ImplicitCastExpr 0x5556a36deba0 <col:33> 'int' <LValueToRValue>
      |                                                                                 |     `-DeclRefExpr 0x5556a36de300 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                 |-BinaryOperator 0x5556a36dec68 <line:520:2, col:22> 'int' '='
      |                                                                                 | |-DeclRefExpr 0x5556a36debd0 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                 | `-BinaryOperator 0x5556a36dec48 <col:12, col:22> 'int' '+'
      |                                                                                 |   |-ImplicitCastExpr 0x5556a36dec30 <col:12> 'int' <LValueToRValue>
      |                                                                                 |   | `-DeclRefExpr 0x5556a36debf0 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                 |   `-IntegerLiteral 0x5556a36dec10 <col:22> 'int' 1
      |                                                                                 `-IfStmt 0x5556a36ee1d8 <line:521:2, line:976:2> has_else
      |                                                                                   |-BinaryOperator 0x5556a36decf8 <line:521:6, col:17> 'int' '=='
      |                                                                                   | |-ImplicitCastExpr 0x5556a36decc8 <col:6> 'int' <LValueToRValue>
      |                                                                                   | | `-DeclRefExpr 0x5556a36dec88 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                   | `-ImplicitCastExpr 0x5556a36dece0 <col:17> 'int' <LValueToRValue>
      |                                                                                   |   `-DeclRefExpr 0x5556a36deca8 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                   |-CompoundStmt 0x5556a36ded30 <line:522:2, line:524:2>
      |                                                                                   | `-GotoStmt 0x5556a36ded18 <line:523:2, col:7> 'label_2604' 0x5556a36cc568
      |                                                                                   `-CompoundStmt 0x5556a36ee1b0 <line:526:2, line:976:2>
      |                                                                                     |-DeclStmt 0x5556a36dedc8 <line:527:2, col:30>
      |                                                                                     | `-VarDecl 0x5556a36ded60 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                                                                                     |-BinaryOperator 0x5556a36dee58 <line:528:2, col:51> 'int' '='
      |                                                                                     | |-DeclRefExpr 0x5556a36dede0 <col:2> 'int' lvalue Var 0x5556a36ded60 'main____CPAchecker_TMP_0' 'int'
      |                                                                                     | `-CallExpr 0x5556a36dee38 <col:29, col:51> 'int'
      |                                                                                     |   `-ImplicitCastExpr 0x5556a36dee20 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                                                                                     |     `-DeclRefExpr 0x5556a36dee00 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                                                                                     `-IfStmt 0x5556a36ee188 <line:529:2, line:975:2> has_else
      |                                                                                       |-UnaryOperator 0x5556a36def10 <line:529:6, col:37> 'int' prefix '!' cannot overflow
      |                                                                                       | `-ParenExpr 0x5556a36deef0 <col:7, col:37> 'int'
      |                                                                                       |   `-BinaryOperator 0x5556a36deed0 <col:8, col:36> 'int' '=='
      |                                                                                       |     |-ImplicitCastExpr 0x5556a36deeb8 <col:8> 'int' <LValueToRValue>
      |                                                                                       |     | `-DeclRefExpr 0x5556a36dee78 <col:8> 'int' lvalue Var 0x5556a36ded60 'main____CPAchecker_TMP_0' 'int'
      |                                                                                       |     `-IntegerLiteral 0x5556a36dee98 <col:36> 'int' 0
      |                                                                                       |-CompoundStmt 0x5556a36df950 <line:530:2, line:562:2>
      |                                                                                       | `-CompoundStmt 0x5556a36df918 <line:531:2, line:561:2>
      |                                                                                       |   |-DeclStmt 0x5556a36defa8 <line:532:2, col:14>
      |                                                                                       |   | `-VarDecl 0x5556a36def40 <col:2, col:6> col:6 used __tmp_29 'int'
      |                                                                                       |   |-BinaryOperator 0x5556a36df058 <line:533:2, col:18> 'int' '='
      |                                                                                       |   | |-DeclRefExpr 0x5556a36defc0 <col:2> 'int' lvalue Var 0x5556a36def40 '__tmp_29' 'int'
      |                                                                                       |   | `-BinaryOperator 0x5556a36df038 <col:13, col:18> 'int' '<='
      |                                                                                       |   |   |-IntegerLiteral 0x5556a36defe0 <col:13> 'int' 0
      |                                                                                       |   |   `-ImplicitCastExpr 0x5556a36df020 <col:18> 'int' <LValueToRValue>
      |                                                                                       |   |     `-DeclRefExpr 0x5556a36df000 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                       |   |-DeclStmt 0x5556a36df0f8 <line:534:2, col:29>
      |                                                                                       |   | `-VarDecl 0x5556a36df090 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                       |   |-BinaryOperator 0x5556a36df168 <line:535:2, col:28> 'int' '='
      |                                                                                       |   | |-DeclRefExpr 0x5556a36df110 <col:2> 'int' lvalue Var 0x5556a36df090 '__VERIFIER_assert__cond' 'int'
      |                                                                                       |   | `-ImplicitCastExpr 0x5556a36df150 <col:28> 'int' <LValueToRValue>
      |                                                                                       |   |   `-DeclRefExpr 0x5556a36df130 <col:28> 'int' lvalue Var 0x5556a36def40 '__tmp_29' 'int'
      |                                                                                       |   `-IfStmt 0x5556a36df8f0 <line:536:2, line:560:2> has_else
      |                                                                                       |     |-BinaryOperator 0x5556a36df1e0 <line:536:6, col:33> 'int' '=='
      |                                                                                       |     | |-ImplicitCastExpr 0x5556a36df1c8 <col:6> 'int' <LValueToRValue>
      |                                                                                       |     | | `-DeclRefExpr 0x5556a36df188 <col:6> 'int' lvalue Var 0x5556a36df090 '__VERIFIER_assert__cond' 'int'
      |                                                                                       |     | `-IntegerLiteral 0x5556a36df1a8 <col:33> 'int' 0
      |                                                                                       |     |-CompoundStmt 0x5556a36df248 <line:537:2, line:539:2>
      |                                                                                       |     | `-ReturnStmt 0x5556a36df238 <line:538:2, col:9>
      |                                                                                       |     |   `-ImplicitCastExpr 0x5556a36df220 <col:9> 'int' <LValueToRValue>
      |                                                                                       |     |     `-DeclRefExpr 0x5556a36df200 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                       |     `-CompoundStmt 0x5556a36df8d8 <line:541:2, line:560:2>
      |                                                                                       |       `-CompoundStmt 0x5556a36df8a0 <line:542:2, line:559:2>
      |                                                                                       |         |-DeclStmt 0x5556a36df2e0 <line:543:2, col:14>
      |                                                                                       |         | `-VarDecl 0x5556a36df278 <col:2, col:6> col:6 used __tmp_30 'int'
      |                                                                                       |         |-BinaryOperator 0x5556a36df3a8 <line:544:2, col:24> 'int' '='
      |                                                                                       |         | |-DeclRefExpr 0x5556a36df2f8 <col:2> 'int' lvalue Var 0x5556a36df278 '__tmp_30' 'int'
      |                                                                                       |         | `-BinaryOperator 0x5556a36df388 <col:13, col:24> 'int' '<='
      |                                                                                       |         |   |-ImplicitCastExpr 0x5556a36df358 <col:13> 'int' <LValueToRValue>
      |                                                                                       |         |   | `-DeclRefExpr 0x5556a36df318 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                       |         |   `-ImplicitCastExpr 0x5556a36df370 <col:24> 'int' <LValueToRValue>
      |                                                                                       |         |     `-DeclRefExpr 0x5556a36df338 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                       |         |-DeclStmt 0x5556a36df448 <line:545:2, col:29>
      |                                                                                       |         | `-VarDecl 0x5556a36df3e0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                       |         |-BinaryOperator 0x5556a36df4b8 <line:546:2, col:28> 'int' '='
      |                                                                                       |         | |-DeclRefExpr 0x5556a36df460 <col:2> 'int' lvalue Var 0x5556a36df3e0 '__VERIFIER_assert__cond' 'int'
      |                                                                                       |         | `-ImplicitCastExpr 0x5556a36df4a0 <col:28> 'int' <LValueToRValue>
      |                                                                                       |         |   `-DeclRefExpr 0x5556a36df480 <col:28> 'int' lvalue Var 0x5556a36df278 '__tmp_30' 'int'
      |                                                                                       |         `-IfStmt 0x5556a36df878 <line:547:2, line:558:2> has_else
      |                                                                                       |           |-BinaryOperator 0x5556a36df530 <line:547:6, col:33> 'int' '=='
      |                                                                                       |           | |-ImplicitCastExpr 0x5556a36df518 <col:6> 'int' <LValueToRValue>
      |                                                                                       |           | | `-DeclRefExpr 0x5556a36df4d8 <col:6> 'int' lvalue Var 0x5556a36df3e0 '__VERIFIER_assert__cond' 'int'
      |                                                                                       |           | `-IntegerLiteral 0x5556a36df4f8 <col:33> 'int' 0
      |                                                                                       |           |-CompoundStmt 0x5556a36df598 <line:548:2, line:550:2>
      |                                                                                       |           | `-ReturnStmt 0x5556a36df588 <line:549:2, col:9>
      |                                                                                       |           |   `-ImplicitCastExpr 0x5556a36df570 <col:9> 'int' <LValueToRValue>
      |                                                                                       |           |     `-DeclRefExpr 0x5556a36df550 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                       |           `-CompoundStmt 0x5556a36df840 <line:552:2, line:558:2>
      |                                                                                       |             |-DeclStmt 0x5556a36df668 <line:553:2, col:40>
      |                                                                                       |             | `-VarDecl 0x5556a36df5c8 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                                                                                       |             |   `-ImplicitCastExpr 0x5556a36df650 <col:33> 'int' <LValueToRValue>
      |                                                                                       |             |     `-DeclRefExpr 0x5556a36df630 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                       |             |-BinaryOperator 0x5556a36df718 <line:554:2, col:22> 'int' '='
      |                                                                                       |             | |-DeclRefExpr 0x5556a36df680 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                       |             | `-BinaryOperator 0x5556a36df6f8 <col:12, col:22> 'int' '+'
      |                                                                                       |             |   |-ImplicitCastExpr 0x5556a36df6e0 <col:12> 'int' <LValueToRValue>
      |                                                                                       |             |   | `-DeclRefExpr 0x5556a36df6a0 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                       |             |   `-IntegerLiteral 0x5556a36df6c0 <col:22> 'int' 1
      |                                                                                       |             |-BinaryOperator 0x5556a36df790 <line:555:2, col:17> 'int' '='
      |                                                                                       |             | |-DeclRefExpr 0x5556a36df738 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                                                                                       |             | `-ImplicitCastExpr 0x5556a36df778 <col:17> 'int' <LValueToRValue>
      |                                                                                       |             |   `-DeclRefExpr 0x5556a36df758 <col:17> 'int' lvalue Var 0x5556a36ded60 'main____CPAchecker_TMP_0' 'int'
      |                                                                                       |             |-BinaryOperator 0x5556a36df808 <line:556:2, col:17> 'int' '='
      |                                                                                       |             | |-DeclRefExpr 0x5556a36df7b0 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                                                                                       |             | `-ImplicitCastExpr 0x5556a36df7f0 <col:17> 'int' <LValueToRValue>
      |                                                                                       |             |   `-DeclRefExpr 0x5556a36df7d0 <col:17> 'int' lvalue Var 0x5556a36df5c8 'main____CPAchecker_TMP_2' 'int'
      |                                                                                       |             `-GotoStmt 0x5556a36df828 <line:557:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                                                                                       `-CompoundStmt 0x5556a36ee170 <line:564:2, line:975:2>
      |                                                                                         `-CompoundStmt 0x5556a36ee138 <line:565:2, line:974:2>
      |                                                                                           |-DeclStmt 0x5556a36df9e8 <line:566:2, col:14>
      |                                                                                           | `-VarDecl 0x5556a36df980 <col:2, col:6> col:6 used __tmp_31 'int'
      |                                                                                           |-BinaryOperator 0x5556a36dfa98 <line:567:2, col:18> 'int' '='
      |                                                                                           | |-DeclRefExpr 0x5556a36dfa00 <col:2> 'int' lvalue Var 0x5556a36df980 '__tmp_31' 'int'
      |                                                                                           | `-BinaryOperator 0x5556a36dfa78 <col:13, col:18> 'int' '<='
      |                                                                                           |   |-IntegerLiteral 0x5556a36dfa20 <col:13> 'int' 0
      |                                                                                           |   `-ImplicitCastExpr 0x5556a36dfa60 <col:18> 'int' <LValueToRValue>
      |                                                                                           |     `-DeclRefExpr 0x5556a36dfa40 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                           |-DeclStmt 0x5556a36dfb38 <line:568:2, col:29>
      |                                                                                           | `-VarDecl 0x5556a36dfad0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                           |-BinaryOperator 0x5556a36e0ca8 <line:569:2, col:28> 'int' '='
      |                                                                                           | |-DeclRefExpr 0x5556a36dfb50 <col:2> 'int' lvalue Var 0x5556a36dfad0 '__VERIFIER_assert__cond' 'int'
      |                                                                                           | `-ImplicitCastExpr 0x5556a36e0c90 <col:28> 'int' <LValueToRValue>
      |                                                                                           |   `-DeclRefExpr 0x5556a36dfb70 <col:28> 'int' lvalue Var 0x5556a36df980 '__tmp_31' 'int'
      |                                                                                           `-IfStmt 0x5556a36ee110 <line:570:2, line:973:2> has_else
      |                                                                                             |-BinaryOperator 0x5556a36e0d20 <line:570:6, col:33> 'int' '=='
      |                                                                                             | |-ImplicitCastExpr 0x5556a36e0d08 <col:6> 'int' <LValueToRValue>
      |                                                                                             | | `-DeclRefExpr 0x5556a36e0cc8 <col:6> 'int' lvalue Var 0x5556a36dfad0 '__VERIFIER_assert__cond' 'int'
      |                                                                                             | `-IntegerLiteral 0x5556a36e0ce8 <col:33> 'int' 0
      |                                                                                             |-CompoundStmt 0x5556a36e0d88 <line:571:2, line:573:2>
      |                                                                                             | `-ReturnStmt 0x5556a36e0d78 <line:572:2, col:9>
      |                                                                                             |   `-ImplicitCastExpr 0x5556a36e0d60 <col:9> 'int' <LValueToRValue>
      |                                                                                             |     `-DeclRefExpr 0x5556a36e0d40 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                             `-CompoundStmt 0x5556a36ee0f8 <line:575:2, line:973:2>
      |                                                                                               `-CompoundStmt 0x5556a36ee0c0 <line:576:2, line:972:2>
      |                                                                                                 |-DeclStmt 0x5556a36e0e20 <line:577:2, col:14>
      |                                                                                                 | `-VarDecl 0x5556a36e0db8 <col:2, col:6> col:6 used __tmp_32 'int'
      |                                                                                                 |-BinaryOperator 0x5556a36e0ee8 <line:578:2, col:24> 'int' '='
      |                                                                                                 | |-DeclRefExpr 0x5556a36e0e38 <col:2> 'int' lvalue Var 0x5556a36e0db8 '__tmp_32' 'int'
      |                                                                                                 | `-BinaryOperator 0x5556a36e0ec8 <col:13, col:24> 'int' '<='
      |                                                                                                 |   |-ImplicitCastExpr 0x5556a36e0e98 <col:13> 'int' <LValueToRValue>
      |                                                                                                 |   | `-DeclRefExpr 0x5556a36e0e58 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                 |   `-ImplicitCastExpr 0x5556a36e0eb0 <col:24> 'int' <LValueToRValue>
      |                                                                                                 |     `-DeclRefExpr 0x5556a36e0e78 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                 |-DeclStmt 0x5556a36e0f88 <line:579:2, col:29>
      |                                                                                                 | `-VarDecl 0x5556a36e0f20 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                 |-BinaryOperator 0x5556a36e0ff8 <line:580:2, col:28> 'int' '='
      |                                                                                                 | |-DeclRefExpr 0x5556a36e0fa0 <col:2> 'int' lvalue Var 0x5556a36e0f20 '__VERIFIER_assert__cond' 'int'
      |                                                                                                 | `-ImplicitCastExpr 0x5556a36e0fe0 <col:28> 'int' <LValueToRValue>
      |                                                                                                 |   `-DeclRefExpr 0x5556a36e0fc0 <col:28> 'int' lvalue Var 0x5556a36e0db8 '__tmp_32' 'int'
      |                                                                                                 `-IfStmt 0x5556a36ee098 <line:581:2, line:971:2> has_else
      |                                                                                                   |-BinaryOperator 0x5556a36e1070 <line:581:6, col:33> 'int' '=='
      |                                                                                                   | |-ImplicitCastExpr 0x5556a36e1058 <col:6> 'int' <LValueToRValue>
      |                                                                                                   | | `-DeclRefExpr 0x5556a36e1018 <col:6> 'int' lvalue Var 0x5556a36e0f20 '__VERIFIER_assert__cond' 'int'
      |                                                                                                   | `-IntegerLiteral 0x5556a36e1038 <col:33> 'int' 0
      |                                                                                                   |-CompoundStmt 0x5556a36e10d8 <line:582:2, line:584:2>
      |                                                                                                   | `-ReturnStmt 0x5556a36e10c8 <line:583:2, col:9>
      |                                                                                                   |   `-ImplicitCastExpr 0x5556a36e10b0 <col:9> 'int' <LValueToRValue>
      |                                                                                                   |     `-DeclRefExpr 0x5556a36e1090 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                   `-CompoundStmt 0x5556a36ee070 <line:586:2, line:971:2>
      |                                                                                                     |-DeclStmt 0x5556a36e11a8 <line:587:2, col:40>
      |                                                                                                     | `-VarDecl 0x5556a36e1108 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
      |                                                                                                     |   `-ImplicitCastExpr 0x5556a36e1190 <col:33> 'int' <LValueToRValue>
      |                                                                                                     |     `-DeclRefExpr 0x5556a36e1170 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                     |-BinaryOperator 0x5556a36e1258 <line:588:2, col:22> 'int' '='
      |                                                                                                     | |-DeclRefExpr 0x5556a36e11c0 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                     | `-BinaryOperator 0x5556a36e1238 <col:12, col:22> 'int' '+'
      |                                                                                                     |   |-ImplicitCastExpr 0x5556a36e1220 <col:12> 'int' <LValueToRValue>
      |                                                                                                     |   | `-DeclRefExpr 0x5556a36e11e0 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                     |   `-IntegerLiteral 0x5556a36e1200 <col:22> 'int' 1
      |                                                                                                     `-IfStmt 0x5556a36ee048 <line:589:2, line:970:2> has_else
      |                                                                                                       |-BinaryOperator 0x5556a36e12e8 <line:589:6, col:17> 'int' '=='
      |                                                                                                       | |-ImplicitCastExpr 0x5556a36e12b8 <col:6> 'int' <LValueToRValue>
      |                                                                                                       | | `-DeclRefExpr 0x5556a36e1278 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                       | `-ImplicitCastExpr 0x5556a36e12d0 <col:17> 'int' <LValueToRValue>
      |                                                                                                       |   `-DeclRefExpr 0x5556a36e1298 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                       |-CompoundStmt 0x5556a36e1320 <line:590:2, line:592:2>
      |                                                                                                       | `-GotoStmt 0x5556a36e1308 <line:591:2, col:7> 'label_2604' 0x5556a36cc568
      |                                                                                                       `-CompoundStmt 0x5556a36ee020 <line:594:2, line:970:2>
      |                                                                                                         |-DeclStmt 0x5556a36e13b8 <line:595:2, col:30>
      |                                                                                                         | `-VarDecl 0x5556a36e1350 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                                                                                                         |-BinaryOperator 0x5556a36e1448 <line:596:2, col:51> 'int' '='
      |                                                                                                         | |-DeclRefExpr 0x5556a36e13d0 <col:2> 'int' lvalue Var 0x5556a36e1350 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                         | `-CallExpr 0x5556a36e1428 <col:29, col:51> 'int'
      |                                                                                                         |   `-ImplicitCastExpr 0x5556a36e1410 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                                                                                                         |     `-DeclRefExpr 0x5556a36e13f0 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                                                                                                         `-IfStmt 0x5556a36edff8 <line:597:2, line:969:2> has_else
      |                                                                                                           |-UnaryOperator 0x5556a36e1500 <line:597:6, col:37> 'int' prefix '!' cannot overflow
      |                                                                                                           | `-ParenExpr 0x5556a36e14e0 <col:7, col:37> 'int'
      |                                                                                                           |   `-BinaryOperator 0x5556a36e14c0 <col:8, col:36> 'int' '=='
      |                                                                                                           |     |-ImplicitCastExpr 0x5556a36e14a8 <col:8> 'int' <LValueToRValue>
      |                                                                                                           |     | `-DeclRefExpr 0x5556a36e1468 <col:8> 'int' lvalue Var 0x5556a36e1350 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                           |     `-IntegerLiteral 0x5556a36e1488 <col:36> 'int' 0
      |                                                                                                           |-CompoundStmt 0x5556a36e3030 <line:598:2, line:630:2>
      |                                                                                                           | `-CompoundStmt 0x5556a36e2ff8 <line:599:2, line:629:2>
      |                                                                                                           |   |-DeclStmt 0x5556a36e1598 <line:600:2, col:14>
      |                                                                                                           |   | `-VarDecl 0x5556a36e1530 <col:2, col:6> col:6 used __tmp_33 'int'
      |                                                                                                           |   |-BinaryOperator 0x5556a36e1648 <line:601:2, col:18> 'int' '='
      |                                                                                                           |   | |-DeclRefExpr 0x5556a36e15b0 <col:2> 'int' lvalue Var 0x5556a36e1530 '__tmp_33' 'int'
      |                                                                                                           |   | `-BinaryOperator 0x5556a36e1628 <col:13, col:18> 'int' '<='
      |                                                                                                           |   |   |-IntegerLiteral 0x5556a36e15d0 <col:13> 'int' 0
      |                                                                                                           |   |   `-ImplicitCastExpr 0x5556a36e1610 <col:18> 'int' <LValueToRValue>
      |                                                                                                           |   |     `-DeclRefExpr 0x5556a36e15f0 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                           |   |-DeclStmt 0x5556a36e16e8 <line:602:2, col:29>
      |                                                                                                           |   | `-VarDecl 0x5556a36e1680 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                           |   |-BinaryOperator 0x5556a36e1758 <line:603:2, col:28> 'int' '='
      |                                                                                                           |   | |-DeclRefExpr 0x5556a36e1700 <col:2> 'int' lvalue Var 0x5556a36e1680 '__VERIFIER_assert__cond' 'int'
      |                                                                                                           |   | `-ImplicitCastExpr 0x5556a36e1740 <col:28> 'int' <LValueToRValue>
      |                                                                                                           |   |   `-DeclRefExpr 0x5556a36e1720 <col:28> 'int' lvalue Var 0x5556a36e1530 '__tmp_33' 'int'
      |                                                                                                           |   `-IfStmt 0x5556a36e2fd0 <line:604:2, line:628:2> has_else
      |                                                                                                           |     |-BinaryOperator 0x5556a36e17d0 <line:604:6, col:33> 'int' '=='
      |                                                                                                           |     | |-ImplicitCastExpr 0x5556a36e17b8 <col:6> 'int' <LValueToRValue>
      |                                                                                                           |     | | `-DeclRefExpr 0x5556a36e1778 <col:6> 'int' lvalue Var 0x5556a36e1680 '__VERIFIER_assert__cond' 'int'
      |                                                                                                           |     | `-IntegerLiteral 0x5556a36e1798 <col:33> 'int' 0
      |                                                                                                           |     |-CompoundStmt 0x5556a36e1838 <line:605:2, line:607:2>
      |                                                                                                           |     | `-ReturnStmt 0x5556a36e1828 <line:606:2, col:9>
      |                                                                                                           |     |   `-ImplicitCastExpr 0x5556a36e1810 <col:9> 'int' <LValueToRValue>
      |                                                                                                           |     |     `-DeclRefExpr 0x5556a36e17f0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                           |     `-CompoundStmt 0x5556a36e2fb8 <line:609:2, line:628:2>
      |                                                                                                           |       `-CompoundStmt 0x5556a36e2f80 <line:610:2, line:627:2>
      |                                                                                                           |         |-DeclStmt 0x5556a36e18d0 <line:611:2, col:14>
      |                                                                                                           |         | `-VarDecl 0x5556a36e1868 <col:2, col:6> col:6 used __tmp_34 'int'
      |                                                                                                           |         |-BinaryOperator 0x5556a36e1998 <line:612:2, col:24> 'int' '='
      |                                                                                                           |         | |-DeclRefExpr 0x5556a36e18e8 <col:2> 'int' lvalue Var 0x5556a36e1868 '__tmp_34' 'int'
      |                                                                                                           |         | `-BinaryOperator 0x5556a36e1978 <col:13, col:24> 'int' '<='
      |                                                                                                           |         |   |-ImplicitCastExpr 0x5556a36e1948 <col:13> 'int' <LValueToRValue>
      |                                                                                                           |         |   | `-DeclRefExpr 0x5556a36e1908 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                           |         |   `-ImplicitCastExpr 0x5556a36e1960 <col:24> 'int' <LValueToRValue>
      |                                                                                                           |         |     `-DeclRefExpr 0x5556a36e1928 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                           |         |-DeclStmt 0x5556a36e1a38 <line:613:2, col:29>
      |                                                                                                           |         | `-VarDecl 0x5556a36e19d0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                           |         |-BinaryOperator 0x5556a36e1aa8 <line:614:2, col:28> 'int' '='
      |                                                                                                           |         | |-DeclRefExpr 0x5556a36e1a50 <col:2> 'int' lvalue Var 0x5556a36e19d0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                           |         | `-ImplicitCastExpr 0x5556a36e1a90 <col:28> 'int' <LValueToRValue>
      |                                                                                                           |         |   `-DeclRefExpr 0x5556a36e1a70 <col:28> 'int' lvalue Var 0x5556a36e1868 '__tmp_34' 'int'
      |                                                                                                           |         `-IfStmt 0x5556a36e2f58 <line:615:2, line:626:2> has_else
      |                                                                                                           |           |-BinaryOperator 0x5556a36e1b20 <line:615:6, col:33> 'int' '=='
      |                                                                                                           |           | |-ImplicitCastExpr 0x5556a36e1b08 <col:6> 'int' <LValueToRValue>
      |                                                                                                           |           | | `-DeclRefExpr 0x5556a36e1ac8 <col:6> 'int' lvalue Var 0x5556a36e19d0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                           |           | `-IntegerLiteral 0x5556a36e1ae8 <col:33> 'int' 0
      |                                                                                                           |           |-CompoundStmt 0x5556a36e1b88 <line:616:2, line:618:2>
      |                                                                                                           |           | `-ReturnStmt 0x5556a36e1b78 <line:617:2, col:9>
      |                                                                                                           |           |   `-ImplicitCastExpr 0x5556a36e1b60 <col:9> 'int' <LValueToRValue>
      |                                                                                                           |           |     `-DeclRefExpr 0x5556a36e1b40 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                           |           `-CompoundStmt 0x5556a36e2f20 <line:620:2, line:626:2>
      |                                                                                                           |             |-DeclStmt 0x5556a36e1c58 <line:621:2, col:40>
      |                                                                                                           |             | `-VarDecl 0x5556a36e1bb8 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                                                                                                           |             |   `-ImplicitCastExpr 0x5556a36e1c40 <col:33> 'int' <LValueToRValue>
      |                                                                                                           |             |     `-DeclRefExpr 0x5556a36e1c20 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                           |             |-BinaryOperator 0x5556a36e2df8 <line:622:2, col:22> 'int' '='
      |                                                                                                           |             | |-DeclRefExpr 0x5556a36e1c70 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                           |             | `-BinaryOperator 0x5556a36e2dd8 <col:12, col:22> 'int' '+'
      |                                                                                                           |             |   |-ImplicitCastExpr 0x5556a36e2dc0 <col:12> 'int' <LValueToRValue>
      |                                                                                                           |             |   | `-DeclRefExpr 0x5556a36e2d80 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                           |             |   `-IntegerLiteral 0x5556a36e2da0 <col:22> 'int' 1
      |                                                                                                           |             |-BinaryOperator 0x5556a36e2e70 <line:623:2, col:17> 'int' '='
      |                                                                                                           |             | |-DeclRefExpr 0x5556a36e2e18 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                                                                                                           |             | `-ImplicitCastExpr 0x5556a36e2e58 <col:17> 'int' <LValueToRValue>
      |                                                                                                           |             |   `-DeclRefExpr 0x5556a36e2e38 <col:17> 'int' lvalue Var 0x5556a36e1350 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                           |             |-BinaryOperator 0x5556a36e2ee8 <line:624:2, col:17> 'int' '='
      |                                                                                                           |             | |-DeclRefExpr 0x5556a36e2e90 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                                                                                                           |             | `-ImplicitCastExpr 0x5556a36e2ed0 <col:17> 'int' <LValueToRValue>
      |                                                                                                           |             |   `-DeclRefExpr 0x5556a36e2eb0 <col:17> 'int' lvalue Var 0x5556a36e1bb8 'main____CPAchecker_TMP_2' 'int'
      |                                                                                                           |             `-GotoStmt 0x5556a36e2f08 <line:625:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                                                                                                           `-CompoundStmt 0x5556a36edfe0 <line:632:2, line:969:2>
      |                                                                                                             `-CompoundStmt 0x5556a36edfa8 <line:633:2, line:968:2>
      |                                                                                                               |-DeclStmt 0x5556a36e30c8 <line:634:2, col:14>
      |                                                                                                               | `-VarDecl 0x5556a36e3060 <col:2, col:6> col:6 used __tmp_35 'int'
      |                                                                                                               |-BinaryOperator 0x5556a36e3178 <line:635:2, col:18> 'int' '='
      |                                                                                                               | |-DeclRefExpr 0x5556a36e30e0 <col:2> 'int' lvalue Var 0x5556a36e3060 '__tmp_35' 'int'
      |                                                                                                               | `-BinaryOperator 0x5556a36e3158 <col:13, col:18> 'int' '<='
      |                                                                                                               |   |-IntegerLiteral 0x5556a36e3100 <col:13> 'int' 0
      |                                                                                                               |   `-ImplicitCastExpr 0x5556a36e3140 <col:18> 'int' <LValueToRValue>
      |                                                                                                               |     `-DeclRefExpr 0x5556a36e3120 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                               |-DeclStmt 0x5556a36e3218 <line:636:2, col:29>
      |                                                                                                               | `-VarDecl 0x5556a36e31b0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                               |-BinaryOperator 0x5556a36e3288 <line:637:2, col:28> 'int' '='
      |                                                                                                               | |-DeclRefExpr 0x5556a36e3230 <col:2> 'int' lvalue Var 0x5556a36e31b0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                               | `-ImplicitCastExpr 0x5556a36e3270 <col:28> 'int' <LValueToRValue>
      |                                                                                                               |   `-DeclRefExpr 0x5556a36e3250 <col:28> 'int' lvalue Var 0x5556a36e3060 '__tmp_35' 'int'
      |                                                                                                               `-IfStmt 0x5556a36edf80 <line:638:2, line:967:2> has_else
      |                                                                                                                 |-BinaryOperator 0x5556a36e3300 <line:638:6, col:33> 'int' '=='
      |                                                                                                                 | |-ImplicitCastExpr 0x5556a36e32e8 <col:6> 'int' <LValueToRValue>
      |                                                                                                                 | | `-DeclRefExpr 0x5556a36e32a8 <col:6> 'int' lvalue Var 0x5556a36e31b0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                 | `-IntegerLiteral 0x5556a36e32c8 <col:33> 'int' 0
      |                                                                                                                 |-CompoundStmt 0x5556a36e3368 <line:639:2, line:641:2>
      |                                                                                                                 | `-ReturnStmt 0x5556a36e3358 <line:640:2, col:9>
      |                                                                                                                 |   `-ImplicitCastExpr 0x5556a36e3340 <col:9> 'int' <LValueToRValue>
      |                                                                                                                 |     `-DeclRefExpr 0x5556a36e3320 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                 `-CompoundStmt 0x5556a36edf68 <line:643:2, line:967:2>
      |                                                                                                                   `-CompoundStmt 0x5556a36edf30 <line:644:2, line:966:2>
      |                                                                                                                     |-DeclStmt 0x5556a36e3400 <line:645:2, col:14>
      |                                                                                                                     | `-VarDecl 0x5556a36e3398 <col:2, col:6> col:6 used __tmp_36 'int'
      |                                                                                                                     |-BinaryOperator 0x5556a36e34c8 <line:646:2, col:24> 'int' '='
      |                                                                                                                     | |-DeclRefExpr 0x5556a36e3418 <col:2> 'int' lvalue Var 0x5556a36e3398 '__tmp_36' 'int'
      |                                                                                                                     | `-BinaryOperator 0x5556a36e34a8 <col:13, col:24> 'int' '<='
      |                                                                                                                     |   |-ImplicitCastExpr 0x5556a36e3478 <col:13> 'int' <LValueToRValue>
      |                                                                                                                     |   | `-DeclRefExpr 0x5556a36e3438 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                     |   `-ImplicitCastExpr 0x5556a36e3490 <col:24> 'int' <LValueToRValue>
      |                                                                                                                     |     `-DeclRefExpr 0x5556a36e3458 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                     |-DeclStmt 0x5556a36e3568 <line:647:2, col:29>
      |                                                                                                                     | `-VarDecl 0x5556a36e3500 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                     |-BinaryOperator 0x5556a36e35d8 <line:648:2, col:28> 'int' '='
      |                                                                                                                     | |-DeclRefExpr 0x5556a36e3580 <col:2> 'int' lvalue Var 0x5556a36e3500 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                     | `-ImplicitCastExpr 0x5556a36e35c0 <col:28> 'int' <LValueToRValue>
      |                                                                                                                     |   `-DeclRefExpr 0x5556a36e35a0 <col:28> 'int' lvalue Var 0x5556a36e3398 '__tmp_36' 'int'
      |                                                                                                                     `-IfStmt 0x5556a36edf08 <line:649:2, line:965:2> has_else
      |                                                                                                                       |-BinaryOperator 0x5556a36e3650 <line:649:6, col:33> 'int' '=='
      |                                                                                                                       | |-ImplicitCastExpr 0x5556a36e3638 <col:6> 'int' <LValueToRValue>
      |                                                                                                                       | | `-DeclRefExpr 0x5556a36e35f8 <col:6> 'int' lvalue Var 0x5556a36e3500 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                       | `-IntegerLiteral 0x5556a36e3618 <col:33> 'int' 0
      |                                                                                                                       |-CompoundStmt 0x5556a36e36b8 <line:650:2, line:652:2>
      |                                                                                                                       | `-ReturnStmt 0x5556a36e36a8 <line:651:2, col:9>
      |                                                                                                                       |   `-ImplicitCastExpr 0x5556a36e3690 <col:9> 'int' <LValueToRValue>
      |                                                                                                                       |     `-DeclRefExpr 0x5556a36e3670 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                       `-CompoundStmt 0x5556a36edee0 <line:654:2, line:965:2>
      |                                                                                                                         |-DeclStmt 0x5556a36e3788 <line:655:2, col:40>
      |                                                                                                                         | `-VarDecl 0x5556a36e36e8 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
      |                                                                                                                         |   `-ImplicitCastExpr 0x5556a36e3770 <col:33> 'int' <LValueToRValue>
      |                                                                                                                         |     `-DeclRefExpr 0x5556a36e3750 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                         |-BinaryOperator 0x5556a36e3838 <line:656:2, col:22> 'int' '='
      |                                                                                                                         | |-DeclRefExpr 0x5556a36e37a0 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                         | `-BinaryOperator 0x5556a36e3818 <col:12, col:22> 'int' '+'
      |                                                                                                                         |   |-ImplicitCastExpr 0x5556a36e3800 <col:12> 'int' <LValueToRValue>
      |                                                                                                                         |   | `-DeclRefExpr 0x5556a36e37c0 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                         |   `-IntegerLiteral 0x5556a36e37e0 <col:22> 'int' 1
      |                                                                                                                         `-IfStmt 0x5556a36edeb8 <line:657:2, line:964:2> has_else
      |                                                                                                                           |-BinaryOperator 0x5556a36e38c8 <line:657:6, col:17> 'int' '=='
      |                                                                                                                           | |-ImplicitCastExpr 0x5556a36e3898 <col:6> 'int' <LValueToRValue>
      |                                                                                                                           | | `-DeclRefExpr 0x5556a36e3858 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                           | `-ImplicitCastExpr 0x5556a36e38b0 <col:17> 'int' <LValueToRValue>
      |                                                                                                                           |   `-DeclRefExpr 0x5556a36e3878 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                           |-CompoundStmt 0x5556a36e3900 <line:658:2, line:660:2>
      |                                                                                                                           | `-GotoStmt 0x5556a36e38e8 <line:659:2, col:7> 'label_2604' 0x5556a36cc568
      |                                                                                                                           `-CompoundStmt 0x5556a36ede90 <line:662:2, line:964:2>
      |                                                                                                                             |-DeclStmt 0x5556a36e3998 <line:663:2, col:30>
      |                                                                                                                             | `-VarDecl 0x5556a36e3930 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                                                                                                                             |-BinaryOperator 0x5556a36e3a28 <line:664:2, col:51> 'int' '='
      |                                                                                                                             | |-DeclRefExpr 0x5556a36e39b0 <col:2> 'int' lvalue Var 0x5556a36e3930 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                             | `-CallExpr 0x5556a36e3a08 <col:29, col:51> 'int'
      |                                                                                                                             |   `-ImplicitCastExpr 0x5556a36e39f0 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                                                                                                                             |     `-DeclRefExpr 0x5556a36e39d0 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                                                                                                                             `-IfStmt 0x5556a36ede68 <line:665:2, line:963:2> has_else
      |                                                                                                                               |-UnaryOperator 0x5556a36e3ae0 <line:665:6, col:37> 'int' prefix '!' cannot overflow
      |                                                                                                                               | `-ParenExpr 0x5556a36e3ac0 <col:7, col:37> 'int'
      |                                                                                                                               |   `-BinaryOperator 0x5556a36e3aa0 <col:8, col:36> 'int' '=='
      |                                                                                                                               |     |-ImplicitCastExpr 0x5556a36e3a88 <col:8> 'int' <LValueToRValue>
      |                                                                                                                               |     | `-DeclRefExpr 0x5556a36e3a48 <col:8> 'int' lvalue Var 0x5556a36e3930 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                               |     `-IntegerLiteral 0x5556a36e3a68 <col:36> 'int' 0
      |                                                                                                                               |-CompoundStmt 0x5556a36e4f58 <line:666:2, line:698:2>
      |                                                                                                                               | `-CompoundStmt 0x5556a36e4f20 <line:667:2, line:697:2>
      |                                                                                                                               |   |-DeclStmt 0x5556a36e3b78 <line:668:2, col:14>
      |                                                                                                                               |   | `-VarDecl 0x5556a36e3b10 <col:2, col:6> col:6 used __tmp_37 'int'
      |                                                                                                                               |   |-BinaryOperator 0x5556a36e3c28 <line:669:2, col:18> 'int' '='
      |                                                                                                                               |   | |-DeclRefExpr 0x5556a36e3b90 <col:2> 'int' lvalue Var 0x5556a36e3b10 '__tmp_37' 'int'
      |                                                                                                                               |   | `-BinaryOperator 0x5556a36e3c08 <col:13, col:18> 'int' '<='
      |                                                                                                                               |   |   |-IntegerLiteral 0x5556a36e3bb0 <col:13> 'int' 0
      |                                                                                                                               |   |   `-ImplicitCastExpr 0x5556a36e3bf0 <col:18> 'int' <LValueToRValue>
      |                                                                                                                               |   |     `-DeclRefExpr 0x5556a36e3bd0 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                               |   |-DeclStmt 0x5556a36e3cc8 <line:670:2, col:29>
      |                                                                                                                               |   | `-VarDecl 0x5556a36e3c60 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                               |   |-BinaryOperator 0x5556a36e3d38 <line:671:2, col:28> 'int' '='
      |                                                                                                                               |   | |-DeclRefExpr 0x5556a36e3ce0 <col:2> 'int' lvalue Var 0x5556a36e3c60 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                               |   | `-ImplicitCastExpr 0x5556a36e3d20 <col:28> 'int' <LValueToRValue>
      |                                                                                                                               |   |   `-DeclRefExpr 0x5556a36e3d00 <col:28> 'int' lvalue Var 0x5556a36e3b10 '__tmp_37' 'int'
      |                                                                                                                               |   `-IfStmt 0x5556a36e4ef8 <line:672:2, line:696:2> has_else
      |                                                                                                                               |     |-BinaryOperator 0x5556a36e47e8 <line:672:6, col:33> 'int' '=='
      |                                                                                                                               |     | |-ImplicitCastExpr 0x5556a36e47d0 <col:6> 'int' <LValueToRValue>
      |                                                                                                                               |     | | `-DeclRefExpr 0x5556a36e3d58 <col:6> 'int' lvalue Var 0x5556a36e3c60 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                               |     | `-IntegerLiteral 0x5556a36e47b0 <col:33> 'int' 0
      |                                                                                                                               |     |-CompoundStmt 0x5556a36e4850 <line:673:2, line:675:2>
      |                                                                                                                               |     | `-ReturnStmt 0x5556a36e4840 <line:674:2, col:9>
      |                                                                                                                               |     |   `-ImplicitCastExpr 0x5556a36e4828 <col:9> 'int' <LValueToRValue>
      |                                                                                                                               |     |     `-DeclRefExpr 0x5556a36e4808 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                               |     `-CompoundStmt 0x5556a36e4ee0 <line:677:2, line:696:2>
      |                                                                                                                               |       `-CompoundStmt 0x5556a36e4ea8 <line:678:2, line:695:2>
      |                                                                                                                               |         |-DeclStmt 0x5556a36e48e8 <line:679:2, col:14>
      |                                                                                                                               |         | `-VarDecl 0x5556a36e4880 <col:2, col:6> col:6 used __tmp_38 'int'
      |                                                                                                                               |         |-BinaryOperator 0x5556a36e49b0 <line:680:2, col:24> 'int' '='
      |                                                                                                                               |         | |-DeclRefExpr 0x5556a36e4900 <col:2> 'int' lvalue Var 0x5556a36e4880 '__tmp_38' 'int'
      |                                                                                                                               |         | `-BinaryOperator 0x5556a36e4990 <col:13, col:24> 'int' '<='
      |                                                                                                                               |         |   |-ImplicitCastExpr 0x5556a36e4960 <col:13> 'int' <LValueToRValue>
      |                                                                                                                               |         |   | `-DeclRefExpr 0x5556a36e4920 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                               |         |   `-ImplicitCastExpr 0x5556a36e4978 <col:24> 'int' <LValueToRValue>
      |                                                                                                                               |         |     `-DeclRefExpr 0x5556a36e4940 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                               |         |-DeclStmt 0x5556a36e4a50 <line:681:2, col:29>
      |                                                                                                                               |         | `-VarDecl 0x5556a36e49e8 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                               |         |-BinaryOperator 0x5556a36e4ac0 <line:682:2, col:28> 'int' '='
      |                                                                                                                               |         | |-DeclRefExpr 0x5556a36e4a68 <col:2> 'int' lvalue Var 0x5556a36e49e8 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                               |         | `-ImplicitCastExpr 0x5556a36e4aa8 <col:28> 'int' <LValueToRValue>
      |                                                                                                                               |         |   `-DeclRefExpr 0x5556a36e4a88 <col:28> 'int' lvalue Var 0x5556a36e4880 '__tmp_38' 'int'
      |                                                                                                                               |         `-IfStmt 0x5556a36e4e80 <line:683:2, line:694:2> has_else
      |                                                                                                                               |           |-BinaryOperator 0x5556a36e4b38 <line:683:6, col:33> 'int' '=='
      |                                                                                                                               |           | |-ImplicitCastExpr 0x5556a36e4b20 <col:6> 'int' <LValueToRValue>
      |                                                                                                                               |           | | `-DeclRefExpr 0x5556a36e4ae0 <col:6> 'int' lvalue Var 0x5556a36e49e8 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                               |           | `-IntegerLiteral 0x5556a36e4b00 <col:33> 'int' 0
      |                                                                                                                               |           |-CompoundStmt 0x5556a36e4ba0 <line:684:2, line:686:2>
      |                                                                                                                               |           | `-ReturnStmt 0x5556a36e4b90 <line:685:2, col:9>
      |                                                                                                                               |           |   `-ImplicitCastExpr 0x5556a36e4b78 <col:9> 'int' <LValueToRValue>
      |                                                                                                                               |           |     `-DeclRefExpr 0x5556a36e4b58 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                               |           `-CompoundStmt 0x5556a36e4e48 <line:688:2, line:694:2>
      |                                                                                                                               |             |-DeclStmt 0x5556a36e4c70 <line:689:2, col:40>
      |                                                                                                                               |             | `-VarDecl 0x5556a36e4bd0 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                                                                                                                               |             |   `-ImplicitCastExpr 0x5556a36e4c58 <col:33> 'int' <LValueToRValue>
      |                                                                                                                               |             |     `-DeclRefExpr 0x5556a36e4c38 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                               |             |-BinaryOperator 0x5556a36e4d20 <line:690:2, col:22> 'int' '='
      |                                                                                                                               |             | |-DeclRefExpr 0x5556a36e4c88 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                               |             | `-BinaryOperator 0x5556a36e4d00 <col:12, col:22> 'int' '+'
      |                                                                                                                               |             |   |-ImplicitCastExpr 0x5556a36e4ce8 <col:12> 'int' <LValueToRValue>
      |                                                                                                                               |             |   | `-DeclRefExpr 0x5556a36e4ca8 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                               |             |   `-IntegerLiteral 0x5556a36e4cc8 <col:22> 'int' 1
      |                                                                                                                               |             |-BinaryOperator 0x5556a36e4d98 <line:691:2, col:17> 'int' '='
      |                                                                                                                               |             | |-DeclRefExpr 0x5556a36e4d40 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                                                                                                                               |             | `-ImplicitCastExpr 0x5556a36e4d80 <col:17> 'int' <LValueToRValue>
      |                                                                                                                               |             |   `-DeclRefExpr 0x5556a36e4d60 <col:17> 'int' lvalue Var 0x5556a36e3930 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                               |             |-BinaryOperator 0x5556a36e4e10 <line:692:2, col:17> 'int' '='
      |                                                                                                                               |             | |-DeclRefExpr 0x5556a36e4db8 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                                                                                                                               |             | `-ImplicitCastExpr 0x5556a36e4df8 <col:17> 'int' <LValueToRValue>
      |                                                                                                                               |             |   `-DeclRefExpr 0x5556a36e4dd8 <col:17> 'int' lvalue Var 0x5556a36e4bd0 'main____CPAchecker_TMP_2' 'int'
      |                                                                                                                               |             `-GotoStmt 0x5556a36e4e30 <line:693:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                                                                                                                               `-CompoundStmt 0x5556a36ede50 <line:700:2, line:963:2>
      |                                                                                                                                 `-CompoundStmt 0x5556a36ede18 <line:701:2, line:962:2>
      |                                                                                                                                   |-DeclStmt 0x5556a36e4ff0 <line:702:2, col:14>
      |                                                                                                                                   | `-VarDecl 0x5556a36e4f88 <col:2, col:6> col:6 used __tmp_39 'int'
      |                                                                                                                                   |-BinaryOperator 0x5556a36e50a0 <line:703:2, col:18> 'int' '='
      |                                                                                                                                   | |-DeclRefExpr 0x5556a36e5008 <col:2> 'int' lvalue Var 0x5556a36e4f88 '__tmp_39' 'int'
      |                                                                                                                                   | `-BinaryOperator 0x5556a36e5080 <col:13, col:18> 'int' '<='
      |                                                                                                                                   |   |-IntegerLiteral 0x5556a36e5028 <col:13> 'int' 0
      |                                                                                                                                   |   `-ImplicitCastExpr 0x5556a36e5068 <col:18> 'int' <LValueToRValue>
      |                                                                                                                                   |     `-DeclRefExpr 0x5556a36e5048 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                   |-DeclStmt 0x5556a36e5140 <line:704:2, col:29>
      |                                                                                                                                   | `-VarDecl 0x5556a36e50d8 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                   |-BinaryOperator 0x5556a36e51b0 <line:705:2, col:28> 'int' '='
      |                                                                                                                                   | |-DeclRefExpr 0x5556a36e5158 <col:2> 'int' lvalue Var 0x5556a36e50d8 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                   | `-ImplicitCastExpr 0x5556a36e5198 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                   |   `-DeclRefExpr 0x5556a36e5178 <col:28> 'int' lvalue Var 0x5556a36e4f88 '__tmp_39' 'int'
      |                                                                                                                                   `-IfStmt 0x5556a36eddf0 <line:706:2, line:961:2> has_else
      |                                                                                                                                     |-BinaryOperator 0x5556a36e5228 <line:706:6, col:33> 'int' '=='
      |                                                                                                                                     | |-ImplicitCastExpr 0x5556a36e5210 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                     | | `-DeclRefExpr 0x5556a36e51d0 <col:6> 'int' lvalue Var 0x5556a36e50d8 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                     | `-IntegerLiteral 0x5556a36e51f0 <col:33> 'int' 0
      |                                                                                                                                     |-CompoundStmt 0x5556a36e5290 <line:707:2, line:709:2>
      |                                                                                                                                     | `-ReturnStmt 0x5556a36e5280 <line:708:2, col:9>
      |                                                                                                                                     |   `-ImplicitCastExpr 0x5556a36e5268 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                     |     `-DeclRefExpr 0x5556a36e5248 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                     `-CompoundStmt 0x5556a36eddd8 <line:711:2, line:961:2>
      |                                                                                                                                       `-CompoundStmt 0x5556a36edda0 <line:712:2, line:960:2>
      |                                                                                                                                         |-DeclStmt 0x5556a36e5328 <line:713:2, col:14>
      |                                                                                                                                         | `-VarDecl 0x5556a36e52c0 <col:2, col:6> col:6 used __tmp_40 'int'
      |                                                                                                                                         |-BinaryOperator 0x5556a36e53f0 <line:714:2, col:24> 'int' '='
      |                                                                                                                                         | |-DeclRefExpr 0x5556a36e5340 <col:2> 'int' lvalue Var 0x5556a36e52c0 '__tmp_40' 'int'
      |                                                                                                                                         | `-BinaryOperator 0x5556a36e53d0 <col:13, col:24> 'int' '<='
      |                                                                                                                                         |   |-ImplicitCastExpr 0x5556a36e53a0 <col:13> 'int' <LValueToRValue>
      |                                                                                                                                         |   | `-DeclRefExpr 0x5556a36e5360 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                         |   `-ImplicitCastExpr 0x5556a36e53b8 <col:24> 'int' <LValueToRValue>
      |                                                                                                                                         |     `-DeclRefExpr 0x5556a36e5380 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                         |-DeclStmt 0x5556a36e5490 <line:715:2, col:29>
      |                                                                                                                                         | `-VarDecl 0x5556a36e5428 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                         |-BinaryOperator 0x5556a36e5500 <line:716:2, col:28> 'int' '='
      |                                                                                                                                         | |-DeclRefExpr 0x5556a36e54a8 <col:2> 'int' lvalue Var 0x5556a36e5428 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                         | `-ImplicitCastExpr 0x5556a36e54e8 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                         |   `-DeclRefExpr 0x5556a36e54c8 <col:28> 'int' lvalue Var 0x5556a36e52c0 '__tmp_40' 'int'
      |                                                                                                                                         `-IfStmt 0x5556a36edd78 <line:717:2, line:959:2> has_else
      |                                                                                                                                           |-BinaryOperator 0x5556a36e5578 <line:717:6, col:33> 'int' '=='
      |                                                                                                                                           | |-ImplicitCastExpr 0x5556a36e5560 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                           | | `-DeclRefExpr 0x5556a36e5520 <col:6> 'int' lvalue Var 0x5556a36e5428 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                           | `-IntegerLiteral 0x5556a36e5540 <col:33> 'int' 0
      |                                                                                                                                           |-CompoundStmt 0x5556a36e55e0 <line:718:2, line:720:2>
      |                                                                                                                                           | `-ReturnStmt 0x5556a36e55d0 <line:719:2, col:9>
      |                                                                                                                                           |   `-ImplicitCastExpr 0x5556a36e55b8 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                           |     `-DeclRefExpr 0x5556a36e5598 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                           `-CompoundStmt 0x5556a36edd50 <line:722:2, line:959:2>
      |                                                                                                                                             |-DeclStmt 0x5556a36e56b0 <line:723:2, col:40>
      |                                                                                                                                             | `-VarDecl 0x5556a36e5610 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
      |                                                                                                                                             |   `-ImplicitCastExpr 0x5556a36e5698 <col:33> 'int' <LValueToRValue>
      |                                                                                                                                             |     `-DeclRefExpr 0x5556a36e5678 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                             |-BinaryOperator 0x5556a36e5760 <line:724:2, col:22> 'int' '='
      |                                                                                                                                             | |-DeclRefExpr 0x5556a36e56c8 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                             | `-BinaryOperator 0x5556a36e5740 <col:12, col:22> 'int' '+'
      |                                                                                                                                             |   |-ImplicitCastExpr 0x5556a36e5728 <col:12> 'int' <LValueToRValue>
      |                                                                                                                                             |   | `-DeclRefExpr 0x5556a36e56e8 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                             |   `-IntegerLiteral 0x5556a36e5708 <col:22> 'int' 1
      |                                                                                                                                             `-IfStmt 0x5556a36edd28 <line:725:2, line:958:2> has_else
      |                                                                                                                                               |-BinaryOperator 0x5556a36e6080 <line:725:6, col:17> 'int' '=='
      |                                                                                                                                               | |-ImplicitCastExpr 0x5556a36e6050 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                               | | `-DeclRefExpr 0x5556a36e5780 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                               | `-ImplicitCastExpr 0x5556a36e6068 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                               |   `-DeclRefExpr 0x5556a36e6030 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                               |-CompoundStmt 0x5556a36e60b8 <line:726:2, line:728:2>
      |                                                                                                                                               | `-GotoStmt 0x5556a36e60a0 <line:727:2, col:7> 'label_2604' 0x5556a36cc568
      |                                                                                                                                               `-CompoundStmt 0x5556a36edd00 <line:730:2, line:958:2>
      |                                                                                                                                                 |-DeclStmt 0x5556a36e6150 <line:731:2, col:30>
      |                                                                                                                                                 | `-VarDecl 0x5556a36e60e8 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                                                                                                                                                 |-BinaryOperator 0x5556a36e61e0 <line:732:2, col:51> 'int' '='
      |                                                                                                                                                 | |-DeclRefExpr 0x5556a36e6168 <col:2> 'int' lvalue Var 0x5556a36e60e8 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                 | `-CallExpr 0x5556a36e61c0 <col:29, col:51> 'int'
      |                                                                                                                                                 |   `-ImplicitCastExpr 0x5556a36e61a8 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                                                                                                                                                 |     `-DeclRefExpr 0x5556a36e6188 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                                                                                                                                                 `-IfStmt 0x5556a36edcd8 <line:733:2, line:957:2> has_else
      |                                                                                                                                                   |-UnaryOperator 0x5556a36e6298 <line:733:6, col:37> 'int' prefix '!' cannot overflow
      |                                                                                                                                                   | `-ParenExpr 0x5556a36e6278 <col:7, col:37> 'int'
      |                                                                                                                                                   |   `-BinaryOperator 0x5556a36e6258 <col:8, col:36> 'int' '=='
      |                                                                                                                                                   |     |-ImplicitCastExpr 0x5556a36e6240 <col:8> 'int' <LValueToRValue>
      |                                                                                                                                                   |     | `-DeclRefExpr 0x5556a36e6200 <col:8> 'int' lvalue Var 0x5556a36e60e8 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                   |     `-IntegerLiteral 0x5556a36e6220 <col:36> 'int' 0
      |                                                                                                                                                   |-CompoundStmt 0x5556a36e6cd8 <line:734:2, line:766:2>
      |                                                                                                                                                   | `-CompoundStmt 0x5556a36e6ca0 <line:735:2, line:765:2>
      |                                                                                                                                                   |   |-DeclStmt 0x5556a36e6330 <line:736:2, col:14>
      |                                                                                                                                                   |   | `-VarDecl 0x5556a36e62c8 <col:2, col:6> col:6 used __tmp_41 'int'
      |                                                                                                                                                   |   |-BinaryOperator 0x5556a36e63e0 <line:737:2, col:18> 'int' '='
      |                                                                                                                                                   |   | |-DeclRefExpr 0x5556a36e6348 <col:2> 'int' lvalue Var 0x5556a36e62c8 '__tmp_41' 'int'
      |                                                                                                                                                   |   | `-BinaryOperator 0x5556a36e63c0 <col:13, col:18> 'int' '<='
      |                                                                                                                                                   |   |   |-IntegerLiteral 0x5556a36e6368 <col:13> 'int' 0
      |                                                                                                                                                   |   |   `-ImplicitCastExpr 0x5556a36e63a8 <col:18> 'int' <LValueToRValue>
      |                                                                                                                                                   |   |     `-DeclRefExpr 0x5556a36e6388 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                   |   |-DeclStmt 0x5556a36e6480 <line:738:2, col:29>
      |                                                                                                                                                   |   | `-VarDecl 0x5556a36e6418 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                   |   |-BinaryOperator 0x5556a36e64f0 <line:739:2, col:28> 'int' '='
      |                                                                                                                                                   |   | |-DeclRefExpr 0x5556a36e6498 <col:2> 'int' lvalue Var 0x5556a36e6418 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                   |   | `-ImplicitCastExpr 0x5556a36e64d8 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                   |   |   `-DeclRefExpr 0x5556a36e64b8 <col:28> 'int' lvalue Var 0x5556a36e62c8 '__tmp_41' 'int'
      |                                                                                                                                                   |   `-IfStmt 0x5556a36e6c78 <line:740:2, line:764:2> has_else
      |                                                                                                                                                   |     |-BinaryOperator 0x5556a36e6568 <line:740:6, col:33> 'int' '=='
      |                                                                                                                                                   |     | |-ImplicitCastExpr 0x5556a36e6550 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                   |     | | `-DeclRefExpr 0x5556a36e6510 <col:6> 'int' lvalue Var 0x5556a36e6418 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                   |     | `-IntegerLiteral 0x5556a36e6530 <col:33> 'int' 0
      |                                                                                                                                                   |     |-CompoundStmt 0x5556a36e65d0 <line:741:2, line:743:2>
      |                                                                                                                                                   |     | `-ReturnStmt 0x5556a36e65c0 <line:742:2, col:9>
      |                                                                                                                                                   |     |   `-ImplicitCastExpr 0x5556a36e65a8 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                   |     |     `-DeclRefExpr 0x5556a36e6588 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                   |     `-CompoundStmt 0x5556a36e6c60 <line:745:2, line:764:2>
      |                                                                                                                                                   |       `-CompoundStmt 0x5556a36e6c28 <line:746:2, line:763:2>
      |                                                                                                                                                   |         |-DeclStmt 0x5556a36e6668 <line:747:2, col:14>
      |                                                                                                                                                   |         | `-VarDecl 0x5556a36e6600 <col:2, col:6> col:6 used __tmp_42 'int'
      |                                                                                                                                                   |         |-BinaryOperator 0x5556a36e6730 <line:748:2, col:24> 'int' '='
      |                                                                                                                                                   |         | |-DeclRefExpr 0x5556a36e6680 <col:2> 'int' lvalue Var 0x5556a36e6600 '__tmp_42' 'int'
      |                                                                                                                                                   |         | `-BinaryOperator 0x5556a36e6710 <col:13, col:24> 'int' '<='
      |                                                                                                                                                   |         |   |-ImplicitCastExpr 0x5556a36e66e0 <col:13> 'int' <LValueToRValue>
      |                                                                                                                                                   |         |   | `-DeclRefExpr 0x5556a36e66a0 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                   |         |   `-ImplicitCastExpr 0x5556a36e66f8 <col:24> 'int' <LValueToRValue>
      |                                                                                                                                                   |         |     `-DeclRefExpr 0x5556a36e66c0 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                                   |         |-DeclStmt 0x5556a36e67d0 <line:749:2, col:29>
      |                                                                                                                                                   |         | `-VarDecl 0x5556a36e6768 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                   |         |-BinaryOperator 0x5556a36e6840 <line:750:2, col:28> 'int' '='
      |                                                                                                                                                   |         | |-DeclRefExpr 0x5556a36e67e8 <col:2> 'int' lvalue Var 0x5556a36e6768 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                   |         | `-ImplicitCastExpr 0x5556a36e6828 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                   |         |   `-DeclRefExpr 0x5556a36e6808 <col:28> 'int' lvalue Var 0x5556a36e6600 '__tmp_42' 'int'
      |                                                                                                                                                   |         `-IfStmt 0x5556a36e6c00 <line:751:2, line:762:2> has_else
      |                                                                                                                                                   |           |-BinaryOperator 0x5556a36e68b8 <line:751:6, col:33> 'int' '=='
      |                                                                                                                                                   |           | |-ImplicitCastExpr 0x5556a36e68a0 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                   |           | | `-DeclRefExpr 0x5556a36e6860 <col:6> 'int' lvalue Var 0x5556a36e6768 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                   |           | `-IntegerLiteral 0x5556a36e6880 <col:33> 'int' 0
      |                                                                                                                                                   |           |-CompoundStmt 0x5556a36e6920 <line:752:2, line:754:2>
      |                                                                                                                                                   |           | `-ReturnStmt 0x5556a36e6910 <line:753:2, col:9>
      |                                                                                                                                                   |           |   `-ImplicitCastExpr 0x5556a36e68f8 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                   |           |     `-DeclRefExpr 0x5556a36e68d8 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                   |           `-CompoundStmt 0x5556a36e6bc8 <line:756:2, line:762:2>
      |                                                                                                                                                   |             |-DeclStmt 0x5556a36e69f0 <line:757:2, col:40>
      |                                                                                                                                                   |             | `-VarDecl 0x5556a36e6950 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                                                                                                                                                   |             |   `-ImplicitCastExpr 0x5556a36e69d8 <col:33> 'int' <LValueToRValue>
      |                                                                                                                                                   |             |     `-DeclRefExpr 0x5556a36e69b8 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                   |             |-BinaryOperator 0x5556a36e6aa0 <line:758:2, col:22> 'int' '='
      |                                                                                                                                                   |             | |-DeclRefExpr 0x5556a36e6a08 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                   |             | `-BinaryOperator 0x5556a36e6a80 <col:12, col:22> 'int' '+'
      |                                                                                                                                                   |             |   |-ImplicitCastExpr 0x5556a36e6a68 <col:12> 'int' <LValueToRValue>
      |                                                                                                                                                   |             |   | `-DeclRefExpr 0x5556a36e6a28 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                   |             |   `-IntegerLiteral 0x5556a36e6a48 <col:22> 'int' 1
      |                                                                                                                                                   |             |-BinaryOperator 0x5556a36e6b18 <line:759:2, col:17> 'int' '='
      |                                                                                                                                                   |             | |-DeclRefExpr 0x5556a36e6ac0 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                                                                                                                                                   |             | `-ImplicitCastExpr 0x5556a36e6b00 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                   |             |   `-DeclRefExpr 0x5556a36e6ae0 <col:17> 'int' lvalue Var 0x5556a36e60e8 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                   |             |-BinaryOperator 0x5556a36e6b90 <line:760:2, col:17> 'int' '='
      |                                                                                                                                                   |             | |-DeclRefExpr 0x5556a36e6b38 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                                                                                                                                                   |             | `-ImplicitCastExpr 0x5556a36e6b78 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                   |             |   `-DeclRefExpr 0x5556a36e6b58 <col:17> 'int' lvalue Var 0x5556a36e6950 'main____CPAchecker_TMP_2' 'int'
      |                                                                                                                                                   |             `-GotoStmt 0x5556a36e6bb0 <line:761:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                                                                                                                                                   `-CompoundStmt 0x5556a36edcc0 <line:768:2, line:957:2>
      |                                                                                                                                                     `-CompoundStmt 0x5556a36edc88 <line:769:2, line:956:2>
      |                                                                                                                                                       |-DeclStmt 0x5556a36e6d70 <line:770:2, col:14>
      |                                                                                                                                                       | `-VarDecl 0x5556a36e6d08 <col:2, col:6> col:6 used __tmp_43 'int'
      |                                                                                                                                                       |-BinaryOperator 0x5556a36e6e20 <line:771:2, col:18> 'int' '='
      |                                                                                                                                                       | |-DeclRefExpr 0x5556a36e6d88 <col:2> 'int' lvalue Var 0x5556a36e6d08 '__tmp_43' 'int'
      |                                                                                                                                                       | `-BinaryOperator 0x5556a36e6e00 <col:13, col:18> 'int' '<='
      |                                                                                                                                                       |   |-IntegerLiteral 0x5556a36e6da8 <col:13> 'int' 0
      |                                                                                                                                                       |   `-ImplicitCastExpr 0x5556a36e6de8 <col:18> 'int' <LValueToRValue>
      |                                                                                                                                                       |     `-DeclRefExpr 0x5556a36e6dc8 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                       |-DeclStmt 0x5556a36e6ec0 <line:772:2, col:29>
      |                                                                                                                                                       | `-VarDecl 0x5556a36e6e58 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                       |-BinaryOperator 0x5556a36e6f30 <line:773:2, col:28> 'int' '='
      |                                                                                                                                                       | |-DeclRefExpr 0x5556a36e6ed8 <col:2> 'int' lvalue Var 0x5556a36e6e58 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                       | `-ImplicitCastExpr 0x5556a36e6f18 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                       |   `-DeclRefExpr 0x5556a36e6ef8 <col:28> 'int' lvalue Var 0x5556a36e6d08 '__tmp_43' 'int'
      |                                                                                                                                                       `-IfStmt 0x5556a36edc60 <line:774:2, line:955:2> has_else
      |                                                                                                                                                         |-BinaryOperator 0x5556a36e6fa8 <line:774:6, col:33> 'int' '=='
      |                                                                                                                                                         | |-ImplicitCastExpr 0x5556a36e6f90 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                         | | `-DeclRefExpr 0x5556a36e6f50 <col:6> 'int' lvalue Var 0x5556a36e6e58 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                         | `-IntegerLiteral 0x5556a36e6f70 <col:33> 'int' 0
      |                                                                                                                                                         |-CompoundStmt 0x5556a36e7010 <line:775:2, line:777:2>
      |                                                                                                                                                         | `-ReturnStmt 0x5556a36e7000 <line:776:2, col:9>
      |                                                                                                                                                         |   `-ImplicitCastExpr 0x5556a36e6fe8 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                         |     `-DeclRefExpr 0x5556a36e6fc8 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                         `-CompoundStmt 0x5556a36edc48 <line:779:2, line:955:2>
      |                                                                                                                                                           `-CompoundStmt 0x5556a36edc10 <line:780:2, line:954:2>
      |                                                                                                                                                             |-DeclStmt 0x5556a36e7ff0 <line:781:2, col:14>
      |                                                                                                                                                             | `-VarDecl 0x5556a36e7f88 <col:2, col:6> col:6 used __tmp_44 'int'
      |                                                                                                                                                             |-BinaryOperator 0x5556a36e80b8 <line:782:2, col:24> 'int' '='
      |                                                                                                                                                             | |-DeclRefExpr 0x5556a36e8008 <col:2> 'int' lvalue Var 0x5556a36e7f88 '__tmp_44' 'int'
      |                                                                                                                                                             | `-BinaryOperator 0x5556a36e8098 <col:13, col:24> 'int' '<='
      |                                                                                                                                                             |   |-ImplicitCastExpr 0x5556a36e8068 <col:13> 'int' <LValueToRValue>
      |                                                                                                                                                             |   | `-DeclRefExpr 0x5556a36e8028 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                             |   `-ImplicitCastExpr 0x5556a36e8080 <col:24> 'int' <LValueToRValue>
      |                                                                                                                                                             |     `-DeclRefExpr 0x5556a36e8048 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                                             |-DeclStmt 0x5556a36e8158 <line:783:2, col:29>
      |                                                                                                                                                             | `-VarDecl 0x5556a36e80f0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                             |-BinaryOperator 0x5556a36e81c8 <line:784:2, col:28> 'int' '='
      |                                                                                                                                                             | |-DeclRefExpr 0x5556a36e8170 <col:2> 'int' lvalue Var 0x5556a36e80f0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                             | `-ImplicitCastExpr 0x5556a36e81b0 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                             |   `-DeclRefExpr 0x5556a36e8190 <col:28> 'int' lvalue Var 0x5556a36e7f88 '__tmp_44' 'int'
      |                                                                                                                                                             `-IfStmt 0x5556a36edbe8 <line:785:2, line:953:2> has_else
      |                                                                                                                                                               |-BinaryOperator 0x5556a36e8240 <line:785:6, col:33> 'int' '=='
      |                                                                                                                                                               | |-ImplicitCastExpr 0x5556a36e8228 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                               | | `-DeclRefExpr 0x5556a36e81e8 <col:6> 'int' lvalue Var 0x5556a36e80f0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                               | `-IntegerLiteral 0x5556a36e8208 <col:33> 'int' 0
      |                                                                                                                                                               |-CompoundStmt 0x5556a36e82a8 <line:786:2, line:788:2>
      |                                                                                                                                                               | `-ReturnStmt 0x5556a36e8298 <line:787:2, col:9>
      |                                                                                                                                                               |   `-ImplicitCastExpr 0x5556a36e8280 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                               |     `-DeclRefExpr 0x5556a36e8260 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                               `-CompoundStmt 0x5556a36edbc0 <line:790:2, line:953:2>
      |                                                                                                                                                                 |-DeclStmt 0x5556a36e8378 <line:791:2, col:40>
      |                                                                                                                                                                 | `-VarDecl 0x5556a36e82d8 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
      |                                                                                                                                                                 |   `-ImplicitCastExpr 0x5556a36e8360 <col:33> 'int' <LValueToRValue>
      |                                                                                                                                                                 |     `-DeclRefExpr 0x5556a36e8340 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                 |-BinaryOperator 0x5556a36e8428 <line:792:2, col:22> 'int' '='
      |                                                                                                                                                                 | |-DeclRefExpr 0x5556a36e8390 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                 | `-BinaryOperator 0x5556a36e8408 <col:12, col:22> 'int' '+'
      |                                                                                                                                                                 |   |-ImplicitCastExpr 0x5556a36e83f0 <col:12> 'int' <LValueToRValue>
      |                                                                                                                                                                 |   | `-DeclRefExpr 0x5556a36e83b0 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                 |   `-IntegerLiteral 0x5556a36e83d0 <col:22> 'int' 1
      |                                                                                                                                                                 `-IfStmt 0x5556a36edb98 <line:793:2, line:952:2> has_else
      |                                                                                                                                                                   |-BinaryOperator 0x5556a36e84b8 <line:793:6, col:17> 'int' '=='
      |                                                                                                                                                                   | |-ImplicitCastExpr 0x5556a36e8488 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                   | | `-DeclRefExpr 0x5556a36e8448 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                   | `-ImplicitCastExpr 0x5556a36e84a0 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                   |   `-DeclRefExpr 0x5556a36e8468 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                                                   |-CompoundStmt 0x5556a36e84f0 <line:794:2, line:796:2>
      |                                                                                                                                                                   | `-GotoStmt 0x5556a36e84d8 <line:795:2, col:7> 'label_2604' 0x5556a36cc568
      |                                                                                                                                                                   `-CompoundStmt 0x5556a36edb70 <line:798:2, line:952:2>
      |                                                                                                                                                                     |-DeclStmt 0x5556a36e8588 <line:799:2, col:30>
      |                                                                                                                                                                     | `-VarDecl 0x5556a36e8520 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                                                                                                                                                                     |-BinaryOperator 0x5556a36e8618 <line:800:2, col:51> 'int' '='
      |                                                                                                                                                                     | |-DeclRefExpr 0x5556a36e85a0 <col:2> 'int' lvalue Var 0x5556a36e8520 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                     | `-CallExpr 0x5556a36e85f8 <col:29, col:51> 'int'
      |                                                                                                                                                                     |   `-ImplicitCastExpr 0x5556a36e85e0 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                                                                                                                                                                     |     `-DeclRefExpr 0x5556a36e85c0 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                                                                                                                                                                     `-IfStmt 0x5556a36edb48 <line:801:2, line:951:2> has_else
      |                                                                                                                                                                       |-UnaryOperator 0x5556a36e86d0 <line:801:6, col:37> 'int' prefix '!' cannot overflow
      |                                                                                                                                                                       | `-ParenExpr 0x5556a36e86b0 <col:7, col:37> 'int'
      |                                                                                                                                                                       |   `-BinaryOperator 0x5556a36e8690 <col:8, col:36> 'int' '=='
      |                                                                                                                                                                       |     |-ImplicitCastExpr 0x5556a36e8678 <col:8> 'int' <LValueToRValue>
      |                                                                                                                                                                       |     | `-DeclRefExpr 0x5556a36e8638 <col:8> 'int' lvalue Var 0x5556a36e8520 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                       |     `-IntegerLiteral 0x5556a36e8658 <col:36> 'int' 0
      |                                                                                                                                                                       |-CompoundStmt 0x5556a36ea200 <line:802:2, line:834:2>
      |                                                                                                                                                                       | `-CompoundStmt 0x5556a36ea1c8 <line:803:2, line:833:2>
      |                                                                                                                                                                       |   |-DeclStmt 0x5556a36e8768 <line:804:2, col:14>
      |                                                                                                                                                                       |   | `-VarDecl 0x5556a36e8700 <col:2, col:6> col:6 used __tmp_45 'int'
      |                                                                                                                                                                       |   |-BinaryOperator 0x5556a36e8818 <line:805:2, col:18> 'int' '='
      |                                                                                                                                                                       |   | |-DeclRefExpr 0x5556a36e8780 <col:2> 'int' lvalue Var 0x5556a36e8700 '__tmp_45' 'int'
      |                                                                                                                                                                       |   | `-BinaryOperator 0x5556a36e87f8 <col:13, col:18> 'int' '<='
      |                                                                                                                                                                       |   |   |-IntegerLiteral 0x5556a36e87a0 <col:13> 'int' 0
      |                                                                                                                                                                       |   |   `-ImplicitCastExpr 0x5556a36e87e0 <col:18> 'int' <LValueToRValue>
      |                                                                                                                                                                       |   |     `-DeclRefExpr 0x5556a36e87c0 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                       |   |-DeclStmt 0x5556a36e88b8 <line:806:2, col:29>
      |                                                                                                                                                                       |   | `-VarDecl 0x5556a36e8850 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                                       |   |-BinaryOperator 0x5556a36e8928 <line:807:2, col:28> 'int' '='
      |                                                                                                                                                                       |   | |-DeclRefExpr 0x5556a36e88d0 <col:2> 'int' lvalue Var 0x5556a36e8850 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                       |   | `-ImplicitCastExpr 0x5556a36e8910 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                                       |   |   `-DeclRefExpr 0x5556a36e88f0 <col:28> 'int' lvalue Var 0x5556a36e8700 '__tmp_45' 'int'
      |                                                                                                                                                                       |   `-IfStmt 0x5556a36ea1a0 <line:808:2, line:832:2> has_else
      |                                                                                                                                                                       |     |-BinaryOperator 0x5556a36e89a0 <line:808:6, col:33> 'int' '=='
      |                                                                                                                                                                       |     | |-ImplicitCastExpr 0x5556a36e8988 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                       |     | | `-DeclRefExpr 0x5556a36e8948 <col:6> 'int' lvalue Var 0x5556a36e8850 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                       |     | `-IntegerLiteral 0x5556a36e8968 <col:33> 'int' 0
      |                                                                                                                                                                       |     |-CompoundStmt 0x5556a36e8a08 <line:809:2, line:811:2>
      |                                                                                                                                                                       |     | `-ReturnStmt 0x5556a36e89f8 <line:810:2, col:9>
      |                                                                                                                                                                       |     |   `-ImplicitCastExpr 0x5556a36e89e0 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                                       |     |     `-DeclRefExpr 0x5556a36e89c0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                                       |     `-CompoundStmt 0x5556a36ea188 <line:813:2, line:832:2>
      |                                                                                                                                                                       |       `-CompoundStmt 0x5556a36ea150 <line:814:2, line:831:2>
      |                                                                                                                                                                       |         |-DeclStmt 0x5556a36e8aa0 <line:815:2, col:14>
      |                                                                                                                                                                       |         | `-VarDecl 0x5556a36e8a38 <col:2, col:6> col:6 used __tmp_46 'int'
      |                                                                                                                                                                       |         |-BinaryOperator 0x5556a36e8b68 <line:816:2, col:24> 'int' '='
      |                                                                                                                                                                       |         | |-DeclRefExpr 0x5556a36e8ab8 <col:2> 'int' lvalue Var 0x5556a36e8a38 '__tmp_46' 'int'
      |                                                                                                                                                                       |         | `-BinaryOperator 0x5556a36e8b48 <col:13, col:24> 'int' '<='
      |                                                                                                                                                                       |         |   |-ImplicitCastExpr 0x5556a36e8b18 <col:13> 'int' <LValueToRValue>
      |                                                                                                                                                                       |         |   | `-DeclRefExpr 0x5556a36e8ad8 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                       |         |   `-ImplicitCastExpr 0x5556a36e8b30 <col:24> 'int' <LValueToRValue>
      |                                                                                                                                                                       |         |     `-DeclRefExpr 0x5556a36e8af8 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                                                       |         |-DeclStmt 0x5556a36e8c08 <line:817:2, col:29>
      |                                                                                                                                                                       |         | `-VarDecl 0x5556a36e8ba0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                                       |         |-BinaryOperator 0x5556a36e8c78 <line:818:2, col:28> 'int' '='
      |                                                                                                                                                                       |         | |-DeclRefExpr 0x5556a36e8c20 <col:2> 'int' lvalue Var 0x5556a36e8ba0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                       |         | `-ImplicitCastExpr 0x5556a36e8c60 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                                       |         |   `-DeclRefExpr 0x5556a36e8c40 <col:28> 'int' lvalue Var 0x5556a36e8a38 '__tmp_46' 'int'
      |                                                                                                                                                                       |         `-IfStmt 0x5556a36ea128 <line:819:2, line:830:2> has_else
      |                                                                                                                                                                       |           |-BinaryOperator 0x5556a36e8cf0 <line:819:6, col:33> 'int' '=='
      |                                                                                                                                                                       |           | |-ImplicitCastExpr 0x5556a36e8cd8 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                       |           | | `-DeclRefExpr 0x5556a36e8c98 <col:6> 'int' lvalue Var 0x5556a36e8ba0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                       |           | `-IntegerLiteral 0x5556a36e8cb8 <col:33> 'int' 0
      |                                                                                                                                                                       |           |-CompoundStmt 0x5556a36e8d58 <line:820:2, line:822:2>
      |                                                                                                                                                                       |           | `-ReturnStmt 0x5556a36e8d48 <line:821:2, col:9>
      |                                                                                                                                                                       |           |   `-ImplicitCastExpr 0x5556a36e8d30 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                                       |           |     `-DeclRefExpr 0x5556a36e8d10 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                                       |           `-CompoundStmt 0x5556a36ea0f0 <line:824:2, line:830:2>
      |                                                                                                                                                                       |             |-DeclStmt 0x5556a36e8e28 <line:825:2, col:40>
      |                                                                                                                                                                       |             | `-VarDecl 0x5556a36e8d88 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                                                                                                                                                                       |             |   `-ImplicitCastExpr 0x5556a36e8e10 <col:33> 'int' <LValueToRValue>
      |                                                                                                                                                                       |             |     `-DeclRefExpr 0x5556a36e8df0 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                       |             |-BinaryOperator 0x5556a36e8ed8 <line:826:2, col:22> 'int' '='
      |                                                                                                                                                                       |             | |-DeclRefExpr 0x5556a36e8e40 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                       |             | `-BinaryOperator 0x5556a36e8eb8 <col:12, col:22> 'int' '+'
      |                                                                                                                                                                       |             |   |-ImplicitCastExpr 0x5556a36e8ea0 <col:12> 'int' <LValueToRValue>
      |                                                                                                                                                                       |             |   | `-DeclRefExpr 0x5556a36e8e60 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                       |             |   `-IntegerLiteral 0x5556a36e8e80 <col:22> 'int' 1
      |                                                                                                                                                                       |             |-BinaryOperator 0x5556a36e8f50 <line:827:2, col:17> 'int' '='
      |                                                                                                                                                                       |             | |-DeclRefExpr 0x5556a36e8ef8 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                                                                                                                                                                       |             | `-ImplicitCastExpr 0x5556a36e8f38 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                       |             |   `-DeclRefExpr 0x5556a36e8f18 <col:17> 'int' lvalue Var 0x5556a36e8520 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                       |             |-BinaryOperator 0x5556a36ea0b8 <line:828:2, col:17> 'int' '='
      |                                                                                                                                                                       |             | |-DeclRefExpr 0x5556a36ea060 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                                                                                                                                                                       |             | `-ImplicitCastExpr 0x5556a36ea0a0 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                       |             |   `-DeclRefExpr 0x5556a36ea080 <col:17> 'int' lvalue Var 0x5556a36e8d88 'main____CPAchecker_TMP_2' 'int'
      |                                                                                                                                                                       |             `-GotoStmt 0x5556a36ea0d8 <line:829:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                                                                                                                                                                       `-CompoundStmt 0x5556a36edb30 <line:836:2, line:951:2>
      |                                                                                                                                                                         `-CompoundStmt 0x5556a36edaf8 <line:837:2, line:950:2>
      |                                                                                                                                                                           |-DeclStmt 0x5556a36ea298 <line:838:2, col:14>
      |                                                                                                                                                                           | `-VarDecl 0x5556a36ea230 <col:2, col:6> col:6 used __tmp_47 'int'
      |                                                                                                                                                                           |-BinaryOperator 0x5556a36ea348 <line:839:2, col:18> 'int' '='
      |                                                                                                                                                                           | |-DeclRefExpr 0x5556a36ea2b0 <col:2> 'int' lvalue Var 0x5556a36ea230 '__tmp_47' 'int'
      |                                                                                                                                                                           | `-BinaryOperator 0x5556a36ea328 <col:13, col:18> 'int' '<='
      |                                                                                                                                                                           |   |-IntegerLiteral 0x5556a36ea2d0 <col:13> 'int' 0
      |                                                                                                                                                                           |   `-ImplicitCastExpr 0x5556a36ea310 <col:18> 'int' <LValueToRValue>
      |                                                                                                                                                                           |     `-DeclRefExpr 0x5556a36ea2f0 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                           |-DeclStmt 0x5556a36ea3e8 <line:840:2, col:29>
      |                                                                                                                                                                           | `-VarDecl 0x5556a36ea380 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                                           |-BinaryOperator 0x5556a36ea458 <line:841:2, col:28> 'int' '='
      |                                                                                                                                                                           | |-DeclRefExpr 0x5556a36ea400 <col:2> 'int' lvalue Var 0x5556a36ea380 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                           | `-ImplicitCastExpr 0x5556a36ea440 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                                           |   `-DeclRefExpr 0x5556a36ea420 <col:28> 'int' lvalue Var 0x5556a36ea230 '__tmp_47' 'int'
      |                                                                                                                                                                           `-IfStmt 0x5556a36edad0 <line:842:2, line:949:2> has_else
      |                                                                                                                                                                             |-BinaryOperator 0x5556a36ea4d0 <line:842:6, col:33> 'int' '=='
      |                                                                                                                                                                             | |-ImplicitCastExpr 0x5556a36ea4b8 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                             | | `-DeclRefExpr 0x5556a36ea478 <col:6> 'int' lvalue Var 0x5556a36ea380 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                             | `-IntegerLiteral 0x5556a36ea498 <col:33> 'int' 0
      |                                                                                                                                                                             |-CompoundStmt 0x5556a36ea538 <line:843:2, line:845:2>
      |                                                                                                                                                                             | `-ReturnStmt 0x5556a36ea528 <line:844:2, col:9>
      |                                                                                                                                                                             |   `-ImplicitCastExpr 0x5556a36ea510 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                                             |     `-DeclRefExpr 0x5556a36ea4f0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                                             `-CompoundStmt 0x5556a36edab8 <line:847:2, line:949:2>
      |                                                                                                                                                                               `-CompoundStmt 0x5556a36eda80 <line:848:2, line:948:2>
      |                                                                                                                                                                                 |-DeclStmt 0x5556a36ea5d0 <line:849:2, col:14>
      |                                                                                                                                                                                 | `-VarDecl 0x5556a36ea568 <col:2, col:6> col:6 used __tmp_48 'int'
      |                                                                                                                                                                                 |-BinaryOperator 0x5556a36ea698 <line:850:2, col:24> 'int' '='
      |                                                                                                                                                                                 | |-DeclRefExpr 0x5556a36ea5e8 <col:2> 'int' lvalue Var 0x5556a36ea568 '__tmp_48' 'int'
      |                                                                                                                                                                                 | `-BinaryOperator 0x5556a36ea678 <col:13, col:24> 'int' '<='
      |                                                                                                                                                                                 |   |-ImplicitCastExpr 0x5556a36ea648 <col:13> 'int' <LValueToRValue>
      |                                                                                                                                                                                 |   | `-DeclRefExpr 0x5556a36ea608 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                 |   `-ImplicitCastExpr 0x5556a36ea660 <col:24> 'int' <LValueToRValue>
      |                                                                                                                                                                                 |     `-DeclRefExpr 0x5556a36ea628 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                                                                 |-DeclStmt 0x5556a36ea738 <line:851:2, col:29>
      |                                                                                                                                                                                 | `-VarDecl 0x5556a36ea6d0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                                                 |-BinaryOperator 0x5556a36ea7a8 <line:852:2, col:28> 'int' '='
      |                                                                                                                                                                                 | |-DeclRefExpr 0x5556a36ea750 <col:2> 'int' lvalue Var 0x5556a36ea6d0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                 | `-ImplicitCastExpr 0x5556a36ea790 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                                                 |   `-DeclRefExpr 0x5556a36ea770 <col:28> 'int' lvalue Var 0x5556a36ea568 '__tmp_48' 'int'
      |                                                                                                                                                                                 `-IfStmt 0x5556a36eda58 <line:853:2, line:947:2> has_else
      |                                                                                                                                                                                   |-BinaryOperator 0x5556a36ea820 <line:853:6, col:33> 'int' '=='
      |                                                                                                                                                                                   | |-ImplicitCastExpr 0x5556a36ea808 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                                   | | `-DeclRefExpr 0x5556a36ea7c8 <col:6> 'int' lvalue Var 0x5556a36ea6d0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                   | `-IntegerLiteral 0x5556a36ea7e8 <col:33> 'int' 0
      |                                                                                                                                                                                   |-CompoundStmt 0x5556a36ea888 <line:854:2, line:856:2>
      |                                                                                                                                                                                   | `-ReturnStmt 0x5556a36ea878 <line:855:2, col:9>
      |                                                                                                                                                                                   |   `-ImplicitCastExpr 0x5556a36ea860 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                                                   |     `-DeclRefExpr 0x5556a36ea840 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                                                   `-CompoundStmt 0x5556a36eda08 <line:858:2, line:947:2>
      |                                                                                                                                                                                     |-DeclStmt 0x5556a36ea958 <line:859:2, col:40>
      |                                                                                                                                                                                     | `-VarDecl 0x5556a36ea8b8 <col:2, col:33> col:6 used main____CPAchecker_TMP_1 'int' cinit
      |                                                                                                                                                                                     |   `-ImplicitCastExpr 0x5556a36ea940 <col:33> 'int' <LValueToRValue>
      |                                                                                                                                                                                     |     `-DeclRefExpr 0x5556a36ea920 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                     |-BinaryOperator 0x5556a36eaa08 <line:860:2, col:22> 'int' '='
      |                                                                                                                                                                                     | |-DeclRefExpr 0x5556a36ea970 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                     | `-BinaryOperator 0x5556a36ea9e8 <col:12, col:22> 'int' '+'
      |                                                                                                                                                                                     |   |-ImplicitCastExpr 0x5556a36ea9d0 <col:12> 'int' <LValueToRValue>
      |                                                                                                                                                                                     |   | `-DeclRefExpr 0x5556a36ea990 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                     |   `-IntegerLiteral 0x5556a36ea9b0 <col:22> 'int' 1
      |                                                                                                                                                                                     |-BinaryOperator 0x5556a36eaa80 <line:861:2, col:17> 'int' '='
      |                                                                                                                                                                                     | |-DeclRefExpr 0x5556a36eaa28 <col:2> 'int' lvalue Var 0x5556a36cbf98 '__tmp_3137_0' 'int'
      |                                                                                                                                                                                     | `-ImplicitCastExpr 0x5556a36eaa68 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                                     |   `-DeclRefExpr 0x5556a36eaa48 <col:17> 'int' lvalue Var 0x5556a36ea8b8 'main____CPAchecker_TMP_1' 'int'
      |                                                                                                                                                                                     |-BinaryOperator 0x5556a36eaaf8 <line:862:2, col:17> 'int' '='
      |                                                                                                                                                                                     | |-DeclRefExpr 0x5556a36eaaa0 <col:2> 'int' lvalue Var 0x5556a36cc018 '__tmp_3137_1' 'int'
      |                                                                                                                                                                                     | `-ImplicitCastExpr 0x5556a36eaae0 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                                     |   `-DeclRefExpr 0x5556a36eaac0 <col:17> 'int' lvalue Var 0x5556a36e8520 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                                     |-LabelStmt 0x5556a36eab70 <line:863:2, col:13> 'label_3137'
      |                                                                                                                                                                                     | `-NullStmt 0x5556a36eab18 <col:13>
      |                                                                                                                                                                                     |-BinaryOperator 0x5556a36eabe0 <line:864:2, col:29> 'int' '='
      |                                                                                                                                                                                     | |-DeclRefExpr 0x5556a36eab88 <col:2> 'int' lvalue Var 0x5556a36ea8b8 'main____CPAchecker_TMP_1' 'int'
      |                                                                                                                                                                                     | `-ImplicitCastExpr 0x5556a36eabc8 <col:29> 'int' <LValueToRValue>
      |                                                                                                                                                                                     |   `-DeclRefExpr 0x5556a36eaba8 <col:29> 'int' lvalue Var 0x5556a36cbf98 '__tmp_3137_0' 'int'
      |                                                                                                                                                                                     |-BinaryOperator 0x5556a36eac58 <line:865:2, col:29> 'int' '='
      |                                                                                                                                                                                     | |-DeclRefExpr 0x5556a36eac00 <col:2> 'int' lvalue Var 0x5556a36e8520 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                                     | `-ImplicitCastExpr 0x5556a36eac40 <col:29> 'int' <LValueToRValue>
      |                                                                                                                                                                                     |   `-DeclRefExpr 0x5556a36eac20 <col:29> 'int' lvalue Var 0x5556a36cc018 '__tmp_3137_1' 'int'
      |                                                                                                                                                                                     `-IfStmt 0x5556a36ed9e0 <line:866:2, line:946:2> has_else
      |                                                                                                                                                                                       |-BinaryOperator 0x5556a36eace8 <line:866:6, col:17> 'int' '=='
      |                                                                                                                                                                                       | |-ImplicitCastExpr 0x5556a36eacb8 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                                       | | `-DeclRefExpr 0x5556a36eac78 <col:6> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                       | `-ImplicitCastExpr 0x5556a36eacd0 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                                       |   `-DeclRefExpr 0x5556a36eac98 <col:17> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                                                                       |-CompoundStmt 0x5556a36ead20 <line:867:2, line:869:2>
      |                                                                                                                                                                                       | `-GotoStmt 0x5556a36ead08 <line:868:2, col:7> 'label_2604' 0x5556a36cc568
      |                                                                                                                                                                                       `-CompoundStmt 0x5556a36ed9b8 <line:871:2, line:946:2>
      |                                                                                                                                                                                         |-DeclStmt 0x5556a36eadb8 <line:872:2, col:30>
      |                                                                                                                                                                                         | `-VarDecl 0x5556a36ead50 <col:2, col:6> col:6 used main____CPAchecker_TMP_0 'int'
      |                                                                                                                                                                                         |-BinaryOperator 0x5556a36eae48 <line:873:2, col:51> 'int' '='
      |                                                                                                                                                                                         | |-DeclRefExpr 0x5556a36eadd0 <col:2> 'int' lvalue Var 0x5556a36ead50 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                                         | `-CallExpr 0x5556a36eae28 <col:29, col:51> 'int'
      |                                                                                                                                                                                         |   `-ImplicitCastExpr 0x5556a36eae10 <col:29> 'int (*)()' <FunctionToPointerDecay>
      |                                                                                                                                                                                         |     `-DeclRefExpr 0x5556a36eadf0 <col:29> 'int ()' Function 0x5556a36cbc98 '__VERIFIER_nondet_int' 'int ()'
      |                                                                                                                                                                                         `-IfStmt 0x5556a36ed990 <line:874:2, line:945:2> has_else
      |                                                                                                                                                                                           |-UnaryOperator 0x5556a36eaf00 <line:874:6, col:37> 'int' prefix '!' cannot overflow
      |                                                                                                                                                                                           | `-ParenExpr 0x5556a36eaee0 <col:7, col:37> 'int'
      |                                                                                                                                                                                           |   `-BinaryOperator 0x5556a36eaec0 <col:8, col:36> 'int' '=='
      |                                                                                                                                                                                           |     |-ImplicitCastExpr 0x5556a36eaea8 <col:8> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |     | `-DeclRefExpr 0x5556a36eae68 <col:8> 'int' lvalue Var 0x5556a36ead50 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                                           |     `-IntegerLiteral 0x5556a36eae88 <col:36> 'int' 0
      |                                                                                                                                                                                           |-CompoundStmt 0x5556a36ec2c8 <line:875:2, line:909:2>
      |                                                                                                                                                                                           | `-CompoundStmt 0x5556a36ec290 <line:876:2, line:908:2>
      |                                                                                                                                                                                           |   |-DeclStmt 0x5556a36eaf98 <line:877:2, col:14>
      |                                                                                                                                                                                           |   | `-VarDecl 0x5556a36eaf30 <col:2, col:6> col:6 used __tmp_49 'int'
      |                                                                                                                                                                                           |   |-BinaryOperator 0x5556a36eb8e0 <line:878:2, col:18> 'int' '='
      |                                                                                                                                                                                           |   | |-DeclRefExpr 0x5556a36eafb0 <col:2> 'int' lvalue Var 0x5556a36eaf30 '__tmp_49' 'int'
      |                                                                                                                                                                                           |   | `-BinaryOperator 0x5556a36eb028 <col:13, col:18> 'int' '<='
      |                                                                                                                                                                                           |   |   |-IntegerLiteral 0x5556a36eafd0 <col:13> 'int' 0
      |                                                                                                                                                                                           |   |   `-ImplicitCastExpr 0x5556a36eb010 <col:18> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |   |     `-DeclRefExpr 0x5556a36eaff0 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                           |   |-DeclStmt 0x5556a36eb980 <line:879:2, col:29>
      |                                                                                                                                                                                           |   | `-VarDecl 0x5556a36eb918 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                                                           |   |-BinaryOperator 0x5556a36eb9f0 <line:880:2, col:28> 'int' '='
      |                                                                                                                                                                                           |   | |-DeclRefExpr 0x5556a36eb998 <col:2> 'int' lvalue Var 0x5556a36eb918 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                           |   | `-ImplicitCastExpr 0x5556a36eb9d8 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |   |   `-DeclRefExpr 0x5556a36eb9b8 <col:28> 'int' lvalue Var 0x5556a36eaf30 '__tmp_49' 'int'
      |                                                                                                                                                                                           |   `-IfStmt 0x5556a36ec268 <line:881:2, line:907:2> has_else
      |                                                                                                                                                                                           |     |-BinaryOperator 0x5556a36eba68 <line:881:6, col:33> 'int' '=='
      |                                                                                                                                                                                           |     | |-ImplicitCastExpr 0x5556a36eba50 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |     | | `-DeclRefExpr 0x5556a36eba10 <col:6> 'int' lvalue Var 0x5556a36eb918 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                           |     | `-IntegerLiteral 0x5556a36eba30 <col:33> 'int' 0
      |                                                                                                                                                                                           |     |-CompoundStmt 0x5556a36ebb40 <line:882:2, line:885:2>
      |                                                                                                                                                                                           |     | |-CompoundStmt 0x5556a36ebae0 <line:883:2, col:17>
      |                                                                                                                                                                                           |     | | `-CallExpr 0x5556a36ebac0 <col:3, col:15> 'void'
      |                                                                                                                                                                                           |     | |   `-ImplicitCastExpr 0x5556a36ebaa8 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |                                                                                                                                                                                           |     | |     `-DeclRefExpr 0x5556a36eba88 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |                                                                                                                                                                                           |     | `-ReturnStmt 0x5556a36ebb30 <line:884:2, col:9>
      |                                                                                                                                                                                           |     |   `-ImplicitCastExpr 0x5556a36ebb18 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |     |     `-DeclRefExpr 0x5556a36ebaf8 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                                                           |     `-CompoundStmt 0x5556a36ec250 <line:887:2, line:907:2>
      |                                                                                                                                                                                           |       `-CompoundStmt 0x5556a36ec218 <line:888:2, line:906:2>
      |                                                                                                                                                                                           |         |-DeclStmt 0x5556a36ebbe0 <line:889:2, col:14>
      |                                                                                                                                                                                           |         | `-VarDecl 0x5556a36ebb78 <col:2, col:6> col:6 used __tmp_50 'int'
      |                                                                                                                                                                                           |         |-BinaryOperator 0x5556a36ebca8 <line:890:2, col:24> 'int' '='
      |                                                                                                                                                                                           |         | |-DeclRefExpr 0x5556a36ebbf8 <col:2> 'int' lvalue Var 0x5556a36ebb78 '__tmp_50' 'int'
      |                                                                                                                                                                                           |         | `-BinaryOperator 0x5556a36ebc88 <col:13, col:24> 'int' '<='
      |                                                                                                                                                                                           |         |   |-ImplicitCastExpr 0x5556a36ebc58 <col:13> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |         |   | `-DeclRefExpr 0x5556a36ebc18 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                           |         |   `-ImplicitCastExpr 0x5556a36ebc70 <col:24> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |         |     `-DeclRefExpr 0x5556a36ebc38 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                                                                           |         |-DeclStmt 0x5556a36ebd48 <line:891:2, col:29>
      |                                                                                                                                                                                           |         | `-VarDecl 0x5556a36ebce0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                                                           |         |-BinaryOperator 0x5556a36ebdb8 <line:892:2, col:28> 'int' '='
      |                                                                                                                                                                                           |         | |-DeclRefExpr 0x5556a36ebd60 <col:2> 'int' lvalue Var 0x5556a36ebce0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                           |         | `-ImplicitCastExpr 0x5556a36ebda0 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |         |   `-DeclRefExpr 0x5556a36ebd80 <col:28> 'int' lvalue Var 0x5556a36ebb78 '__tmp_50' 'int'
      |                                                                                                                                                                                           |         `-IfStmt 0x5556a36ec1f0 <line:893:2, line:905:2> has_else
      |                                                                                                                                                                                           |           |-BinaryOperator 0x5556a36ebe30 <line:893:6, col:33> 'int' '=='
      |                                                                                                                                                                                           |           | |-ImplicitCastExpr 0x5556a36ebe18 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |           | | `-DeclRefExpr 0x5556a36ebdd8 <col:6> 'int' lvalue Var 0x5556a36ebce0 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                           |           | `-IntegerLiteral 0x5556a36ebdf8 <col:33> 'int' 0
      |                                                                                                                                                                                           |           |-CompoundStmt 0x5556a36ebf08 <line:894:2, line:897:2>
      |                                                                                                                                                                                           |           | |-CompoundStmt 0x5556a36ebea8 <line:895:2, col:17>
      |                                                                                                                                                                                           |           | | `-CallExpr 0x5556a36ebe88 <col:3, col:15> 'void'
      |                                                                                                                                                                                           |           | |   `-ImplicitCastExpr 0x5556a36ebe70 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |                                                                                                                                                                                           |           | |     `-DeclRefExpr 0x5556a36ebe50 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |                                                                                                                                                                                           |           | `-ReturnStmt 0x5556a36ebef8 <line:896:2, col:9>
      |                                                                                                                                                                                           |           |   `-ImplicitCastExpr 0x5556a36ebee0 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |           |     `-DeclRefExpr 0x5556a36ebec0 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                                                           |           `-CompoundStmt 0x5556a36ec1b8 <line:899:2, line:905:2>
      |                                                                                                                                                                                           |             |-DeclStmt 0x5556a36ebfe0 <line:900:2, col:40>
      |                                                                                                                                                                                           |             | `-VarDecl 0x5556a36ebf40 <col:2, col:33> col:6 used main____CPAchecker_TMP_2 'int' cinit
      |                                                                                                                                                                                           |             |   `-ImplicitCastExpr 0x5556a36ebfc8 <col:33> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |             |     `-DeclRefExpr 0x5556a36ebfa8 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                           |             |-BinaryOperator 0x5556a36ec090 <line:901:2, col:22> 'int' '='
      |                                                                                                                                                                                           |             | |-DeclRefExpr 0x5556a36ebff8 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                           |             | `-BinaryOperator 0x5556a36ec070 <col:12, col:22> 'int' '+'
      |                                                                                                                                                                                           |             |   |-ImplicitCastExpr 0x5556a36ec058 <col:12> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |             |   | `-DeclRefExpr 0x5556a36ec018 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                           |             |   `-IntegerLiteral 0x5556a36ec038 <col:22> 'int' 1
      |                                                                                                                                                                                           |             |-BinaryOperator 0x5556a36ec108 <line:902:2, col:17> 'int' '='
      |                                                                                                                                                                                           |             | |-DeclRefExpr 0x5556a36ec0b0 <col:2> 'int' lvalue Var 0x5556a36cbe98 '__tmp_2624_0' 'int'
      |                                                                                                                                                                                           |             | `-ImplicitCastExpr 0x5556a36ec0f0 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |             |   `-DeclRefExpr 0x5556a36ec0d0 <col:17> 'int' lvalue Var 0x5556a36ead50 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                                           |             |-BinaryOperator 0x5556a36ec180 <line:903:2, col:17> 'int' '='
      |                                                                                                                                                                                           |             | |-DeclRefExpr 0x5556a36ec128 <col:2> 'int' lvalue Var 0x5556a36cbf18 '__tmp_2624_1' 'int'
      |                                                                                                                                                                                           |             | `-ImplicitCastExpr 0x5556a36ec168 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                                           |             |   `-DeclRefExpr 0x5556a36ec148 <col:17> 'int' lvalue Var 0x5556a36ebf40 'main____CPAchecker_TMP_2' 'int'
      |                                                                                                                                                                                           |             `-GotoStmt 0x5556a36ec1a0 <line:904:2, col:7> 'label_2624' 0x5556a36d1fd0
      |                                                                                                                                                                                           `-CompoundStmt 0x5556a36ed978 <line:911:2, line:945:2>
      |                                                                                                                                                                                             `-CompoundStmt 0x5556a36ed940 <line:912:2, line:944:2>
      |                                                                                                                                                                                               |-DeclStmt 0x5556a36ec360 <line:913:2, col:14>
      |                                                                                                                                                                                               | `-VarDecl 0x5556a36ec2f8 <col:2, col:6> col:6 used __tmp_51 'int'
      |                                                                                                                                                                                               |-BinaryOperator 0x5556a36ec410 <line:914:2, col:18> 'int' '='
      |                                                                                                                                                                                               | |-DeclRefExpr 0x5556a36ec378 <col:2> 'int' lvalue Var 0x5556a36ec2f8 '__tmp_51' 'int'
      |                                                                                                                                                                                               | `-BinaryOperator 0x5556a36ec3f0 <col:13, col:18> 'int' '<='
      |                                                                                                                                                                                               |   |-IntegerLiteral 0x5556a36ec398 <col:13> 'int' 0
      |                                                                                                                                                                                               |   `-ImplicitCastExpr 0x5556a36ec3d8 <col:18> 'int' <LValueToRValue>
      |                                                                                                                                                                                               |     `-DeclRefExpr 0x5556a36ec3b8 <col:18> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                               |-DeclStmt 0x5556a36ec4b0 <line:915:2, col:29>
      |                                                                                                                                                                                               | `-VarDecl 0x5556a36ec448 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                                                               |-BinaryOperator 0x5556a36ec520 <line:916:2, col:28> 'int' '='
      |                                                                                                                                                                                               | |-DeclRefExpr 0x5556a36ec4c8 <col:2> 'int' lvalue Var 0x5556a36ec448 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                               | `-ImplicitCastExpr 0x5556a36ec508 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                                                               |   `-DeclRefExpr 0x5556a36ec4e8 <col:28> 'int' lvalue Var 0x5556a36ec2f8 '__tmp_51' 'int'
      |                                                                                                                                                                                               `-IfStmt 0x5556a36ed918 <line:917:2, line:943:2> has_else
      |                                                                                                                                                                                                 |-BinaryOperator 0x5556a36ec598 <line:917:6, col:33> 'int' '=='
      |                                                                                                                                                                                                 | |-ImplicitCastExpr 0x5556a36ec580 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                                                 | | `-DeclRefExpr 0x5556a36ec540 <col:6> 'int' lvalue Var 0x5556a36ec448 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                                 | `-IntegerLiteral 0x5556a36ec560 <col:33> 'int' 0
      |                                                                                                                                                                                                 |-CompoundStmt 0x5556a36ec670 <line:918:2, line:921:2>
      |                                                                                                                                                                                                 | |-CompoundStmt 0x5556a36ec610 <line:919:2, col:17>
      |                                                                                                                                                                                                 | | `-CallExpr 0x5556a36ec5f0 <col:3, col:15> 'void'
      |                                                                                                                                                                                                 | |   `-ImplicitCastExpr 0x5556a36ec5d8 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |                                                                                                                                                                                                 | |     `-DeclRefExpr 0x5556a36ec5b8 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |                                                                                                                                                                                                 | `-ReturnStmt 0x5556a36ec660 <line:920:2, col:9>
      |                                                                                                                                                                                                 |   `-ImplicitCastExpr 0x5556a36ec648 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                                                                 |     `-DeclRefExpr 0x5556a36ec628 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                                                                 `-CompoundStmt 0x5556a36ed900 <line:923:2, line:943:2>
      |                                                                                                                                                                                                   `-CompoundStmt 0x5556a36ed8c8 <line:924:2, line:942:2>
      |                                                                                                                                                                                                     |-DeclStmt 0x5556a36ec710 <line:925:2, col:14>
      |                                                                                                                                                                                                     | `-VarDecl 0x5556a36ec6a8 <col:2, col:6> col:6 used __tmp_52 'int'
      |                                                                                                                                                                                                     |-BinaryOperator 0x5556a36ec7d8 <line:926:2, col:24> 'int' '='
      |                                                                                                                                                                                                     | |-DeclRefExpr 0x5556a36ec728 <col:2> 'int' lvalue Var 0x5556a36ec6a8 '__tmp_52' 'int'
      |                                                                                                                                                                                                     | `-BinaryOperator 0x5556a36ec7b8 <col:13, col:24> 'int' '<='
      |                                                                                                                                                                                                     |   |-ImplicitCastExpr 0x5556a36ec788 <col:13> 'int' <LValueToRValue>
      |                                                                                                                                                                                                     |   | `-DeclRefExpr 0x5556a36ec748 <col:13> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                                     |   `-ImplicitCastExpr 0x5556a36ec7a0 <col:24> 'int' <LValueToRValue>
      |                                                                                                                                                                                                     |     `-DeclRefExpr 0x5556a36ec768 <col:24> 'int' lvalue Var 0x5556a36cc160 'main__tagbuf_len' 'int'
      |                                                                                                                                                                                                     |-DeclStmt 0x5556a36ec878 <line:927:2, col:29>
      |                                                                                                                                                                                                     | `-VarDecl 0x5556a36ec810 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
      |                                                                                                                                                                                                     |-BinaryOperator 0x5556a36ed468 <line:928:2, col:28> 'int' '='
      |                                                                                                                                                                                                     | |-DeclRefExpr 0x5556a36ec890 <col:2> 'int' lvalue Var 0x5556a36ec810 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                                     | `-ImplicitCastExpr 0x5556a36ed450 <col:28> 'int' <LValueToRValue>
      |                                                                                                                                                                                                     |   `-DeclRefExpr 0x5556a36ec8b0 <col:28> 'int' lvalue Var 0x5556a36ec6a8 '__tmp_52' 'int'
      |                                                                                                                                                                                                     `-IfStmt 0x5556a36ed8a0 <line:929:2, line:941:2> has_else
      |                                                                                                                                                                                                       |-BinaryOperator 0x5556a36ed4e0 <line:929:6, col:33> 'int' '=='
      |                                                                                                                                                                                                       | |-ImplicitCastExpr 0x5556a36ed4c8 <col:6> 'int' <LValueToRValue>
      |                                                                                                                                                                                                       | | `-DeclRefExpr 0x5556a36ed488 <col:6> 'int' lvalue Var 0x5556a36ec810 '__VERIFIER_assert__cond' 'int'
      |                                                                                                                                                                                                       | `-IntegerLiteral 0x5556a36ed4a8 <col:33> 'int' 0
      |                                                                                                                                                                                                       |-CompoundStmt 0x5556a36ed5b8 <line:930:2, line:933:2>
      |                                                                                                                                                                                                       | |-CompoundStmt 0x5556a36ed558 <line:931:2, col:17>
      |                                                                                                                                                                                                       | | `-CallExpr 0x5556a36ed538 <col:3, col:15> 'void'
      |                                                                                                                                                                                                       | |   `-ImplicitCastExpr 0x5556a36ed520 <col:3> 'void (*)()' <FunctionToPointerDecay>
      |                                                                                                                                                                                                       | |     `-DeclRefExpr 0x5556a36ed500 <col:3> 'void ()' Function 0x5556a36c8358 'reach_error' 'void ()'
      |                                                                                                                                                                                                       | `-ReturnStmt 0x5556a36ed5a8 <line:932:2, col:9>
      |                                                                                                                                                                                                       |   `-ImplicitCastExpr 0x5556a36ed590 <col:9> 'int' <LValueToRValue>
      |                                                                                                                                                                                                       |     `-DeclRefExpr 0x5556a36ed570 <col:9> 'int' lvalue Var 0x5556a36c7c38 '__return_main' 'int'
      |                                                                                                                                                                                                       `-CompoundStmt 0x5556a36ed868 <line:935:2, line:941:2>
      |                                                                                                                                                                                                         |-DeclStmt 0x5556a36ed690 <line:936:2, col:40>
      |                                                                                                                                                                                                         | `-VarDecl 0x5556a36ed5f0 <col:2, col:33> col:6 used main____CPAchecker_TMP_1 'int' cinit
      |                                                                                                                                                                                                         |   `-ImplicitCastExpr 0x5556a36ed678 <col:33> 'int' <LValueToRValue>
      |                                                                                                                                                                                                         |     `-DeclRefExpr 0x5556a36ed658 <col:33> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                                         |-BinaryOperator 0x5556a36ed740 <line:937:2, col:22> 'int' '='
      |                                                                                                                                                                                                         | |-DeclRefExpr 0x5556a36ed6a8 <col:2> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                                         | `-BinaryOperator 0x5556a36ed720 <col:12, col:22> 'int' '+'
      |                                                                                                                                                                                                         |   |-ImplicitCastExpr 0x5556a36ed708 <col:12> 'int' <LValueToRValue>
      |                                                                                                                                                                                                         |   | `-DeclRefExpr 0x5556a36ed6c8 <col:12> 'int' lvalue Var 0x5556a36cc1f8 'main__t' 'int'
      |                                                                                                                                                                                                         |   `-IntegerLiteral 0x5556a36ed6e8 <col:22> 'int' 1
      |                                                                                                                                                                                                         |-BinaryOperator 0x5556a36ed7b8 <line:938:2, col:17> 'int' '='
      |                                                                                                                                                                                                         | |-DeclRefExpr 0x5556a36ed760 <col:2> 'int' lvalue Var 0x5556a36cbf98 '__tmp_3137_0' 'int'
      |                                                                                                                                                                                                         | `-ImplicitCastExpr 0x5556a36ed7a0 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                                                         |   `-DeclRefExpr 0x5556a36ed780 <col:17> 'int' lvalue Var 0x5556a36ed5f0 'main____CPAchecker_TMP_1' 'int'
      |                                                                                                                                                                                                         |-BinaryOperator 0x5556a36ed830 <line:939:2, col:17> 'int' '='
      |                                                                                                                                                                                                         | |-DeclRefExpr 0x5556a36ed7d8 <col:2> 'int' lvalue Var 0x5556a36cc018 '__tmp_3137_1' 'int'
      |                                                                                                                                                                                                         | `-ImplicitCastExpr 0x5556a36ed818 <col:17> 'int' <LValueToRValue>
      |                                                                                                                                                                                                         |   `-DeclRefExpr 0x5556a36ed7f8 <col:17> 'int' lvalue Var 0x5556a36ead50 'main____CPAchecker_TMP_0' 'int'
      |                                                                                                                                                                                                         `-GotoStmt 0x5556a36ed850 <line:940:2, col:7> 'label_3137' 0x5556a36eab20
      `-CompoundStmt 0x5556a36e0000 <line:1003:2, line:1005:2>
        `-GotoStmt 0x5556a36dffe8 <line:1004:2, col:7> 'label_2597' 0x5556a36d12b8
1 warning generated.
