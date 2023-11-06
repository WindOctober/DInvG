./Benchmark/PLDI/SVComp/loops-crafted-1/sum_by_3_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/sum_by_3_abstracted.c:12:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55cd93ef5f28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55cd93ef67c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55cd93ef64c0 '__int128'
|-TypedefDecl 0x55cd93ef6830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55cd93ef64e0 'unsigned __int128'
|-TypedefDecl 0x55cd93ef6b38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55cd93ef6910 'struct __NSConstantString_tag'
|   `-Record 0x55cd93ef6888 '__NSConstantString_tag'
|-TypedefDecl 0x55cd93ef6bd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55cd93ef6b90 'char *'
|   `-BuiltinType 0x55cd93ef5fc0 'char'
|-TypedefDecl 0x55cd93ef6ec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55cd93ef6e70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55cd93ef6cb0 'struct __va_list_tag'
|     `-Record 0x55cd93ef6c28 '__va_list_tag'
|-FunctionDecl 0x55cd93f56218 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/sum_by_3_abstracted.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55cd93f562b8 prev 0x55cd93f56218 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55cd93f563b0 <line:2:1, col:34> col:12 __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x55cd93f564e8 <line:3:1, col:37> col:14 __VERIFIER_nondet_bool '_Bool ()' extern
|-FunctionDecl 0x55cd93f565d8 <line:4:1, col:36> col:13 __VERIFIER_nondet_char 'char ()' extern
|-FunctionDecl 0x55cd93f566d0 <line:5:1, col:40> col:15 __VERIFIER_nondet_double 'double ()' extern
|-FunctionDecl 0x55cd93f567c0 <line:6:1, col:38> col:14 __VERIFIER_nondet_float 'float ()' extern
|-FunctionDecl 0x55cd93f568b0 <line:7:1, col:46> col:22 __VERIFIER_nondet_ulong 'unsigned long ()' extern
|-FunctionDecl 0x55cd93f569a0 <line:8:1, col:55> col:27 __VERIFIER_nondet_ulonglong 'unsigned long long ()' extern
|-FunctionDecl 0x55cd93f56a90 <line:9:1, col:44> col:21 used __VERIFIER_nondet_uint 'unsigned int ()' extern
|-FunctionDecl 0x55cd93f56b58 prev 0x55cd93f563b0 <line:10:1, col:34> col:12 __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x55cd93f56c90 prev 0x55cd93f562b8 <line:11:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55cd93f57008 <line:12:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55cd93f56d48 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55cd93f56dc8 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55cd93f56e48 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55cd93f56ec8 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55cd93f570c8 <col:99>
|-FunctionDecl 0x55cd93f58188 <line:13:1, col:85> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55cd93f584c8 <col:20, col:85>
|   `-CallExpr 0x55cd93f583e0 <col:22, col:82> 'void'
|     |-ImplicitCastExpr 0x55cd93f583c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55cd93f58228 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55cd93f57008 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55cd93f58438 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55cd93f58420 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55cd93f58288 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55cd93f58468 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55cd93f58450 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55cd93f582e8 <col:41> 'char [22]' lvalue "sum_by_3_abstracted.c"
|     |-ImplicitCastExpr 0x55cd93f58480 <col:66> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55cd93f58318 <col:66> 'int' 3
|     `-ImplicitCastExpr 0x55cd93f584b0 <col:69> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55cd93f58498 <col:69> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55cd93f58378 <col:69> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55cd93f58578 prev 0x55cd93f56c90 <line:14:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55cd93f586f8 <line:15:1, line:17:1> line:15:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55cd93f58630 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55cd93f588a0 <col:36, line:17:1>
|   `-IfStmt 0x55cd93f58888 <line:16:3, col:22>
|     |-UnaryOperator 0x55cd93f587d8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55cd93f587c0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55cd93f587a0 <col:7> 'int' lvalue ParmVar 0x55cd93f58630 'cond' 'int'
|     `-CompoundStmt 0x55cd93f58870 <col:13, col:22>
|       `-CallExpr 0x55cd93f58850 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55cd93f58838 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55cd93f587f0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55cd93f58578 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55cd93f58960 <line:18:1, line:23:1> line:18:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55cd93f588d0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55cd93f58c20 <col:34, line:23:1>
|   |-IfStmt 0x55cd93f58bf8 <line:19:3, line:21:3>
|   | |-UnaryOperator 0x55cd93f58a60 <line:19:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55cd93f58a48 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55cd93f58a28 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55cd93f58a08 <col:9> 'int' lvalue ParmVar 0x55cd93f588d0 'cond' 'int'
|   | `-CompoundStmt 0x55cd93f58be0 <col:16, line:21:3>
|   |   `-LabelStmt 0x55cd93f58bc8 <line:20:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55cd93f58b58 <col:12, col:35>
|   |       |-CallExpr 0x55cd93f58ae0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55cd93f58ac8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55cd93f58a78 <col:13> 'void ()' Function 0x55cd93f58188 'reach_error' 'void ()'
|   |       `-CallExpr 0x55cd93f58b38 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55cd93f58b20 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55cd93f58b00 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55cd93f58578 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55cd93f58c10 <line:22:3>
|-VarDecl 0x55cd93f58c58 <line:24:1, col:12> col:5 used SIZE 'int' cinit
| `-IntegerLiteral 0x55cd93f58cc0 <col:12> 'int' 20000001
|-FunctionDecl 0x55cd93f58d08 prev 0x55cd93f56a90 <line:25:1, col:37> col:14 used __VERIFIER_nondet_uint 'unsigned int ()'
`-FunctionDecl 0x55cd93f58dd0 <line:26:1, line:51:1> line:26:5 main 'int ()'
  `-CompoundStmt 0x55cd93f5b918 <col:12, line:51:1>
    |-DeclStmt 0x55cd93f59010 <line:27:3, col:21>
    | |-VarDecl 0x55cd93f58e88 <col:3, col:16> col:16 used n 'unsigned int'
    | |-VarDecl 0x55cd93f58f08 <col:3, col:18> col:18 used i 'unsigned int'
    | `-VarDecl 0x55cd93f58f88 <col:3, col:20> col:20 used k 'unsigned int'
    |-BinaryOperator 0x55cd93f590d0 <line:28:3, col:30> 'unsigned int' '='
    | |-DeclRefExpr 0x55cd93f59028 <col:3> 'unsigned int' lvalue Var 0x55cd93f58e88 'n' 'unsigned int'
    | `-CallExpr 0x55cd93f590b0 <col:7, col:30> 'unsigned int'
    |   `-ImplicitCastExpr 0x55cd93f59098 <col:7> 'unsigned int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55cd93f59048 <col:7> 'unsigned int ()' Function 0x55cd93f58d08 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |-IfStmt 0x55cd93f5ac10 <line:29:3, col:28>
    | |-UnaryOperator 0x55cd93f5abc8 <col:7, col:18> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55cd93f5aba8 <col:8, col:18> 'int'
    | |   `-BinaryOperator 0x55cd93f5ab88 <col:9, col:14> 'int' '<='
    | |     |-ImplicitCastExpr 0x55cd93f5ab40 <col:9> 'unsigned int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x55cd93f590f0 <col:9> 'unsigned int' lvalue Var 0x55cd93f58e88 'n' 'unsigned int'
    | |     `-ImplicitCastExpr 0x55cd93f5ab70 <col:14> 'unsigned int' <IntegralCast>
    | |       `-ImplicitCastExpr 0x55cd93f5ab58 <col:14> 'int' <LValueToRValue>
    | |         `-DeclRefExpr 0x55cd93f59110 <col:14> 'int' lvalue Var 0x55cd93f58c58 'SIZE' 'int'
    | `-ReturnStmt 0x55cd93f5ac00 <col:21, col:28>
    |   `-IntegerLiteral 0x55cd93f5abe0 <col:28> 'int' 0
    |-BinaryOperator 0x55cd93f5ac80 <line:30:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x55cd93f5ac28 <col:3> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    | `-ImplicitCastExpr 0x55cd93f5ac68 <col:7> 'unsigned int' <IntegralCast>
    |   `-IntegerLiteral 0x55cd93f5ac48 <col:7> 'int' 0
    |-IfStmt 0x55cd93f5b1c0 <line:32:3, line:39:3>
    | |-BinaryOperator 0x55cd93f5ad10 <line:32:7, col:11> 'int' '<'
    | | |-ImplicitCastExpr 0x55cd93f5ace0 <col:7> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55cd93f5aca0 <col:7> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    | | `-ImplicitCastExpr 0x55cd93f5acf8 <col:11> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55cd93f5acc0 <col:11> 'unsigned int' lvalue Var 0x55cd93f58e88 'n' 'unsigned int'
    | `-CompoundStmt 0x55cd93f5b190 <col:14, line:39:3>
    |   |-BinaryOperator 0x55cd93f5ada8 <line:33:3, col:30> 'unsigned int' '='
    |   | |-DeclRefExpr 0x55cd93f5ad30 <col:3> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    |   | `-CallExpr 0x55cd93f5ad88 <col:7, col:30> 'unsigned int'
    |   |   `-ImplicitCastExpr 0x55cd93f5ad70 <col:7> 'unsigned int (*)()' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x55cd93f5ad50 <col:7> 'unsigned int ()' Function 0x55cd93f58d08 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |   |-IfStmt 0x55cd93f5aee8 <line:34:3, col:23>
    |   | |-UnaryOperator 0x55cd93f5ae78 <col:7, col:14> 'int' prefix '!' cannot overflow
    |   | | `-ParenExpr 0x55cd93f5ae58 <col:8, col:14> 'int'
    |   | |   `-BinaryOperator 0x55cd93f5ae38 <col:9, col:13> 'int' '<'
    |   | |     |-ImplicitCastExpr 0x55cd93f5ae08 <col:9> 'unsigned int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x55cd93f5adc8 <col:9> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    |   | |     `-ImplicitCastExpr 0x55cd93f5ae20 <col:13> 'unsigned int' <LValueToRValue>
    |   | |       `-DeclRefExpr 0x55cd93f5ade8 <col:13> 'unsigned int' lvalue Var 0x55cd93f58e88 'n' 'unsigned int'
    |   | `-CallExpr 0x55cd93f5aec8 <col:17, col:23> 'void'
    |   |   `-ImplicitCastExpr 0x55cd93f5aeb0 <col:17> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x55cd93f5ae90 <col:17> 'void (void) __attribute__((noreturn))' Function 0x55cd93f58578 'abort' 'void (void) __attribute__((noreturn))'
    |   |-IfStmt 0x55cd93f5b078 <line:35:3, line:37:5>
    |   | |-BinaryOperator 0x55cd93f5af70 <line:35:7, col:11> 'int' '<'
    |   | | |-ImplicitCastExpr 0x55cd93f5af40 <col:7> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55cd93f5af00 <col:7> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x55cd93f5af58 <col:11> 'unsigned int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x55cd93f5af20 <col:11> 'unsigned int' lvalue Var 0x55cd93f58e88 'n' 'unsigned int'
    |   | `-CompoundStmt 0x55cd93f5b060 <col:15, line:37:5>
    |   |   `-BinaryOperator 0x55cd93f5b040 <line:36:7, col:15> 'unsigned int' '='
    |   |     |-DeclRefExpr 0x55cd93f5af90 <col:7> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    |   |     `-BinaryOperator 0x55cd93f5b020 <col:11, col:15> 'unsigned int' '+'
    |   |       |-ImplicitCastExpr 0x55cd93f5aff0 <col:11> 'unsigned int' <LValueToRValue>
    |   |       | `-DeclRefExpr 0x55cd93f5afb0 <col:11> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    |   |       `-ImplicitCastExpr 0x55cd93f5b008 <col:15> 'unsigned int' <IntegralCast>
    |   |         `-IntegerLiteral 0x55cd93f5afd0 <col:15> 'int' 1
    |   `-IfStmt 0x55cd93f5b178 <line:38:3, col:20>
    |     |-BinaryOperator 0x55cd93f5b100 <col:7, col:11> 'int' '<'
    |     | |-ImplicitCastExpr 0x55cd93f5b0d0 <col:7> 'unsigned int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55cd93f5b090 <col:7> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    |     | `-ImplicitCastExpr 0x55cd93f5b0e8 <col:11> 'unsigned int' <LValueToRValue>
    |     |   `-DeclRefExpr 0x55cd93f5b0b0 <col:11> 'unsigned int' lvalue Var 0x55cd93f58e88 'n' 'unsigned int'
    |     `-CallExpr 0x55cd93f5b158 <col:14, col:20> 'void'
    |       `-ImplicitCastExpr 0x55cd93f5b140 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x55cd93f5b120 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55cd93f58578 'abort' 'void (void) __attribute__((noreturn))'
    |-DeclStmt 0x55cd93f5b2a8 <line:41:3, col:12>
    | `-VarDecl 0x55cd93f5b1f0 <col:3, col:11> col:7 used j 'int' cinit
    |   `-ImplicitCastExpr 0x55cd93f5b290 <col:11> 'int' <IntegralCast>
    |     `-ImplicitCastExpr 0x55cd93f5b278 <col:11> 'unsigned int' <LValueToRValue>
    |       `-DeclRefExpr 0x55cd93f5b258 <col:11> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    |-WhileStmt 0x55cd93f5b438 <line:42:3, line:44:3>
    | |-BinaryOperator 0x55cd93f5b348 <line:42:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x55cd93f5b330 <col:10> 'unsigned int' <IntegralCast>
    | | | `-ImplicitCastExpr 0x55cd93f5b300 <col:10> 'int' <LValueToRValue>
    | | |   `-DeclRefExpr 0x55cd93f5b2c0 <col:10> 'int' lvalue Var 0x55cd93f5b1f0 'j' 'int'
    | | `-ImplicitCastExpr 0x55cd93f5b318 <col:14> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55cd93f5b2e0 <col:14> 'unsigned int' lvalue Var 0x55cd93f58e88 'n' 'unsigned int'
    | `-CompoundStmt 0x55cd93f5b420 <col:18, line:44:3>
    |   `-BinaryOperator 0x55cd93f5b400 <line:43:5, col:11> 'int' '='
    |     |-DeclRefExpr 0x55cd93f5b368 <col:5> 'int' lvalue Var 0x55cd93f5b1f0 'j' 'int'
    |     `-BinaryOperator 0x55cd93f5b3e0 <col:9, col:11> 'int' '+'
    |       |-ImplicitCastExpr 0x55cd93f5b3c8 <col:9> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55cd93f5b388 <col:9> 'int' lvalue Var 0x55cd93f5b1f0 'j' 'int'
    |       `-IntegerLiteral 0x55cd93f5b3a8 <col:11> 'int' 1
    |-BinaryOperator 0x55cd93f5b4c0 <line:45:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x55cd93f5b450 <col:3> 'unsigned int' lvalue Var 0x55cd93f58f88 'k' 'unsigned int'
    | `-ImplicitCastExpr 0x55cd93f5b4a8 <col:7> 'unsigned int' <IntegralCast>
    |   `-ImplicitCastExpr 0x55cd93f5b490 <col:7> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x55cd93f5b470 <col:7> 'int' lvalue Var 0x55cd93f5b1f0 'j' 'int'
    |-WhileStmt 0x55cd93f5b658 <line:46:3, line:48:3>
    | |-BinaryOperator 0x55cd93f5b550 <line:46:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x55cd93f5b520 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55cd93f5b4e0 <col:10> 'unsigned int' lvalue Var 0x55cd93f58f88 'k' 'unsigned int'
    | | `-ImplicitCastExpr 0x55cd93f5b538 <col:14> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55cd93f5b500 <col:14> 'unsigned int' lvalue Var 0x55cd93f58e88 'n' 'unsigned int'
    | `-CompoundStmt 0x55cd93f5b640 <col:18, line:48:3>
    |   `-BinaryOperator 0x55cd93f5b620 <line:47:5, col:11> 'unsigned int' '='
    |     |-DeclRefExpr 0x55cd93f5b570 <col:5> 'unsigned int' lvalue Var 0x55cd93f58f88 'k' 'unsigned int'
    |     `-BinaryOperator 0x55cd93f5b600 <col:9, col:11> 'unsigned int' '+'
    |       |-ImplicitCastExpr 0x55cd93f5b5d0 <col:9> 'unsigned int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55cd93f5b590 <col:9> 'unsigned int' lvalue Var 0x55cd93f58f88 'k' 'unsigned int'
    |       `-ImplicitCastExpr 0x55cd93f5b5e8 <col:11> 'unsigned int' <IntegralCast>
    |         `-IntegerLiteral 0x55cd93f5b5b0 <col:11> 'int' 1
    |-CallExpr 0x55cd93f5b8c0 <line:49:3, col:38> 'void'
    | |-ImplicitCastExpr 0x55cd93f5b8a8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55cd93f5b670 <col:3> 'void (int)' Function 0x55cd93f58960 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55cd93f5b858 <col:21, col:34> 'int' '<='
    |   |-BinaryOperator 0x55cd93f5b7e8 <col:21, col:29> 'unsigned int' '/'
    |   | |-ParenExpr 0x55cd93f5b790 <col:21, col:27> 'unsigned int'
    |   | | `-BinaryOperator 0x55cd93f5b770 <col:22, col:26> 'unsigned int' '+'
    |   | |   |-BinaryOperator 0x55cd93f5b718 <col:22, col:24> 'unsigned int' '+'
    |   | |   | |-ImplicitCastExpr 0x55cd93f5b6d0 <col:22> 'unsigned int' <LValueToRValue>
    |   | |   | | `-DeclRefExpr 0x55cd93f5b690 <col:22> 'unsigned int' lvalue Var 0x55cd93f58f08 'i' 'unsigned int'
    |   | |   | `-ImplicitCastExpr 0x55cd93f5b700 <col:24> 'unsigned int' <IntegralCast>
    |   | |   |   `-ImplicitCastExpr 0x55cd93f5b6e8 <col:24> 'int' <LValueToRValue>
    |   | |   |     `-DeclRefExpr 0x55cd93f5b6b0 <col:24> 'int' lvalue Var 0x55cd93f5b1f0 'j' 'int'
    |   | |   `-ImplicitCastExpr 0x55cd93f5b758 <col:26> 'unsigned int' <LValueToRValue>
    |   | |     `-DeclRefExpr 0x55cd93f5b738 <col:26> 'unsigned int' lvalue Var 0x55cd93f58f88 'k' 'unsigned int'
    |   | `-ImplicitCastExpr 0x55cd93f5b7d0 <col:29> 'unsigned int' <IntegralCast>
    |   |   `-IntegerLiteral 0x55cd93f5b7b0 <col:29> 'int' 3
    |   `-ImplicitCastExpr 0x55cd93f5b840 <col:34> 'unsigned int' <IntegralCast>
    |     `-ImplicitCastExpr 0x55cd93f5b828 <col:34> 'int' <LValueToRValue>
    |       `-DeclRefExpr 0x55cd93f5b808 <col:34> 'int' lvalue Var 0x55cd93f58c58 'SIZE' 'int'
    `-ReturnStmt 0x55cd93f5b908 <line:50:3, col:10>
      `-IntegerLiteral 0x55cd93f5b8e8 <col:10> 'int' 0
1 warning generated.
