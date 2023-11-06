./Benchmark/PLDI/SVComp/loops-crafted-1/nested_delay_notd2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/nested_delay_notd2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x558675a5ef28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x558675a5f7c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x558675a5f4c0 '__int128'
|-TypedefDecl 0x558675a5f830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x558675a5f4e0 'unsigned __int128'
|-TypedefDecl 0x558675a5fb38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x558675a5f910 'struct __NSConstantString_tag'
|   `-Record 0x558675a5f888 '__NSConstantString_tag'
|-TypedefDecl 0x558675a5fbd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x558675a5fb90 'char *'
|   `-BuiltinType 0x558675a5efc0 'char'
|-TypedefDecl 0x558675a5fec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x558675a5fe70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x558675a5fcb0 'struct __va_list_tag'
|     `-Record 0x558675a5fc28 '__va_list_tag'
|-FunctionDecl 0x558675abf078 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/nested_delay_notd2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558675abf118 prev 0x558675abf078 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558675abf498 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x558675abf1d0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x558675abf250 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x558675abf2d0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x558675abf350 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x558675abf558 <col:99>
|-FunctionDecl 0x558675abf648 <line:3:1, col:84> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x558675abf988 <col:20, col:84>
|   `-CallExpr 0x558675abf8a0 <col:22, col:81> 'void'
|     |-ImplicitCastExpr 0x558675abf888 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x558675abf6e8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x558675abf498 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x558675abf8f8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x558675abf8e0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x558675abf748 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x558675abf928 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x558675abf910 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x558675abf7a8 <col:41> 'char [21]' lvalue "nested_delay_notd2.c"
|     |-ImplicitCastExpr 0x558675abf940 <col:65> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x558675abf7d8 <col:65> 'int' 3
|     `-ImplicitCastExpr 0x558675abf970 <col:68> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x558675abf958 <col:68> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x558675abf838 <col:68> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x558675abfa38 prev 0x558675abf118 <line:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558675abfbb8 <line:5:1, line:7:1> line:5:6 used assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x558675abfaf0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x558675abfd60 <col:36, line:7:1>
|   `-IfStmt 0x558675abfd48 <line:6:3, col:22>
|     |-UnaryOperator 0x558675abfc98 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x558675abfc80 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x558675abfc60 <col:7> 'int' lvalue ParmVar 0x558675abfaf0 'cond' 'int'
|     `-CompoundStmt 0x558675abfd30 <col:13, col:22>
|       `-CallExpr 0x558675abfd10 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x558675abfcf8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x558675abfcb0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x558675abfa38 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x558675abfe40 <line:8:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-VarDecl 0x558675abfef8 <line:9:1, col:5> col:5 used last 'int'
|-FunctionDecl 0x558675ac1860 <line:10:1, line:15:1> line:10:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x558675ac17d0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x558675ac1b20 <col:34, line:15:1>
|   |-IfStmt 0x558675ac1af8 <line:11:3, line:13:3>
|   | |-UnaryOperator 0x558675ac1960 <line:11:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x558675ac1948 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x558675ac1928 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x558675ac1908 <col:9> 'int' lvalue ParmVar 0x558675ac17d0 'cond' 'int'
|   | `-CompoundStmt 0x558675ac1ae0 <col:16, line:13:3>
|   |   `-LabelStmt 0x558675ac1ac8 <line:12:6, col:36> 'ERROR'
|   |     `-CompoundStmt 0x558675ac1a58 <col:13, col:36>
|   |       |-CallExpr 0x558675ac19e0 <col:14, col:26> 'void'
|   |       | `-ImplicitCastExpr 0x558675ac19c8 <col:14> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x558675ac1978 <col:14> 'void ()' Function 0x558675abf648 'reach_error' 'void ()'
|   |       `-CallExpr 0x558675ac1a38 <col:28, col:34> 'void'
|   |         `-ImplicitCastExpr 0x558675ac1a20 <col:28> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x558675ac1a00 <col:28> 'void (void) __attribute__((noreturn))' Function 0x558675abfa38 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x558675ac1b10 <line:14:3>
|-VarDecl 0x558675ac1b58 <line:18:1, col:12> col:5 used SIZE 'int' cinit
| `-IntegerLiteral 0x558675ac1bc0 <col:12> 'int' 20
`-FunctionDecl 0x558675ac1c30 <line:19:1, line:45:1> line:19:5 main 'int ()'
  `-CompoundStmt 0x558675ac36e8 <col:12, line:45:1>
    |-BinaryOperator 0x558675ac1d70 <line:20:2, col:31> 'int' '='
    | |-DeclRefExpr 0x558675ac1cd0 <col:2> 'int' lvalue Var 0x558675abfef8 'last' 'int'
    | `-CallExpr 0x558675ac1d50 <col:9, col:31> 'int'
    |   `-ImplicitCastExpr 0x558675ac1d38 <col:9> 'int (*)(void)' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x558675ac1cf0 <col:9> 'int (void)' Function 0x558675abfe40 '__VERIFIER_nondet_int' 'int (void)'
    |-CallExpr 0x558675ac1e70 <line:21:2, col:30> 'void'
    | |-ImplicitCastExpr 0x558675ac1e58 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x558675ac1d90 <col:2> 'void (int)' Function 0x558675abfbb8 'assume_abort_if_not' 'void (int)'
    | `-BinaryOperator 0x558675ac1e08 <col:22, col:29> 'int' '>'
    |   |-ImplicitCastExpr 0x558675ac1df0 <col:22> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x558675ac1db0 <col:22> 'int' lvalue Var 0x558675abfef8 'last' 'int'
    |   `-IntegerLiteral 0x558675ac1dd0 <col:29> 'int' 0
    |-DeclStmt 0x558675ac21e8 <line:22:2, col:26>
    | |-VarDecl 0x558675ac1eb0 <col:2, col:8> col:6 used a 'int' cinit
    | | `-IntegerLiteral 0x558675ac1f18 <col:8> 'int' 0
    | |-VarDecl 0x558675ac1f50 <col:2, col:12> col:10 used b 'int' cinit
    | | `-IntegerLiteral 0x558675ac1fb8 <col:12> 'int' 0
    | |-VarDecl 0x558675ac1ff0 <col:2, col:16> col:14 used c 'int' cinit
    | | `-IntegerLiteral 0x558675ac2058 <col:16> 'int' 0
    | |-VarDecl 0x558675ac2090 <col:2, col:21> col:18 used st 'int' cinit
    | | `-IntegerLiteral 0x558675ac20f8 <col:21> 'int' 0
    | `-VarDecl 0x558675ac2130 <col:2, col:25> col:23 used d 'int' cinit
    |   `-IntegerLiteral 0x558675ac2198 <col:25> 'int' 0
    |-WhileStmt 0x558675ac36a0 <line:23:2, line:43:2>
    | |-IntegerLiteral 0x558675ac2200 <line:23:8> 'int' 1
    | `-CompoundStmt 0x558675ac3660 <col:11, line:43:2>
    |   |-BinaryOperator 0x558675ac2260 <line:24:3, col:6> 'int' '='
    |   | |-DeclRefExpr 0x558675ac2220 <col:3> 'int' lvalue Var 0x558675ac2090 'st' 'int'
    |   | `-IntegerLiteral 0x558675ac2240 <col:6> 'int' 1
    |   |-ForStmt 0x558675ac24e0 <line:25:3, line:27:3>
    |   | |-BinaryOperator 0x558675ac22c0 <line:25:7, col:9> 'int' '='
    |   | | |-DeclRefExpr 0x558675ac2280 <col:7> 'int' lvalue Var 0x558675ac1ff0 'c' 'int'
    |   | | `-IntegerLiteral 0x558675ac22a0 <col:9> 'int' 0
    |   | |-<<<NULL>>>
    |   | |-BinaryOperator 0x558675ac2350 <col:11, col:13> 'int' '<'
    |   | | |-ImplicitCastExpr 0x558675ac2320 <col:11> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x558675ac22e0 <col:11> 'int' lvalue Var 0x558675ac1ff0 'c' 'int'
    |   | | `-ImplicitCastExpr 0x558675ac2338 <col:13> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x558675ac2300 <col:13> 'int' lvalue Var 0x558675ac1b58 'SIZE' 'int'
    |   | |-UnaryOperator 0x558675ac2390 <col:18, col:19> 'int' postfix '++'
    |   | | `-DeclRefExpr 0x558675ac2370 <col:18> 'int' lvalue Var 0x558675ac1ff0 'c' 'int'
    |   | `-CompoundStmt 0x558675ac24c8 <col:23, line:27:3>
    |   |   `-IfStmt 0x558675ac24b0 <line:26:4, col:28>
    |   |     |-BinaryOperator 0x558675ac2418 <col:8, col:11> 'int' '>='
    |   |     | |-ImplicitCastExpr 0x558675ac23e8 <col:8> 'int' <LValueToRValue>
    |   |     | | `-DeclRefExpr 0x558675ac23a8 <col:8> 'int' lvalue Var 0x558675ac1ff0 'c' 'int'
    |   |     | `-ImplicitCastExpr 0x558675ac2400 <col:11> 'int' <LValueToRValue>
    |   |     |   `-DeclRefExpr 0x558675ac23c8 <col:11> 'int' lvalue Var 0x558675abfef8 'last' 'int'
    |   |     `-CompoundStmt 0x558675ac2498 <col:18, col:28>
    |   |       `-BinaryOperator 0x558675ac2478 <col:20, col:25> 'int' '='
    |   |         |-DeclRefExpr 0x558675ac2438 <col:20> 'int' lvalue Var 0x558675ac2090 'st' 'int'
    |   |         `-IntegerLiteral 0x558675ac2458 <col:25> 'int' 0
    |   |-IfStmt 0x558675ac2f60 <line:28:3, line:30:22> has_else
    |   | |-BinaryOperator 0x558675ac2660 <line:28:6, col:23> 'int' '&&'
    |   | | |-BinaryOperator 0x558675ac2570 <col:6, col:10> 'int' '=='
    |   | | | |-ImplicitCastExpr 0x558675ac2558 <col:6> 'int' <LValueToRValue>
    |   | | | | `-DeclRefExpr 0x558675ac2518 <col:6> 'int' lvalue Var 0x558675ac2090 'st' 'int'
    |   | | | `-IntegerLiteral 0x558675ac2538 <col:10> 'int' 0
    |   | | `-BinaryOperator 0x558675ac2640 <col:15, col:23> 'int' '=='
    |   | |   |-ImplicitCastExpr 0x558675ac2628 <col:15> 'int' <LValueToRValue>
    |   | |   | `-DeclRefExpr 0x558675ac2590 <col:15> 'int' lvalue Var 0x558675ac1ff0 'c' 'int'
    |   | |   `-BinaryOperator 0x558675ac2608 <col:18, col:23> 'int' '+'
    |   | |     |-ImplicitCastExpr 0x558675ac25f0 <col:18> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x558675ac25b0 <col:18> 'int' lvalue Var 0x558675abfef8 'last' 'int'
    |   | |     `-IntegerLiteral 0x558675ac25d0 <col:23> 'int' 1
    |   | |-CompoundStmt 0x558675ac2760 <col:25, line:29:15>
    |   | | |-CompoundAssignOperator 0x558675ac26c0 <col:4, col:7> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   | | | |-DeclRefExpr 0x558675ac2680 <col:4> 'int' lvalue Var 0x558675ac1eb0 'a' 'int'
    |   | | | `-IntegerLiteral 0x558675ac26a0 <col:7> 'int' 3
    |   | | `-CompoundAssignOperator 0x558675ac2730 <col:10, col:13> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   | |   |-DeclRefExpr 0x558675ac26f0 <col:10> 'int' lvalue Var 0x558675ac1f50 'b' 'int'
    |   | |   `-IntegerLiteral 0x558675ac2710 <col:13> 'int' 3
    |   | `-CompoundStmt 0x558675ac2f40 <line:30:8, col:22>
    |   |   |-CompoundAssignOperator 0x558675ac2ea0 <col:10, col:13> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   |   | |-DeclRefExpr 0x558675ac2780 <col:10> 'int' lvalue Var 0x558675ac1eb0 'a' 'int'
    |   |   | `-IntegerLiteral 0x558675ac27a0 <col:13> 'int' 2
    |   |   `-CompoundAssignOperator 0x558675ac2f10 <col:16, col:19> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   |     |-DeclRefExpr 0x558675ac2ed0 <col:16> 'int' lvalue Var 0x558675ac1f50 'b' 'int'
    |   |     `-IntegerLiteral 0x558675ac2ef0 <col:19> 'int' 2
    |   |-IfStmt 0x558675ac3310 <line:31:3, line:36:3> has_else
    |   | |-BinaryOperator 0x558675ac3090 <line:31:6, col:21> 'int' '&&'
    |   | | |-BinaryOperator 0x558675ac2ff8 <col:6, col:9> 'int' '=='
    |   | | | |-ImplicitCastExpr 0x558675ac2fc8 <col:6> 'int' <LValueToRValue>
    |   | | | | `-DeclRefExpr 0x558675ac2f88 <col:6> 'int' lvalue Var 0x558675ac1ff0 'c' 'int'
    |   | | | `-ImplicitCastExpr 0x558675ac2fe0 <col:9> 'int' <LValueToRValue>
    |   | | |   `-DeclRefExpr 0x558675ac2fa8 <col:9> 'int' lvalue Var 0x558675abfef8 'last' 'int'
    |   | | `-BinaryOperator 0x558675ac3070 <col:17, col:21> 'int' '=='
    |   | |   |-ImplicitCastExpr 0x558675ac3058 <col:17> 'int' <LValueToRValue>
    |   | |   | `-DeclRefExpr 0x558675ac3018 <col:17> 'int' lvalue Var 0x558675ac2090 'st' 'int'
    |   | |   `-IntegerLiteral 0x558675ac3038 <col:21> 'int' 0
    |   | |-CompoundStmt 0x558675ac3168 <col:24, line:33:3>
    |   | | `-BinaryOperator 0x558675ac3148 <line:32:4, col:10> 'int' '='
    |   | |   |-DeclRefExpr 0x558675ac30b0 <col:4> 'int' lvalue Var 0x558675ac1eb0 'a' 'int'
    |   | |   `-BinaryOperator 0x558675ac3128 <col:8, col:10> 'int' '+'
    |   | |     |-ImplicitCastExpr 0x558675ac3110 <col:8> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x558675ac30d0 <col:8> 'int' lvalue Var 0x558675ac1eb0 'a' 'int'
    |   | |     `-IntegerLiteral 0x558675ac30f0 <col:10> 'int' 1
    |   | `-IfStmt 0x558675ac32f8 <line:34:8, line:36:3>
    |   |   |-BinaryOperator 0x558675ac3288 <line:34:11, col:26> 'int' '&&'
    |   |   | |-BinaryOperator 0x558675ac31d8 <col:11, col:15> 'int' '=='
    |   |   | | |-ImplicitCastExpr 0x558675ac31c0 <col:11> 'int' <LValueToRValue>
    |   |   | | | `-DeclRefExpr 0x558675ac3180 <col:11> 'int' lvalue Var 0x558675ac2090 'st' 'int'
    |   |   | | `-IntegerLiteral 0x558675ac31a0 <col:15> 'int' 1
    |   |   | `-BinaryOperator 0x558675ac3268 <col:20, col:26> 'int' '>='
    |   |   |   |-ImplicitCastExpr 0x558675ac3238 <col:20> 'int' <LValueToRValue>
    |   |   |   | `-DeclRefExpr 0x558675ac31f8 <col:20> 'int' lvalue Var 0x558675abfef8 'last' 'int'
    |   |   |   `-ImplicitCastExpr 0x558675ac3250 <col:26> 'int' <LValueToRValue>
    |   |   |     `-DeclRefExpr 0x558675ac3218 <col:26> 'int' lvalue Var 0x558675ac1b58 'SIZE' 'int'
    |   |   `-CompoundStmt 0x558675ac32e0 <col:32, line:36:3>
    |   |     `-UnaryOperator 0x558675ac32c8 <line:35:4, col:5> 'int' postfix '++'
    |   |       `-DeclRefExpr 0x558675ac32a8 <col:4> 'int' lvalue Var 0x558675ac2130 'd' 'int'
    |   |-IfStmt 0x558675ac34a8 <line:37:3, line:40:3>
    |   | |-BinaryOperator 0x558675ac33a8 <line:37:6, col:11> 'int' '=='
    |   | | |-ImplicitCastExpr 0x558675ac3378 <col:6> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x558675ac3338 <col:6> 'int' lvalue Var 0x558675ac2130 'd' 'int'
    |   | | `-ImplicitCastExpr 0x558675ac3390 <col:11> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x558675ac3358 <col:11> 'int' lvalue Var 0x558675ac1b58 'SIZE' 'int'
    |   | `-CompoundStmt 0x558675ac3488 <col:17, line:40:3>
    |   |   |-BinaryOperator 0x558675ac3408 <line:38:4, col:8> 'int' '='
    |   |   | |-DeclRefExpr 0x558675ac33c8 <col:4> 'int' lvalue Var 0x558675ac1eb0 'a' 'int'
    |   |   | `-IntegerLiteral 0x558675ac33e8 <col:8> 'int' 0
    |   |   `-BinaryOperator 0x558675ac3468 <line:39:4, col:8> 'int' '='
    |   |     |-DeclRefExpr 0x558675ac3428 <col:4> 'int' lvalue Var 0x558675ac1f50 'b' 'int'
    |   |     `-IntegerLiteral 0x558675ac3448 <col:8> 'int' 1
    |   `-CallExpr 0x558675ac3638 <line:42:3, col:36> 'void'
    |     |-ImplicitCastExpr 0x558675ac3620 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x558675ac34c0 <col:3> 'void (int)' Function 0x558675ac1860 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x558675ac3600 <col:21, col:32> 'int' '&&'
    |       |-BinaryOperator 0x558675ac3550 <col:21, col:24> 'int' '=='
    |       | |-ImplicitCastExpr 0x558675ac3520 <col:21> 'int' <LValueToRValue>
    |       | | `-DeclRefExpr 0x558675ac34e0 <col:21> 'int' lvalue Var 0x558675ac1eb0 'a' 'int'
    |       | `-ImplicitCastExpr 0x558675ac3538 <col:24> 'int' <LValueToRValue>
    |       |   `-DeclRefExpr 0x558675ac3500 <col:24> 'int' lvalue Var 0x558675ac1f50 'b' 'int'
    |       `-BinaryOperator 0x558675ac35e0 <col:29, col:32> 'int' '=='
    |         |-ImplicitCastExpr 0x558675ac35b0 <col:29> 'int' <LValueToRValue>
    |         | `-DeclRefExpr 0x558675ac3570 <col:29> 'int' lvalue Var 0x558675ac1ff0 'c' 'int'
    |         `-ImplicitCastExpr 0x558675ac35c8 <col:32> 'int' <LValueToRValue>
    |           `-DeclRefExpr 0x558675ac3590 <col:32> 'int' lvalue Var 0x558675ac1b58 'SIZE' 'int'
    `-ReturnStmt 0x558675ac36d8 <line:44:2, col:9>
      `-IntegerLiteral 0x558675ac36b8 <col:9> 'int' 0
1 warning generated.
