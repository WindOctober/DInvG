./Benchmark/PLDI/SVComp/loops/trex03-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex03-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5565e361cdc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5565e361d660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5565e361d360 '__int128'
|-TypedefDecl 0x5565e361d6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5565e361d380 'unsigned __int128'
|-TypedefDecl 0x5565e361d9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5565e361d7b0 'struct __NSConstantString_tag'
|   `-Record 0x5565e361d728 '__NSConstantString_tag'
|-TypedefDecl 0x5565e361da70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5565e361da30 'char *'
|   `-BuiltinType 0x5565e361ce60 'char'
|-TypedefDecl 0x5565e361dd68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5565e361dd10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5565e361db50 'struct __va_list_tag'
|     `-Record 0x5565e361dac8 '__va_list_tag'
|-FunctionDecl 0x5565e367cec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex03-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5565e367cf68 prev 0x5565e367cec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5565e367d2e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5565e367d020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5565e367d0a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5565e367d120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5565e367d1a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5565e367d3a8 <col:99>
|-FunctionDecl 0x5565e367d498 <line:3:1, col:74> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5565e367d7c8 <col:20, col:74>
|   `-CallExpr 0x5565e367d6e0 <col:22, col:71> 'void'
|     |-ImplicitCastExpr 0x5565e367d6c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5565e367d538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5565e367d2e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5565e367d738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5565e367d720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5565e367d598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5565e367d768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5565e367d750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5565e367d5f8 <col:41> 'char [11]' lvalue "trex03-1.c"
|     |-ImplicitCastExpr 0x5565e367d780 <col:55> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5565e367d620 <col:55> 'int' 3
|     `-ImplicitCastExpr 0x5565e367d7b0 <col:58> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5565e367d798 <col:58> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5565e367d678 <col:58> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5565e367d8b8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5565e367d7f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5565e367db98 <col:34, line:10:1>
|   |-IfStmt 0x5565e367db70 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x5565e367d9b8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5565e367d9a0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5565e367d980 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5565e367d960 <col:9> 'int' lvalue ParmVar 0x5565e367d7f8 'cond' 'int'
|   | `-CompoundStmt 0x5565e367db58 <col:16, line:8:3>
|   |   `-LabelStmt 0x5565e367db40 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5565e367dad0 <col:12, col:35>
|   |       |-CallExpr 0x5565e367da30 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5565e367da18 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5565e367d9d0 <col:13> 'void ()' Function 0x5565e367d498 'reach_error' 'void ()'
|   |       `-CallExpr 0x5565e367dab0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5565e367da98 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5565e367da50 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5565e367cf68 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5565e367db88 <line:9:3>
|-FunctionDecl 0x5565e367dc10 <line:12:1, col:44> col:21 used __VERIFIER_nondet_uint 'unsigned int ()' extern
|-FunctionDecl 0x5565e367dcf8 <line:13:1, col:37> col:14 used __VERIFIER_nondet_bool '_Bool ()' extern
`-FunctionDecl 0x5565e367f7f8 <line:15:1, line:32:1> line:15:5 main 'int ()'
  `-CompoundStmt 0x5565e3680e38 <line:16:1, line:32:1>
    |-DeclStmt 0x5565e367fb70 <line:17:3, col:101>
    | |-VarDecl 0x5565e367f8b0 <col:3, col:42> col:16 used x1 'unsigned int' cinit
    | | `-CallExpr 0x5565e367f980 <col:19, col:42> 'unsigned int'
    | |   `-ImplicitCastExpr 0x5565e367f968 <col:19> 'unsigned int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x5565e367f918 <col:19> 'unsigned int ()' Function 0x5565e367dc10 '__VERIFIER_nondet_uint' 'unsigned int ()'
    | |-VarDecl 0x5565e367f9b8 <col:3, col:71> col:45 used x2 'unsigned int' cinit
    | | `-CallExpr 0x5565e367fa58 <col:48, col:71> 'unsigned int'
    | |   `-ImplicitCastExpr 0x5565e367fa40 <col:48> 'unsigned int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x5565e367fa20 <col:48> 'unsigned int ()' Function 0x5565e367dc10 '__VERIFIER_nondet_uint' 'unsigned int ()'
    | `-VarDecl 0x5565e367fa90 <col:3, col:100> col:74 used x3 'unsigned int' cinit
    |   `-CallExpr 0x5565e367fb30 <col:77, col:100> 'unsigned int'
    |     `-ImplicitCastExpr 0x5565e367fb18 <col:77> 'unsigned int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5565e367faf8 <col:77> 'unsigned int ()' Function 0x5565e367dc10 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |-DeclStmt 0x5565e367fdd0 <line:18:3, col:32>
    | |-VarDecl 0x5565e367fba0 <col:3, col:19> col:16 used d1 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x5565e367fc28 <col:19> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5565e367fc08 <col:19> 'int' 1
    | |-VarDecl 0x5565e367fc58 <col:3, col:25> col:22 used d2 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x5565e367fce0 <col:25> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5565e367fcc0 <col:25> 'int' 1
    | `-VarDecl 0x5565e367fd10 <col:3, col:31> col:28 used d3 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5565e367fd98 <col:31> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5565e367fd78 <col:31> 'int' 1
    |-DeclStmt 0x5565e367ffc8 <line:19:3, col:65>
    | |-VarDecl 0x5565e367fdf8 <col:3, col:35> col:9 used c1 '_Bool' cinit
    | | `-CallExpr 0x5565e367fec0 <col:12, col:35> '_Bool'
    | |   `-ImplicitCastExpr 0x5565e367fea8 <col:12> '_Bool (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x5565e367fe60 <col:12> '_Bool ()' Function 0x5565e367dcf8 '__VERIFIER_nondet_bool' '_Bool ()'
    | `-VarDecl 0x5565e367fef0 <col:3, col:64> col:38 used c2 '_Bool' cinit
    |   `-CallExpr 0x5565e367ff90 <col:41, col:64> '_Bool'
    |     `-ImplicitCastExpr 0x5565e367ff78 <col:41> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5565e367ff58 <col:41> '_Bool ()' Function 0x5565e367dcf8 '__VERIFIER_nondet_bool' '_Bool ()'
    |-WhileStmt 0x5565e3680658 <line:21:3, line:28:3>
    | |-BinaryOperator 0x5565e36801b0 <line:21:9, col:28> 'int' '&&'
    | | |-BinaryOperator 0x5565e3680100 <col:9, col:20> 'int' '&&'
    | | | |-BinaryOperator 0x5565e3680050 <col:9, col:12> 'int' '>'
    | | | | |-ImplicitCastExpr 0x5565e3680020 <col:9> 'unsigned int' <LValueToRValue>
    | | | | | `-DeclRefExpr 0x5565e367ffe0 <col:9> 'unsigned int' lvalue Var 0x5565e367f8b0 'x1' 'unsigned int'
    | | | | `-ImplicitCastExpr 0x5565e3680038 <col:12> 'unsigned int' <IntegralCast>
    | | | |   `-IntegerLiteral 0x5565e3680000 <col:12> 'int' 0
    | | | `-BinaryOperator 0x5565e36800e0 <col:17, col:20> 'int' '>'
    | | |   |-ImplicitCastExpr 0x5565e36800b0 <col:17> 'unsigned int' <LValueToRValue>
    | | |   | `-DeclRefExpr 0x5565e3680070 <col:17> 'unsigned int' lvalue Var 0x5565e367f9b8 'x2' 'unsigned int'
    | | |   `-ImplicitCastExpr 0x5565e36800c8 <col:20> 'unsigned int' <IntegralCast>
    | | |     `-IntegerLiteral 0x5565e3680090 <col:20> 'int' 0
    | | `-BinaryOperator 0x5565e3680190 <col:25, col:28> 'int' '>'
    | |   |-ImplicitCastExpr 0x5565e3680160 <col:25> 'unsigned int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x5565e3680120 <col:25> 'unsigned int' lvalue Var 0x5565e367fa90 'x3' 'unsigned int'
    | |   `-ImplicitCastExpr 0x5565e3680178 <col:28> 'unsigned int' <IntegralCast>
    | |     `-IntegerLiteral 0x5565e3680140 <col:28> 'int' 0
    | `-CompoundStmt 0x5565e3680630 <line:22:3, line:28:3>
    |   |-IfStmt 0x5565e36804d8 <line:23:5, line:25:16> has_else
    |   | |-ImplicitCastExpr 0x5565e36801f0 <line:23:9> '_Bool' <LValueToRValue>
    |   | | `-DeclRefExpr 0x5565e36801d0 <col:9> '_Bool' lvalue Var 0x5565e367fdf8 'c1' '_Bool'
    |   | |-BinaryOperator 0x5565e36802b8 <col:13, col:19> 'unsigned int' '='
    |   | | |-DeclRefExpr 0x5565e3680208 <col:13> 'unsigned int' lvalue Var 0x5565e367f8b0 'x1' 'unsigned int'
    |   | | `-BinaryOperator 0x5565e3680298 <col:16, col:19> 'unsigned int' '-'
    |   | |   |-ImplicitCastExpr 0x5565e3680268 <col:16> 'unsigned int' <LValueToRValue>
    |   | |   | `-DeclRefExpr 0x5565e3680228 <col:16> 'unsigned int' lvalue Var 0x5565e367f8b0 'x1' 'unsigned int'
    |   | |   `-ImplicitCastExpr 0x5565e3680280 <col:19> 'unsigned int' <LValueToRValue>
    |   | |     `-DeclRefExpr 0x5565e3680248 <col:19> 'unsigned int' lvalue Var 0x5565e367fba0 'd1' 'unsigned int'
    |   | `-IfStmt 0x5565e36804b0 <line:24:10, line:25:16> has_else
    |   |   |-ImplicitCastExpr 0x5565e36802f8 <line:24:14> '_Bool' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x5565e36802d8 <col:14> '_Bool' lvalue Var 0x5565e367fef0 'c2' '_Bool'
    |   |   |-BinaryOperator 0x5565e36803c0 <col:18, col:24> 'unsigned int' '='
    |   |   | |-DeclRefExpr 0x5565e3680310 <col:18> 'unsigned int' lvalue Var 0x5565e367f9b8 'x2' 'unsigned int'
    |   |   | `-BinaryOperator 0x5565e36803a0 <col:21, col:24> 'unsigned int' '-'
    |   |   |   |-ImplicitCastExpr 0x5565e3680370 <col:21> 'unsigned int' <LValueToRValue>
    |   |   |   | `-DeclRefExpr 0x5565e3680330 <col:21> 'unsigned int' lvalue Var 0x5565e367f9b8 'x2' 'unsigned int'
    |   |   |   `-ImplicitCastExpr 0x5565e3680388 <col:24> 'unsigned int' <LValueToRValue>
    |   |   |     `-DeclRefExpr 0x5565e3680350 <col:24> 'unsigned int' lvalue Var 0x5565e367fc58 'd2' 'unsigned int'
    |   |   `-BinaryOperator 0x5565e3680490 <line:25:10, col:16> 'unsigned int' '='
    |   |     |-DeclRefExpr 0x5565e36803e0 <col:10> 'unsigned int' lvalue Var 0x5565e367fa90 'x3' 'unsigned int'
    |   |     `-BinaryOperator 0x5565e3680470 <col:13, col:16> 'unsigned int' '-'
    |   |       |-ImplicitCastExpr 0x5565e3680440 <col:13> 'unsigned int' <LValueToRValue>
    |   |       | `-DeclRefExpr 0x5565e3680400 <col:13> 'unsigned int' lvalue Var 0x5565e367fa90 'x3' 'unsigned int'
    |   |       `-ImplicitCastExpr 0x5565e3680458 <col:16> 'unsigned int' <LValueToRValue>
    |   |         `-DeclRefExpr 0x5565e3680420 <col:16> 'unsigned int' lvalue Var 0x5565e367fd10 'd3' 'unsigned int'
    |   |-BinaryOperator 0x5565e3680578 <line:26:5, col:31> '_Bool' '='
    |   | |-DeclRefExpr 0x5565e3680500 <col:5> '_Bool' lvalue Var 0x5565e367fdf8 'c1' '_Bool'
    |   | `-CallExpr 0x5565e3680558 <col:8, col:31> '_Bool'
    |   |   `-ImplicitCastExpr 0x5565e3680540 <col:8> '_Bool (*)()' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x5565e3680520 <col:8> '_Bool ()' Function 0x5565e367dcf8 '__VERIFIER_nondet_bool' '_Bool ()'
    |   `-BinaryOperator 0x5565e3680610 <line:27:5, col:31> '_Bool' '='
    |     |-DeclRefExpr 0x5565e3680598 <col:5> '_Bool' lvalue Var 0x5565e367fef0 'c2' '_Bool'
    |     `-CallExpr 0x5565e36805f0 <col:8, col:31> '_Bool'
    |       `-ImplicitCastExpr 0x5565e36805d8 <col:8> '_Bool (*)()' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x5565e36805b8 <col:8> '_Bool ()' Function 0x5565e367dcf8 '__VERIFIER_nondet_bool' '_Bool ()'
    |-CallExpr 0x5565e3680de0 <line:30:3, col:44> 'void'
    | |-ImplicitCastExpr 0x5565e3680dc8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5565e3680670 <col:3> 'void (int)' Function 0x5565e367d8b8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5565e3680d80 <col:21, col:43> 'int' '&&'
    |   |-BinaryOperator 0x5565e36807b0 <col:21, col:34> 'int' '&&'
    |   | |-BinaryOperator 0x5565e3680700 <col:21, col:25> 'int' '=='
    |   | | |-ImplicitCastExpr 0x5565e36806d0 <col:21> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x5565e3680690 <col:21> 'unsigned int' lvalue Var 0x5565e367f8b0 'x1' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x5565e36806e8 <col:25> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x5565e36806b0 <col:25> 'int' 0
    |   | `-BinaryOperator 0x5565e3680790 <col:30, col:34> 'int' '=='
    |   |   |-ImplicitCastExpr 0x5565e3680760 <col:30> 'unsigned int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x5565e3680720 <col:30> 'unsigned int' lvalue Var 0x5565e367f9b8 'x2' 'unsigned int'
    |   |   `-ImplicitCastExpr 0x5565e3680778 <col:34> 'unsigned int' <IntegralCast>
    |   |     `-IntegerLiteral 0x5565e3680740 <col:34> 'int' 0
    |   `-BinaryOperator 0x5565e3680d60 <col:39, col:43> 'int' '=='
    |     |-ImplicitCastExpr 0x5565e3680d30 <col:39> 'unsigned int' <LValueToRValue>
    |     | `-DeclRefExpr 0x5565e3680cf0 <col:39> 'unsigned int' lvalue Var 0x5565e367fa90 'x3' 'unsigned int'
    |     `-ImplicitCastExpr 0x5565e3680d48 <col:43> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x5565e3680d10 <col:43> 'int' 0
    `-ReturnStmt 0x5565e3680e28 <line:31:3, col:10>
      `-IntegerLiteral 0x5565e3680e08 <col:10> 'int' 0
1 warning generated.
