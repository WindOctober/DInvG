./Benchmark/PLDI/SVComp/loops/trex03-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex03-2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55a1aa6b9dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55a1aa6ba660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55a1aa6ba360 '__int128'
|-TypedefDecl 0x55a1aa6ba6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55a1aa6ba380 'unsigned __int128'
|-TypedefDecl 0x55a1aa6ba9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55a1aa6ba7b0 'struct __NSConstantString_tag'
|   `-Record 0x55a1aa6ba728 '__NSConstantString_tag'
|-TypedefDecl 0x55a1aa6baa70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55a1aa6baa30 'char *'
|   `-BuiltinType 0x55a1aa6b9e60 'char'
|-TypedefDecl 0x55a1aa6bad68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55a1aa6bad10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55a1aa6bab50 'struct __va_list_tag'
|     `-Record 0x55a1aa6baac8 '__va_list_tag'
|-FunctionDecl 0x55a1aa719eb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex03-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a1aa719f58 prev 0x55a1aa719eb8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a1aa71a2d8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55a1aa71a010 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55a1aa71a090 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55a1aa71a110 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55a1aa71a190 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55a1aa71a398 <col:99>
|-FunctionDecl 0x55a1aa71a488 <line:3:1, col:74> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55a1aa71a7b8 <col:20, col:74>
|   `-CallExpr 0x55a1aa71a6d0 <col:22, col:71> 'void'
|     |-ImplicitCastExpr 0x55a1aa71a6b8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55a1aa71a528 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55a1aa71a2d8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55a1aa71a728 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55a1aa71a710 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55a1aa71a588 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55a1aa71a758 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55a1aa71a740 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55a1aa71a5e8 <col:41> 'char [11]' lvalue "trex03-2.c"
|     |-ImplicitCastExpr 0x55a1aa71a770 <col:55> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55a1aa71a610 <col:55> 'int' 3
|     `-ImplicitCastExpr 0x55a1aa71a7a0 <col:58> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55a1aa71a788 <col:58> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55a1aa71a668 <col:58> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55a1aa71a8a8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55a1aa71a7e8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55a1aa71ab88 <col:34, line:10:1>
|   |-IfStmt 0x55a1aa71ab60 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55a1aa71a9a8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55a1aa71a990 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55a1aa71a970 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55a1aa71a950 <col:9> 'int' lvalue ParmVar 0x55a1aa71a7e8 'cond' 'int'
|   | `-CompoundStmt 0x55a1aa71ab48 <col:16, line:8:3>
|   |   `-LabelStmt 0x55a1aa71ab30 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55a1aa71aac0 <col:12, col:35>
|   |       |-CallExpr 0x55a1aa71aa20 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55a1aa71aa08 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55a1aa71a9c0 <col:13> 'void ()' Function 0x55a1aa71a488 'reach_error' 'void ()'
|   |       `-CallExpr 0x55a1aa71aaa0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55a1aa71aa88 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55a1aa71aa40 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55a1aa719f58 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55a1aa71ab78 <line:9:3>
|-FunctionDecl 0x55a1aa71ac00 <line:11:1, col:37> col:14 used __VERIFIER_nondet_uint 'unsigned int ()'
|-FunctionDecl 0x55a1aa71ace8 <line:12:1, col:30> col:7 used __VERIFIER_nondet_bool '_Bool ()'
`-FunctionDecl 0x55a1aa71c7e8 <line:14:1, line:31:1> line:14:5 main 'int ()'
  `-CompoundStmt 0x55a1aa71de28 <line:15:1, line:31:1>
    |-DeclStmt 0x55a1aa71cb60 <line:16:3, col:101>
    | |-VarDecl 0x55a1aa71c8a0 <col:3, col:42> col:16 used x1 'unsigned int' cinit
    | | `-CallExpr 0x55a1aa71c970 <col:19, col:42> 'unsigned int'
    | |   `-ImplicitCastExpr 0x55a1aa71c958 <col:19> 'unsigned int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55a1aa71c908 <col:19> 'unsigned int ()' Function 0x55a1aa71ac00 '__VERIFIER_nondet_uint' 'unsigned int ()'
    | |-VarDecl 0x55a1aa71c9a8 <col:3, col:71> col:45 used x2 'unsigned int' cinit
    | | `-CallExpr 0x55a1aa71ca48 <col:48, col:71> 'unsigned int'
    | |   `-ImplicitCastExpr 0x55a1aa71ca30 <col:48> 'unsigned int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55a1aa71ca10 <col:48> 'unsigned int ()' Function 0x55a1aa71ac00 '__VERIFIER_nondet_uint' 'unsigned int ()'
    | `-VarDecl 0x55a1aa71ca80 <col:3, col:100> col:74 used x3 'unsigned int' cinit
    |   `-CallExpr 0x55a1aa71cb20 <col:77, col:100> 'unsigned int'
    |     `-ImplicitCastExpr 0x55a1aa71cb08 <col:77> 'unsigned int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55a1aa71cae8 <col:77> 'unsigned int ()' Function 0x55a1aa71ac00 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |-DeclStmt 0x55a1aa71cdc0 <line:17:3, col:32>
    | |-VarDecl 0x55a1aa71cb90 <col:3, col:19> col:16 used d1 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55a1aa71cc18 <col:19> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55a1aa71cbf8 <col:19> 'int' 1
    | |-VarDecl 0x55a1aa71cc48 <col:3, col:25> col:22 used d2 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55a1aa71ccd0 <col:25> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55a1aa71ccb0 <col:25> 'int' 1
    | `-VarDecl 0x55a1aa71cd00 <col:3, col:31> col:28 used d3 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55a1aa71cd88 <col:31> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55a1aa71cd68 <col:31> 'int' 1
    |-DeclStmt 0x55a1aa71cfb8 <line:18:3, col:65>
    | |-VarDecl 0x55a1aa71cde8 <col:3, col:35> col:9 used c1 '_Bool' cinit
    | | `-CallExpr 0x55a1aa71ceb0 <col:12, col:35> '_Bool'
    | |   `-ImplicitCastExpr 0x55a1aa71ce98 <col:12> '_Bool (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55a1aa71ce50 <col:12> '_Bool ()' Function 0x55a1aa71ace8 '__VERIFIER_nondet_bool' '_Bool ()'
    | `-VarDecl 0x55a1aa71cee0 <col:3, col:64> col:38 used c2 '_Bool' cinit
    |   `-CallExpr 0x55a1aa71cf80 <col:41, col:64> '_Bool'
    |     `-ImplicitCastExpr 0x55a1aa71cf68 <col:41> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55a1aa71cf48 <col:41> '_Bool ()' Function 0x55a1aa71ace8 '__VERIFIER_nondet_bool' '_Bool ()'
    |-WhileStmt 0x55a1aa71d648 <line:20:3, line:27:3>
    | |-BinaryOperator 0x55a1aa71d1a0 <line:20:9, col:28> 'int' '&&'
    | | |-BinaryOperator 0x55a1aa71d0f0 <col:9, col:20> 'int' '&&'
    | | | |-BinaryOperator 0x55a1aa71d040 <col:9, col:12> 'int' '>'
    | | | | |-ImplicitCastExpr 0x55a1aa71d010 <col:9> 'unsigned int' <LValueToRValue>
    | | | | | `-DeclRefExpr 0x55a1aa71cfd0 <col:9> 'unsigned int' lvalue Var 0x55a1aa71c8a0 'x1' 'unsigned int'
    | | | | `-ImplicitCastExpr 0x55a1aa71d028 <col:12> 'unsigned int' <IntegralCast>
    | | | |   `-IntegerLiteral 0x55a1aa71cff0 <col:12> 'int' 0
    | | | `-BinaryOperator 0x55a1aa71d0d0 <col:17, col:20> 'int' '>'
    | | |   |-ImplicitCastExpr 0x55a1aa71d0a0 <col:17> 'unsigned int' <LValueToRValue>
    | | |   | `-DeclRefExpr 0x55a1aa71d060 <col:17> 'unsigned int' lvalue Var 0x55a1aa71c9a8 'x2' 'unsigned int'
    | | |   `-ImplicitCastExpr 0x55a1aa71d0b8 <col:20> 'unsigned int' <IntegralCast>
    | | |     `-IntegerLiteral 0x55a1aa71d080 <col:20> 'int' 0
    | | `-BinaryOperator 0x55a1aa71d180 <col:25, col:28> 'int' '>'
    | |   |-ImplicitCastExpr 0x55a1aa71d150 <col:25> 'unsigned int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x55a1aa71d110 <col:25> 'unsigned int' lvalue Var 0x55a1aa71ca80 'x3' 'unsigned int'
    | |   `-ImplicitCastExpr 0x55a1aa71d168 <col:28> 'unsigned int' <IntegralCast>
    | |     `-IntegerLiteral 0x55a1aa71d130 <col:28> 'int' 0
    | `-CompoundStmt 0x55a1aa71d620 <line:21:3, line:27:3>
    |   |-IfStmt 0x55a1aa71d4c8 <line:22:5, line:24:16> has_else
    |   | |-ImplicitCastExpr 0x55a1aa71d1e0 <line:22:9> '_Bool' <LValueToRValue>
    |   | | `-DeclRefExpr 0x55a1aa71d1c0 <col:9> '_Bool' lvalue Var 0x55a1aa71cde8 'c1' '_Bool'
    |   | |-BinaryOperator 0x55a1aa71d2a8 <col:13, col:19> 'unsigned int' '='
    |   | | |-DeclRefExpr 0x55a1aa71d1f8 <col:13> 'unsigned int' lvalue Var 0x55a1aa71c8a0 'x1' 'unsigned int'
    |   | | `-BinaryOperator 0x55a1aa71d288 <col:16, col:19> 'unsigned int' '-'
    |   | |   |-ImplicitCastExpr 0x55a1aa71d258 <col:16> 'unsigned int' <LValueToRValue>
    |   | |   | `-DeclRefExpr 0x55a1aa71d218 <col:16> 'unsigned int' lvalue Var 0x55a1aa71c8a0 'x1' 'unsigned int'
    |   | |   `-ImplicitCastExpr 0x55a1aa71d270 <col:19> 'unsigned int' <LValueToRValue>
    |   | |     `-DeclRefExpr 0x55a1aa71d238 <col:19> 'unsigned int' lvalue Var 0x55a1aa71cb90 'd1' 'unsigned int'
    |   | `-IfStmt 0x55a1aa71d4a0 <line:23:10, line:24:16> has_else
    |   |   |-ImplicitCastExpr 0x55a1aa71d2e8 <line:23:14> '_Bool' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55a1aa71d2c8 <col:14> '_Bool' lvalue Var 0x55a1aa71cee0 'c2' '_Bool'
    |   |   |-BinaryOperator 0x55a1aa71d3b0 <col:18, col:24> 'unsigned int' '='
    |   |   | |-DeclRefExpr 0x55a1aa71d300 <col:18> 'unsigned int' lvalue Var 0x55a1aa71c9a8 'x2' 'unsigned int'
    |   |   | `-BinaryOperator 0x55a1aa71d390 <col:21, col:24> 'unsigned int' '-'
    |   |   |   |-ImplicitCastExpr 0x55a1aa71d360 <col:21> 'unsigned int' <LValueToRValue>
    |   |   |   | `-DeclRefExpr 0x55a1aa71d320 <col:21> 'unsigned int' lvalue Var 0x55a1aa71c9a8 'x2' 'unsigned int'
    |   |   |   `-ImplicitCastExpr 0x55a1aa71d378 <col:24> 'unsigned int' <LValueToRValue>
    |   |   |     `-DeclRefExpr 0x55a1aa71d340 <col:24> 'unsigned int' lvalue Var 0x55a1aa71cc48 'd2' 'unsigned int'
    |   |   `-BinaryOperator 0x55a1aa71d480 <line:24:10, col:16> 'unsigned int' '='
    |   |     |-DeclRefExpr 0x55a1aa71d3d0 <col:10> 'unsigned int' lvalue Var 0x55a1aa71ca80 'x3' 'unsigned int'
    |   |     `-BinaryOperator 0x55a1aa71d460 <col:13, col:16> 'unsigned int' '-'
    |   |       |-ImplicitCastExpr 0x55a1aa71d430 <col:13> 'unsigned int' <LValueToRValue>
    |   |       | `-DeclRefExpr 0x55a1aa71d3f0 <col:13> 'unsigned int' lvalue Var 0x55a1aa71ca80 'x3' 'unsigned int'
    |   |       `-ImplicitCastExpr 0x55a1aa71d448 <col:16> 'unsigned int' <LValueToRValue>
    |   |         `-DeclRefExpr 0x55a1aa71d410 <col:16> 'unsigned int' lvalue Var 0x55a1aa71cd00 'd3' 'unsigned int'
    |   |-BinaryOperator 0x55a1aa71d568 <line:25:5, col:31> '_Bool' '='
    |   | |-DeclRefExpr 0x55a1aa71d4f0 <col:5> '_Bool' lvalue Var 0x55a1aa71cde8 'c1' '_Bool'
    |   | `-CallExpr 0x55a1aa71d548 <col:8, col:31> '_Bool'
    |   |   `-ImplicitCastExpr 0x55a1aa71d530 <col:8> '_Bool (*)()' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x55a1aa71d510 <col:8> '_Bool ()' Function 0x55a1aa71ace8 '__VERIFIER_nondet_bool' '_Bool ()'
    |   `-BinaryOperator 0x55a1aa71d600 <line:26:5, col:31> '_Bool' '='
    |     |-DeclRefExpr 0x55a1aa71d588 <col:5> '_Bool' lvalue Var 0x55a1aa71cee0 'c2' '_Bool'
    |     `-CallExpr 0x55a1aa71d5e0 <col:8, col:31> '_Bool'
    |       `-ImplicitCastExpr 0x55a1aa71d5c8 <col:8> '_Bool (*)()' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x55a1aa71d5a8 <col:8> '_Bool ()' Function 0x55a1aa71ace8 '__VERIFIER_nondet_bool' '_Bool ()'
    |-CallExpr 0x55a1aa71ddd0 <line:29:3, col:44> 'void'
    | |-ImplicitCastExpr 0x55a1aa71ddb8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55a1aa71d660 <col:3> 'void (int)' Function 0x55a1aa71a8a8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55a1aa71dd70 <col:21, col:43> 'int' '||'
    |   |-BinaryOperator 0x55a1aa71d7a0 <col:21, col:34> 'int' '||'
    |   | |-BinaryOperator 0x55a1aa71d6f0 <col:21, col:25> 'int' '=='
    |   | | |-ImplicitCastExpr 0x55a1aa71d6c0 <col:21> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55a1aa71d680 <col:21> 'unsigned int' lvalue Var 0x55a1aa71c8a0 'x1' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x55a1aa71d6d8 <col:25> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x55a1aa71d6a0 <col:25> 'int' 0
    |   | `-BinaryOperator 0x55a1aa71d780 <col:30, col:34> 'int' '=='
    |   |   |-ImplicitCastExpr 0x55a1aa71d750 <col:30> 'unsigned int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55a1aa71d710 <col:30> 'unsigned int' lvalue Var 0x55a1aa71c9a8 'x2' 'unsigned int'
    |   |   `-ImplicitCastExpr 0x55a1aa71d768 <col:34> 'unsigned int' <IntegralCast>
    |   |     `-IntegerLiteral 0x55a1aa71d730 <col:34> 'int' 0
    |   `-BinaryOperator 0x55a1aa71dd50 <col:39, col:43> 'int' '=='
    |     |-ImplicitCastExpr 0x55a1aa71dd20 <col:39> 'unsigned int' <LValueToRValue>
    |     | `-DeclRefExpr 0x55a1aa71dce0 <col:39> 'unsigned int' lvalue Var 0x55a1aa71ca80 'x3' 'unsigned int'
    |     `-ImplicitCastExpr 0x55a1aa71dd38 <col:43> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x55a1aa71dd00 <col:43> 'int' 0
    `-ReturnStmt 0x55a1aa71de18 <line:30:3, col:10>
      `-IntegerLiteral 0x55a1aa71ddf8 <col:10> 'int' 0
1 warning generated.
