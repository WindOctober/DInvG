./Benchmark/PLDI/SVComp/loop-acceleration/simple_2-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/simple_2-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55f758924eb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55f758925750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55f758925450 '__int128'
|-TypedefDecl 0x55f7589257c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55f758925470 'unsigned __int128'
|-TypedefDecl 0x55f758925ac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55f7589258a0 'struct __NSConstantString_tag'
|   `-Record 0x55f758925818 '__NSConstantString_tag'
|-TypedefDecl 0x55f758925b60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55f758925b20 'char *'
|   `-BuiltinType 0x55f758924f50 'char'
|-TypedefDecl 0x55f758925e58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55f758925e00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55f758925c40 'struct __va_list_tag'
|     `-Record 0x55f758925bb8 '__va_list_tag'
|-FunctionDecl 0x55f758984e78 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/simple_2-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f758984f18 prev 0x55f758984e78 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f758985298 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f758984fd0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55f758985050 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55f7589850d0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55f758985150 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55f758985358 <col:99>
|-FunctionDecl 0x55f758985448 <line:3:1, col:76> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55f758985778 <col:20, col:76>
|   `-CallExpr 0x55f758985690 <col:22, col:73> 'void'
|     |-ImplicitCastExpr 0x55f758985678 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55f7589854e8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55f758985298 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55f7589856e8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55f7589856d0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55f758985548 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55f758985718 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55f758985700 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55f7589855a8 <col:41> 'char [13]' lvalue "simple_2-1.c"
|     |-ImplicitCastExpr 0x55f758985730 <col:57> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55f7589855d0 <col:57> 'int' 3
|     `-ImplicitCastExpr 0x55f758985760 <col:60> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55f758985748 <col:60> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55f758985628 <col:60> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55f758985860 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55f7589859d8 <line:6:1, line:11:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55f758985918 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55f758985cb8 <col:34, line:11:1>
|   |-IfStmt 0x55f758985c90 <line:7:3, line:9:3>
|   | |-UnaryOperator 0x55f758985ad8 <line:7:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55f758985ac0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55f758985aa0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55f758985a80 <col:9> 'int' lvalue ParmVar 0x55f758985918 'cond' 'int'
|   | `-CompoundStmt 0x55f758985c78 <col:16, line:9:3>
|   |   `-LabelStmt 0x55f758985c60 <line:8:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55f758985bf0 <col:12, col:35>
|   |       |-CallExpr 0x55f758985b50 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55f758985b38 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55f758985af0 <col:13> 'void ()' Function 0x55f758985448 'reach_error' 'void ()'
|   |       `-CallExpr 0x55f758985bd0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55f758985bb8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55f758985b70 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55f758984f18 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55f758985ca8 <line:10:3>
`-FunctionDecl 0x55f7589877a8 <line:13:1, line:21:1> line:13:5 main 'int (void)'
  `-CompoundStmt 0x55f758987ba8 <col:16, line:21:1>
    |-DeclStmt 0x55f758987980 <line:14:3, col:44>
    | `-VarDecl 0x55f758987890 <col:3, col:43> col:16 used x 'unsigned int' cinit
    |   `-CallExpr 0x55f758987960 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55f758987948 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55f7589878f8 <col:20> 'unsigned int (void)' Function 0x55f758985860 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-WhileStmt 0x55f758987a78 <line:16:3, line:18:3>
    | |-BinaryOperator 0x55f758987a08 <line:16:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x55f7589879d8 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f758987998 <col:10> 'unsigned int' lvalue Var 0x55f758987890 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55f7589879f0 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55f7589879b8 <col:14> 'int' 268435455
    | `-CompoundStmt 0x55f758987a60 <col:26, line:18:3>
    |   `-UnaryOperator 0x55f758987a48 <line:17:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55f758987a28 <col:5> 'unsigned int' lvalue Var 0x55f758987890 'x' 'unsigned int'
    `-CallExpr 0x55f758987b80 <line:20:3, col:36> 'void'
      |-ImplicitCastExpr 0x55f758987b68 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55f758987a90 <col:3> 'void (int)' Function 0x55f7589859d8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55f758987b20 <col:21, col:26> 'int' '>='
        |-ImplicitCastExpr 0x55f758987af0 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x55f758987ab0 <col:21> 'unsigned int' lvalue Var 0x55f758987890 'x' 'unsigned int'
        `-ImplicitCastExpr 0x55f758987b08 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x55f758987ad0 <col:26> 'int' 268435455
1 warning generated.
