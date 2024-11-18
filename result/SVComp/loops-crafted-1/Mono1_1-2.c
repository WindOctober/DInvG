./Benchmark/PLDI/SVComp/loops-crafted-1/Mono1_1-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono1_1-2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55ecef936eb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55ecef937750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55ecef937450 '__int128'
|-TypedefDecl 0x55ecef9377c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55ecef937470 'unsigned __int128'
|-TypedefDecl 0x55ecef937ac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55ecef9378a0 'struct __NSConstantString_tag'
|   `-Record 0x55ecef937818 '__NSConstantString_tag'
|-TypedefDecl 0x55ecef937b60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55ecef937b20 'char *'
|   `-BuiltinType 0x55ecef936f50 'char'
|-TypedefDecl 0x55ecef937e58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55ecef937e00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55ecef937c40 'struct __va_list_tag'
|     `-Record 0x55ecef937bb8 '__va_list_tag'
|-FunctionDecl 0x55ecef996e58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono1_1-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ecef996ef8 prev 0x55ecef996e58 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ecef997278 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55ecef996fb0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55ecef997030 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55ecef9970b0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55ecef997130 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55ecef997338 <col:99>
|-FunctionDecl 0x55ecef997428 <line:3:1, col:75> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55ecef997728 <col:20, col:75>
|   `-CallExpr 0x55ecef997640 <col:22, col:72> 'void'
|     |-ImplicitCastExpr 0x55ecef997628 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55ecef9974c8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55ecef997278 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55ecef997698 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55ecef997680 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55ecef997528 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55ecef9976c8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55ecef9976b0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55ecef997588 <col:41> 'char [12]' lvalue "Mono1_1-2.c"
|     |-ImplicitCastExpr 0x55ecef9976e0 <col:56> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55ecef9975b0 <col:56> 'int' 3
|     `-ImplicitCastExpr 0x55ecef997710 <col:59> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55ecef9976f8 <col:59> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55ecef9975d0 <col:59> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55ecef997818 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55ecef997758 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55ecef997ae8 <col:34, col:84>
|   `-IfStmt 0x55ecef997ad0 <col:36, col:82>
|     |-UnaryOperator 0x55ecef997918 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55ecef997900 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x55ecef9978e0 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x55ecef9978c0 <col:41> 'int' lvalue ParmVar 0x55ecef997758 'cond' 'int'
|     `-CompoundStmt 0x55ecef997ab8 <col:48, col:82>
|       `-LabelStmt 0x55ecef997aa0 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x55ecef997a30 <col:57, col:80>
|           |-CallExpr 0x55ecef997990 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x55ecef997978 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x55ecef997930 <col:58> 'void ()' Function 0x55ecef997428 'reach_error' 'void ()'
|           `-CallExpr 0x55ecef997a10 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x55ecef9979f8 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x55ecef9979b0 <col:72> 'void (void) __attribute__((noreturn))' Function 0x55ecef996ef8 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x55ecef997bd0 <line:5:1, line:17:1> line:5:5 main 'int (void)'
  `-CompoundStmt 0x55ecef999af8 <col:16, line:17:1>
    |-DeclStmt 0x55ecef999760 <line:6:3, col:21>
    | `-VarDecl 0x55ecef997cb0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55ecef997d38 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55ecef997d18 <col:20> 'int' 0
    |-WhileStmt 0x55ecef9999c8 <line:8:3, line:14:3>
    | |-BinaryOperator 0x55ecef9997e8 <line:8:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x55ecef9997b8 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55ecef999778 <col:10> 'unsigned int' lvalue Var 0x55ecef997cb0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55ecef9997d0 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55ecef999798 <col:14> 'int' 100000000
    | `-CompoundStmt 0x55ecef9999b0 <col:25, line:14:3>
    |   `-IfStmt 0x55ecef999988 <line:9:5, line:13:5> has_else
    |     |-BinaryOperator 0x55ecef999878 <line:9:9, col:13> 'int' '<'
    |     | |-ImplicitCastExpr 0x55ecef999848 <col:9> 'unsigned int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55ecef999808 <col:9> 'unsigned int' lvalue Var 0x55ecef997cb0 'x' 'unsigned int'
    |     | `-ImplicitCastExpr 0x55ecef999860 <col:13> 'unsigned int' <IntegralCast>
    |     |   `-IntegerLiteral 0x55ecef999828 <col:13> 'int' 10000000
    |     |-CompoundStmt 0x55ecef9998d0 <col:23, line:11:5>
    |     | `-UnaryOperator 0x55ecef9998b8 <line:10:7, col:8> 'unsigned int' postfix '++'
    |     |   `-DeclRefExpr 0x55ecef999898 <col:7> 'unsigned int' lvalue Var 0x55ecef997cb0 'x' 'unsigned int'
    |     `-CompoundStmt 0x55ecef999970 <line:11:12, line:13:5>
    |       `-CompoundAssignOperator 0x55ecef999940 <line:12:7, col:12> 'unsigned int' '+=' ComputeLHSTy='unsigned int' ComputeResultTy='unsigned int'
    |         |-DeclRefExpr 0x55ecef9998e8 <col:7> 'unsigned int' lvalue Var 0x55ecef997cb0 'x' 'unsigned int'
    |         `-ImplicitCastExpr 0x55ecef999928 <col:12> 'unsigned int' <IntegralCast>
    |           `-IntegerLiteral 0x55ecef999908 <col:12> 'int' 2
    `-CallExpr 0x55ecef999ad0 <line:16:3, col:35> 'void'
      |-ImplicitCastExpr 0x55ecef999ab8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55ecef9999e0 <col:3> 'void (int)' Function 0x55ecef997818 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55ecef999a70 <col:21, col:26> 'int' '=='
        |-ImplicitCastExpr 0x55ecef999a40 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x55ecef999a00 <col:21> 'unsigned int' lvalue Var 0x55ecef997cb0 'x' 'unsigned int'
        `-ImplicitCastExpr 0x55ecef999a58 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x55ecef999a20 <col:26> 'int' 100000000
1 warning generated.
