./Benchmark/PLDI/SVComp/loop-acceleration/underapprox_2-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/underapprox_2-2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x558e6abe5f28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x558e6abe67c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x558e6abe64c0 '__int128'
|-TypedefDecl 0x558e6abe6830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x558e6abe64e0 'unsigned __int128'
|-TypedefDecl 0x558e6abe6b38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x558e6abe6910 'struct __NSConstantString_tag'
|   `-Record 0x558e6abe6888 '__NSConstantString_tag'
|-TypedefDecl 0x558e6abe6bd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x558e6abe6b90 'char *'
|   `-BuiltinType 0x558e6abe5fc0 'char'
|-TypedefDecl 0x558e6abe6ec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x558e6abe6e70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x558e6abe6cb0 'struct __va_list_tag'
|     `-Record 0x558e6abe6c28 '__va_list_tag'
|-FunctionDecl 0x558e6ac45eb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/underapprox_2-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558e6ac45f58 prev 0x558e6ac45eb8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558e6ac462d8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x558e6ac46010 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x558e6ac46090 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x558e6ac46110 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x558e6ac46190 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x558e6ac46398 <col:99>
|-FunctionDecl 0x558e6ac46488 <line:3:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x558e6ac467c8 <col:20, col:81>
|   `-CallExpr 0x558e6ac466e0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x558e6ac466c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x558e6ac46528 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x558e6ac462d8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x558e6ac46738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x558e6ac46720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x558e6ac46588 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x558e6ac46768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x558e6ac46750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x558e6ac465e8 <col:41> 'char [18]' lvalue "underapprox_2-2.c"
|     |-ImplicitCastExpr 0x558e6ac46780 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x558e6ac46618 <col:62> 'int' 3
|     `-ImplicitCastExpr 0x558e6ac467b0 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x558e6ac46798 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x558e6ac46678 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x558e6ac468b8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x558e6ac467f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x558e6ac46b98 <col:34, line:10:1>
|   |-IfStmt 0x558e6ac46b70 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x558e6ac469b8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x558e6ac469a0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x558e6ac46980 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x558e6ac46960 <col:9> 'int' lvalue ParmVar 0x558e6ac467f8 'cond' 'int'
|   | `-CompoundStmt 0x558e6ac46b58 <col:16, line:8:3>
|   |   `-LabelStmt 0x558e6ac46b40 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x558e6ac46ad0 <col:12, col:35>
|   |       |-CallExpr 0x558e6ac46a30 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x558e6ac46a18 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x558e6ac469d0 <col:13> 'void ()' Function 0x558e6ac46488 'reach_error' 'void ()'
|   |       `-CallExpr 0x558e6ac46ab0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x558e6ac46a98 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x558e6ac46a50 <col:27> 'void (void) __attribute__((noreturn))' Function 0x558e6ac45f58 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x558e6ac46b88 <line:9:3>
`-FunctionDecl 0x558e6ac46c80 <line:12:1, line:22:1> line:12:5 main 'int (void)'
  `-CompoundStmt 0x558e6ac48be8 <col:16, line:22:1>
    |-DeclStmt 0x558e6ac48860 <line:13:3, col:21>
    | `-VarDecl 0x558e6ac487c0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x558e6ac48848 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x558e6ac48828 <col:20> 'int' 0
    |-DeclStmt 0x558e6ac48930 <line:14:3, col:21>
    | `-VarDecl 0x558e6ac48890 <col:3, col:20> col:16 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x558e6ac48918 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x558e6ac488f8 <col:20> 'int' 1
    |-WhileStmt 0x558e6ac48ab8 <line:16:3, line:19:3>
    | |-BinaryOperator 0x558e6ac489b8 <line:16:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x558e6ac48988 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558e6ac48948 <col:10> 'unsigned int' lvalue Var 0x558e6ac487c0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x558e6ac489a0 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x558e6ac48968 <col:14> 'int' 6
    | `-CompoundStmt 0x558e6ac48a98 <col:17, line:19:3>
    |   |-UnaryOperator 0x558e6ac489f8 <line:17:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x558e6ac489d8 <col:5> 'unsigned int' lvalue Var 0x558e6ac487c0 'x' 'unsigned int'
    |   `-CompoundAssignOperator 0x558e6ac48a68 <line:18:5, col:10> 'unsigned int' '*=' ComputeLHSTy='unsigned int' ComputeResultTy='unsigned int'
    |     |-DeclRefExpr 0x558e6ac48a10 <col:5> 'unsigned int' lvalue Var 0x558e6ac48890 'y' 'unsigned int'
    |     `-ImplicitCastExpr 0x558e6ac48a50 <col:10> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x558e6ac48a30 <col:10> 'int' 2
    `-CallExpr 0x558e6ac48bc0 <line:21:3, col:27> 'void'
      |-ImplicitCastExpr 0x558e6ac48ba8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x558e6ac48ad0 <col:3> 'void (int)' Function 0x558e6ac468b8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x558e6ac48b60 <col:21, col:26> 'int' '=='
        |-ImplicitCastExpr 0x558e6ac48b30 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x558e6ac48af0 <col:21> 'unsigned int' lvalue Var 0x558e6ac487c0 'x' 'unsigned int'
        `-ImplicitCastExpr 0x558e6ac48b48 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x558e6ac48b10 <col:26> 'int' 6
1 warning generated.
