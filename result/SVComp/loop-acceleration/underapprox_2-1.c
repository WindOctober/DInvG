./Benchmark/PLDI/SVComp/loop-acceleration/underapprox_2-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/underapprox_2-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55a0056ddf28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55a0056de7c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55a0056de4c0 '__int128'
|-TypedefDecl 0x55a0056de830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55a0056de4e0 'unsigned __int128'
|-TypedefDecl 0x55a0056deb38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55a0056de910 'struct __NSConstantString_tag'
|   `-Record 0x55a0056de888 '__NSConstantString_tag'
|-TypedefDecl 0x55a0056debd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55a0056deb90 'char *'
|   `-BuiltinType 0x55a0056ddfc0 'char'
|-TypedefDecl 0x55a0056deec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55a0056dee70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55a0056decb0 'struct __va_list_tag'
|     `-Record 0x55a0056dec28 '__va_list_tag'
|-FunctionDecl 0x55a00573deb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/underapprox_2-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a00573df58 prev 0x55a00573deb8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a00573e2d8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55a00573e010 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55a00573e090 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55a00573e110 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55a00573e190 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55a00573e398 <col:99>
|-FunctionDecl 0x55a00573e488 <line:3:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55a00573e7c8 <col:20, col:81>
|   `-CallExpr 0x55a00573e6e0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x55a00573e6c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55a00573e528 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55a00573e2d8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55a00573e738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55a00573e720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55a00573e588 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55a00573e768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55a00573e750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55a00573e5e8 <col:41> 'char [18]' lvalue "underapprox_2-1.c"
|     |-ImplicitCastExpr 0x55a00573e780 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55a00573e618 <col:62> 'int' 3
|     `-ImplicitCastExpr 0x55a00573e7b0 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55a00573e798 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55a00573e678 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55a00573e8b8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55a00573e7f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55a00573eb98 <col:34, line:10:1>
|   |-IfStmt 0x55a00573eb70 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55a00573e9b8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55a00573e9a0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55a00573e980 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55a00573e960 <col:9> 'int' lvalue ParmVar 0x55a00573e7f8 'cond' 'int'
|   | `-CompoundStmt 0x55a00573eb58 <col:16, line:8:3>
|   |   `-LabelStmt 0x55a00573eb40 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55a00573ead0 <col:12, col:35>
|   |       |-CallExpr 0x55a00573ea30 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55a00573ea18 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55a00573e9d0 <col:13> 'void ()' Function 0x55a00573e488 'reach_error' 'void ()'
|   |       `-CallExpr 0x55a00573eab0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55a00573ea98 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55a00573ea50 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55a00573df58 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55a00573eb88 <line:9:3>
`-FunctionDecl 0x55a00573ec80 <line:12:1, line:22:1> line:12:5 main 'int (void)'
  `-CompoundStmt 0x55a005740be8 <col:16, line:22:1>
    |-DeclStmt 0x55a005740860 <line:13:3, col:21>
    | `-VarDecl 0x55a0057407c0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55a005740848 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55a005740828 <col:20> 'int' 0
    |-DeclStmt 0x55a005740930 <line:14:3, col:21>
    | `-VarDecl 0x55a005740890 <col:3, col:20> col:16 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55a005740918 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55a0057408f8 <col:20> 'int' 1
    |-WhileStmt 0x55a005740ab8 <line:16:3, line:19:3>
    | |-BinaryOperator 0x55a0057409b8 <line:16:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x55a005740988 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55a005740948 <col:10> 'unsigned int' lvalue Var 0x55a0057407c0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55a0057409a0 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55a005740968 <col:14> 'int' 6
    | `-CompoundStmt 0x55a005740a98 <col:17, line:19:3>
    |   |-UnaryOperator 0x55a0057409f8 <line:17:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x55a0057409d8 <col:5> 'unsigned int' lvalue Var 0x55a0057407c0 'x' 'unsigned int'
    |   `-CompoundAssignOperator 0x55a005740a68 <line:18:5, col:10> 'unsigned int' '*=' ComputeLHSTy='unsigned int' ComputeResultTy='unsigned int'
    |     |-DeclRefExpr 0x55a005740a10 <col:5> 'unsigned int' lvalue Var 0x55a005740890 'y' 'unsigned int'
    |     `-ImplicitCastExpr 0x55a005740a50 <col:10> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x55a005740a30 <col:10> 'int' 2
    `-CallExpr 0x55a005740bc0 <line:21:3, col:27> 'void'
      |-ImplicitCastExpr 0x55a005740ba8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55a005740ad0 <col:3> 'void (int)' Function 0x55a00573e8b8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55a005740b60 <col:21, col:26> 'int' '!='
        |-ImplicitCastExpr 0x55a005740b30 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x55a005740af0 <col:21> 'unsigned int' lvalue Var 0x55a0057407c0 'x' 'unsigned int'
        `-ImplicitCastExpr 0x55a005740b48 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x55a005740b10 <col:26> 'int' 6
1 warning generated.
