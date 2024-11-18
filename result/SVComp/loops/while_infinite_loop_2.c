./Benchmark/PLDI/SVComp/loops/while_infinite_loop_2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/while_infinite_loop_2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55d744f4fee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55d744f50780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55d744f50480 '__int128'
|-TypedefDecl 0x55d744f507f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55d744f504a0 'unsigned __int128'
|-TypedefDecl 0x55d744f50af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55d744f508d0 'struct __NSConstantString_tag'
|   `-Record 0x55d744f50848 '__NSConstantString_tag'
|-TypedefDecl 0x55d744f50b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55d744f50b50 'char *'
|   `-BuiltinType 0x55d744f4ff80 'char'
|-TypedefDecl 0x55d744f50e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55d744f50e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55d744f50c70 'struct __va_list_tag'
|     `-Record 0x55d744f50be8 '__va_list_tag'
|-FunctionDecl 0x55d744fafe48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/while_infinite_loop_2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55d744fafee8 prev 0x55d744fafe48 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55d744fb0268 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55d744faffa0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55d744fb0020 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55d744fb00a0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55d744fb0120 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55d744fb0328 <col:99>
|-FunctionDecl 0x55d744fb0418 <line:3:1, col:87> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55d744fb0758 <col:20, col:87>
|   `-CallExpr 0x55d744fb0670 <col:22, col:84> 'void'
|     |-ImplicitCastExpr 0x55d744fb0658 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55d744fb04b8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55d744fb0268 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55d744fb06c8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d744fb06b0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d744fb0518 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55d744fb06f8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d744fb06e0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d744fb0578 <col:41> 'char [24]' lvalue "while_infinite_loop_2.c"
|     |-ImplicitCastExpr 0x55d744fb0710 <col:68> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55d744fb05a8 <col:68> 'int' 3
|     `-ImplicitCastExpr 0x55d744fb0740 <col:71> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55d744fb0728 <col:71> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55d744fb0608 <col:71> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55d744fb0848 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55d744fb0788 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55d744fb0b28 <col:34, line:10:1>
|   |-IfStmt 0x55d744fb0b00 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55d744fb0948 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55d744fb0930 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55d744fb0910 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55d744fb08f0 <col:9> 'int' lvalue ParmVar 0x55d744fb0788 'cond' 'int'
|   | `-CompoundStmt 0x55d744fb0ae8 <col:16, line:8:3>
|   |   `-LabelStmt 0x55d744fb0ad0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55d744fb0a60 <col:12, col:35>
|   |       |-CallExpr 0x55d744fb09c0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55d744fb09a8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55d744fb0960 <col:13> 'void ()' Function 0x55d744fb0418 'reach_error' 'void ()'
|   |       `-CallExpr 0x55d744fb0a40 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55d744fb0a28 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55d744fb09e0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55d744fafee8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55d744fb0b18 <line:9:3>
`-FunctionDecl 0x55d744fb0ba0 <line:11:1, line:20:1> line:11:5 main 'int ()'
  `-CompoundStmt 0x55d744fb2790 <col:12, line:20:1>
    |-DeclStmt 0x55d744fb0ce0 <line:12:3, col:10>
    | `-VarDecl 0x55d744fb0c58 <col:3, col:9> col:7 used x 'int' cinit
    |   `-IntegerLiteral 0x55d744fb0cc0 <col:9> 'int' 0
    |-WhileStmt 0x55d744fb26a0 <line:14:3, line:17:3>
    | |-IntegerLiteral 0x55d744fb0cf8 <line:14:9> 'int' 1
    | `-CompoundStmt 0x55d744fb2688 <line:15:3, line:17:3>
    |   `-CallExpr 0x55d744fb2660 <line:16:5, col:27> 'void'
    |     |-ImplicitCastExpr 0x55d744fb2648 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x55d744fb0d18 <col:5> 'void (int)' Function 0x55d744fb0848 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x55d744fb25f8 <col:23, col:26> 'int' '=='
    |       |-ImplicitCastExpr 0x55d744fb25e0 <col:23> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55d744fb25a0 <col:23> 'int' lvalue Var 0x55d744fb0c58 'x' 'int'
    |       `-IntegerLiteral 0x55d744fb25c0 <col:26> 'int' 0
    `-CallExpr 0x55d744fb2768 <line:19:3, col:25> 'void'
      |-ImplicitCastExpr 0x55d744fb2750 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55d744fb26b8 <col:3> 'void (int)' Function 0x55d744fb0848 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55d744fb2730 <col:21, col:24> 'int' '=='
        |-ImplicitCastExpr 0x55d744fb2718 <col:21> 'int' <LValueToRValue>
        | `-DeclRefExpr 0x55d744fb26d8 <col:21> 'int' lvalue Var 0x55d744fb0c58 'x' 'int'
        `-IntegerLiteral 0x55d744fb26f8 <col:24> 'int' 0
1 warning generated.
