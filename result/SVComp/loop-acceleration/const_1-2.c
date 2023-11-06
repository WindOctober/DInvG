./Benchmark/PLDI/SVComp/loop-acceleration/const_1-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/const_1-2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x561ca1388eb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x561ca1389750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x561ca1389450 '__int128'
|-TypedefDecl 0x561ca13897c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x561ca1389470 'unsigned __int128'
|-TypedefDecl 0x561ca1389ac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x561ca13898a0 'struct __NSConstantString_tag'
|   `-Record 0x561ca1389818 '__NSConstantString_tag'
|-TypedefDecl 0x561ca1389b60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x561ca1389b20 'char *'
|   `-BuiltinType 0x561ca1388f50 'char'
|-TypedefDecl 0x561ca1389e58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x561ca1389e00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x561ca1389c40 'struct __va_list_tag'
|     `-Record 0x561ca1389bb8 '__va_list_tag'
|-FunctionDecl 0x561ca13e8e38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/const_1-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x561ca13e8ed8 prev 0x561ca13e8e38 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x561ca13e9258 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x561ca13e8f90 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x561ca13e9010 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x561ca13e9090 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x561ca13e9110 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x561ca13e9318 <col:99>
|-FunctionDecl 0x561ca13e9408 <line:3:1, col:75> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x561ca13e9708 <col:20, col:75>
|   `-CallExpr 0x561ca13e9620 <col:22, col:72> 'void'
|     |-ImplicitCastExpr 0x561ca13e9608 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x561ca13e94a8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x561ca13e9258 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x561ca13e9678 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x561ca13e9660 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x561ca13e9508 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x561ca13e96a8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x561ca13e9690 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x561ca13e9568 <col:41> 'char [12]' lvalue "const_1-2.c"
|     |-ImplicitCastExpr 0x561ca13e96c0 <col:56> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x561ca13e9590 <col:56> 'int' 3
|     `-ImplicitCastExpr 0x561ca13e96f0 <col:59> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x561ca13e96d8 <col:59> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x561ca13e95b0 <col:59> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x561ca13e97f8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x561ca13e9738 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x561ca13e9ad8 <col:34, line:10:1>
|   |-IfStmt 0x561ca13e9ab0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x561ca13e98f8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x561ca13e98e0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x561ca13e98c0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x561ca13e98a0 <col:9> 'int' lvalue ParmVar 0x561ca13e9738 'cond' 'int'
|   | `-CompoundStmt 0x561ca13e9a98 <col:16, line:8:3>
|   |   `-LabelStmt 0x561ca13e9a80 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x561ca13e9a10 <col:12, col:35>
|   |       |-CallExpr 0x561ca13e9970 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x561ca13e9958 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x561ca13e9910 <col:13> 'void ()' Function 0x561ca13e9408 'reach_error' 'void ()'
|   |       `-CallExpr 0x561ca13e99f0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x561ca13e99d8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x561ca13e9990 <col:27> 'void (void) __attribute__((noreturn))' Function 0x561ca13e8ed8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x561ca13e9ac8 <line:9:3>
`-FunctionDecl 0x561ca13e9bc0 <line:12:1, line:20:1> line:12:5 main 'int (void)'
  `-CompoundStmt 0x561ca13ebab8 <col:16, line:20:1>
    |-DeclStmt 0x561ca13eb740 <line:13:3, col:21>
    | `-VarDecl 0x561ca13e9ca0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x561ca13e9d28 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x561ca13e9d08 <col:20> 'int' 1
    |-DeclStmt 0x561ca13eb810 <line:14:3, col:21>
    | `-VarDecl 0x561ca13eb770 <col:3, col:20> col:16 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x561ca13eb7f8 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x561ca13eb7d8 <col:20> 'int' 0
    |-WhileStmt 0x561ca13eb988 <line:15:3, line:18:3>
    | |-BinaryOperator 0x561ca13eb898 <line:15:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x561ca13eb868 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x561ca13eb828 <col:10> 'unsigned int' lvalue Var 0x561ca13eb770 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x561ca13eb880 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x561ca13eb848 <col:14> 'int' 1024
    | `-CompoundStmt 0x561ca13eb968 <col:20, line:18:3>
    |   |-BinaryOperator 0x561ca13eb910 <line:16:5, col:9> 'unsigned int' '='
    |   | |-DeclRefExpr 0x561ca13eb8b8 <col:5> 'unsigned int' lvalue Var 0x561ca13e9ca0 'x' 'unsigned int'
    |   | `-ImplicitCastExpr 0x561ca13eb8f8 <col:9> 'unsigned int' <IntegralCast>
    |   |   `-IntegerLiteral 0x561ca13eb8d8 <col:9> 'int' 0
    |   `-UnaryOperator 0x561ca13eb950 <line:17:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x561ca13eb930 <col:5> 'unsigned int' lvalue Var 0x561ca13eb770 'y' 'unsigned int'
    `-CallExpr 0x561ca13eba90 <line:19:3, col:27> 'void'
      |-ImplicitCastExpr 0x561ca13eba78 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x561ca13eb9a0 <col:3> 'void (int)' Function 0x561ca13e97f8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x561ca13eba30 <col:21, col:26> 'int' '=='
        |-ImplicitCastExpr 0x561ca13eba00 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x561ca13eb9c0 <col:21> 'unsigned int' lvalue Var 0x561ca13e9ca0 'x' 'unsigned int'
        `-ImplicitCastExpr 0x561ca13eba18 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x561ca13eb9e0 <col:26> 'int' 1
1 warning generated.
