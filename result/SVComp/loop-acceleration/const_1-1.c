./Benchmark/PLDI/SVComp/loop-acceleration/const_1-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/const_1-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55817653eeb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55817653f750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55817653f450 '__int128'
|-TypedefDecl 0x55817653f7c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55817653f470 'unsigned __int128'
|-TypedefDecl 0x55817653fac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55817653f8a0 'struct __NSConstantString_tag'
|   `-Record 0x55817653f818 '__NSConstantString_tag'
|-TypedefDecl 0x55817653fb60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55817653fb20 'char *'
|   `-BuiltinType 0x55817653ef50 'char'
|-TypedefDecl 0x55817653fe58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55817653fe00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55817653fc40 'struct __va_list_tag'
|     `-Record 0x55817653fbb8 '__va_list_tag'
|-FunctionDecl 0x55817659ee38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/const_1-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55817659eed8 prev 0x55817659ee38 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55817659f258 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55817659ef90 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55817659f010 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55817659f090 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55817659f110 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55817659f318 <col:99>
|-FunctionDecl 0x55817659f408 <line:3:1, col:75> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55817659f708 <col:20, col:75>
|   `-CallExpr 0x55817659f620 <col:22, col:72> 'void'
|     |-ImplicitCastExpr 0x55817659f608 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55817659f4a8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55817659f258 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55817659f678 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55817659f660 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55817659f508 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55817659f6a8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55817659f690 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55817659f568 <col:41> 'char [12]' lvalue "const_1-1.c"
|     |-ImplicitCastExpr 0x55817659f6c0 <col:56> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55817659f590 <col:56> 'int' 3
|     `-ImplicitCastExpr 0x55817659f6f0 <col:59> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55817659f6d8 <col:59> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55817659f5b0 <col:59> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55817659f7f8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55817659f738 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55817659fad8 <col:34, line:10:1>
|   |-IfStmt 0x55817659fab0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55817659f8f8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55817659f8e0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55817659f8c0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55817659f8a0 <col:9> 'int' lvalue ParmVar 0x55817659f738 'cond' 'int'
|   | `-CompoundStmt 0x55817659fa98 <col:16, line:8:3>
|   |   `-LabelStmt 0x55817659fa80 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55817659fa10 <col:12, col:35>
|   |       |-CallExpr 0x55817659f970 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55817659f958 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55817659f910 <col:13> 'void ()' Function 0x55817659f408 'reach_error' 'void ()'
|   |       `-CallExpr 0x55817659f9f0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55817659f9d8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55817659f990 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55817659eed8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55817659fac8 <line:9:3>
`-FunctionDecl 0x55817659fbc0 <line:12:1, line:22:1> line:12:5 main 'int (void)'
  `-CompoundStmt 0x5581765a1ab8 <col:16, line:22:1>
    |-DeclStmt 0x5581765a1740 <line:13:3, col:21>
    | `-VarDecl 0x55817659fca0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55817659fd28 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55817659fd08 <col:20> 'int' 1
    |-DeclStmt 0x5581765a1810 <line:14:3, col:21>
    | `-VarDecl 0x5581765a1770 <col:3, col:20> col:16 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5581765a17f8 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5581765a17d8 <col:20> 'int' 0
    |-WhileStmt 0x5581765a1988 <line:16:3, line:19:3>
    | |-BinaryOperator 0x5581765a1898 <line:16:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x5581765a1868 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5581765a1828 <col:10> 'unsigned int' lvalue Var 0x5581765a1770 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x5581765a1880 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5581765a1848 <col:14> 'int' 1024
    | `-CompoundStmt 0x5581765a1968 <col:20, line:19:3>
    |   |-BinaryOperator 0x5581765a1910 <line:17:5, col:9> 'unsigned int' '='
    |   | |-DeclRefExpr 0x5581765a18b8 <col:5> 'unsigned int' lvalue Var 0x55817659fca0 'x' 'unsigned int'
    |   | `-ImplicitCastExpr 0x5581765a18f8 <col:9> 'unsigned int' <IntegralCast>
    |   |   `-IntegerLiteral 0x5581765a18d8 <col:9> 'int' 0
    |   `-UnaryOperator 0x5581765a1950 <line:18:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x5581765a1930 <col:5> 'unsigned int' lvalue Var 0x5581765a1770 'y' 'unsigned int'
    `-CallExpr 0x5581765a1a90 <line:21:3, col:27> 'void'
      |-ImplicitCastExpr 0x5581765a1a78 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x5581765a19a0 <col:3> 'void (int)' Function 0x55817659f7f8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x5581765a1a30 <col:21, col:26> 'int' '=='
        |-ImplicitCastExpr 0x5581765a1a00 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x5581765a19c0 <col:21> 'unsigned int' lvalue Var 0x55817659fca0 'x' 'unsigned int'
        `-ImplicitCastExpr 0x5581765a1a18 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x5581765a19e0 <col:26> 'int' 0
1 warning generated.
