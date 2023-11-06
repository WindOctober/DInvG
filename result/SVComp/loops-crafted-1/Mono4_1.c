./Benchmark/PLDI/SVComp/loops-crafted-1/Mono4_1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono4_1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x559f8fc99e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x559f8fc9a730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x559f8fc9a430 '__int128'
|-TypedefDecl 0x559f8fc9a7a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x559f8fc9a450 'unsigned __int128'
|-TypedefDecl 0x559f8fc9aaa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x559f8fc9a880 'struct __NSConstantString_tag'
|   `-Record 0x559f8fc9a7f8 '__NSConstantString_tag'
|-TypedefDecl 0x559f8fc9ab40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x559f8fc9ab00 'char *'
|   `-BuiltinType 0x559f8fc99f30 'char'
|-TypedefDecl 0x559f8fc9ae38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x559f8fc9ade0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x559f8fc9ac20 'struct __va_list_tag'
|     `-Record 0x559f8fc9ab98 '__va_list_tag'
|-FunctionDecl 0x559f8fcf9e48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono4_1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559f8fcf9ee8 prev 0x559f8fcf9e48 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559f8fcfa268 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559f8fcf9fa0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x559f8fcfa020 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x559f8fcfa0a0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x559f8fcfa120 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x559f8fcfa328 <col:99>
|-FunctionDecl 0x559f8fcfa418 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x559f8fcfa748 <col:20, col:73>
|   `-CallExpr 0x559f8fcfa660 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x559f8fcfa648 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x559f8fcfa4b8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x559f8fcfa268 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x559f8fcfa6b8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x559f8fcfa6a0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x559f8fcfa518 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x559f8fcfa6e8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x559f8fcfa6d0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x559f8fcfa578 <col:41> 'char [10]' lvalue "Mono4_1.c"
|     |-ImplicitCastExpr 0x559f8fcfa700 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x559f8fcfa5a0 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x559f8fcfa730 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x559f8fcfa718 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x559f8fcfa5f8 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x559f8fcfa838 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x559f8fcfa778 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x559f8fcfab08 <col:34, col:84>
|   `-IfStmt 0x559f8fcfaaf0 <col:36, col:82>
|     |-UnaryOperator 0x559f8fcfa938 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x559f8fcfa920 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x559f8fcfa900 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x559f8fcfa8e0 <col:41> 'int' lvalue ParmVar 0x559f8fcfa778 'cond' 'int'
|     `-CompoundStmt 0x559f8fcfaad8 <col:48, col:82>
|       `-LabelStmt 0x559f8fcfaac0 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x559f8fcfaa50 <col:57, col:80>
|           |-CallExpr 0x559f8fcfa9b0 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x559f8fcfa998 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x559f8fcfa950 <col:58> 'void ()' Function 0x559f8fcfa418 'reach_error' 'void ()'
|           `-CallExpr 0x559f8fcfaa30 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x559f8fcfaa18 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x559f8fcfa9d0 <col:72> 'void (void) __attribute__((noreturn))' Function 0x559f8fcf9ee8 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x559f8fcfab70 <line:6:1, line:19:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x559f8fcfcc78 <col:12, line:19:1>
    |-DeclStmt 0x559f8fcfacb0 <line:7:5, col:14>
    | `-VarDecl 0x559f8fcfac28 <col:5, col:13> col:9 used x 'int' cinit
    |   `-IntegerLiteral 0x559f8fcfac90 <col:13> 'int' 0
    |-DeclStmt 0x559f8fcfc770 <line:8:5, col:19>
    | `-VarDecl 0x559f8fcface0 <col:5, col:13> col:9 used y 'int' cinit
    |   `-IntegerLiteral 0x559f8fcfc750 <col:13> 'int' 500000
    |-WhileStmt 0x559f8fcfcb18 <line:9:5, line:16:5>
    | |-BinaryOperator 0x559f8fcfc7e0 <line:9:11, col:15> 'int' '<'
    | | |-ImplicitCastExpr 0x559f8fcfc7c8 <col:11> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x559f8fcfc788 <col:11> 'int' lvalue Var 0x559f8fcfac28 'x' 'int'
    | | `-IntegerLiteral 0x559f8fcfc7a8 <col:15> 'int' 1000000
    | `-CompoundStmt 0x559f8fcfcb00 <col:24, line:16:5>
    |   `-IfStmt 0x559f8fcfcad8 <line:10:2, line:15:2> has_else
    |     |-BinaryOperator 0x559f8fcfc858 <line:10:6, col:10> 'int' '<'
    |     | |-ImplicitCastExpr 0x559f8fcfc840 <col:6> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x559f8fcfc800 <col:6> 'int' lvalue Var 0x559f8fcfac28 'x' 'int'
    |     | `-IntegerLiteral 0x559f8fcfc820 <col:10> 'int' 500000
    |     |-CompoundStmt 0x559f8fcfc930 <col:18, line:12:2>
    |     | `-BinaryOperator 0x559f8fcfc910 <line:11:6, col:14> 'int' '='
    |     |   |-DeclRefExpr 0x559f8fcfc878 <col:6> 'int' lvalue Var 0x559f8fcfac28 'x' 'int'
    |     |   `-BinaryOperator 0x559f8fcfc8f0 <col:10, col:14> 'int' '+'
    |     |     |-ImplicitCastExpr 0x559f8fcfc8d8 <col:10> 'int' <LValueToRValue>
    |     |     | `-DeclRefExpr 0x559f8fcfc898 <col:10> 'int' lvalue Var 0x559f8fcfac28 'x' 'int'
    |     |     `-IntegerLiteral 0x559f8fcfc8b8 <col:14> 'int' 1
    |     `-CompoundStmt 0x559f8fcfcab8 <line:12:9, line:15:2>
    |       |-BinaryOperator 0x559f8fcfc9e0 <line:13:6, col:14> 'int' '='
    |       | |-DeclRefExpr 0x559f8fcfc948 <col:6> 'int' lvalue Var 0x559f8fcfac28 'x' 'int'
    |       | `-BinaryOperator 0x559f8fcfc9c0 <col:10, col:14> 'int' '+'
    |       |   |-ImplicitCastExpr 0x559f8fcfc9a8 <col:10> 'int' <LValueToRValue>
    |       |   | `-DeclRefExpr 0x559f8fcfc968 <col:10> 'int' lvalue Var 0x559f8fcfac28 'x' 'int'
    |       |   `-IntegerLiteral 0x559f8fcfc988 <col:14> 'int' 1
    |       `-BinaryOperator 0x559f8fcfca98 <line:14:6, col:14> 'int' '='
    |         |-DeclRefExpr 0x559f8fcfca00 <col:6> 'int' lvalue Var 0x559f8fcface0 'y' 'int'
    |         `-BinaryOperator 0x559f8fcfca78 <col:10, col:14> 'int' '+'
    |           |-ImplicitCastExpr 0x559f8fcfca60 <col:10> 'int' <LValueToRValue>
    |           | `-DeclRefExpr 0x559f8fcfca20 <col:10> 'int' lvalue Var 0x559f8fcface0 'y' 'int'
    |           `-IntegerLiteral 0x559f8fcfca40 <col:14> 'int' 1
    |-CallExpr 0x559f8fcfcc20 <line:17:5, col:27> 'void'
    | |-ImplicitCastExpr 0x559f8fcfcc08 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x559f8fcfcb30 <col:5> 'void (int)' Function 0x559f8fcfa838 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x559f8fcfcbc0 <col:23, col:26> 'int' '!='
    |   |-ImplicitCastExpr 0x559f8fcfcb90 <col:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x559f8fcfcb50 <col:23> 'int' lvalue Var 0x559f8fcface0 'y' 'int'
    |   `-ImplicitCastExpr 0x559f8fcfcba8 <col:26> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x559f8fcfcb70 <col:26> 'int' lvalue Var 0x559f8fcfac28 'x' 'int'
    `-ReturnStmt 0x559f8fcfcc68 <line:18:5, col:12>
      `-IntegerLiteral 0x559f8fcfcc48 <col:12> 'int' 0
1 warning generated.
