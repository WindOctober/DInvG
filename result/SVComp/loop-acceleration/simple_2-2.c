./Benchmark/PLDI/SVComp/loop-acceleration/simple_2-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/simple_2-2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55b153117eb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55b153118750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55b153118450 '__int128'
|-TypedefDecl 0x55b1531187c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55b153118470 'unsigned __int128'
|-TypedefDecl 0x55b153118ac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55b1531188a0 'struct __NSConstantString_tag'
|   `-Record 0x55b153118818 '__NSConstantString_tag'
|-TypedefDecl 0x55b153118b60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55b153118b20 'char *'
|   `-BuiltinType 0x55b153117f50 'char'
|-TypedefDecl 0x55b153118e58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55b153118e00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55b153118c40 'struct __va_list_tag'
|     `-Record 0x55b153118bb8 '__va_list_tag'
|-FunctionDecl 0x55b153177e78 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/simple_2-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b153177f18 prev 0x55b153177e78 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b153178298 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55b153177fd0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55b153178050 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55b1531780d0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55b153178150 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55b153178358 <col:99>
|-FunctionDecl 0x55b153178448 <line:3:1, col:76> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55b153178778 <col:20, col:76>
|   `-CallExpr 0x55b153178690 <col:22, col:73> 'void'
|     |-ImplicitCastExpr 0x55b153178678 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55b1531784e8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55b153178298 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55b1531786e8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55b1531786d0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55b153178548 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55b153178718 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55b153178700 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55b1531785a8 <col:41> 'char [13]' lvalue "simple_2-2.c"
|     |-ImplicitCastExpr 0x55b153178730 <col:57> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55b1531785d0 <col:57> 'int' 3
|     `-ImplicitCastExpr 0x55b153178760 <col:60> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55b153178748 <col:60> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55b153178628 <col:60> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55b153178860 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x55b1531789d8 <line:6:1, line:11:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55b153178918 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55b153178cb8 <col:34, line:11:1>
|   |-IfStmt 0x55b153178c90 <line:7:3, line:9:3>
|   | |-UnaryOperator 0x55b153178ad8 <line:7:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55b153178ac0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55b153178aa0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55b153178a80 <col:9> 'int' lvalue ParmVar 0x55b153178918 'cond' 'int'
|   | `-CompoundStmt 0x55b153178c78 <col:16, line:9:3>
|   |   `-LabelStmt 0x55b153178c60 <line:8:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55b153178bf0 <col:12, col:35>
|   |       |-CallExpr 0x55b153178b50 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55b153178b38 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55b153178af0 <col:13> 'void ()' Function 0x55b153178448 'reach_error' 'void ()'
|   |       `-CallExpr 0x55b153178bd0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55b153178bb8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55b153178b70 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55b153177f18 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55b153178ca8 <line:10:3>
`-FunctionDecl 0x55b15317a7a8 <line:13:1, line:21:1> line:13:5 main 'int (void)'
  `-CompoundStmt 0x55b15317aba8 <col:16, line:21:1>
    |-DeclStmt 0x55b15317a980 <line:14:3, col:44>
    | `-VarDecl 0x55b15317a890 <col:3, col:43> col:16 used x 'unsigned int' cinit
    |   `-CallExpr 0x55b15317a960 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55b15317a948 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55b15317a8f8 <col:20> 'unsigned int (void)' Function 0x55b153178860 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-WhileStmt 0x55b15317aa78 <line:16:3, line:18:3>
    | |-BinaryOperator 0x55b15317aa08 <line:16:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x55b15317a9d8 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55b15317a998 <col:10> 'unsigned int' lvalue Var 0x55b15317a890 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55b15317a9f0 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55b15317a9b8 <col:14> 'int' 268435455
    | `-CompoundStmt 0x55b15317aa60 <col:26, line:18:3>
    |   `-UnaryOperator 0x55b15317aa48 <line:17:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55b15317aa28 <col:5> 'unsigned int' lvalue Var 0x55b15317a890 'x' 'unsigned int'
    `-CallExpr 0x55b15317ab80 <line:20:3, col:35> 'void'
      |-ImplicitCastExpr 0x55b15317ab68 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55b15317aa90 <col:3> 'void (int)' Function 0x55b1531789d8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55b15317ab20 <col:21, col:25> 'int' '>'
        |-ImplicitCastExpr 0x55b15317aaf0 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x55b15317aab0 <col:21> 'unsigned int' lvalue Var 0x55b15317a890 'x' 'unsigned int'
        `-ImplicitCastExpr 0x55b15317ab08 <col:25> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x55b15317aad0 <col:25> 'int' 268435455
1 warning generated.
