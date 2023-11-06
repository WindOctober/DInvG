./Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_9.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_9.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55f4a2c66f28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55f4a2c677c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55f4a2c674c0 '__int128'
|-TypedefDecl 0x55f4a2c67830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55f4a2c674e0 'unsigned __int128'
|-TypedefDecl 0x55f4a2c67b38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55f4a2c67910 'struct __NSConstantString_tag'
|   `-Record 0x55f4a2c67888 '__NSConstantString_tag'
|-TypedefDecl 0x55f4a2c67bd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55f4a2c67b90 'char *'
|   `-BuiltinType 0x55f4a2c66fc0 'char'
|-TypedefDecl 0x55f4a2c67ec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55f4a2c67e70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55f4a2c67cb0 'struct __va_list_tag'
|     `-Record 0x55f4a2c67c28 '__va_list_tag'
|-FunctionDecl 0x55f4a2cc6ec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_9.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f4a2cc6f68 prev 0x55f4a2cc6ec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f4a2cc72e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f4a2cc7020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55f4a2cc70a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55f4a2cc7120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55f4a2cc71a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55f4a2cc73a8 <col:99>
|-FunctionDecl 0x55f4a2cc7498 <line:3:1, col:80> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55f4a2cc77c8 <col:20, col:80>
|   `-CallExpr 0x55f4a2cc76e0 <col:22, col:77> 'void'
|     |-ImplicitCastExpr 0x55f4a2cc76c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55f4a2cc7538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55f4a2cc72e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55f4a2cc7738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55f4a2cc7720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55f4a2cc7598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55f4a2cc7768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55f4a2cc7750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55f4a2cc75f8 <col:41> 'char [17]' lvalue "mono-crafted_9.c"
|     |-ImplicitCastExpr 0x55f4a2cc7780 <col:61> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55f4a2cc7620 <col:61> 'int' 3
|     `-ImplicitCastExpr 0x55f4a2cc77b0 <col:64> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55f4a2cc7798 <col:64> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55f4a2cc7678 <col:64> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55f4a2cc78b8 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55f4a2cc77f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55f4a2cc7b88 <col:34, col:84>
|   `-IfStmt 0x55f4a2cc7b70 <col:36, col:82>
|     |-UnaryOperator 0x55f4a2cc79b8 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55f4a2cc79a0 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x55f4a2cc7980 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x55f4a2cc7960 <col:41> 'int' lvalue ParmVar 0x55f4a2cc77f8 'cond' 'int'
|     `-CompoundStmt 0x55f4a2cc7b58 <col:48, col:82>
|       `-LabelStmt 0x55f4a2cc7b40 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x55f4a2cc7ad0 <col:57, col:80>
|           |-CallExpr 0x55f4a2cc7a30 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x55f4a2cc7a18 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x55f4a2cc79d0 <col:58> 'void ()' Function 0x55f4a2cc7498 'reach_error' 'void ()'
|           `-CallExpr 0x55f4a2cc7ab0 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x55f4a2cc7a98 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x55f4a2cc7a50 <col:72> 'void (void) __attribute__((noreturn))' Function 0x55f4a2cc6f68 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x55f4a2cc7bf0 <line:6:1, line:20:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x55f4a2cc9cf8 <line:7:1, line:20:1>
    |-DeclStmt 0x55f4a2cc7d30 <line:8:2, col:11>
    | `-VarDecl 0x55f4a2cc7ca8 <col:2, col:10> col:6 used x 'int' cinit
    |   `-IntegerLiteral 0x55f4a2cc7d10 <col:10> 'int' 0
    |-DeclStmt 0x55f4a2cc97f0 <line:9:2, col:16>
    | `-VarDecl 0x55f4a2cc7d60 <col:2, col:10> col:6 used y 'int' cinit
    |   `-IntegerLiteral 0x55f4a2cc97d0 <col:10> 'int' 500000
    |-WhileStmt 0x55f4a2cc9b98 <line:10:2, line:17:2>
    | |-BinaryOperator 0x55f4a2cc9860 <line:10:8, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x55f4a2cc9848 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f4a2cc9808 <col:8> 'int' lvalue Var 0x55f4a2cc7ca8 'x' 'int'
    | | `-IntegerLiteral 0x55f4a2cc9828 <col:12> 'int' 1000000
    | `-CompoundStmt 0x55f4a2cc9b80 <col:21, line:17:2>
    |   `-IfStmt 0x55f4a2cc9b58 <line:11:3, line:16:3> has_else
    |     |-BinaryOperator 0x55f4a2cc98d8 <line:11:7, col:11> 'int' '<'
    |     | |-ImplicitCastExpr 0x55f4a2cc98c0 <col:7> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55f4a2cc9880 <col:7> 'int' lvalue Var 0x55f4a2cc7ca8 'x' 'int'
    |     | `-IntegerLiteral 0x55f4a2cc98a0 <col:11> 'int' 500000
    |     |-CompoundStmt 0x55f4a2cc99b0 <col:19, line:13:3>
    |     | `-BinaryOperator 0x55f4a2cc9990 <line:12:4, col:12> 'int' '='
    |     |   |-DeclRefExpr 0x55f4a2cc98f8 <col:4> 'int' lvalue Var 0x55f4a2cc7ca8 'x' 'int'
    |     |   `-BinaryOperator 0x55f4a2cc9970 <col:8, col:12> 'int' '+'
    |     |     |-ImplicitCastExpr 0x55f4a2cc9958 <col:8> 'int' <LValueToRValue>
    |     |     | `-DeclRefExpr 0x55f4a2cc9918 <col:8> 'int' lvalue Var 0x55f4a2cc7ca8 'x' 'int'
    |     |     `-IntegerLiteral 0x55f4a2cc9938 <col:12> 'int' 1
    |     `-CompoundStmt 0x55f4a2cc9b38 <line:13:10, line:16:3>
    |       |-BinaryOperator 0x55f4a2cc9a60 <line:14:4, col:12> 'int' '='
    |       | |-DeclRefExpr 0x55f4a2cc99c8 <col:4> 'int' lvalue Var 0x55f4a2cc7ca8 'x' 'int'
    |       | `-BinaryOperator 0x55f4a2cc9a40 <col:8, col:12> 'int' '+'
    |       |   |-ImplicitCastExpr 0x55f4a2cc9a28 <col:8> 'int' <LValueToRValue>
    |       |   | `-DeclRefExpr 0x55f4a2cc99e8 <col:8> 'int' lvalue Var 0x55f4a2cc7ca8 'x' 'int'
    |       |   `-IntegerLiteral 0x55f4a2cc9a08 <col:12> 'int' 1
    |       `-BinaryOperator 0x55f4a2cc9b18 <line:15:4, col:12> 'int' '='
    |         |-DeclRefExpr 0x55f4a2cc9a80 <col:4> 'int' lvalue Var 0x55f4a2cc7d60 'y' 'int'
    |         `-BinaryOperator 0x55f4a2cc9af8 <col:8, col:12> 'int' '+'
    |           |-ImplicitCastExpr 0x55f4a2cc9ae0 <col:8> 'int' <LValueToRValue>
    |           | `-DeclRefExpr 0x55f4a2cc9aa0 <col:8> 'int' lvalue Var 0x55f4a2cc7d60 'y' 'int'
    |           `-IntegerLiteral 0x55f4a2cc9ac0 <col:12> 'int' 1
    |-CallExpr 0x55f4a2cc9ca0 <line:18:2, col:24> 'void'
    | |-ImplicitCastExpr 0x55f4a2cc9c88 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55f4a2cc9bb0 <col:2> 'void (int)' Function 0x55f4a2cc78b8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55f4a2cc9c40 <col:20, col:23> 'int' '=='
    |   |-ImplicitCastExpr 0x55f4a2cc9c10 <col:20> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55f4a2cc9bd0 <col:20> 'int' lvalue Var 0x55f4a2cc7d60 'y' 'int'
    |   `-ImplicitCastExpr 0x55f4a2cc9c28 <col:23> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x55f4a2cc9bf0 <col:23> 'int' lvalue Var 0x55f4a2cc7ca8 'x' 'int'
    `-ReturnStmt 0x55f4a2cc9ce8 <line:19:2, col:9>
      `-IntegerLiteral 0x55f4a2cc9cc8 <col:9> 'int' 0
1 warning generated.
