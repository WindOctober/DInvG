./Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x559829dbbf28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x559829dbc7c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x559829dbc4c0 '__int128'
|-TypedefDecl 0x559829dbc830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x559829dbc4e0 'unsigned __int128'
|-TypedefDecl 0x559829dbcb38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x559829dbc910 'struct __NSConstantString_tag'
|   `-Record 0x559829dbc888 '__NSConstantString_tag'
|-TypedefDecl 0x559829dbcbd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x559829dbcb90 'char *'
|   `-BuiltinType 0x559829dbbfc0 'char'
|-TypedefDecl 0x559829dbcec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x559829dbce70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x559829dbccb0 'struct __va_list_tag'
|     `-Record 0x559829dbcc28 '__va_list_tag'
|-FunctionDecl 0x559829e1bec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559829e1bf68 prev 0x559829e1bec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559829e1c2e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559829e1c020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x559829e1c0a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x559829e1c120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x559829e1c1a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x559829e1c3a8 <col:99>
|-FunctionDecl 0x559829e1c498 <line:3:1, col:80> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x559829e1c7c8 <col:20, col:80>
|   `-CallExpr 0x559829e1c6e0 <col:22, col:77> 'void'
|     |-ImplicitCastExpr 0x559829e1c6c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x559829e1c538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x559829e1c2e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x559829e1c738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x559829e1c720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x559829e1c598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x559829e1c768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x559829e1c750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x559829e1c5f8 <col:41> 'char [17]' lvalue "mono-crafted_1.c"
|     |-ImplicitCastExpr 0x559829e1c780 <col:61> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x559829e1c620 <col:61> 'int' 3
|     `-ImplicitCastExpr 0x559829e1c7b0 <col:64> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x559829e1c798 <col:64> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x559829e1c678 <col:64> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x559829e1c8b8 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x559829e1c7f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x559829e1cb88 <col:34, col:84>
|   `-IfStmt 0x559829e1cb70 <col:36, col:82>
|     |-UnaryOperator 0x559829e1c9b8 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x559829e1c9a0 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x559829e1c980 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x559829e1c960 <col:41> 'int' lvalue ParmVar 0x559829e1c7f8 'cond' 'int'
|     `-CompoundStmt 0x559829e1cb58 <col:48, col:82>
|       `-LabelStmt 0x559829e1cb40 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x559829e1cad0 <col:57, col:80>
|           |-CallExpr 0x559829e1ca30 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x559829e1ca18 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x559829e1c9d0 <col:58> 'void ()' Function 0x559829e1c498 'reach_error' 'void ()'
|           `-CallExpr 0x559829e1cab0 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x559829e1ca98 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x559829e1ca50 <col:72> 'void (void) __attribute__((noreturn))' Function 0x559829e1bf68 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x559829e1cbf0 <line:6:1, line:24:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x559829e1ed98 <line:7:1, line:24:1>
    |-DeclStmt 0x559829e1e890 <line:8:2, col:21>
    | |-VarDecl 0x559829e1cca8 <col:2, col:8> col:6 used x 'int' cinit
    | | `-IntegerLiteral 0x559829e1cd10 <col:8> 'int' 0
    | |-VarDecl 0x559829e1cd48 <col:2, col:12> col:10 used y 'int' cinit
    | | `-IntegerLiteral 0x559829e1cdb0 <col:12> 'int' 50000
    | `-VarDecl 0x559829e1e7e8 <col:2, col:20> col:18 used z 'int' cinit
    |   `-IntegerLiteral 0x559829e1e850 <col:20> 'int' 0
    |-BinaryOperator 0x559829e1e8e8 <line:9:2, col:4> 'int' '='
    | |-DeclRefExpr 0x559829e1e8a8 <col:2> 'int' lvalue Var 0x559829e1cca8 'x' 'int'
    | `-IntegerLiteral 0x559829e1e8c8 <col:4> 'int' 0
    |-WhileStmt 0x559829e1eb00 <line:10:2, line:17:2>
    | |-BinaryOperator 0x559829e1e960 <line:10:8, col:10> 'int' '<'
    | | |-ImplicitCastExpr 0x559829e1e948 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x559829e1e908 <col:8> 'int' lvalue Var 0x559829e1cca8 'x' 'int'
    | | `-IntegerLiteral 0x559829e1e928 <col:10> 'int' 1000000
    | `-CompoundStmt 0x559829e1eae8 <col:18, line:17:2>
    |   `-IfStmt 0x559829e1eac0 <line:11:3, line:16:3> has_else
    |     |-BinaryOperator 0x559829e1e9d8 <line:11:6, col:8> 'int' '<'
    |     | |-ImplicitCastExpr 0x559829e1e9c0 <col:6> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x559829e1e980 <col:6> 'int' lvalue Var 0x559829e1cca8 'x' 'int'
    |     | `-IntegerLiteral 0x559829e1e9a0 <col:8> 'int' 50000
    |     |-UnaryOperator 0x559829e1ea18 <line:12:4, col:5> 'int' postfix '++'
    |     | `-DeclRefExpr 0x559829e1e9f8 <col:4> 'int' lvalue Var 0x559829e1cca8 'x' 'int'
    |     `-CompoundStmt 0x559829e1eaa0 <line:13:7, line:16:3>
    |       |-UnaryOperator 0x559829e1ea50 <line:14:4, col:5> 'int' postfix '++'
    |       | `-DeclRefExpr 0x559829e1ea30 <col:4> 'int' lvalue Var 0x559829e1cca8 'x' 'int'
    |       `-UnaryOperator 0x559829e1ea88 <line:15:4, col:5> 'int' postfix '++'
    |         `-DeclRefExpr 0x559829e1ea68 <col:4> 'int' lvalue Var 0x559829e1cd48 'y' 'int'
    |-WhileStmt 0x559829e1ec38 <line:18:2, line:21:2>
    | |-BinaryOperator 0x559829e1eb88 <line:18:8, col:10> 'int' '>'
    | | |-ImplicitCastExpr 0x559829e1eb58 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x559829e1eb18 <col:8> 'int' lvalue Var 0x559829e1cd48 'y' 'int'
    | | `-ImplicitCastExpr 0x559829e1eb70 <col:10> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x559829e1eb38 <col:10> 'int' lvalue Var 0x559829e1e7e8 'z' 'int'
    | `-CompoundStmt 0x559829e1ec18 <col:12, line:21:2>
    |   |-UnaryOperator 0x559829e1ebc8 <line:19:3, col:4> 'int' postfix '--'
    |   | `-DeclRefExpr 0x559829e1eba8 <col:3> 'int' lvalue Var 0x559829e1cd48 'y' 'int'
    |   `-UnaryOperator 0x559829e1ec00 <line:20:3, col:4> 'int' postfix '--'
    |     `-DeclRefExpr 0x559829e1ebe0 <col:3> 'int' lvalue Var 0x559829e1cca8 'x' 'int'
    |-CallExpr 0x559829e1ed40 <line:22:2, col:24> 'void'
    | |-ImplicitCastExpr 0x559829e1ed28 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x559829e1ec50 <col:2> 'void (int)' Function 0x559829e1c8b8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x559829e1ece0 <col:20, col:23> 'int' '=='
    |   |-ImplicitCastExpr 0x559829e1ecb0 <col:20> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x559829e1ec70 <col:20> 'int' lvalue Var 0x559829e1cca8 'x' 'int'
    |   `-ImplicitCastExpr 0x559829e1ecc8 <col:23> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x559829e1ec90 <col:23> 'int' lvalue Var 0x559829e1e7e8 'z' 'int'
    `-ReturnStmt 0x559829e1ed88 <line:23:2, col:9>
      `-IntegerLiteral 0x559829e1ed68 <col:9> 'int' 0
1 warning generated.
