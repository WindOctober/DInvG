./Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_7.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_7.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55576de24f28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55576de257c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55576de254c0 '__int128'
|-TypedefDecl 0x55576de25830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55576de254e0 'unsigned __int128'
|-TypedefDecl 0x55576de25b38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55576de25910 'struct __NSConstantString_tag'
|   `-Record 0x55576de25888 '__NSConstantString_tag'
|-TypedefDecl 0x55576de25bd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55576de25b90 'char *'
|   `-BuiltinType 0x55576de24fc0 'char'
|-TypedefDecl 0x55576de25ec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55576de25e70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55576de25cb0 'struct __va_list_tag'
|     `-Record 0x55576de25c28 '__va_list_tag'
|-FunctionDecl 0x55576de84ec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_7.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55576de84f68 prev 0x55576de84ec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55576de852e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55576de85020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55576de850a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55576de85120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55576de851a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55576de853a8 <col:99>
|-FunctionDecl 0x55576de85498 <line:3:1, col:80> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55576de857c8 <col:20, col:80>
|   `-CallExpr 0x55576de856e0 <col:22, col:77> 'void'
|     |-ImplicitCastExpr 0x55576de856c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55576de85538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55576de852e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55576de85738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55576de85720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55576de85598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55576de85768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55576de85750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55576de855f8 <col:41> 'char [17]' lvalue "mono-crafted_7.c"
|     |-ImplicitCastExpr 0x55576de85780 <col:61> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55576de85620 <col:61> 'int' 3
|     `-ImplicitCastExpr 0x55576de857b0 <col:64> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55576de85798 <col:64> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55576de85678 <col:64> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55576de858b8 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55576de857f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55576de85b88 <col:34, col:84>
|   `-IfStmt 0x55576de85b70 <col:36, col:82>
|     |-UnaryOperator 0x55576de859b8 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55576de859a0 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x55576de85980 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x55576de85960 <col:41> 'int' lvalue ParmVar 0x55576de857f8 'cond' 'int'
|     `-CompoundStmt 0x55576de85b58 <col:48, col:82>
|       `-LabelStmt 0x55576de85b40 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x55576de85ad0 <col:57, col:80>
|           |-CallExpr 0x55576de85a30 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x55576de85a18 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x55576de859d0 <col:58> 'void ()' Function 0x55576de85498 'reach_error' 'void ()'
|           `-CallExpr 0x55576de85ab0 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x55576de85a98 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x55576de85a50 <col:72> 'void (void) __attribute__((noreturn))' Function 0x55576de84f68 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x55576de85bf0 <line:6:1, line:24:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x55576de87e88 <line:7:1, line:24:1>
    |-DeclStmt 0x55576de87890 <line:8:2, col:21>
    | |-VarDecl 0x55576de85ca8 <col:2, col:8> col:6 used x 'int' cinit
    | | `-IntegerLiteral 0x55576de85d10 <col:8> 'int' 0
    | |-VarDecl 0x55576de85d48 <col:2, col:12> col:10 used y 'int' cinit
    | | `-IntegerLiteral 0x55576de85db0 <col:12> 'int' 50000
    | `-VarDecl 0x55576de877e8 <col:2, col:20> col:18 used z 'int' cinit
    |   `-IntegerLiteral 0x55576de87850 <col:20> 'int' 0
    |-BinaryOperator 0x55576de878e8 <line:9:2, col:4> 'int' '='
    | |-DeclRefExpr 0x55576de878a8 <col:2> 'int' lvalue Var 0x55576de85ca8 'x' 'int'
    | `-IntegerLiteral 0x55576de878c8 <col:4> 'int' 0
    |-WhileStmt 0x55576de87b00 <line:10:2, line:17:2>
    | |-BinaryOperator 0x55576de87960 <line:10:8, col:10> 'int' '<'
    | | |-ImplicitCastExpr 0x55576de87948 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55576de87908 <col:8> 'int' lvalue Var 0x55576de85ca8 'x' 'int'
    | | `-IntegerLiteral 0x55576de87928 <col:10> 'int' 1000000
    | `-CompoundStmt 0x55576de87ae8 <col:18, line:17:2>
    |   `-IfStmt 0x55576de87ac0 <line:11:3, line:16:3> has_else
    |     |-BinaryOperator 0x55576de879d8 <line:11:6, col:8> 'int' '<'
    |     | |-ImplicitCastExpr 0x55576de879c0 <col:6> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55576de87980 <col:6> 'int' lvalue Var 0x55576de85ca8 'x' 'int'
    |     | `-IntegerLiteral 0x55576de879a0 <col:8> 'int' 50000
    |     |-UnaryOperator 0x55576de87a18 <line:12:4, col:5> 'int' postfix '++'
    |     | `-DeclRefExpr 0x55576de879f8 <col:4> 'int' lvalue Var 0x55576de85ca8 'x' 'int'
    |     `-CompoundStmt 0x55576de87aa0 <line:13:7, line:16:3>
    |       |-UnaryOperator 0x55576de87a50 <line:14:4, col:5> 'int' postfix '++'
    |       | `-DeclRefExpr 0x55576de87a30 <col:4> 'int' lvalue Var 0x55576de85ca8 'x' 'int'
    |       `-UnaryOperator 0x55576de87a88 <line:15:4, col:5> 'int' postfix '++'
    |         `-DeclRefExpr 0x55576de87a68 <col:4> 'int' lvalue Var 0x55576de85d48 'y' 'int'
    |-WhileStmt 0x55576de87d20 <line:18:2, line:21:2>
    | |-BinaryOperator 0x55576de87b70 <line:18:8, col:10> 'int' '>'
    | | |-ImplicitCastExpr 0x55576de87b58 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55576de87b18 <col:8> 'int' lvalue Var 0x55576de85d48 'y' 'int'
    | | `-IntegerLiteral 0x55576de87b38 <col:10> 'int' 0
    | `-CompoundStmt 0x55576de87d00 <col:12, line:21:2>
    |   |-BinaryOperator 0x55576de87c28 <line:19:3, col:7> 'int' '='
    |   | |-DeclRefExpr 0x55576de87b90 <col:3> 'int' lvalue Var 0x55576de85d48 'y' 'int'
    |   | `-BinaryOperator 0x55576de87c08 <col:5, col:7> 'int' '-'
    |   |   |-ImplicitCastExpr 0x55576de87bf0 <col:5> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55576de87bb0 <col:5> 'int' lvalue Var 0x55576de85d48 'y' 'int'
    |   |   `-IntegerLiteral 0x55576de87bd0 <col:7> 'int' 2
    |   `-BinaryOperator 0x55576de87ce0 <line:20:3, col:7> 'int' '='
    |     |-DeclRefExpr 0x55576de87c48 <col:3> 'int' lvalue Var 0x55576de85ca8 'x' 'int'
    |     `-BinaryOperator 0x55576de87cc0 <col:5, col:7> 'int' '-'
    |       |-ImplicitCastExpr 0x55576de87ca8 <col:5> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55576de87c68 <col:5> 'int' lvalue Var 0x55576de85ca8 'x' 'int'
    |       `-IntegerLiteral 0x55576de87c88 <col:7> 'int' 2
    |-CallExpr 0x55576de87e30 <line:22:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55576de87e18 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55576de87d38 <col:3> 'void (int)' Function 0x55576de858b8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55576de87dc8 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55576de87d98 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55576de87d58 <col:21> 'int' lvalue Var 0x55576de877e8 'z' 'int'
    |   `-ImplicitCastExpr 0x55576de87db0 <col:24> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x55576de87d78 <col:24> 'int' lvalue Var 0x55576de85ca8 'x' 'int'
    `-ReturnStmt 0x55576de87e78 <line:23:2, col:9>
      `-IntegerLiteral 0x55576de87e58 <col:9> 'int' 0
1 warning generated.
