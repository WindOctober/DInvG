./Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_6.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_6.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55da44403f28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55da444047c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55da444044c0 '__int128'
|-TypedefDecl 0x55da44404830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55da444044e0 'unsigned __int128'
|-TypedefDecl 0x55da44404b38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55da44404910 'struct __NSConstantString_tag'
|   `-Record 0x55da44404888 '__NSConstantString_tag'
|-TypedefDecl 0x55da44404bd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55da44404b90 'char *'
|   `-BuiltinType 0x55da44403fc0 'char'
|-TypedefDecl 0x55da44404ec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55da44404e70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55da44404cb0 'struct __va_list_tag'
|     `-Record 0x55da44404c28 '__va_list_tag'
|-FunctionDecl 0x55da44463ee8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_6.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55da44463f88 prev 0x55da44463ee8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55da44464308 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55da44464040 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55da444640c0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55da44464140 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55da444641c0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55da444643c8 <col:99>
|-FunctionDecl 0x55da444644b8 <line:3:1, col:80> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55da444647e8 <col:20, col:80>
|   `-CallExpr 0x55da44464700 <col:22, col:77> 'void'
|     |-ImplicitCastExpr 0x55da444646e8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55da44464558 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55da44464308 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55da44464758 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55da44464740 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55da444645b8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55da44464788 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55da44464770 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55da44464618 <col:41> 'char [17]' lvalue "mono-crafted_6.c"
|     |-ImplicitCastExpr 0x55da444647a0 <col:61> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55da44464640 <col:61> 'int' 3
|     `-ImplicitCastExpr 0x55da444647d0 <col:64> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55da444647b8 <col:64> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55da44464698 <col:64> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55da444648d8 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55da44464818 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55da44464ba8 <col:34, col:84>
|   `-IfStmt 0x55da44464b90 <col:36, col:82>
|     |-UnaryOperator 0x55da444649d8 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55da444649c0 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x55da444649a0 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x55da44464980 <col:41> 'int' lvalue ParmVar 0x55da44464818 'cond' 'int'
|     `-CompoundStmt 0x55da44464b78 <col:48, col:82>
|       `-LabelStmt 0x55da44464b60 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x55da44464af0 <col:57, col:80>
|           |-CallExpr 0x55da44464a50 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x55da44464a38 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x55da444649f0 <col:58> 'void ()' Function 0x55da444644b8 'reach_error' 'void ()'
|           `-CallExpr 0x55da44464ad0 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x55da44464ab8 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x55da44464a70 <col:72> 'void (void) __attribute__((noreturn))' Function 0x55da44463f88 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x55da44464c10 <line:6:1, line:25:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x55da44466df8 <line:7:1, line:25:1>
    |-DeclStmt 0x55da444668b0 <line:8:2, col:22>
    | |-VarDecl 0x55da44464cc8 <col:2, col:8> col:6 used x 'int' cinit
    | | `-IntegerLiteral 0x55da44464d30 <col:8> 'int' 0
    | |-VarDecl 0x55da44464d68 <col:2, col:12> col:10 used y 'int' cinit
    | | `-IntegerLiteral 0x55da44464dd0 <col:12> 'int' 500000
    | `-VarDecl 0x55da44466808 <col:2, col:21> col:19 z 'int' cinit
    |   `-IntegerLiteral 0x55da44466870 <col:21> 'int' 0
    |-BinaryOperator 0x55da44466908 <line:9:2, col:4> 'int' '='
    | |-DeclRefExpr 0x55da444668c8 <col:2> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    | `-IntegerLiteral 0x55da444668e8 <col:4> 'int' 0
    |-WhileStmt 0x55da44466ca8 <line:10:2, line:22:2>
    | |-BinaryOperator 0x55da44466980 <line:10:8, col:10> 'int' '<'
    | | |-ImplicitCastExpr 0x55da44466968 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55da44466928 <col:8> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    | | `-IntegerLiteral 0x55da44466948 <col:10> 'int' 1000000
    | `-CompoundStmt 0x55da44466c90 <col:18, line:22:2>
    |   `-IfStmt 0x55da44466c68 <line:11:3, line:21:3> has_else
    |     |-BinaryOperator 0x55da444669f8 <line:11:6, col:8> 'int' '<'
    |     | |-ImplicitCastExpr 0x55da444669e0 <col:6> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55da444669a0 <col:6> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    |     | `-IntegerLiteral 0x55da444669c0 <col:8> 'int' 500000
    |     |-UnaryOperator 0x55da44466a38 <line:12:4, col:5> 'int' postfix '++'
    |     | `-DeclRefExpr 0x55da44466a18 <col:4> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    |     `-CompoundStmt 0x55da44466c48 <line:13:7, line:21:3>
    |       |-IfStmt 0x55da44466be8 <line:14:4, line:19:4> has_else
    |       | |-BinaryOperator 0x55da44466aa8 <line:14:7, col:9> 'int' '<'
    |       | | |-ImplicitCastExpr 0x55da44466a90 <col:7> 'int' <LValueToRValue>
    |       | | | `-DeclRefExpr 0x55da44466a50 <col:7> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    |       | | `-IntegerLiteral 0x55da44466a70 <col:9> 'int' 750000
    |       | |-CompoundStmt 0x55da44466b00 <col:16, line:16:4>
    |       | | `-UnaryOperator 0x55da44466ae8 <line:15:5, col:6> 'int' postfix '++'
    |       | |   `-DeclRefExpr 0x55da44466ac8 <col:5> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    |       | `-CompoundStmt 0x55da44466bd0 <line:17:8, line:19:4>
    |       |   `-BinaryOperator 0x55da44466bb0 <line:18:5, col:9> 'int' '='
    |       |     |-DeclRefExpr 0x55da44466b18 <col:5> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    |       |     `-BinaryOperator 0x55da44466b90 <col:7, col:9> 'int' '+'
    |       |       |-ImplicitCastExpr 0x55da44466b78 <col:7> 'int' <LValueToRValue>
    |       |       | `-DeclRefExpr 0x55da44466b38 <col:7> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    |       |       `-IntegerLiteral 0x55da44466b58 <col:9> 'int' 2
    |       `-UnaryOperator 0x55da44466c30 <line:20:4, col:5> 'int' postfix '++'
    |         `-DeclRefExpr 0x55da44466c10 <col:4> 'int' lvalue Var 0x55da44464d68 'y' 'int'
    |-CallExpr 0x55da44466da0 <line:23:3, col:31> 'void'
    | |-ImplicitCastExpr 0x55da44466d88 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55da44466cc0 <col:3> 'void (int)' Function 0x55da444648d8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55da44466d38 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55da44466d20 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55da44466ce0 <col:21> 'int' lvalue Var 0x55da44464cc8 'x' 'int'
    |   `-IntegerLiteral 0x55da44466d00 <col:24> 'int' 1000000
    `-ReturnStmt 0x55da44466de8 <line:24:2, col:9>
      `-IntegerLiteral 0x55da44466dc8 <col:9> 'int' 0
1 warning generated.
