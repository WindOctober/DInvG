./Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_3.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_3.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x560b61c11f28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x560b61c127c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x560b61c124c0 '__int128'
|-TypedefDecl 0x560b61c12830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x560b61c124e0 'unsigned __int128'
|-TypedefDecl 0x560b61c12b38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x560b61c12910 'struct __NSConstantString_tag'
|   `-Record 0x560b61c12888 '__NSConstantString_tag'
|-TypedefDecl 0x560b61c12bd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x560b61c12b90 'char *'
|   `-BuiltinType 0x560b61c11fc0 'char'
|-TypedefDecl 0x560b61c12ec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x560b61c12e70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x560b61c12cb0 'struct __va_list_tag'
|     `-Record 0x560b61c12c28 '__va_list_tag'
|-FunctionDecl 0x560b61c71ed8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_3.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x560b61c71f78 prev 0x560b61c71ed8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x560b61c722f8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x560b61c72030 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x560b61c720b0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x560b61c72130 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x560b61c721b0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x560b61c723b8 <col:99>
|-FunctionDecl 0x560b61c724a8 <line:3:1, col:80> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x560b61c727d8 <col:20, col:80>
|   `-CallExpr 0x560b61c726f0 <col:22, col:77> 'void'
|     |-ImplicitCastExpr 0x560b61c726d8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x560b61c72548 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x560b61c722f8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x560b61c72748 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x560b61c72730 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x560b61c725a8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x560b61c72778 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x560b61c72760 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x560b61c72608 <col:41> 'char [17]' lvalue "mono-crafted_3.c"
|     |-ImplicitCastExpr 0x560b61c72790 <col:61> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x560b61c72630 <col:61> 'int' 3
|     `-ImplicitCastExpr 0x560b61c727c0 <col:64> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x560b61c727a8 <col:64> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x560b61c72688 <col:64> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x560b61c728c8 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x560b61c72808 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x560b61c72b98 <col:34, col:84>
|   `-IfStmt 0x560b61c72b80 <col:36, col:82>
|     |-UnaryOperator 0x560b61c729c8 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x560b61c729b0 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x560b61c72990 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x560b61c72970 <col:41> 'int' lvalue ParmVar 0x560b61c72808 'cond' 'int'
|     `-CompoundStmt 0x560b61c72b68 <col:48, col:82>
|       `-LabelStmt 0x560b61c72b50 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x560b61c72ae0 <col:57, col:80>
|           |-CallExpr 0x560b61c72a40 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x560b61c72a28 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x560b61c729e0 <col:58> 'void ()' Function 0x560b61c724a8 'reach_error' 'void ()'
|           `-CallExpr 0x560b61c72ac0 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x560b61c72aa8 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x560b61c72a60 <col:72> 'void (void) __attribute__((noreturn))' Function 0x560b61c71f78 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x560b61c72c00 <line:6:1, line:25:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x560b61c74e58 <line:7:1, line:25:1>
    |-DeclStmt 0x560b61c748a0 <line:8:2, col:22>
    | |-VarDecl 0x560b61c72cb8 <col:2, col:8> col:6 used x 'int' cinit
    | | `-IntegerLiteral 0x560b61c72d20 <col:8> 'int' 0
    | |-VarDecl 0x560b61c72d58 <col:2, col:12> col:10 used y 'int' cinit
    | | `-IntegerLiteral 0x560b61c72dc0 <col:12> 'int' 500000
    | `-VarDecl 0x560b61c747f8 <col:2, col:21> col:19 used z 'int' cinit
    |   `-IntegerLiteral 0x560b61c74860 <col:21> 'int' 0
    |-BinaryOperator 0x560b61c748f8 <line:9:2, col:4> 'int' '='
    | |-DeclRefExpr 0x560b61c748b8 <col:2> 'int' lvalue Var 0x560b61c72cb8 'x' 'int'
    | `-IntegerLiteral 0x560b61c748d8 <col:4> 'int' 0
    |-WhileStmt 0x560b61c74b10 <line:10:2, line:17:2>
    | |-BinaryOperator 0x560b61c74970 <line:10:8, col:10> 'int' '<'
    | | |-ImplicitCastExpr 0x560b61c74958 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x560b61c74918 <col:8> 'int' lvalue Var 0x560b61c72cb8 'x' 'int'
    | | `-IntegerLiteral 0x560b61c74938 <col:10> 'int' 1000000
    | `-CompoundStmt 0x560b61c74af8 <col:18, line:17:2>
    |   `-IfStmt 0x560b61c74ad0 <line:11:3, line:16:3> has_else
    |     |-BinaryOperator 0x560b61c749e8 <line:11:6, col:8> 'int' '<'
    |     | |-ImplicitCastExpr 0x560b61c749d0 <col:6> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x560b61c74990 <col:6> 'int' lvalue Var 0x560b61c72cb8 'x' 'int'
    |     | `-IntegerLiteral 0x560b61c749b0 <col:8> 'int' 500000
    |     |-UnaryOperator 0x560b61c74a28 <line:12:4, col:5> 'int' postfix '++'
    |     | `-DeclRefExpr 0x560b61c74a08 <col:4> 'int' lvalue Var 0x560b61c72cb8 'x' 'int'
    |     `-CompoundStmt 0x560b61c74ab0 <line:13:7, line:16:3>
    |       |-UnaryOperator 0x560b61c74a60 <line:14:4, col:5> 'int' postfix '++'
    |       | `-DeclRefExpr 0x560b61c74a40 <col:4> 'int' lvalue Var 0x560b61c72cb8 'x' 'int'
    |       `-UnaryOperator 0x560b61c74a98 <line:15:4, col:5> 'int' postfix '++'
    |         `-DeclRefExpr 0x560b61c74a78 <col:4> 'int' lvalue Var 0x560b61c72d58 'y' 'int'
    |-WhileStmt 0x560b61c74cf0 <line:18:2, line:22:2>
    | |-BinaryOperator 0x560b61c74b80 <line:18:8, col:10> 'int' '>'
    | | |-ImplicitCastExpr 0x560b61c74b68 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x560b61c74b28 <col:8> 'int' lvalue Var 0x560b61c72d58 'y' 'int'
    | | `-IntegerLiteral 0x560b61c74b48 <col:10> 'int' 0
    | `-CompoundStmt 0x560b61c74cc8 <col:12, line:22:2>
    |   |-UnaryOperator 0x560b61c74bc0 <line:19:3, col:4> 'int' postfix '--'
    |   | `-DeclRefExpr 0x560b61c74ba0 <col:3> 'int' lvalue Var 0x560b61c72cb8 'x' 'int'
    |   |-UnaryOperator 0x560b61c74bf8 <line:20:3, col:4> 'int' postfix '++'
    |   | `-DeclRefExpr 0x560b61c74bd8 <col:3> 'int' lvalue Var 0x560b61c747f8 'z' 'int'
    |   `-BinaryOperator 0x560b61c74ca8 <line:21:3, col:7> 'int' '='
    |     |-DeclRefExpr 0x560b61c74c10 <col:3> 'int' lvalue Var 0x560b61c72d58 'y' 'int'
    |     `-BinaryOperator 0x560b61c74c88 <col:5, col:7> 'int' '-'
    |       |-ImplicitCastExpr 0x560b61c74c70 <col:5> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x560b61c74c30 <col:5> 'int' lvalue Var 0x560b61c72d58 'y' 'int'
    |       `-IntegerLiteral 0x560b61c74c50 <col:7> 'int' 2
    |-CallExpr 0x560b61c74e00 <line:23:2, col:24> 'void'
    | |-ImplicitCastExpr 0x560b61c74de8 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x560b61c74d08 <col:2> 'void (int)' Function 0x560b61c728c8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x560b61c74d98 <col:20, col:23> 'int' '=='
    |   |-ImplicitCastExpr 0x560b61c74d68 <col:20> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x560b61c74d28 <col:20> 'int' lvalue Var 0x560b61c72cb8 'x' 'int'
    |   `-ImplicitCastExpr 0x560b61c74d80 <col:23> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x560b61c74d48 <col:23> 'int' lvalue Var 0x560b61c747f8 'z' 'int'
    `-ReturnStmt 0x560b61c74e48 <line:24:2, col:9>
      `-IntegerLiteral 0x560b61c74e28 <col:9> 'int' 0
1 warning generated.
