./Benchmark/PLDI/SVComp/loop-simple/nested_6.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-simple/nested_6.c:12:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5624684d2dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5624684d3660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5624684d3360 '__int128'
|-TypedefDecl 0x5624684d36d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5624684d3380 'unsigned __int128'
|-TypedefDecl 0x5624684d39d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5624684d37b0 'struct __NSConstantString_tag'
|   `-Record 0x5624684d3728 '__NSConstantString_tag'
|-TypedefDecl 0x5624684d3a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5624684d3a30 'char *'
|   `-BuiltinType 0x5624684d2e60 'char'
|-TypedefDecl 0x5624684d3d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5624684d3d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5624684d3b50 'struct __va_list_tag'
|     `-Record 0x5624684d3ac8 '__va_list_tag'
|-FunctionDecl 0x562468533108 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-simple/nested_6.c:12:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x562468532e48 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x562468532ec8 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x562468532f48 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x562468532fc8 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5624685331c8 <col:99>
|-FunctionDecl 0x5624685332b8 <line:13:1, col:75> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5624685335e8 <col:20, col:75>
|   `-CallExpr 0x562468533500 <col:22, col:72> 'void'
|     |-ImplicitCastExpr 0x5624685334e8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x562468533358 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x562468533108 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x562468533558 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x562468533540 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5624685333b8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x562468533588 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x562468533570 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x562468533418 <col:41> 'char [11]' lvalue "nested_6.c"
|     |-ImplicitCastExpr 0x5624685335a0 <col:55> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x562468533440 <col:55> 'int' 13
|     `-ImplicitCastExpr 0x5624685335d0 <col:59> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5624685335b8 <col:59> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x562468533498 <col:59> 'char [12]' lvalue "reach_error"
`-FunctionDecl 0x562468533650 <line:15:1, line:40:1> line:15:5 main 'int ()'
  `-CompoundStmt 0x562468536580 <col:12, line:40:1>
    |-DeclStmt 0x562468533790 <line:16:2, col:11>
    | `-VarDecl 0x562468533708 <col:2, col:10> col:6 used a 'int' cinit
    |   `-IntegerLiteral 0x562468533770 <col:10> 'int' 6
    |-DeclStmt 0x562468533848 <line:17:2, col:11>
    | `-VarDecl 0x5624685337c0 <col:2, col:10> col:6 used b 'int' cinit
    |   `-IntegerLiteral 0x562468533828 <col:10> 'int' 6
    |-DeclStmt 0x562468533900 <line:18:2, col:11>
    | `-VarDecl 0x562468533878 <col:2, col:10> col:6 used c 'int' cinit
    |   `-IntegerLiteral 0x5624685338e0 <col:10> 'int' 6
    |-DeclStmt 0x5624685339b8 <line:19:2, col:11>
    | `-VarDecl 0x562468533930 <col:2, col:10> col:6 used d 'int' cinit
    |   `-IntegerLiteral 0x562468533998 <col:10> 'int' 6
    |-DeclStmt 0x562468533a70 <line:20:2, col:11>
    | `-VarDecl 0x5624685339e8 <col:2, col:10> col:6 used e 'int' cinit
    |   `-IntegerLiteral 0x562468533a50 <col:10> 'int' 6
    |-DeclStmt 0x562468533b28 <line:21:2, col:11>
    | `-VarDecl 0x562468533aa0 <col:2, col:10> col:6 used f 'int' cinit
    |   `-IntegerLiteral 0x562468533b08 <col:10> 'int' 6
    |-ForStmt 0x5624685360b8 <line:23:2, line:35:2>
    | |-BinaryOperator 0x562468533b80 <line:23:6, col:10> 'int' '='
    | | |-DeclRefExpr 0x562468533b40 <col:6> 'int' lvalue Var 0x562468533708 'a' 'int'
    | | `-IntegerLiteral 0x562468533b60 <col:10> 'int' 0
    | |-<<<NULL>>>
    | |-BinaryOperator 0x562468533bf8 <col:13, col:17> 'int' '<'
    | | |-ImplicitCastExpr 0x562468533be0 <col:13> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x562468533ba0 <col:13> 'int' lvalue Var 0x562468533708 'a' 'int'
    | | `-IntegerLiteral 0x562468533bc0 <col:17> 'int' 6
    | |-UnaryOperator 0x562468533c38 <col:20, col:22> 'int' prefix '++'
    | | `-DeclRefExpr 0x562468533c18 <col:22> 'int' lvalue Var 0x562468533708 'a' 'int'
    | `-CompoundStmt 0x5624685360a0 <col:25, line:35:2>
    |   `-ForStmt 0x562468536068 <line:24:3, line:34:3>
    |     |-BinaryOperator 0x562468533c90 <line:24:7, col:11> 'int' '='
    |     | |-DeclRefExpr 0x562468533c50 <col:7> 'int' lvalue Var 0x5624685337c0 'b' 'int'
    |     | `-IntegerLiteral 0x562468533c70 <col:11> 'int' 0
    |     |-<<<NULL>>>
    |     |-BinaryOperator 0x562468533d08 <col:14, col:18> 'int' '<'
    |     | |-ImplicitCastExpr 0x562468533cf0 <col:14> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x562468533cb0 <col:14> 'int' lvalue Var 0x5624685337c0 'b' 'int'
    |     | `-IntegerLiteral 0x562468533cd0 <col:18> 'int' 6
    |     |-UnaryOperator 0x562468533d48 <col:21, col:23> 'int' prefix '++'
    |     | `-DeclRefExpr 0x562468533d28 <col:23> 'int' lvalue Var 0x5624685337c0 'b' 'int'
    |     `-CompoundStmt 0x562468536050 <col:26, line:34:3>
    |       `-ForStmt 0x562468536018 <line:25:4, line:33:4>
    |         |-BinaryOperator 0x562468533da0 <line:25:8, col:12> 'int' '='
    |         | |-DeclRefExpr 0x562468533d60 <col:8> 'int' lvalue Var 0x562468533878 'c' 'int'
    |         | `-IntegerLiteral 0x562468533d80 <col:12> 'int' 0
    |         |-<<<NULL>>>
    |         |-BinaryOperator 0x562468535b90 <col:15, col:19> 'int' '<'
    |         | |-ImplicitCastExpr 0x562468533e00 <col:15> 'int' <LValueToRValue>
    |         | | `-DeclRefExpr 0x562468533dc0 <col:15> 'int' lvalue Var 0x562468533878 'c' 'int'
    |         | `-IntegerLiteral 0x562468533de0 <col:19> 'int' 6
    |         |-UnaryOperator 0x562468535bd0 <col:22, col:24> 'int' prefix '++'
    |         | `-DeclRefExpr 0x562468535bb0 <col:24> 'int' lvalue Var 0x562468533878 'c' 'int'
    |         `-CompoundStmt 0x562468536000 <col:27, line:33:4>
    |           `-ForStmt 0x562468535fc8 <line:26:5, line:32:5>
    |             |-BinaryOperator 0x562468535c28 <line:26:9, col:13> 'int' '='
    |             | |-DeclRefExpr 0x562468535be8 <col:9> 'int' lvalue Var 0x562468533930 'd' 'int'
    |             | `-IntegerLiteral 0x562468535c08 <col:13> 'int' 0
    |             |-<<<NULL>>>
    |             |-BinaryOperator 0x562468535ca0 <col:16, col:20> 'int' '<'
    |             | |-ImplicitCastExpr 0x562468535c88 <col:16> 'int' <LValueToRValue>
    |             | | `-DeclRefExpr 0x562468535c48 <col:16> 'int' lvalue Var 0x562468533930 'd' 'int'
    |             | `-IntegerLiteral 0x562468535c68 <col:20> 'int' 6
    |             |-UnaryOperator 0x562468535ce0 <col:23, col:25> 'int' prefix '++'
    |             | `-DeclRefExpr 0x562468535cc0 <col:25> 'int' lvalue Var 0x562468533930 'd' 'int'
    |             `-CompoundStmt 0x562468535fb0 <col:28, line:32:5>
    |               `-ForStmt 0x562468535f78 <line:27:6, line:31:6>
    |                 |-BinaryOperator 0x562468535d38 <line:27:10, col:14> 'int' '='
    |                 | |-DeclRefExpr 0x562468535cf8 <col:10> 'int' lvalue Var 0x5624685339e8 'e' 'int'
    |                 | `-IntegerLiteral 0x562468535d18 <col:14> 'int' 0
    |                 |-<<<NULL>>>
    |                 |-BinaryOperator 0x562468535db0 <col:17, col:21> 'int' '<'
    |                 | |-ImplicitCastExpr 0x562468535d98 <col:17> 'int' <LValueToRValue>
    |                 | | `-DeclRefExpr 0x562468535d58 <col:17> 'int' lvalue Var 0x5624685339e8 'e' 'int'
    |                 | `-IntegerLiteral 0x562468535d78 <col:21> 'int' 6
    |                 |-UnaryOperator 0x562468535df0 <col:24, col:26> 'int' prefix '++'
    |                 | `-DeclRefExpr 0x562468535dd0 <col:26> 'int' lvalue Var 0x5624685339e8 'e' 'int'
    |                 `-CompoundStmt 0x562468535f60 <col:29, line:31:6>
    |                   `-ForStmt 0x562468535f28 <line:28:7, line:30:7>
    |                     |-BinaryOperator 0x562468535e48 <line:28:11, col:15> 'int' '='
    |                     | |-DeclRefExpr 0x562468535e08 <col:11> 'int' lvalue Var 0x562468533aa0 'f' 'int'
    |                     | `-IntegerLiteral 0x562468535e28 <col:15> 'int' 0
    |                     |-<<<NULL>>>
    |                     |-BinaryOperator 0x562468535ec0 <col:18, col:22> 'int' '<'
    |                     | |-ImplicitCastExpr 0x562468535ea8 <col:18> 'int' <LValueToRValue>
    |                     | | `-DeclRefExpr 0x562468535e68 <col:18> 'int' lvalue Var 0x562468533aa0 'f' 'int'
    |                     | `-IntegerLiteral 0x562468535e88 <col:22> 'int' 6
    |                     |-UnaryOperator 0x562468535f00 <col:25, col:27> 'int' prefix '++'
    |                     | `-DeclRefExpr 0x562468535ee0 <col:27> 'int' lvalue Var 0x562468533aa0 'f' 'int'
    |                     `-CompoundStmt 0x562468535f18 <col:30, line:30:7>
    |-IfStmt 0x562468536538 <line:36:2, line:38:2>
    | |-UnaryOperator 0x562468536480 <line:36:5, col:63> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x562468536460 <col:6, col:63> 'int'
    | |   `-BinaryOperator 0x562468536440 <col:7, col:62> 'int' '&&'
    | |     |-BinaryOperator 0x5624685363a8 <col:7, col:52> 'int' '&&'
    | |     | |-BinaryOperator 0x562468536310 <col:7, col:42> 'int' '&&'
    | |     | | |-BinaryOperator 0x562468536278 <col:7, col:32> 'int' '&&'
    | |     | | | |-BinaryOperator 0x5624685361e0 <col:7, col:22> 'int' '&&'
    | |     | | | | |-BinaryOperator 0x562468536148 <col:7, col:12> 'int' '=='
    | |     | | | | | |-ImplicitCastExpr 0x562468536130 <col:7> 'int' <LValueToRValue>
    | |     | | | | | | `-DeclRefExpr 0x5624685360f0 <col:7> 'int' lvalue Var 0x562468533708 'a' 'int'
    | |     | | | | | `-IntegerLiteral 0x562468536110 <col:12> 'int' 6
    | |     | | | | `-BinaryOperator 0x5624685361c0 <col:17, col:22> 'int' '=='
    | |     | | | |   |-ImplicitCastExpr 0x5624685361a8 <col:17> 'int' <LValueToRValue>
    | |     | | | |   | `-DeclRefExpr 0x562468536168 <col:17> 'int' lvalue Var 0x5624685337c0 'b' 'int'
    | |     | | | |   `-IntegerLiteral 0x562468536188 <col:22> 'int' 6
    | |     | | | `-BinaryOperator 0x562468536258 <col:27, col:32> 'int' '=='
    | |     | | |   |-ImplicitCastExpr 0x562468536240 <col:27> 'int' <LValueToRValue>
    | |     | | |   | `-DeclRefExpr 0x562468536200 <col:27> 'int' lvalue Var 0x562468533878 'c' 'int'
    | |     | | |   `-IntegerLiteral 0x562468536220 <col:32> 'int' 6
    | |     | | `-BinaryOperator 0x5624685362f0 <col:37, col:42> 'int' '=='
    | |     | |   |-ImplicitCastExpr 0x5624685362d8 <col:37> 'int' <LValueToRValue>
    | |     | |   | `-DeclRefExpr 0x562468536298 <col:37> 'int' lvalue Var 0x562468533930 'd' 'int'
    | |     | |   `-IntegerLiteral 0x5624685362b8 <col:42> 'int' 6
    | |     | `-BinaryOperator 0x562468536388 <col:47, col:52> 'int' '=='
    | |     |   |-ImplicitCastExpr 0x562468536370 <col:47> 'int' <LValueToRValue>
    | |     |   | `-DeclRefExpr 0x562468536330 <col:47> 'int' lvalue Var 0x5624685339e8 'e' 'int'
    | |     |   `-IntegerLiteral 0x562468536350 <col:52> 'int' 6
    | |     `-BinaryOperator 0x562468536420 <col:57, col:62> 'int' '=='
    | |       |-ImplicitCastExpr 0x562468536408 <col:57> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5624685363c8 <col:57> 'int' lvalue Var 0x562468533aa0 'f' 'int'
    | |       `-IntegerLiteral 0x5624685363e8 <col:62> 'int' 6
    | `-CompoundStmt 0x562468536520 <col:66, line:38:2>
    |   `-CallExpr 0x562468536500 <line:37:3, col:15> 'void'
    |     `-ImplicitCastExpr 0x5624685364e8 <col:3> 'void (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562468536498 <col:3> 'void ()' Function 0x5624685332b8 'reach_error' 'void ()'
    `-ReturnStmt 0x562468536570 <line:39:2, col:9>
      `-IntegerLiteral 0x562468536550 <col:9> 'int' 1
1 warning generated.
