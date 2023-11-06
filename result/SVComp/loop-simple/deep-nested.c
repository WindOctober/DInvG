./Benchmark/PLDI/SVComp/loop-simple/deep-nested.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-simple/deep-nested.c:1:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5633a51dfeb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5633a51e0750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5633a51e0450 '__int128'
|-TypedefDecl 0x5633a51e07c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5633a51e0470 'unsigned __int128'
|-TypedefDecl 0x5633a51e0ac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5633a51e08a0 'struct __NSConstantString_tag'
|   `-Record 0x5633a51e0818 '__NSConstantString_tag'
|-TypedefDecl 0x5633a51e0b60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5633a51e0b20 'char *'
|   `-BuiltinType 0x5633a51dff50 'char'
|-TypedefDecl 0x5633a51e0e58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5633a51e0e00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5633a51e0c40 'struct __va_list_tag'
|     `-Record 0x5633a51e0bb8 '__va_list_tag'
|-FunctionDecl 0x5633a52400d8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-simple/deep-nested.c:1:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5633a523fe18 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5633a523fe98 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5633a523ff18 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5633a523ff98 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5633a5240198 <col:99>
|-FunctionDecl 0x5633a5240288 <line:2:1, col:77> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5633a52405b8 <col:20, col:77>
|   `-CallExpr 0x5633a52404d0 <col:22, col:74> 'void'
|     |-ImplicitCastExpr 0x5633a52404b8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5633a5240328 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5633a52400d8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5633a5240528 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5633a5240510 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5633a5240388 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5633a5240558 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5633a5240540 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5633a52403e8 <col:41> 'char [14]' lvalue "deep-nested.c"
|     |-ImplicitCastExpr 0x5633a5240570 <col:58> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5633a5240410 <col:58> 'int' 2
|     `-ImplicitCastExpr 0x5633a52405a0 <col:61> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5633a5240588 <col:61> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5633a5240468 <col:61> 'char [12]' lvalue "reach_error"
`-FunctionDecl 0x5633a5240620 <line:4:1, line:25:1> line:4:5 main 'int ()'
  `-CompoundStmt 0x5633a52436d8 <col:12, line:25:1>
    |-DeclStmt 0x5633a5240970 <line:5:2, col:24>
    | |-VarDecl 0x5633a52406d8 <col:2, col:11> col:11 used a 'unsigned int'
    | |-VarDecl 0x5633a5240758 <col:2, col:14> col:14 used b 'unsigned int'
    | |-VarDecl 0x5633a52407d8 <col:2, col:17> col:17 used c 'unsigned int'
    | |-VarDecl 0x5633a5240858 <col:2, col:20> col:20 used d 'unsigned int'
    | `-VarDecl 0x5633a52408d8 <col:2, col:23> col:23 used e 'unsigned int'
    |-DeclStmt 0x5633a5240a08 <line:7:2, col:21>
    | `-VarDecl 0x5633a52409a0 <col:2, col:11> col:11 used uint32_max 'unsigned int'
    |-BinaryOperator 0x5633a5240a60 <line:8:2, col:15> 'unsigned int' '='
    | |-DeclRefExpr 0x5633a5240a20 <col:2> 'unsigned int' lvalue Var 0x5633a52409a0 'uint32_max' 'unsigned int'
    | `-IntegerLiteral 0x5633a5240a40 <col:15> 'unsigned int' 4294967295
    |-ForStmt 0x5633a5243670 <line:10:2, line:22:2>
    | |-BinaryOperator 0x5633a5240ad8 <line:10:7, col:11> 'unsigned int' '='
    | | |-DeclRefExpr 0x5633a5240a80 <col:7> 'unsigned int' lvalue Var 0x5633a52406d8 'a' 'unsigned int'
    | | `-ImplicitCastExpr 0x5633a5240ac0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5633a5240aa0 <col:11> 'int' 0
    | |-<<<NULL>>>
    | |-BinaryOperator 0x5633a5240bc0 <col:14, col:31> 'int' '<'
    | | |-ImplicitCastExpr 0x5633a5240ba8 <col:14> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5633a5240af8 <col:14> 'unsigned int' lvalue Var 0x5633a52406d8 'a' 'unsigned int'
    | | `-BinaryOperator 0x5633a5240b88 <col:18, col:31> 'unsigned int' '-'
    | |   |-ImplicitCastExpr 0x5633a5240b58 <col:18> 'unsigned int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x5633a5240b18 <col:18> 'unsigned int' lvalue Var 0x5633a52409a0 'uint32_max' 'unsigned int'
    | |   `-ImplicitCastExpr 0x5633a5240b70 <col:31> 'unsigned int' <IntegralCast>
    | |     `-IntegerLiteral 0x5633a5240b38 <col:31> 'int' 1
    | |-UnaryOperator 0x5633a5240c00 <col:34, col:36> 'unsigned int' prefix '++'
    | | `-DeclRefExpr 0x5633a5240be0 <col:36> 'unsigned int' lvalue Var 0x5633a52406d8 'a' 'unsigned int'
    | `-CompoundStmt 0x5633a5243658 <col:39, line:22:2>
    |   `-ForStmt 0x5633a5243620 <line:11:3, line:21:3>
    |     |-BinaryOperator 0x5633a5240c70 <line:11:8, col:12> 'unsigned int' '='
    |     | |-DeclRefExpr 0x5633a5240c18 <col:8> 'unsigned int' lvalue Var 0x5633a5240758 'b' 'unsigned int'
    |     | `-ImplicitCastExpr 0x5633a5240c58 <col:12> 'unsigned int' <IntegralCast>
    |     |   `-IntegerLiteral 0x5633a5240c38 <col:12> 'int' 0
    |     |-<<<NULL>>>
    |     |-BinaryOperator 0x5633a5240d58 <col:15, col:32> 'int' '<'
    |     | |-ImplicitCastExpr 0x5633a5240d40 <col:15> 'unsigned int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x5633a5240c90 <col:15> 'unsigned int' lvalue Var 0x5633a5240758 'b' 'unsigned int'
    |     | `-BinaryOperator 0x5633a5240d20 <col:19, col:32> 'unsigned int' '-'
    |     |   |-ImplicitCastExpr 0x5633a5240cf0 <col:19> 'unsigned int' <LValueToRValue>
    |     |   | `-DeclRefExpr 0x5633a5240cb0 <col:19> 'unsigned int' lvalue Var 0x5633a52409a0 'uint32_max' 'unsigned int'
    |     |   `-ImplicitCastExpr 0x5633a5240d08 <col:32> 'unsigned int' <IntegralCast>
    |     |     `-IntegerLiteral 0x5633a5240cd0 <col:32> 'int' 1
    |     |-UnaryOperator 0x5633a5240d98 <col:35, col:37> 'unsigned int' prefix '++'
    |     | `-DeclRefExpr 0x5633a5240d78 <col:37> 'unsigned int' lvalue Var 0x5633a5240758 'b' 'unsigned int'
    |     `-CompoundStmt 0x5633a5243608 <col:40, line:21:3>
    |       `-ForStmt 0x5633a52435d0 <line:12:4, line:20:4>
    |         |-BinaryOperator 0x5633a5242b78 <line:12:9, col:13> 'unsigned int' '='
    |         | |-DeclRefExpr 0x5633a5240db0 <col:9> 'unsigned int' lvalue Var 0x5633a52407d8 'c' 'unsigned int'
    |         | `-ImplicitCastExpr 0x5633a5242b60 <col:13> 'unsigned int' <IntegralCast>
    |         |   `-IntegerLiteral 0x5633a5240dd0 <col:13> 'int' 0
    |         |-<<<NULL>>>
    |         |-BinaryOperator 0x5633a5242c60 <col:16, col:33> 'int' '<'
    |         | |-ImplicitCastExpr 0x5633a5242c48 <col:16> 'unsigned int' <LValueToRValue>
    |         | | `-DeclRefExpr 0x5633a5242b98 <col:16> 'unsigned int' lvalue Var 0x5633a52407d8 'c' 'unsigned int'
    |         | `-BinaryOperator 0x5633a5242c28 <col:20, col:33> 'unsigned int' '-'
    |         |   |-ImplicitCastExpr 0x5633a5242bf8 <col:20> 'unsigned int' <LValueToRValue>
    |         |   | `-DeclRefExpr 0x5633a5242bb8 <col:20> 'unsigned int' lvalue Var 0x5633a52409a0 'uint32_max' 'unsigned int'
    |         |   `-ImplicitCastExpr 0x5633a5242c10 <col:33> 'unsigned int' <IntegralCast>
    |         |     `-IntegerLiteral 0x5633a5242bd8 <col:33> 'int' 1
    |         |-UnaryOperator 0x5633a5242ca0 <col:36, col:38> 'unsigned int' prefix '++'
    |         | `-DeclRefExpr 0x5633a5242c80 <col:38> 'unsigned int' lvalue Var 0x5633a52407d8 'c' 'unsigned int'
    |         `-CompoundStmt 0x5633a52435b8 <col:41, line:20:4>
    |           `-ForStmt 0x5633a5243580 <line:13:5, line:19:5>
    |             |-BinaryOperator 0x5633a5242d10 <line:13:10, col:14> 'unsigned int' '='
    |             | |-DeclRefExpr 0x5633a5242cb8 <col:10> 'unsigned int' lvalue Var 0x5633a5240858 'd' 'unsigned int'
    |             | `-ImplicitCastExpr 0x5633a5242cf8 <col:14> 'unsigned int' <IntegralCast>
    |             |   `-IntegerLiteral 0x5633a5242cd8 <col:14> 'int' 0
    |             |-<<<NULL>>>
    |             |-BinaryOperator 0x5633a5242df8 <col:17, col:34> 'int' '<'
    |             | |-ImplicitCastExpr 0x5633a5242de0 <col:17> 'unsigned int' <LValueToRValue>
    |             | | `-DeclRefExpr 0x5633a5242d30 <col:17> 'unsigned int' lvalue Var 0x5633a5240858 'd' 'unsigned int'
    |             | `-BinaryOperator 0x5633a5242dc0 <col:21, col:34> 'unsigned int' '-'
    |             |   |-ImplicitCastExpr 0x5633a5242d90 <col:21> 'unsigned int' <LValueToRValue>
    |             |   | `-DeclRefExpr 0x5633a5242d50 <col:21> 'unsigned int' lvalue Var 0x5633a52409a0 'uint32_max' 'unsigned int'
    |             |   `-ImplicitCastExpr 0x5633a5242da8 <col:34> 'unsigned int' <IntegralCast>
    |             |     `-IntegerLiteral 0x5633a5242d70 <col:34> 'int' 1
    |             |-UnaryOperator 0x5633a5242e38 <col:37, col:39> 'unsigned int' prefix '++'
    |             | `-DeclRefExpr 0x5633a5242e18 <col:39> 'unsigned int' lvalue Var 0x5633a5240858 'd' 'unsigned int'
    |             `-CompoundStmt 0x5633a5243568 <col:42, line:19:5>
    |               `-ForStmt 0x5633a5243530 <line:14:6, line:18:6>
    |                 |-BinaryOperator 0x5633a5242ea8 <line:14:11, col:15> 'unsigned int' '='
    |                 | |-DeclRefExpr 0x5633a5242e50 <col:11> 'unsigned int' lvalue Var 0x5633a52408d8 'e' 'unsigned int'
    |                 | `-ImplicitCastExpr 0x5633a5242e90 <col:15> 'unsigned int' <IntegralCast>
    |                 |   `-IntegerLiteral 0x5633a5242e70 <col:15> 'int' 0
    |                 |-<<<NULL>>>
    |                 |-BinaryOperator 0x5633a5242f90 <col:18, col:35> 'int' '<'
    |                 | |-ImplicitCastExpr 0x5633a5242f78 <col:18> 'unsigned int' <LValueToRValue>
    |                 | | `-DeclRefExpr 0x5633a5242ec8 <col:18> 'unsigned int' lvalue Var 0x5633a52408d8 'e' 'unsigned int'
    |                 | `-BinaryOperator 0x5633a5242f58 <col:22, col:35> 'unsigned int' '-'
    |                 |   |-ImplicitCastExpr 0x5633a5242f28 <col:22> 'unsigned int' <LValueToRValue>
    |                 |   | `-DeclRefExpr 0x5633a5242ee8 <col:22> 'unsigned int' lvalue Var 0x5633a52409a0 'uint32_max' 'unsigned int'
    |                 |   `-ImplicitCastExpr 0x5633a5242f40 <col:35> 'unsigned int' <IntegralCast>
    |                 |     `-IntegerLiteral 0x5633a5242f08 <col:35> 'int' 1
    |                 |-UnaryOperator 0x5633a5242fd0 <col:38, col:40> 'unsigned int' prefix '++'
    |                 | `-DeclRefExpr 0x5633a5242fb0 <col:40> 'unsigned int' lvalue Var 0x5633a52408d8 'e' 'unsigned int'
    |                 `-CompoundStmt 0x5633a5243518 <col:43, line:18:6>
    |                   `-IfStmt 0x5633a5243500 <line:15:7, line:17:7>
    |                     |-BinaryOperator 0x5633a5243430 <line:15:11, col:81> 'int' '&&'
    |                     | |-BinaryOperator 0x5633a52432e8 <col:11, col:54> 'int' '&&'
    |                     | | |-BinaryOperator 0x5633a5243218 <col:11, col:42> 'int' '&&'
    |                     | | | |-BinaryOperator 0x5633a5243148 <col:11, col:30> 'int' '&&'
    |                     | | | | |-ParenExpr 0x5633a5243078 <col:11, col:18> 'int'
    |                     | | | | | `-BinaryOperator 0x5633a5243058 <col:12, col:17> 'int' '=='
    |                     | | | | |   |-ImplicitCastExpr 0x5633a5243028 <col:12> 'unsigned int' <LValueToRValue>
    |                     | | | | |   | `-DeclRefExpr 0x5633a5242fe8 <col:12> 'unsigned int' lvalue Var 0x5633a52406d8 'a' 'unsigned int'
    |                     | | | | |   `-ImplicitCastExpr 0x5633a5243040 <col:17> 'unsigned int' <LValueToRValue>
    |                     | | | | |     `-DeclRefExpr 0x5633a5243008 <col:17> 'unsigned int' lvalue Var 0x5633a5240758 'b' 'unsigned int'
    |                     | | | | `-ParenExpr 0x5633a5243128 <col:23, col:30> 'int'
    |                     | | | |   `-BinaryOperator 0x5633a5243108 <col:24, col:29> 'int' '=='
    |                     | | | |     |-ImplicitCastExpr 0x5633a52430d8 <col:24> 'unsigned int' <LValueToRValue>
    |                     | | | |     | `-DeclRefExpr 0x5633a5243098 <col:24> 'unsigned int' lvalue Var 0x5633a5240758 'b' 'unsigned int'
    |                     | | | |     `-ImplicitCastExpr 0x5633a52430f0 <col:29> 'unsigned int' <LValueToRValue>
    |                     | | | |       `-DeclRefExpr 0x5633a52430b8 <col:29> 'unsigned int' lvalue Var 0x5633a52407d8 'c' 'unsigned int'
    |                     | | | `-ParenExpr 0x5633a52431f8 <col:35, col:42> 'int'
    |                     | | |   `-BinaryOperator 0x5633a52431d8 <col:36, col:41> 'int' '=='
    |                     | | |     |-ImplicitCastExpr 0x5633a52431a8 <col:36> 'unsigned int' <LValueToRValue>
    |                     | | |     | `-DeclRefExpr 0x5633a5243168 <col:36> 'unsigned int' lvalue Var 0x5633a52407d8 'c' 'unsigned int'
    |                     | | |     `-ImplicitCastExpr 0x5633a52431c0 <col:41> 'unsigned int' <LValueToRValue>
    |                     | | |       `-DeclRefExpr 0x5633a5243188 <col:41> 'unsigned int' lvalue Var 0x5633a5240858 'd' 'unsigned int'
    |                     | | `-ParenExpr 0x5633a52432c8 <col:47, col:54> 'int'
    |                     | |   `-BinaryOperator 0x5633a52432a8 <col:48, col:53> 'int' '=='
    |                     | |     |-ImplicitCastExpr 0x5633a5243278 <col:48> 'unsigned int' <LValueToRValue>
    |                     | |     | `-DeclRefExpr 0x5633a5243238 <col:48> 'unsigned int' lvalue Var 0x5633a5240858 'd' 'unsigned int'
    |                     | |     `-ImplicitCastExpr 0x5633a5243290 <col:53> 'unsigned int' <LValueToRValue>
    |                     | |       `-DeclRefExpr 0x5633a5243258 <col:53> 'unsigned int' lvalue Var 0x5633a52408d8 'e' 'unsigned int'
    |                     | `-ParenExpr 0x5633a5243410 <col:59, col:81> 'int'
    |                     |   `-BinaryOperator 0x5633a52433f0 <col:60, col:80> 'int' '=='
    |                     |     |-ImplicitCastExpr 0x5633a52433d8 <col:60> 'unsigned int' <LValueToRValue>
    |                     |     | `-DeclRefExpr 0x5633a5243308 <col:60> 'unsigned int' lvalue Var 0x5633a52408d8 'e' 'unsigned int'
    |                     |     `-ParenExpr 0x5633a52433b8 <col:65, col:80> 'unsigned int'
    |                     |       `-BinaryOperator 0x5633a5243398 <col:66, col:79> 'unsigned int' '-'
    |                     |         |-ImplicitCastExpr 0x5633a5243368 <col:66> 'unsigned int' <LValueToRValue>
    |                     |         | `-DeclRefExpr 0x5633a5243328 <col:66> 'unsigned int' lvalue Var 0x5633a52409a0 'uint32_max' 'unsigned int'
    |                     |         `-ImplicitCastExpr 0x5633a5243380 <col:79> 'unsigned int' <IntegralCast>
    |                     |           `-IntegerLiteral 0x5633a5243348 <col:79> 'int' 2
    |                     `-CompoundStmt 0x5633a52434e8 <col:84, line:17:7>
    |                       `-CompoundStmt 0x5633a52434d0 <line:16:8, col:23>
    |                         `-CallExpr 0x5633a52434b0 <col:9, col:21> 'void'
    |                           `-ImplicitCastExpr 0x5633a5243498 <col:9> 'void (*)()' <FunctionToPointerDecay>
    |                             `-DeclRefExpr 0x5633a5243450 <col:9> 'void ()' Function 0x5633a5240288 'reach_error' 'void ()'
    `-ReturnStmt 0x5633a52436c8 <line:24:2, col:9>
      `-IntegerLiteral 0x5633a52436a8 <col:9> 'int' 0
1 warning generated.
