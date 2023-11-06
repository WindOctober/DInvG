./Benchmark/PLDI/SVComp/loops-crafted-1/Mono6_1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono6_1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55a56d696e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55a56d697730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55a56d697430 '__int128'
|-TypedefDecl 0x55a56d6977a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55a56d697450 'unsigned __int128'
|-TypedefDecl 0x55a56d697aa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55a56d697880 'struct __NSConstantString_tag'
|   `-Record 0x55a56d6977f8 '__NSConstantString_tag'
|-TypedefDecl 0x55a56d697b40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55a56d697b00 'char *'
|   `-BuiltinType 0x55a56d696f30 'char'
|-TypedefDecl 0x55a56d697e38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55a56d697de0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55a56d697c20 'struct __va_list_tag'
|     `-Record 0x55a56d697b98 '__va_list_tag'
|-FunctionDecl 0x55a56d6f6e28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono6_1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a56d6f6ec8 prev 0x55a56d6f6e28 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a56d6f7248 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55a56d6f6f80 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55a56d6f7000 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55a56d6f7080 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55a56d6f7100 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55a56d6f7308 <col:99>
|-FunctionDecl 0x55a56d6f73f8 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55a56d6f7728 <col:20, col:73>
|   `-CallExpr 0x55a56d6f7640 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x55a56d6f7628 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55a56d6f7498 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55a56d6f7248 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55a56d6f7698 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55a56d6f7680 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55a56d6f74f8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55a56d6f76c8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55a56d6f76b0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55a56d6f7558 <col:41> 'char [10]' lvalue "Mono6_1.c"
|     |-ImplicitCastExpr 0x55a56d6f76e0 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55a56d6f7580 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x55a56d6f7710 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55a56d6f76f8 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55a56d6f75d8 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55a56d6f7818 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55a56d6f7758 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55a56d6f7ae8 <col:34, col:84>
|   `-IfStmt 0x55a56d6f7ad0 <col:36, col:82>
|     |-UnaryOperator 0x55a56d6f7918 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55a56d6f7900 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x55a56d6f78e0 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x55a56d6f78c0 <col:41> 'int' lvalue ParmVar 0x55a56d6f7758 'cond' 'int'
|     `-CompoundStmt 0x55a56d6f7ab8 <col:48, col:82>
|       `-LabelStmt 0x55a56d6f7aa0 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x55a56d6f7a30 <col:57, col:80>
|           |-CallExpr 0x55a56d6f7990 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x55a56d6f7978 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x55a56d6f7930 <col:58> 'void ()' Function 0x55a56d6f73f8 'reach_error' 'void ()'
|           `-CallExpr 0x55a56d6f7a10 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x55a56d6f79f8 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x55a56d6f79b0 <col:72> 'void (void) __attribute__((noreturn))' Function 0x55a56d6f6ec8 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x55a56d6f7bd0 <line:6:1, line:17:1> line:6:5 main 'int (void)'
  `-CompoundStmt 0x55a56d6f9c48 <col:16, line:17:1>
    |-DeclStmt 0x55a56d6f9768 <line:7:1, col:19>
    | `-VarDecl 0x55a56d6f7cb0 <col:1, col:18> col:14 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55a56d6f9750 <col:18> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55a56d6f9730 <col:18> 'int' 0
    |-DeclStmt 0x55a56d6f9838 <line:8:1, col:26>
    | `-VarDecl 0x55a56d6f9798 <col:1, col:18> col:14 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55a56d6f9820 <col:18> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55a56d6f9800 <col:18> 'int' 10000000
    |-DeclStmt 0x55a56d6f9908 <line:9:1, col:23>
    | `-VarDecl 0x55a56d6f9868 <col:1, col:16> col:14 used z 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55a56d6f98f0 <col:16> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55a56d6f98d0 <col:16> 'int' 5000000
    |-WhileStmt 0x55a56d6f9ae8 <line:10:2, line:14:2>
    | |-BinaryOperator 0x55a56d6f9990 <line:10:8, col:10> 'int' '<'
    | | |-ImplicitCastExpr 0x55a56d6f9960 <col:8> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55a56d6f9920 <col:8> 'unsigned int' lvalue Var 0x55a56d6f7cb0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55a56d6f9978 <col:10> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55a56d6f9940 <col:10> 'unsigned int' lvalue Var 0x55a56d6f9798 'y' 'unsigned int'
    | `-CompoundStmt 0x55a56d6f9ac8 <col:12, line:14:2>
    |   |-IfStmt 0x55a56d6f9a78 <line:11:3, line:12:5>
    |   | |-BinaryOperator 0x55a56d6f9a20 <line:11:6, col:9> 'int' '>='
    |   | | |-ImplicitCastExpr 0x55a56d6f99f0 <col:6> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55a56d6f99b0 <col:6> 'unsigned int' lvalue Var 0x55a56d6f7cb0 'x' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x55a56d6f9a08 <col:9> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x55a56d6f99d0 <col:9> 'int' 5000000
    |   | `-UnaryOperator 0x55a56d6f9a60 <line:12:4, col:5> 'unsigned int' postfix '++'
    |   |   `-DeclRefExpr 0x55a56d6f9a40 <col:4> 'unsigned int' lvalue Var 0x55a56d6f9868 'z' 'unsigned int'
    |   `-UnaryOperator 0x55a56d6f9ab0 <line:13:3, col:4> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55a56d6f9a90 <col:3> 'unsigned int' lvalue Var 0x55a56d6f7cb0 'x' 'unsigned int'
    |-CallExpr 0x55a56d6f9bf0 <line:15:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55a56d6f9bd8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55a56d6f9b00 <col:3> 'void (int)' Function 0x55a56d6f7818 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55a56d6f9b90 <col:21, col:24> 'int' '!='
    |   |-ImplicitCastExpr 0x55a56d6f9b60 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55a56d6f9b20 <col:21> 'unsigned int' lvalue Var 0x55a56d6f9868 'z' 'unsigned int'
    |   `-ImplicitCastExpr 0x55a56d6f9b78 <col:24> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55a56d6f9b40 <col:24> 'unsigned int' lvalue Var 0x55a56d6f7cb0 'x' 'unsigned int'
    `-ReturnStmt 0x55a56d6f9c38 <line:16:3, col:10>
      `-IntegerLiteral 0x55a56d6f9c18 <col:10> 'int' 0
1 warning generated.
