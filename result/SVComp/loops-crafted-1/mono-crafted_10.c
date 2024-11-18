./Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_10.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_10.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55d566eadf28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55d566eae7c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55d566eae4c0 '__int128'
|-TypedefDecl 0x55d566eae830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55d566eae4e0 'unsigned __int128'
|-TypedefDecl 0x55d566eaeb38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55d566eae910 'struct __NSConstantString_tag'
|   `-Record 0x55d566eae888 '__NSConstantString_tag'
|-TypedefDecl 0x55d566eaebd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55d566eaeb90 'char *'
|   `-BuiltinType 0x55d566eadfc0 'char'
|-TypedefDecl 0x55d566eaeec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55d566eaee70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55d566eaecb0 'struct __va_list_tag'
|     `-Record 0x55d566eaec28 '__va_list_tag'
|-FunctionDecl 0x55d566f0dec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_10.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55d566f0df68 prev 0x55d566f0dec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55d566f0e2e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55d566f0e020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55d566f0e0a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55d566f0e120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55d566f0e1a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55d566f0e3a8 <col:99>
|-FunctionDecl 0x55d566f0e498 <line:3:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55d566f0e7d8 <col:20, col:81>
|   `-CallExpr 0x55d566f0e6f0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x55d566f0e6d8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55d566f0e538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55d566f0e2e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55d566f0e748 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d566f0e730 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d566f0e598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55d566f0e778 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d566f0e760 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d566f0e5f8 <col:41> 'char [18]' lvalue "mono-crafted_10.c"
|     |-ImplicitCastExpr 0x55d566f0e790 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55d566f0e628 <col:62> 'int' 3
|     `-ImplicitCastExpr 0x55d566f0e7c0 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55d566f0e7a8 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55d566f0e688 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55d566f0e8c8 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55d566f0e808 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55d566f0eb98 <col:34, col:84>
|   `-IfStmt 0x55d566f0eb80 <col:36, col:82>
|     |-UnaryOperator 0x55d566f0e9c8 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55d566f0e9b0 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x55d566f0e990 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x55d566f0e970 <col:41> 'int' lvalue ParmVar 0x55d566f0e808 'cond' 'int'
|     `-CompoundStmt 0x55d566f0eb68 <col:48, col:82>
|       `-LabelStmt 0x55d566f0eb50 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x55d566f0eae0 <col:57, col:80>
|           |-CallExpr 0x55d566f0ea40 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x55d566f0ea28 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x55d566f0e9e0 <col:58> 'void ()' Function 0x55d566f0e498 'reach_error' 'void ()'
|           `-CallExpr 0x55d566f0eac0 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x55d566f0eaa8 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x55d566f0ea60 <col:72> 'void (void) __attribute__((noreturn))' Function 0x55d566f0df68 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x55d566f0ec80 <line:6:1, line:18:1> line:6:5 main 'int (void)'
  `-CompoundStmt 0x55d566f10ce8 <line:7:1, line:18:1>
    |-DeclStmt 0x55d566f10808 <line:8:2, col:20>
    | `-VarDecl 0x55d566f0ed60 <col:2, col:19> col:15 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55d566f107f0 <col:19> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55d566f107d0 <col:19> 'int' 0
    |-DeclStmt 0x55d566f108d8 <line:9:2, col:27>
    | `-VarDecl 0x55d566f10838 <col:2, col:19> col:15 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55d566f108c0 <col:19> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55d566f108a0 <col:19> 'int' 10000000
    |-DeclStmt 0x55d566f109a8 <line:10:2, col:24>
    | `-VarDecl 0x55d566f10908 <col:2, col:17> col:15 used z 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55d566f10990 <col:17> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55d566f10970 <col:17> 'int' 5000000
    |-WhileStmt 0x55d566f10b88 <line:11:2, line:15:2>
    | |-BinaryOperator 0x55d566f10a30 <line:11:8, col:10> 'int' '<'
    | | |-ImplicitCastExpr 0x55d566f10a00 <col:8> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55d566f109c0 <col:8> 'unsigned int' lvalue Var 0x55d566f0ed60 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55d566f10a18 <col:10> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55d566f109e0 <col:10> 'unsigned int' lvalue Var 0x55d566f10838 'y' 'unsigned int'
    | `-CompoundStmt 0x55d566f10b68 <col:12, line:15:2>
    |   |-IfStmt 0x55d566f10b18 <line:12:3, line:13:5>
    |   | |-BinaryOperator 0x55d566f10ac0 <line:12:6, col:9> 'int' '>='
    |   | | |-ImplicitCastExpr 0x55d566f10a90 <col:6> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55d566f10a50 <col:6> 'unsigned int' lvalue Var 0x55d566f0ed60 'x' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x55d566f10aa8 <col:9> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x55d566f10a70 <col:9> 'int' 5000000
    |   | `-UnaryOperator 0x55d566f10b00 <line:13:4, col:5> 'unsigned int' postfix '++'
    |   |   `-DeclRefExpr 0x55d566f10ae0 <col:4> 'unsigned int' lvalue Var 0x55d566f10908 'z' 'unsigned int'
    |   `-UnaryOperator 0x55d566f10b50 <line:14:3, col:4> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55d566f10b30 <col:3> 'unsigned int' lvalue Var 0x55d566f0ed60 'x' 'unsigned int'
    |-CallExpr 0x55d566f10c90 <line:16:2, col:24> 'void'
    | |-ImplicitCastExpr 0x55d566f10c78 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55d566f10ba0 <col:2> 'void (int)' Function 0x55d566f0e8c8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55d566f10c30 <col:20, col:23> 'int' '=='
    |   |-ImplicitCastExpr 0x55d566f10c00 <col:20> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55d566f10bc0 <col:20> 'unsigned int' lvalue Var 0x55d566f10908 'z' 'unsigned int'
    |   `-ImplicitCastExpr 0x55d566f10c18 <col:23> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x55d566f10be0 <col:23> 'unsigned int' lvalue Var 0x55d566f0ed60 'x' 'unsigned int'
    `-ReturnStmt 0x55d566f10cd8 <line:17:2, col:9>
      `-IntegerLiteral 0x55d566f10cb8 <col:9> 'int' 0
1 warning generated.
