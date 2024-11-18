./Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_8.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_8.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x56091e006f28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x56091e0077c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x56091e0074c0 '__int128'
|-TypedefDecl 0x56091e007830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x56091e0074e0 'unsigned __int128'
|-TypedefDecl 0x56091e007b38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x56091e007910 'struct __NSConstantString_tag'
|   `-Record 0x56091e007888 '__NSConstantString_tag'
|-TypedefDecl 0x56091e007bd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x56091e007b90 'char *'
|   `-BuiltinType 0x56091e006fc0 'char'
|-TypedefDecl 0x56091e007ec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x56091e007e70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x56091e007cb0 'struct __va_list_tag'
|     `-Record 0x56091e007c28 '__va_list_tag'
|-FunctionDecl 0x56091e066ec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/mono-crafted_8.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56091e066f68 prev 0x56091e066ec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56091e0672e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x56091e067020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x56091e0670a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x56091e067120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x56091e0671a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x56091e0673a8 <col:99>
|-FunctionDecl 0x56091e067498 <line:3:1, col:80> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x56091e0677c8 <col:20, col:80>
|   `-CallExpr 0x56091e0676e0 <col:22, col:77> 'void'
|     |-ImplicitCastExpr 0x56091e0676c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x56091e067538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x56091e0672e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x56091e067738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56091e067720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56091e067598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x56091e067768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56091e067750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56091e0675f8 <col:41> 'char [17]' lvalue "mono-crafted_8.c"
|     |-ImplicitCastExpr 0x56091e067780 <col:61> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x56091e067620 <col:61> 'int' 3
|     `-ImplicitCastExpr 0x56091e0677b0 <col:64> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x56091e067798 <col:64> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x56091e067678 <col:64> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x56091e0678b8 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x56091e0677f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x56091e067b88 <col:34, col:84>
|   `-IfStmt 0x56091e067b70 <col:36, col:82>
|     |-UnaryOperator 0x56091e0679b8 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x56091e0679a0 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x56091e067980 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x56091e067960 <col:41> 'int' lvalue ParmVar 0x56091e0677f8 'cond' 'int'
|     `-CompoundStmt 0x56091e067b58 <col:48, col:82>
|       `-LabelStmt 0x56091e067b40 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x56091e067ad0 <col:57, col:80>
|           |-CallExpr 0x56091e067a30 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x56091e067a18 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x56091e0679d0 <col:58> 'void ()' Function 0x56091e067498 'reach_error' 'void ()'
|           `-CallExpr 0x56091e067ab0 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x56091e067a98 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x56091e067a50 <col:72> 'void (void) __attribute__((noreturn))' Function 0x56091e066f68 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x56091e067bf0 <line:6:1, line:18:1> line:6:5 main 'int ()'
  `-CompoundStmt 0x56091e069c88 <line:7:1, line:18:1>
    |-DeclStmt 0x56091e067d48 <line:8:2, col:20>
    | `-VarDecl 0x56091e067ca8 <col:2, col:19> col:15 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x56091e067d30 <col:19> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x56091e067d10 <col:19> 'int' 0
    |-DeclStmt 0x56091e069870 <line:9:2, col:27>
    | `-VarDecl 0x56091e0697d0 <col:2, col:19> col:15 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x56091e069858 <col:19> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x56091e069838 <col:19> 'int' 10000000
    |-DeclStmt 0x56091e069940 <line:10:2, col:24>
    | `-VarDecl 0x56091e0698a0 <col:2, col:17> col:15 used z 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x56091e069928 <col:17> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x56091e069908 <col:17> 'int' 5000000
    |-WhileStmt 0x56091e069b20 <line:11:2, line:15:2>
    | |-BinaryOperator 0x56091e0699c8 <line:11:8, col:10> 'int' '<'
    | | |-ImplicitCastExpr 0x56091e069998 <col:8> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x56091e069958 <col:8> 'unsigned int' lvalue Var 0x56091e067ca8 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x56091e0699b0 <col:10> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x56091e069978 <col:10> 'unsigned int' lvalue Var 0x56091e0697d0 'y' 'unsigned int'
    | `-CompoundStmt 0x56091e069b00 <col:12, line:15:2>
    |   |-IfStmt 0x56091e069ab0 <line:12:3, line:13:5>
    |   | |-BinaryOperator 0x56091e069a58 <line:12:6, col:9> 'int' '>='
    |   | | |-ImplicitCastExpr 0x56091e069a28 <col:6> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x56091e0699e8 <col:6> 'unsigned int' lvalue Var 0x56091e067ca8 'x' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x56091e069a40 <col:9> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x56091e069a08 <col:9> 'int' 5000000
    |   | `-UnaryOperator 0x56091e069a98 <line:13:4, col:5> 'unsigned int' postfix '--'
    |   |   `-DeclRefExpr 0x56091e069a78 <col:4> 'unsigned int' lvalue Var 0x56091e0698a0 'z' 'unsigned int'
    |   `-UnaryOperator 0x56091e069ae8 <line:14:3, col:4> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x56091e069ac8 <col:3> 'unsigned int' lvalue Var 0x56091e067ca8 'x' 'unsigned int'
    |-CallExpr 0x56091e069c30 <line:16:2, col:24> 'void'
    | |-ImplicitCastExpr 0x56091e069c18 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x56091e069b38 <col:2> 'void (int)' Function 0x56091e0678b8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x56091e069bc8 <col:20, col:23> 'int' '=='
    |   |-ImplicitCastExpr 0x56091e069b98 <col:20> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x56091e069b58 <col:20> 'unsigned int' lvalue Var 0x56091e0698a0 'z' 'unsigned int'
    |   `-ImplicitCastExpr 0x56091e069bb0 <col:23> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x56091e069b78 <col:23> 'int' 0
    `-ReturnStmt 0x56091e069c78 <line:17:2, col:9>
      `-IntegerLiteral 0x56091e069c58 <col:9> 'int' 0
1 warning generated.
