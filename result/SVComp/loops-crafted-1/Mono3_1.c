./Benchmark/PLDI/SVComp/loops-crafted-1/Mono3_1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono3_1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5580b71dae98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5580b71db730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5580b71db430 '__int128'
|-TypedefDecl 0x5580b71db7a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5580b71db450 'unsigned __int128'
|-TypedefDecl 0x5580b71dbaa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5580b71db880 'struct __NSConstantString_tag'
|   `-Record 0x5580b71db7f8 '__NSConstantString_tag'
|-TypedefDecl 0x5580b71dbb40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5580b71dbb00 'char *'
|   `-BuiltinType 0x5580b71daf30 'char'
|-TypedefDecl 0x5580b71dbe38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5580b71dbde0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5580b71dbc20 'struct __va_list_tag'
|     `-Record 0x5580b71dbb98 '__va_list_tag'
|-FunctionDecl 0x5580b723ae28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono3_1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5580b723aec8 prev 0x5580b723ae28 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5580b723b248 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5580b723af80 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5580b723b000 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5580b723b080 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5580b723b100 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5580b723b308 <col:99>
|-FunctionDecl 0x5580b723b3f8 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5580b723b728 <col:20, col:73>
|   `-CallExpr 0x5580b723b640 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x5580b723b628 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5580b723b498 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5580b723b248 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5580b723b698 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5580b723b680 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5580b723b4f8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5580b723b6c8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5580b723b6b0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5580b723b558 <col:41> 'char [10]' lvalue "Mono3_1.c"
|     |-ImplicitCastExpr 0x5580b723b6e0 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5580b723b580 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x5580b723b710 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5580b723b6f8 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5580b723b5d8 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5580b723b818 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5580b723b758 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5580b723bae8 <col:34, col:84>
|   `-IfStmt 0x5580b723bad0 <col:36, col:82>
|     |-UnaryOperator 0x5580b723b918 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5580b723b900 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x5580b723b8e0 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x5580b723b8c0 <col:41> 'int' lvalue ParmVar 0x5580b723b758 'cond' 'int'
|     `-CompoundStmt 0x5580b723bab8 <col:48, col:82>
|       `-LabelStmt 0x5580b723baa0 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x5580b723ba30 <col:57, col:80>
|           |-CallExpr 0x5580b723b990 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x5580b723b978 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x5580b723b930 <col:58> 'void ()' Function 0x5580b723b3f8 'reach_error' 'void ()'
|           `-CallExpr 0x5580b723ba10 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x5580b723b9f8 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x5580b723b9b0 <col:72> 'void (void) __attribute__((noreturn))' Function 0x5580b723aec8 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x5580b723bbd0 <line:6:1, line:18:1> line:6:5 main 'int (void)'
  `-CompoundStmt 0x5580b723dbc8 <col:16, line:18:1>
    |-DeclStmt 0x5580b723d768 <line:7:3, col:21>
    | `-VarDecl 0x5580b723bcb0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5580b723d750 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5580b723d730 <col:20> 'int' 0
    |-DeclStmt 0x5580b723d838 <line:8:3, col:21>
    | `-VarDecl 0x5580b723d798 <col:3, col:20> col:16 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5580b723d820 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5580b723d800 <col:20> 'int' 0
    |-WhileStmt 0x5580b723da90 <line:9:3, line:16:3>
    | |-BinaryOperator 0x5580b723d8c0 <line:9:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x5580b723d890 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5580b723d850 <col:10> 'unsigned int' lvalue Var 0x5580b723bcb0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x5580b723d8a8 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5580b723d870 <col:14> 'int' 1000000
    | `-CompoundStmt 0x5580b723da70 <col:23, line:16:3>
    |   |-IfStmt 0x5580b723da10 <line:10:5, line:14:5> has_else
    |   | |-BinaryOperator 0x5580b723d950 <line:10:9, col:11> 'int' '<'
    |   | | |-ImplicitCastExpr 0x5580b723d920 <col:9> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x5580b723d8e0 <col:9> 'unsigned int' lvalue Var 0x5580b723bcb0 'x' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x5580b723d938 <col:11> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x5580b723d900 <col:11> 'int' 500000
    |   | |-CompoundStmt 0x5580b723d9a8 <col:19, line:12:5>
    |   | | `-UnaryOperator 0x5580b723d990 <line:11:2, col:3> 'unsigned int' postfix '++'
    |   | |   `-DeclRefExpr 0x5580b723d970 <col:2> 'unsigned int' lvalue Var 0x5580b723d798 'y' 'unsigned int'
    |   | `-CompoundStmt 0x5580b723d9f8 <line:12:12, line:14:5>
    |   |   `-UnaryOperator 0x5580b723d9e0 <line:13:2, col:3> 'unsigned int' postfix '--'
    |   |     `-DeclRefExpr 0x5580b723d9c0 <col:2> 'unsigned int' lvalue Var 0x5580b723d798 'y' 'unsigned int'
    |   `-UnaryOperator 0x5580b723da58 <line:15:2, col:3> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x5580b723da38 <col:2> 'unsigned int' lvalue Var 0x5580b723bcb0 'x' 'unsigned int'
    `-CallExpr 0x5580b723dba0 <line:17:3, col:25> 'void'
      |-ImplicitCastExpr 0x5580b723db88 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x5580b723daa8 <col:3> 'void (int)' Function 0x5580b723b818 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x5580b723db38 <col:21, col:24> 'int' '!='
        |-ImplicitCastExpr 0x5580b723db08 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x5580b723dac8 <col:21> 'unsigned int' lvalue Var 0x5580b723d798 'y' 'unsigned int'
        `-ImplicitCastExpr 0x5580b723db20 <col:24> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x5580b723dae8 <col:24> 'int' 0
1 warning generated.
