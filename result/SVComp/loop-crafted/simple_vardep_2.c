./Benchmark/PLDI/SVComp/loop-crafted/simple_vardep_2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-crafted/simple_vardep_2.c:5:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5560e3717ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5560e3718780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5560e3718480 '__int128'
|-TypedefDecl 0x5560e37187f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5560e37184a0 'unsigned __int128'
|-TypedefDecl 0x5560e3718af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5560e37188d0 'struct __NSConstantString_tag'
|   `-Record 0x5560e3718848 '__NSConstantString_tag'
|-TypedefDecl 0x5560e3718b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5560e3718b50 'char *'
|   `-BuiltinType 0x5560e3717f80 'char'
|-TypedefDecl 0x5560e3718e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5560e3718e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5560e3718c70 'struct __va_list_tag'
|     `-Record 0x5560e3718be8 '__va_list_tag'
|-FunctionDecl 0x5560e3777fb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-crafted/simple_vardep_2.c:4:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5560e3778058 prev 0x5560e3777fb8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5560e37783d8 <line:5:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5560e3778110 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5560e3778190 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5560e3778210 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5560e3778290 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5560e3778498 <col:99>
|-FunctionDecl 0x5560e3778588 <line:6:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5560e37788c8 <col:20, col:81>
|   `-CallExpr 0x5560e37787e0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x5560e37787c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5560e3778628 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5560e37783d8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5560e3778838 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5560e3778820 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5560e3778688 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5560e3778868 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5560e3778850 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5560e37786e8 <col:41> 'char [18]' lvalue "simple_vardep_2.c"
|     |-ImplicitCastExpr 0x5560e3778880 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5560e3778718 <col:62> 'int' 6
|     `-ImplicitCastExpr 0x5560e37788b0 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5560e3778898 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5560e3778778 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5560e37789b8 <line:7:1, line:13:1> line:7:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5560e37788f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5560e3778c98 <line:8:1, line:13:1>
|   |-IfStmt 0x5560e3778c70 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x5560e3778ab8 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5560e3778aa0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5560e3778a80 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5560e3778a60 <col:9> 'int' lvalue ParmVar 0x5560e37788f8 'cond' 'int'
|   | `-CompoundStmt 0x5560e3778c58 <col:16, line:11:3>
|   |   `-LabelStmt 0x5560e3778c40 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5560e3778bd0 <col:12, col:35>
|   |       |-CallExpr 0x5560e3778b30 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5560e3778b18 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5560e3778ad0 <col:13> 'void ()' Function 0x5560e3778588 'reach_error' 'void ()'
|   |       `-CallExpr 0x5560e3778bb0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5560e3778b98 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5560e3778b50 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5560e3778058 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5560e3778c88 <line:12:3>
`-FunctionDecl 0x5560e3778d10 <line:15:1, line:28:1> line:15:5 main 'int ()'
  `-CompoundStmt 0x5560e377b050 <line:16:1, line:28:1>
    |-DeclStmt 0x5560e3778e68 <line:17:3, col:21>
    | `-VarDecl 0x5560e3778dc8 <col:3, col:20> col:16 used i 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5560e3778e50 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5560e3778e30 <col:20> 'int' 0
    |-DeclStmt 0x5560e377a960 <line:18:3, col:21>
    | `-VarDecl 0x5560e377a8c0 <col:3, col:20> col:16 used j 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5560e377a948 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5560e377a928 <col:20> 'int' 0
    |-DeclStmt 0x5560e377aa30 <line:19:3, col:21>
    | `-VarDecl 0x5560e377a990 <col:3, col:20> col:16 used k 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5560e377aa18 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5560e377a9f8 <col:20> 'int' 0
    `-WhileStmt 0x5560e377b038 <line:21:3, line:26:3>
      |-BinaryOperator 0x5560e377aab8 <line:21:10, col:14> 'int' '<'
      | |-ImplicitCastExpr 0x5560e377aa88 <col:10> 'unsigned int' <LValueToRValue>
      | | `-DeclRefExpr 0x5560e377aa48 <col:10> 'unsigned int' lvalue Var 0x5560e377a990 'k' 'unsigned int'
      | `-ImplicitCastExpr 0x5560e377aaa0 <col:14> 'unsigned int' <IntegralCast>
      |   `-IntegerLiteral 0x5560e377aa68 <col:14> 'int' 268435455
      `-CompoundStmt 0x5560e377b008 <col:26, line:26:3>
        |-BinaryOperator 0x5560e377ab88 <line:22:5, col:13> 'unsigned int' '='
        | |-DeclRefExpr 0x5560e377aad8 <col:5> 'unsigned int' lvalue Var 0x5560e3778dc8 'i' 'unsigned int'
        | `-BinaryOperator 0x5560e377ab68 <col:9, col:13> 'unsigned int' '+'
        |   |-ImplicitCastExpr 0x5560e377ab38 <col:9> 'unsigned int' <LValueToRValue>
        |   | `-DeclRefExpr 0x5560e377aaf8 <col:9> 'unsigned int' lvalue Var 0x5560e3778dc8 'i' 'unsigned int'
        |   `-ImplicitCastExpr 0x5560e377ab50 <col:13> 'unsigned int' <IntegralCast>
        |     `-IntegerLiteral 0x5560e377ab18 <col:13> 'int' 1
        |-BinaryOperator 0x5560e377ac58 <line:23:5, col:13> 'unsigned int' '='
        | |-DeclRefExpr 0x5560e377aba8 <col:5> 'unsigned int' lvalue Var 0x5560e377a8c0 'j' 'unsigned int'
        | `-BinaryOperator 0x5560e377ac38 <col:9, col:13> 'unsigned int' '+'
        |   |-ImplicitCastExpr 0x5560e377ac08 <col:9> 'unsigned int' <LValueToRValue>
        |   | `-DeclRefExpr 0x5560e377abc8 <col:9> 'unsigned int' lvalue Var 0x5560e377a8c0 'j' 'unsigned int'
        |   `-ImplicitCastExpr 0x5560e377ac20 <col:13> 'unsigned int' <IntegralCast>
        |     `-IntegerLiteral 0x5560e377abe8 <col:13> 'int' 2
        |-BinaryOperator 0x5560e377ad28 <line:24:5, col:13> 'unsigned int' '='
        | |-DeclRefExpr 0x5560e377ac78 <col:5> 'unsigned int' lvalue Var 0x5560e377a990 'k' 'unsigned int'
        | `-BinaryOperator 0x5560e377ad08 <col:9, col:13> 'unsigned int' '+'
        |   |-ImplicitCastExpr 0x5560e377acd8 <col:9> 'unsigned int' <LValueToRValue>
        |   | `-DeclRefExpr 0x5560e377ac98 <col:9> 'unsigned int' lvalue Var 0x5560e377a990 'k' 'unsigned int'
        |   `-ImplicitCastExpr 0x5560e377acf0 <col:13> 'unsigned int' <IntegralCast>
        |     `-IntegerLiteral 0x5560e377acb8 <col:13> 'int' 3
        `-CallExpr 0x5560e377afe0 <line:25:5, col:47> 'void'
          |-ImplicitCastExpr 0x5560e377afc8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
          | `-DeclRefExpr 0x5560e377ad48 <col:5> 'void (int)' Function 0x5560e37789b8 '__VERIFIER_assert' 'void (int)'
          `-BinaryOperator 0x5560e377af78 <col:23, col:46> 'int' '&&'
            |-ParenExpr 0x5560e377ae50 <col:23, col:32> 'int'
            | `-BinaryOperator 0x5560e377ae30 <col:24, col:31> 'int' '=='
            |   |-ImplicitCastExpr 0x5560e377ae18 <col:24> 'unsigned int' <LValueToRValue>
            |   | `-DeclRefExpr 0x5560e377ad68 <col:24> 'unsigned int' lvalue Var 0x5560e377a990 'k' 'unsigned int'
            |   `-BinaryOperator 0x5560e377adf8 <col:29, col:31> 'unsigned int' '*'
            |     |-ImplicitCastExpr 0x5560e377ade0 <col:29> 'unsigned int' <IntegralCast>
            |     | `-IntegerLiteral 0x5560e377ad88 <col:29> 'int' 3
            |     `-ImplicitCastExpr 0x5560e377adc8 <col:31> 'unsigned int' <LValueToRValue>
            |       `-DeclRefExpr 0x5560e377ada8 <col:31> 'unsigned int' lvalue Var 0x5560e3778dc8 'i' 'unsigned int'
            `-ParenExpr 0x5560e377af58 <col:37, col:46> 'int'
              `-BinaryOperator 0x5560e377af38 <col:38, col:45> 'int' '=='
                |-ImplicitCastExpr 0x5560e377af20 <col:38> 'unsigned int' <LValueToRValue>
                | `-DeclRefExpr 0x5560e377ae70 <col:38> 'unsigned int' lvalue Var 0x5560e377a8c0 'j' 'unsigned int'
                `-BinaryOperator 0x5560e377af00 <col:43, col:45> 'unsigned int' '*'
                  |-ImplicitCastExpr 0x5560e377aee8 <col:43> 'unsigned int' <IntegralCast>
                  | `-IntegerLiteral 0x5560e377ae90 <col:43> 'int' 2
                  `-ImplicitCastExpr 0x5560e377aed0 <col:45> 'unsigned int' <LValueToRValue>
                    `-DeclRefExpr 0x5560e377aeb0 <col:45> 'unsigned int' lvalue Var 0x5560e3778dc8 'i' 'unsigned int'
1 warning generated.
