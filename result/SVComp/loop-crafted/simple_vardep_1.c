./Benchmark/PLDI/SVComp/loop-crafted/simple_vardep_1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-crafted/simple_vardep_1.c:5:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x562d5aa6fee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x562d5aa70780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x562d5aa70480 '__int128'
|-TypedefDecl 0x562d5aa707f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562d5aa704a0 'unsigned __int128'
|-TypedefDecl 0x562d5aa70af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x562d5aa708d0 'struct __NSConstantString_tag'
|   `-Record 0x562d5aa70848 '__NSConstantString_tag'
|-TypedefDecl 0x562d5aa70b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562d5aa70b50 'char *'
|   `-BuiltinType 0x562d5aa6ff80 'char'
|-TypedefDecl 0x562d5aa70e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562d5aa70e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562d5aa70c70 'struct __va_list_tag'
|     `-Record 0x562d5aa70be8 '__va_list_tag'
|-FunctionDecl 0x562d5aacffa8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-crafted/simple_vardep_1.c:4:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562d5aad0048 prev 0x562d5aacffa8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562d5aad03c8 <line:5:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x562d5aad0100 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x562d5aad0180 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x562d5aad0200 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x562d5aad0280 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x562d5aad0488 <col:99>
|-FunctionDecl 0x562d5aad0578 <line:6:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x562d5aad08b8 <col:20, col:81>
|   `-CallExpr 0x562d5aad07d0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x562d5aad07b8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x562d5aad0618 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x562d5aad03c8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x562d5aad0828 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x562d5aad0810 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x562d5aad0678 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x562d5aad0858 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x562d5aad0840 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x562d5aad06d8 <col:41> 'char [18]' lvalue "simple_vardep_1.c"
|     |-ImplicitCastExpr 0x562d5aad0870 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x562d5aad0708 <col:62> 'int' 6
|     `-ImplicitCastExpr 0x562d5aad08a0 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x562d5aad0888 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x562d5aad0768 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x562d5aad09a8 <line:7:1, line:13:1> line:7:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x562d5aad08e8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x562d5aad0c88 <line:8:1, line:13:1>
|   |-IfStmt 0x562d5aad0c60 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x562d5aad0aa8 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x562d5aad0a90 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x562d5aad0a70 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x562d5aad0a50 <col:9> 'int' lvalue ParmVar 0x562d5aad08e8 'cond' 'int'
|   | `-CompoundStmt 0x562d5aad0c48 <col:16, line:11:3>
|   |   `-LabelStmt 0x562d5aad0c30 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x562d5aad0bc0 <col:12, col:35>
|   |       |-CallExpr 0x562d5aad0b20 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x562d5aad0b08 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x562d5aad0ac0 <col:13> 'void ()' Function 0x562d5aad0578 'reach_error' 'void ()'
|   |       `-CallExpr 0x562d5aad0ba0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x562d5aad0b88 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x562d5aad0b40 <col:27> 'void (void) __attribute__((noreturn))' Function 0x562d5aad0048 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x562d5aad0c78 <line:12:3>
`-FunctionDecl 0x562d5aad0d00 <line:15:1, line:29:1> line:15:5 main 'int ()'
  `-CompoundStmt 0x562d5aad2f10 <line:16:1, line:29:1>
    |-DeclStmt 0x562d5aad0e58 <line:17:3, col:21>
    | `-VarDecl 0x562d5aad0db8 <col:3, col:20> col:16 used i 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x562d5aad0e40 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x562d5aad0e20 <col:20> 'int' 0
    |-DeclStmt 0x562d5aad2950 <line:18:3, col:21>
    | `-VarDecl 0x562d5aad28b0 <col:3, col:20> col:16 used j 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x562d5aad2938 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x562d5aad2918 <col:20> 'int' 0
    |-DeclStmt 0x562d5aad2a20 <line:19:3, col:21>
    | `-VarDecl 0x562d5aad2980 <col:3, col:20> col:16 used k 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x562d5aad2a08 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x562d5aad29e8 <col:20> 'int' 0
    `-WhileStmt 0x562d5aad2ef8 <line:21:3, line:27:3>
      |-BinaryOperator 0x562d5aad2aa8 <line:21:10, col:14> 'int' '<'
      | |-ImplicitCastExpr 0x562d5aad2a78 <col:10> 'unsigned int' <LValueToRValue>
      | | `-DeclRefExpr 0x562d5aad2a38 <col:10> 'unsigned int' lvalue Var 0x562d5aad2980 'k' 'unsigned int'
      | `-ImplicitCastExpr 0x562d5aad2a90 <col:14> 'unsigned int' <IntegralCast>
      |   `-IntegerLiteral 0x562d5aad2a58 <col:14> 'int' 268435455
      `-CompoundStmt 0x562d5aad2ec8 <col:26, line:27:3>
        |-BinaryOperator 0x562d5aad2b78 <line:22:5, col:13> 'unsigned int' '='
        | |-DeclRefExpr 0x562d5aad2ac8 <col:5> 'unsigned int' lvalue Var 0x562d5aad0db8 'i' 'unsigned int'
        | `-BinaryOperator 0x562d5aad2b58 <col:9, col:13> 'unsigned int' '+'
        |   |-ImplicitCastExpr 0x562d5aad2b28 <col:9> 'unsigned int' <LValueToRValue>
        |   | `-DeclRefExpr 0x562d5aad2ae8 <col:9> 'unsigned int' lvalue Var 0x562d5aad0db8 'i' 'unsigned int'
        |   `-ImplicitCastExpr 0x562d5aad2b40 <col:13> 'unsigned int' <IntegralCast>
        |     `-IntegerLiteral 0x562d5aad2b08 <col:13> 'int' 1
        |-BinaryOperator 0x562d5aad2c48 <line:23:5, col:13> 'unsigned int' '='
        | |-DeclRefExpr 0x562d5aad2b98 <col:5> 'unsigned int' lvalue Var 0x562d5aad28b0 'j' 'unsigned int'
        | `-BinaryOperator 0x562d5aad2c28 <col:9, col:13> 'unsigned int' '+'
        |   |-ImplicitCastExpr 0x562d5aad2bf8 <col:9> 'unsigned int' <LValueToRValue>
        |   | `-DeclRefExpr 0x562d5aad2bb8 <col:9> 'unsigned int' lvalue Var 0x562d5aad28b0 'j' 'unsigned int'
        |   `-ImplicitCastExpr 0x562d5aad2c10 <col:13> 'unsigned int' <IntegralCast>
        |     `-IntegerLiteral 0x562d5aad2bd8 <col:13> 'int' 2
        |-BinaryOperator 0x562d5aad2d18 <line:24:5, col:13> 'unsigned int' '='
        | |-DeclRefExpr 0x562d5aad2c68 <col:5> 'unsigned int' lvalue Var 0x562d5aad2980 'k' 'unsigned int'
        | `-BinaryOperator 0x562d5aad2cf8 <col:9, col:13> 'unsigned int' '+'
        |   |-ImplicitCastExpr 0x562d5aad2cc8 <col:9> 'unsigned int' <LValueToRValue>
        |   | `-DeclRefExpr 0x562d5aad2c88 <col:9> 'unsigned int' lvalue Var 0x562d5aad2980 'k' 'unsigned int'
        |   `-ImplicitCastExpr 0x562d5aad2ce0 <col:13> 'unsigned int' <IntegralCast>
        |     `-IntegerLiteral 0x562d5aad2ca8 <col:13> 'int' 3
        `-CallExpr 0x562d5aad2ea0 <line:26:5, col:35> 'void'
          |-ImplicitCastExpr 0x562d5aad2e88 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
          | `-DeclRefExpr 0x562d5aad2d38 <col:5> 'void (int)' Function 0x562d5aad09a8 '__VERIFIER_assert' 'void (int)'
          `-BinaryOperator 0x562d5aad2e40 <col:23, col:34> 'int' '=='
            |-ImplicitCastExpr 0x562d5aad2e28 <col:23> 'unsigned int' <LValueToRValue>
            | `-DeclRefExpr 0x562d5aad2d58 <col:23> 'unsigned int' lvalue Var 0x562d5aad2980 'k' 'unsigned int'
            `-ParenExpr 0x562d5aad2e08 <col:28, col:34> 'unsigned int'
              `-BinaryOperator 0x562d5aad2de8 <col:29, col:33> 'unsigned int' '+'
                |-ImplicitCastExpr 0x562d5aad2db8 <col:29> 'unsigned int' <LValueToRValue>
                | `-DeclRefExpr 0x562d5aad2d78 <col:29> 'unsigned int' lvalue Var 0x562d5aad0db8 'i' 'unsigned int'
                `-ImplicitCastExpr 0x562d5aad2dd0 <col:33> 'unsigned int' <LValueToRValue>
                  `-DeclRefExpr 0x562d5aad2d98 <col:33> 'unsigned int' lvalue Var 0x562d5aad28b0 'j' 'unsigned int'
1 warning generated.
