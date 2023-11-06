./Benchmark/PLDI/SVComp/loop-zilu/benchmark04_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark04_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x560c7c727f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x560c7c7287e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x560c7c7284e0 '__int128'
|-TypedefDecl 0x560c7c728850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x560c7c728500 'unsigned __int128'
|-TypedefDecl 0x560c7c728b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x560c7c728930 'struct __NSConstantString_tag'
|   `-Record 0x560c7c7288a8 '__NSConstantString_tag'
|-TypedefDecl 0x560c7c728bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x560c7c728bb0 'char *'
|   `-BuiltinType 0x560c7c727fe0 'char'
|-TypedefDecl 0x560c7c728ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x560c7c728e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x560c7c728cd0 'struct __va_list_tag'
|     `-Record 0x560c7c728c48 '__va_list_tag'
|-FunctionDecl 0x560c7c787f08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark04_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x560c7c788198 <col:24, col:35>
|   `-CallExpr 0x560c7c788170 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x560c7c788158 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x560c7c7880f0 <col:25> 'int ()' Function 0x560c7c788040 'assert' 'int ()'
|     `-IntegerLiteral 0x560c7c788110 <col:32> 'int' 0
|-FunctionDecl 0x560c7c788280 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x560c7c7883e8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x560c7c788568 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x560c7c7884a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x560c7c788710 <col:34, line:10:1>
|   `-IfStmt 0x560c7c7886f8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x560c7c788648 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x560c7c788630 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x560c7c788610 <col:8> 'int' lvalue ParmVar 0x560c7c7884a0 'cond' 'int'
|     `-CompoundStmt 0x560c7c7886e0 <col:14, line:9:3>
|       `-CallExpr 0x560c7c7886c0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x560c7c7886a8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x560c7c788660 <col:5> 'void (void)' Function 0x560c7c787f08 'reach_error' 'void (void)'
`-FunctionDecl 0x560c7c788750 <line:23:1, line:35:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x560c7c7893e8 <col:12, line:35:1>
    |-DeclStmt 0x560c7c7888f0 <line:24:3, col:34>
    | `-VarDecl 0x560c7c788808 <col:3, col:33> col:7 used k 'int' cinit
    |   `-CallExpr 0x560c7c7888d0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x560c7c7888b8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x560c7c788870 <col:11> 'int (void)' Function 0x560c7c788280 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x560c7c7889e0 <line:25:3, col:34>
    | `-VarDecl 0x560c7c788920 <col:3, col:33> col:7 used j 'int' cinit
    |   `-CallExpr 0x560c7c7889c0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x560c7c7889a8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x560c7c788988 <col:11> 'int (void)' Function 0x560c7c788280 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x560c7c788ad0 <line:26:3, col:34>
    | `-VarDecl 0x560c7c788a10 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x560c7c788ab0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x560c7c788a98 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x560c7c788a78 <col:11> 'int (void)' Function 0x560c7c788280 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x560c7c788d10 <line:28:3, col:39>
    | |-UnaryOperator 0x560c7c788cc8 <col:7, col:29> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x560c7c788ca8 <col:8, col:29> 'int'
    | |   `-BinaryOperator 0x560c7c788c88 <col:9, col:28> 'int' '&&'
    | |     |-BinaryOperator 0x560c7c788bf0 <col:9, col:20> 'int' '&&'
    | |     | |-BinaryOperator 0x560c7c788b40 <col:9, col:12> 'int' '>='
    | |     | | |-ImplicitCastExpr 0x560c7c788b28 <col:9> 'int' <LValueToRValue>
    | |     | | | `-DeclRefExpr 0x560c7c788ae8 <col:9> 'int' lvalue Var 0x560c7c788a10 'n' 'int'
    | |     | | `-IntegerLiteral 0x560c7c788b08 <col:12> 'int' 1
    | |     | `-BinaryOperator 0x560c7c788bd0 <col:17, col:20> 'int' '>='
    | |     |   |-ImplicitCastExpr 0x560c7c788ba0 <col:17> 'int' <LValueToRValue>
    | |     |   | `-DeclRefExpr 0x560c7c788b60 <col:17> 'int' lvalue Var 0x560c7c788808 'k' 'int'
    | |     |   `-ImplicitCastExpr 0x560c7c788bb8 <col:20> 'int' <LValueToRValue>
    | |     |     `-DeclRefExpr 0x560c7c788b80 <col:20> 'int' lvalue Var 0x560c7c788a10 'n' 'int'
    | |     `-BinaryOperator 0x560c7c788c68 <col:25, col:28> 'int' '=='
    | |       |-ImplicitCastExpr 0x560c7c788c50 <col:25> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x560c7c788c10 <col:25> 'int' lvalue Var 0x560c7c788920 'j' 'int'
    | |       `-IntegerLiteral 0x560c7c788c30 <col:28> 'int' 0
    | `-ReturnStmt 0x560c7c788d00 <col:32, col:39>
    |   `-IntegerLiteral 0x560c7c788ce0 <col:39> 'int' 0
    |-WhileStmt 0x560c7c789298 <line:29:3, line:32:3>
    | |-BinaryOperator 0x560c7c788dd8 <line:29:10, col:15> 'int' '<='
    | | |-ImplicitCastExpr 0x560c7c788dc0 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x560c7c788d28 <col:10> 'int' lvalue Var 0x560c7c788920 'j' 'int'
    | | `-BinaryOperator 0x560c7c788da0 <col:13, col:15> 'int' '-'
    | |   |-ImplicitCastExpr 0x560c7c788d88 <col:13> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x560c7c788d48 <col:13> 'int' lvalue Var 0x560c7c788a10 'n' 'int'
    | |   `-IntegerLiteral 0x560c7c788d68 <col:15> 'int' 1
    | `-CompoundStmt 0x560c7c789278 <col:18, line:32:3>
    |   |-UnaryOperator 0x560c7c788e18 <line:30:5, col:6> 'int' postfix '++'
    |   | `-DeclRefExpr 0x560c7c788df8 <col:5> 'int' lvalue Var 0x560c7c788920 'j' 'int'
    |   `-UnaryOperator 0x560c7c789260 <line:31:5, col:6> 'int' postfix '--'
    |     `-DeclRefExpr 0x560c7c789240 <col:5> 'int' lvalue Var 0x560c7c788808 'k' 'int'
    |-CallExpr 0x560c7c789390 <line:33:3, col:25> 'void'
    | |-ImplicitCastExpr 0x560c7c789378 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x560c7c7892b0 <col:3> 'void (int)' Function 0x560c7c788568 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x560c7c789328 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x560c7c789310 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x560c7c7892d0 <col:21> 'int' lvalue Var 0x560c7c788808 'k' 'int'
    |   `-IntegerLiteral 0x560c7c7892f0 <col:24> 'int' 0
    `-ReturnStmt 0x560c7c7893d8 <line:34:3, col:10>
      `-IntegerLiteral 0x560c7c7893b8 <col:10> 'int' 0
1 warning generated.
