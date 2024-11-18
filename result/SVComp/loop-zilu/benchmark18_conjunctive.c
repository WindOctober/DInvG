./Benchmark/PLDI/SVComp/loop-zilu/benchmark18_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark18_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x559eb796ff48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x559eb79707e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x559eb79704e0 '__int128'
|-TypedefDecl 0x559eb7970850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x559eb7970500 'unsigned __int128'
|-TypedefDecl 0x559eb7970b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x559eb7970930 'struct __NSConstantString_tag'
|   `-Record 0x559eb79708a8 '__NSConstantString_tag'
|-TypedefDecl 0x559eb7970bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x559eb7970bb0 'char *'
|   `-BuiltinType 0x559eb796ffe0 'char'
|-TypedefDecl 0x559eb7970ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x559eb7970e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x559eb7970cd0 'struct __va_list_tag'
|     `-Record 0x559eb7970c48 '__va_list_tag'
|-FunctionDecl 0x559eb79cff08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark18_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x559eb79d0198 <col:24, col:35>
|   `-CallExpr 0x559eb79d0170 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x559eb79d0158 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x559eb79d00f0 <col:25> 'int ()' Function 0x559eb79d0040 'assert' 'int ()'
|     `-IntegerLiteral 0x559eb79d0110 <col:32> 'int' 0
|-FunctionDecl 0x559eb79d0280 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x559eb79d03e8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x559eb79d0568 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x559eb79d04a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x559eb79d0710 <col:34, line:10:1>
|   `-IfStmt 0x559eb79d06f8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x559eb79d0648 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x559eb79d0630 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x559eb79d0610 <col:8> 'int' lvalue ParmVar 0x559eb79d04a0 'cond' 'int'
|     `-CompoundStmt 0x559eb79d06e0 <col:14, line:9:3>
|       `-CallExpr 0x559eb79d06c0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x559eb79d06a8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x559eb79d0660 <col:5> 'void (void)' Function 0x559eb79cff08 'reach_error' 'void (void)'
`-FunctionDecl 0x559eb79d0750 <line:20:1, line:30:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x559eb79d14e8 <col:12, line:30:1>
    |-DeclStmt 0x559eb79d08f0 <line:21:3, col:34>
    | `-VarDecl 0x559eb79d0808 <col:3, col:33> col:7 used i 'int' cinit
    |   `-CallExpr 0x559eb79d08d0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x559eb79d08b8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x559eb79d0870 <col:11> 'int (void)' Function 0x559eb79d0280 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x559eb79d09e0 <line:22:3, col:34>
    | `-VarDecl 0x559eb79d0920 <col:3, col:33> col:7 used k 'int' cinit
    |   `-CallExpr 0x559eb79d09c0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x559eb79d09a8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x559eb79d0988 <col:11> 'int (void)' Function 0x559eb79d0280 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x559eb79d0ad0 <line:23:3, col:34>
    | `-VarDecl 0x559eb79d0a10 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x559eb79d0ab0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x559eb79d0a98 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x559eb79d0a78 <col:11> 'int (void)' Function 0x559eb79d0280 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x559eb79d0d58 <line:24:3, col:44>
    | |-UnaryOperator 0x559eb79d0d10 <col:7, col:34> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x559eb79d0cf0 <col:8, col:34> 'int'
    | |   `-BinaryOperator 0x559eb79d0cd0 <col:9, col:33> 'int' '&&'
    | |     |-BinaryOperator 0x559eb79d0c18 <col:9, col:24> 'int' '&&'
    | |     | |-ParenExpr 0x559eb79d0b60 <col:9, col:14> 'int'
    | |     | | `-BinaryOperator 0x559eb79d0b40 <col:10, col:13> 'int' '=='
    | |     | |   |-ImplicitCastExpr 0x559eb79d0b28 <col:10> 'int' <LValueToRValue>
    | |     | |   | `-DeclRefExpr 0x559eb79d0ae8 <col:10> 'int' lvalue Var 0x559eb79d0808 'i' 'int'
    | |     | |   `-IntegerLiteral 0x559eb79d0b08 <col:13> 'int' 0
    | |     | `-ParenExpr 0x559eb79d0bf8 <col:19, col:24> 'int'
    | |     |   `-BinaryOperator 0x559eb79d0bd8 <col:20, col:23> 'int' '=='
    | |     |     |-ImplicitCastExpr 0x559eb79d0bc0 <col:20> 'int' <LValueToRValue>
    | |     |     | `-DeclRefExpr 0x559eb79d0b80 <col:20> 'int' lvalue Var 0x559eb79d0920 'k' 'int'
    | |     |     `-IntegerLiteral 0x559eb79d0ba0 <col:23> 'int' 0
    | |     `-ParenExpr 0x559eb79d0cb0 <col:29, col:33> 'int'
    | |       `-BinaryOperator 0x559eb79d0c90 <col:30, col:32> 'int' '>'
    | |         |-ImplicitCastExpr 0x559eb79d0c78 <col:30> 'int' <LValueToRValue>
    | |         | `-DeclRefExpr 0x559eb79d0c38 <col:30> 'int' lvalue Var 0x559eb79d0a10 'n' 'int'
    | |         `-IntegerLiteral 0x559eb79d0c58 <col:32> 'int' 0
    | `-ReturnStmt 0x559eb79d0d48 <col:37, col:44>
    |   `-IntegerLiteral 0x559eb79d0d28 <col:44> 'int' 0
    |-WhileStmt 0x559eb79d1298 <line:25:3, line:27:3>
    | |-BinaryOperator 0x559eb79d0de0 <line:25:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x559eb79d0db0 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x559eb79d0d70 <col:10> 'int' lvalue Var 0x559eb79d0808 'i' 'int'
    | | `-ImplicitCastExpr 0x559eb79d0dc8 <col:14> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x559eb79d0d90 <col:14> 'int' lvalue Var 0x559eb79d0a10 'n' 'int'
    | `-CompoundStmt 0x559eb79d1278 <col:17, line:27:3>
    |   |-UnaryOperator 0x559eb79d0e20 <line:26:5, col:6> 'int' postfix '++'
    |   | `-DeclRefExpr 0x559eb79d0e00 <col:5> 'int' lvalue Var 0x559eb79d0808 'i' 'int'
    |   `-UnaryOperator 0x559eb79d1260 <col:9, col:10> 'int' postfix '++'
    |     `-DeclRefExpr 0x559eb79d1240 <col:9> 'int' lvalue Var 0x559eb79d0920 'k' 'int'
    |-CallExpr 0x559eb79d1490 <line:28:3, col:41> 'void'
    | |-ImplicitCastExpr 0x559eb79d1478 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x559eb79d12b0 <col:3> 'void (int)' Function 0x559eb79d0568 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x559eb79d1430 <col:21, col:40> 'int' '&&'
    |   |-ParenExpr 0x559eb79d1360 <col:21, col:28> 'int'
    |   | `-BinaryOperator 0x559eb79d1340 <col:22, col:27> 'int' '=='
    |   |   |-ImplicitCastExpr 0x559eb79d1310 <col:22> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x559eb79d12d0 <col:22> 'int' lvalue Var 0x559eb79d0808 'i' 'int'
    |   |   `-ImplicitCastExpr 0x559eb79d1328 <col:27> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x559eb79d12f0 <col:27> 'int' lvalue Var 0x559eb79d0920 'k' 'int'
    |   `-ParenExpr 0x559eb79d1410 <col:33, col:40> 'int'
    |     `-BinaryOperator 0x559eb79d13f0 <col:34, col:39> 'int' '=='
    |       |-ImplicitCastExpr 0x559eb79d13c0 <col:34> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x559eb79d1380 <col:34> 'int' lvalue Var 0x559eb79d0920 'k' 'int'
    |       `-ImplicitCastExpr 0x559eb79d13d8 <col:39> 'int' <LValueToRValue>
    |         `-DeclRefExpr 0x559eb79d13a0 <col:39> 'int' lvalue Var 0x559eb79d0a10 'n' 'int'
    `-ReturnStmt 0x559eb79d14d8 <line:29:3, col:10>
      `-IntegerLiteral 0x559eb79d14b8 <col:10> 'int' 0
1 warning generated.
