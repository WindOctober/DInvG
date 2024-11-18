./Benchmark/PLDI/SVComp/loop-zilu/benchmark09_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark09_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x56232617ff48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5623261807e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5623261804e0 '__int128'
|-TypedefDecl 0x562326180850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562326180500 'unsigned __int128'
|-TypedefDecl 0x562326180b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x562326180930 'struct __NSConstantString_tag'
|   `-Record 0x5623261808a8 '__NSConstantString_tag'
|-TypedefDecl 0x562326180bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562326180bb0 'char *'
|   `-BuiltinType 0x56232617ffe0 'char'
|-TypedefDecl 0x562326180ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562326180e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562326180cd0 'struct __va_list_tag'
|     `-Record 0x562326180c48 '__va_list_tag'
|-FunctionDecl 0x5623261dff08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark09_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x5623261e0198 <col:24, col:35>
|   `-CallExpr 0x5623261e0170 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x5623261e0158 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5623261e00f0 <col:25> 'int ()' Function 0x5623261e0040 'assert' 'int ()'
|     `-IntegerLiteral 0x5623261e0110 <col:32> 'int' 0
|-FunctionDecl 0x5623261e0280 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x5623261e03e8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x5623261e0568 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5623261e04a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5623261e0710 <col:34, line:10:1>
|   `-IfStmt 0x5623261e06f8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x5623261e0648 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5623261e0630 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5623261e0610 <col:8> 'int' lvalue ParmVar 0x5623261e04a0 'cond' 'int'
|     `-CompoundStmt 0x5623261e06e0 <col:14, line:9:3>
|       `-CallExpr 0x5623261e06c0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x5623261e06a8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5623261e0660 <col:5> 'void (void)' Function 0x5623261dff08 'reach_error' 'void (void)'
`-FunctionDecl 0x5623261e0750 <line:23:1, line:35:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x5623261e1698 <col:12, line:35:1>
    |-DeclStmt 0x5623261e08f0 <line:24:3, col:34>
    | `-VarDecl 0x5623261e0808 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x5623261e08d0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5623261e08b8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5623261e0870 <col:11> 'int (void)' Function 0x5623261e0280 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x5623261e09e0 <line:25:3, col:34>
    | `-VarDecl 0x5623261e0920 <col:3, col:33> col:7 used y 'int' cinit
    |   `-CallExpr 0x5623261e09c0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5623261e09a8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5623261e0988 <col:11> 'int (void)' Function 0x5623261e0280 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x5623261e0b88 <line:27:3, col:34>
    | |-UnaryOperator 0x5623261e0b40 <col:7, col:24> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5623261e0b20 <col:8, col:24> 'int'
    | |   `-BinaryOperator 0x5623261e0b00 <col:9, col:23> 'int' '&&'
    | |     |-BinaryOperator 0x5623261e0a68 <col:9, col:14> 'int' '=='
    | |     | |-ImplicitCastExpr 0x5623261e0a38 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x5623261e09f8 <col:9> 'int' lvalue Var 0x5623261e0808 'x' 'int'
    | |     | `-ImplicitCastExpr 0x5623261e0a50 <col:14> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x5623261e0a18 <col:14> 'int' lvalue Var 0x5623261e0920 'y' 'int'
    | |     `-BinaryOperator 0x5623261e0ae0 <col:19, col:23> 'int' '>='
    | |       |-ImplicitCastExpr 0x5623261e0ac8 <col:19> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5623261e0a88 <col:19> 'int' lvalue Var 0x5623261e0920 'y' 'int'
    | |       `-IntegerLiteral 0x5623261e0aa8 <col:23> 'int' 0
    | `-ReturnStmt 0x5623261e0b78 <col:27, col:34>
    |   `-IntegerLiteral 0x5623261e0b58 <col:34> 'int' 0
    |-WhileStmt 0x5623261e0de0 <line:28:3, line:32:3>
    | |-BinaryOperator 0x5623261e0bf8 <line:28:10, col:13> 'int' '!='
    | | |-ImplicitCastExpr 0x5623261e0be0 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5623261e0ba0 <col:10> 'int' lvalue Var 0x5623261e0808 'x' 'int'
    | | `-IntegerLiteral 0x5623261e0bc0 <col:13> 'int' 0
    | `-CompoundStmt 0x5623261e0db8 <col:16, line:32:3>
    |   |-UnaryOperator 0x5623261e0c38 <line:29:5, col:6> 'int' postfix '--'
    |   | `-DeclRefExpr 0x5623261e0c18 <col:5> 'int' lvalue Var 0x5623261e0808 'x' 'int'
    |   |-UnaryOperator 0x5623261e0c70 <line:30:5, col:6> 'int' postfix '--'
    |   | `-DeclRefExpr 0x5623261e0c50 <col:5> 'int' lvalue Var 0x5623261e0920 'y' 'int'
    |   `-IfStmt 0x5623261e0da0 <line:31:5, col:21>
    |     |-BinaryOperator 0x5623261e0d78 <col:9, col:18> 'int' '||'
    |     | |-BinaryOperator 0x5623261e0ce0 <col:9, col:11> 'int' '<'
    |     | | |-ImplicitCastExpr 0x5623261e0cc8 <col:9> 'int' <LValueToRValue>
    |     | | | `-DeclRefExpr 0x5623261e0c88 <col:9> 'int' lvalue Var 0x5623261e0808 'x' 'int'
    |     | | `-IntegerLiteral 0x5623261e0ca8 <col:11> 'int' 0
    |     | `-BinaryOperator 0x5623261e0d58 <col:16, col:18> 'int' '<'
    |     |   |-ImplicitCastExpr 0x5623261e0d40 <col:16> 'int' <LValueToRValue>
    |     |   | `-DeclRefExpr 0x5623261e0d00 <col:16> 'int' lvalue Var 0x5623261e0920 'y' 'int'
    |     |   `-IntegerLiteral 0x5623261e0d20 <col:18> 'int' 0
    |     `-BreakStmt 0x5623261e0d98 <col:21>
    |-CallExpr 0x5623261e1640 <line:33:3, col:25> 'void'
    | |-ImplicitCastExpr 0x5623261e1628 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5623261e0df8 <col:3> 'void (int)' Function 0x5623261e0568 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5623261e15d8 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x5623261e15c0 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5623261e0e18 <col:21> 'int' lvalue Var 0x5623261e0920 'y' 'int'
    |   `-IntegerLiteral 0x5623261e15a0 <col:24> 'int' 0
    `-ReturnStmt 0x5623261e1688 <line:34:3, col:10>
      `-IntegerLiteral 0x5623261e1668 <col:10> 'int' 0
1 warning generated.
