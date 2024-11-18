./Benchmark/PLDI/SVComp/loop-zilu/benchmark26_linear_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark26_linear_abstracted.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x559e969fc028 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x559e969fc8c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x559e969fc5c0 '__int128'
|-TypedefDecl 0x559e969fc930 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x559e969fc5e0 'unsigned __int128'
|-TypedefDecl 0x559e969fcc38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x559e969fca10 'struct __NSConstantString_tag'
|   `-Record 0x559e969fc988 '__NSConstantString_tag'
|-TypedefDecl 0x559e969fccd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x559e969fcc90 'char *'
|   `-BuiltinType 0x559e969fc0c0 'char'
|-TypedefDecl 0x559e969fcfc8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x559e969fcf70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x559e969fcdb0 'struct __va_list_tag'
|     `-Record 0x559e969fcd28 '__va_list_tag'
|-FunctionDecl 0x559e96a5c038 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark26_linear_abstracted.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x559e96a5c2c8 <col:24, col:35>
|   `-CallExpr 0x559e96a5c2a0 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x559e96a5c288 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x559e96a5c220 <col:25> 'int ()' Function 0x559e96a5c170 'assert' 'int ()'
|     `-IntegerLiteral 0x559e96a5c240 <col:32> 'int' 0
|-FunctionDecl 0x559e96a5c3a8 <line:2:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559e96a5c448 prev 0x559e96a5c3a8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559e96a5c5b0 <line:4:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x559e96a5c718 <line:5:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x559e96a5c898 <line:7:1, line:11:1> line:7:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x559e96a5c7d0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x559e96a5ca40 <col:34, line:11:1>
|   `-IfStmt 0x559e96a5ca28 <line:8:3, line:10:3>
|     |-UnaryOperator 0x559e96a5c978 <line:8:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x559e96a5c960 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x559e96a5c940 <col:8> 'int' lvalue ParmVar 0x559e96a5c7d0 'cond' 'int'
|     `-CompoundStmt 0x559e96a5ca10 <col:14, line:10:3>
|       `-CallExpr 0x559e96a5c9f0 <line:9:5, col:17> 'void'
|         `-ImplicitCastExpr 0x559e96a5c9d8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x559e96a5c990 <col:5> 'void (void)' Function 0x559e96a5c038 'reach_error' 'void (void)'
`-FunctionDecl 0x559e96a5ca80 <line:21:1, line:37:1> line:21:5 main 'int ()'
  `-CompoundStmt 0x559e96a5da98 <col:12, line:37:1>
    |-DeclStmt 0x559e96a5cc20 <line:22:3, col:34>
    | `-VarDecl 0x559e96a5cb38 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x559e96a5cc00 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x559e96a5cbe8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x559e96a5cba0 <col:11> 'int (void)' Function 0x559e96a5c5b0 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x559e96a5cd10 <line:23:3, col:34>
    | `-VarDecl 0x559e96a5cc50 <col:3, col:33> col:7 used y 'int' cinit
    |   `-CallExpr 0x559e96a5ccf0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x559e96a5ccd8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x559e96a5ccb8 <col:11> 'int (void)' Function 0x559e96a5c5b0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x559e96a5ce20 <line:24:3, col:22>
    | |-UnaryOperator 0x559e96a5cdd8 <col:7, col:12> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x559e96a5cdb8 <col:8, col:12> 'int'
    | |   `-BinaryOperator 0x559e96a5cd98 <col:9, col:11> 'int' '<'
    | |     |-ImplicitCastExpr 0x559e96a5cd68 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x559e96a5cd28 <col:9> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    | |     `-ImplicitCastExpr 0x559e96a5cd80 <col:11> 'int' <LValueToRValue>
    | |       `-DeclRefExpr 0x559e96a5cd48 <col:11> 'int' lvalue Var 0x559e96a5cc50 'y' 'int'
    | `-ReturnStmt 0x559e96a5ce10 <col:15, col:22>
    |   `-IntegerLiteral 0x559e96a5cdf0 <col:22> 'int' 0
    |-IfStmt 0x559e96a5d930 <line:26:3, line:33:3>
    | |-BinaryOperator 0x559e96a5cea8 <line:26:7, col:11> 'int' '<'
    | | |-ImplicitCastExpr 0x559e96a5ce78 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x559e96a5ce38 <col:7> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    | | `-ImplicitCastExpr 0x559e96a5ce90 <col:11> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x559e96a5ce58 <col:11> 'int' lvalue Var 0x559e96a5cc50 'y' 'int'
    | `-CompoundStmt 0x559e96a5d900 <col:14, line:33:3>
    |   |-BinaryOperator 0x559e96a5cf40 <line:27:3, col:29> 'int' '='
    |   | |-DeclRefExpr 0x559e96a5cec8 <col:3> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    |   | `-CallExpr 0x559e96a5cf20 <col:7, col:29> 'int'
    |   |   `-ImplicitCastExpr 0x559e96a5cf08 <col:7> 'int (*)(void)' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x559e96a5cee8 <col:7> 'int (void)' Function 0x559e96a5c5b0 '__VERIFIER_nondet_int' 'int (void)'
    |   |-IfStmt 0x559e96a5d670 <line:28:3, col:23>
    |   | |-UnaryOperator 0x559e96a5d5d0 <col:7, col:14> 'int' prefix '!' cannot overflow
    |   | | `-ParenExpr 0x559e96a5d5b0 <col:8, col:14> 'int'
    |   | |   `-BinaryOperator 0x559e96a5d590 <col:9, col:13> 'int' '<'
    |   | |     |-ImplicitCastExpr 0x559e96a5d560 <col:9> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x559e96a5d520 <col:9> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    |   | |     `-ImplicitCastExpr 0x559e96a5d578 <col:13> 'int' <LValueToRValue>
    |   | |       `-DeclRefExpr 0x559e96a5d540 <col:13> 'int' lvalue Var 0x559e96a5cc50 'y' 'int'
    |   | `-CallExpr 0x559e96a5d650 <col:17, col:23> 'void'
    |   |   `-ImplicitCastExpr 0x559e96a5d638 <col:17> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x559e96a5d5e8 <col:17> 'void (void) __attribute__((noreturn))' Function 0x559e96a5c448 'abort' 'void (void) __attribute__((noreturn))'
    |   |-IfStmt 0x559e96a5d7e8 <line:29:3, line:31:5>
    |   | |-BinaryOperator 0x559e96a5d6f8 <line:29:7, col:9> 'int' '<'
    |   | | |-ImplicitCastExpr 0x559e96a5d6c8 <col:7> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x559e96a5d688 <col:7> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    |   | | `-ImplicitCastExpr 0x559e96a5d6e0 <col:9> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x559e96a5d6a8 <col:9> 'int' lvalue Var 0x559e96a5cc50 'y' 'int'
    |   | `-CompoundStmt 0x559e96a5d7d0 <col:12, line:31:5>
    |   |   `-BinaryOperator 0x559e96a5d7b0 <line:30:7, col:11> 'int' '='
    |   |     |-DeclRefExpr 0x559e96a5d718 <col:7> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    |   |     `-BinaryOperator 0x559e96a5d790 <col:9, col:11> 'int' '+'
    |   |       |-ImplicitCastExpr 0x559e96a5d778 <col:9> 'int' <LValueToRValue>
    |   |       | `-DeclRefExpr 0x559e96a5d738 <col:9> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    |   |       `-IntegerLiteral 0x559e96a5d758 <col:11> 'int' 1
    |   `-IfStmt 0x559e96a5d8e8 <line:32:3, col:20>
    |     |-BinaryOperator 0x559e96a5d870 <col:7, col:11> 'int' '<'
    |     | |-ImplicitCastExpr 0x559e96a5d840 <col:7> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x559e96a5d800 <col:7> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    |     | `-ImplicitCastExpr 0x559e96a5d858 <col:11> 'int' <LValueToRValue>
    |     |   `-DeclRefExpr 0x559e96a5d820 <col:11> 'int' lvalue Var 0x559e96a5cc50 'y' 'int'
    |     `-CallExpr 0x559e96a5d8c8 <col:14, col:20> 'void'
    |       `-ImplicitCastExpr 0x559e96a5d8b0 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x559e96a5d890 <col:14> 'void (void) __attribute__((noreturn))' Function 0x559e96a5c448 'abort' 'void (void) __attribute__((noreturn))'
    |-CallExpr 0x559e96a5da40 <line:35:3, col:25> 'void'
    | |-ImplicitCastExpr 0x559e96a5da28 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x559e96a5d948 <col:3> 'void (int)' Function 0x559e96a5c898 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x559e96a5d9d8 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x559e96a5d9a8 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x559e96a5d968 <col:21> 'int' lvalue Var 0x559e96a5cb38 'x' 'int'
    |   `-ImplicitCastExpr 0x559e96a5d9c0 <col:24> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x559e96a5d988 <col:24> 'int' lvalue Var 0x559e96a5cc50 'y' 'int'
    `-ReturnStmt 0x559e96a5da88 <line:36:3, col:10>
      `-IntegerLiteral 0x559e96a5da68 <col:10> 'int' 0
1 warning generated.
