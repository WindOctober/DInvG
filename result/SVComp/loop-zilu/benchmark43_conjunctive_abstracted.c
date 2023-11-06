./Benchmark/PLDI/SVComp/loop-zilu/benchmark43_conjunctive_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark43_conjunctive_abstracted.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x5644baafb028 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5644baafb8c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5644baafb5c0 '__int128'
|-TypedefDecl 0x5644baafb930 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5644baafb5e0 'unsigned __int128'
|-TypedefDecl 0x5644baafbc38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5644baafba10 'struct __NSConstantString_tag'
|   `-Record 0x5644baafb988 '__NSConstantString_tag'
|-TypedefDecl 0x5644baafbcd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5644baafbc90 'char *'
|   `-BuiltinType 0x5644baafb0c0 'char'
|-TypedefDecl 0x5644baafbfc8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5644baafbf70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5644baafbdb0 'struct __va_list_tag'
|     `-Record 0x5644baafbd28 '__va_list_tag'
|-FunctionDecl 0x5644bab5b108 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark43_conjunctive_abstracted.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x5644bab5b398 <col:24, col:35>
|   `-CallExpr 0x5644bab5b370 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x5644bab5b358 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5644bab5b2f0 <col:25> 'int ()' Function 0x5644bab5b240 'assert' 'int ()'
|     `-IntegerLiteral 0x5644bab5b310 <col:32> 'int' 0
|-FunctionDecl 0x5644bab5b478 <line:2:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5644bab5b518 prev 0x5644bab5b478 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5644bab5b680 <line:4:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x5644bab5b7e8 <line:5:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x5644bab5b968 <line:7:1, line:11:1> line:7:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5644bab5b8a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5644bab5bb10 <col:34, line:11:1>
|   `-IfStmt 0x5644bab5baf8 <line:8:3, line:10:3>
|     |-UnaryOperator 0x5644bab5ba48 <line:8:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5644bab5ba30 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5644bab5ba10 <col:8> 'int' lvalue ParmVar 0x5644bab5b8a0 'cond' 'int'
|     `-CompoundStmt 0x5644bab5bae0 <col:14, line:10:3>
|       `-CallExpr 0x5644bab5bac0 <line:9:5, col:17> 'void'
|         `-ImplicitCastExpr 0x5644bab5baa8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5644bab5ba60 <col:5> 'void (void)' Function 0x5644bab5b108 'reach_error' 'void (void)'
`-FunctionDecl 0x5644bab5bb50 <line:21:1, line:39:1> line:21:5 main 'int ()'
  `-CompoundStmt 0x5644bab5cf78 <col:12, line:39:1>
    |-DeclStmt 0x5644bab5bcf0 <line:22:3, col:34>
    | `-VarDecl 0x5644bab5bc08 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x5644bab5bcd0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5644bab5bcb8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5644bab5bc70 <col:11> 'int (void)' Function 0x5644bab5b680 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x5644bab5bde0 <line:23:3, col:34>
    | `-VarDecl 0x5644bab5bd20 <col:3, col:33> col:7 used y 'int' cinit
    |   `-CallExpr 0x5644bab5bdc0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5644bab5bda8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5644bab5bd88 <col:11> 'int (void)' Function 0x5644bab5b680 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x5644bab5bf70 <line:24:3, col:37>
    | |-UnaryOperator 0x5644bab5bf28 <col:7, col:27> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5644bab5bf08 <col:8, col:27> 'int'
    | |   `-BinaryOperator 0x5644bab5bee8 <col:9, col:24> 'int' '&&'
    | |     |-BinaryOperator 0x5644bab5be50 <col:9, col:13> 'int' '<'
    | |     | |-ImplicitCastExpr 0x5644bab5be38 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x5644bab5bdf8 <col:9> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    | |     | `-IntegerLiteral 0x5644bab5be18 <col:13> 'int' 100
    | |     `-BinaryOperator 0x5644bab5bec8 <col:20, col:24> 'int' '<'
    | |       |-ImplicitCastExpr 0x5644bab5beb0 <col:20> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5644bab5be70 <col:20> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    | |       `-IntegerLiteral 0x5644bab5be90 <col:24> 'int' 100
    | `-ReturnStmt 0x5644bab5bf60 <col:30, col:37>
    |   `-IntegerLiteral 0x5644bab5bf40 <col:37> 'int' 0
    |-IfStmt 0x5644bab5cd98 <line:26:3, line:35:3>
    | |-BinaryOperator 0x5644bab5c4f8 <line:26:7, col:31> 'int' '&'
    | | |-ParenExpr 0x5644bab5c020 <col:7, col:17> 'int'
    | | | `-BinaryOperator 0x5644bab5c000 <col:8, col:16> 'int' '<'
    | | |   |-ImplicitCastExpr 0x5644bab5bfe8 <col:8> 'int' <LValueToRValue>
    | | |   | `-DeclRefExpr 0x5644bab5bf88 <col:8> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    | | |   `-ParenExpr 0x5644bab5bfc8 <col:12, col:16> 'int'
    | | |     `-IntegerLiteral 0x5644bab5bfa8 <col:13> 'int' 100
    | | `-ParenExpr 0x5644bab5c4d8 <col:21, col:31> 'int'
    | |   `-BinaryOperator 0x5644bab5c4b8 <col:22, col:30> 'int' '<'
    | |     |-ImplicitCastExpr 0x5644bab5c4a0 <col:22> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x5644bab5c440 <col:22> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    | |     `-ParenExpr 0x5644bab5c480 <col:26, col:30> 'int'
    | |       `-IntegerLiteral 0x5644bab5c460 <col:27> 'int' 100
    | `-CompoundStmt 0x5644bab5cd60 <col:34, line:35:3>
    |   |-BinaryOperator 0x5644bab5c590 <line:27:3, col:29> 'int' '='
    |   | |-DeclRefExpr 0x5644bab5c518 <col:3> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    |   | `-CallExpr 0x5644bab5c570 <col:7, col:29> 'int'
    |   |   `-ImplicitCastExpr 0x5644bab5c558 <col:7> 'int (*)(void)' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x5644bab5c538 <col:7> 'int (void)' Function 0x5644bab5b680 '__VERIFIER_nondet_int' 'int (void)'
    |   |-BinaryOperator 0x5644bab5c628 <line:28:3, col:29> 'int' '='
    |   | |-DeclRefExpr 0x5644bab5c5b0 <col:3> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    |   | `-CallExpr 0x5644bab5c608 <col:7, col:29> 'int'
    |   |   `-ImplicitCastExpr 0x5644bab5c5f0 <col:7> 'int (*)(void)' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x5644bab5c5d0 <col:7> 'int (void)' Function 0x5644bab5b680 '__VERIFIER_nondet_int' 'int (void)'
    |   |-IfStmt 0x5644bab5c890 <line:29:3, col:43>
    |   | |-UnaryOperator 0x5644bab5c7f8 <col:7, col:34> 'int' prefix '!' cannot overflow
    |   | | `-ParenExpr 0x5644bab5c7d8 <col:8, col:34> 'int'
    |   | |   `-BinaryOperator 0x5644bab5c7b8 <col:9, col:33> 'int' '&'
    |   | |     |-ParenExpr 0x5644bab5c6e0 <col:9, col:19> 'int'
    |   | |     | `-BinaryOperator 0x5644bab5c6c0 <col:10, col:18> 'int' '<'
    |   | |     |   |-ImplicitCastExpr 0x5644bab5c6a8 <col:10> 'int' <LValueToRValue>
    |   | |     |   | `-DeclRefExpr 0x5644bab5c648 <col:10> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    |   | |     |   `-ParenExpr 0x5644bab5c688 <col:14, col:18> 'int'
    |   | |     |     `-IntegerLiteral 0x5644bab5c668 <col:15> 'int' 100
    |   | |     `-ParenExpr 0x5644bab5c798 <col:23, col:33> 'int'
    |   | |       `-BinaryOperator 0x5644bab5c778 <col:24, col:32> 'int' '<'
    |   | |         |-ImplicitCastExpr 0x5644bab5c760 <col:24> 'int' <LValueToRValue>
    |   | |         | `-DeclRefExpr 0x5644bab5c700 <col:24> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    |   | |         `-ParenExpr 0x5644bab5c740 <col:28, col:32> 'int'
    |   | |           `-IntegerLiteral 0x5644bab5c720 <col:29> 'int' 100
    |   | `-CallExpr 0x5644bab5c870 <col:37, col:43> 'void'
    |   |   `-ImplicitCastExpr 0x5644bab5c858 <col:37> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x5644bab5c810 <col:37> 'void (void) __attribute__((noreturn))' Function 0x5644bab5b518 'abort' 'void (void) __attribute__((noreturn))'
    |   |-IfStmt 0x5644bab5cb48 <line:30:3, line:33:5>
    |   | |-BinaryOperator 0x5644bab5c998 <line:30:7, col:22> 'int' '&&'
    |   | | |-BinaryOperator 0x5644bab5c900 <col:7, col:11> 'int' '<'
    |   | | | |-ImplicitCastExpr 0x5644bab5c8e8 <col:7> 'int' <LValueToRValue>
    |   | | | | `-DeclRefExpr 0x5644bab5c8a8 <col:7> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    |   | | | `-IntegerLiteral 0x5644bab5c8c8 <col:11> 'int' 100
    |   | | `-BinaryOperator 0x5644bab5c978 <col:18, col:22> 'int' '<'
    |   | |   |-ImplicitCastExpr 0x5644bab5c960 <col:18> 'int' <LValueToRValue>
    |   | |   | `-DeclRefExpr 0x5644bab5c920 <col:18> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    |   | |   `-IntegerLiteral 0x5644bab5c940 <col:22> 'int' 100
    |   | `-CompoundStmt 0x5644bab5cb28 <col:27, line:33:5>
    |   |   |-BinaryOperator 0x5644bab5ca50 <line:31:7, col:11> 'int' '='
    |   |   | |-DeclRefExpr 0x5644bab5c9b8 <col:7> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    |   |   | `-BinaryOperator 0x5644bab5ca30 <col:9, col:11> 'int' '+'
    |   |   |   |-ImplicitCastExpr 0x5644bab5ca18 <col:9> 'int' <LValueToRValue>
    |   |   |   | `-DeclRefExpr 0x5644bab5c9d8 <col:9> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    |   |   |   `-IntegerLiteral 0x5644bab5c9f8 <col:11> 'int' 1
    |   |   `-BinaryOperator 0x5644bab5cb08 <line:32:7, col:11> 'int' '='
    |   |     |-DeclRefExpr 0x5644bab5ca70 <col:7> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    |   |     `-BinaryOperator 0x5644bab5cae8 <col:9, col:11> 'int' '+'
    |   |       |-ImplicitCastExpr 0x5644bab5cad0 <col:9> 'int' <LValueToRValue>
    |   |       | `-DeclRefExpr 0x5644bab5ca90 <col:9> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    |   |       `-IntegerLiteral 0x5644bab5cab0 <col:11> 'int' 1
    |   `-IfStmt 0x5644bab5cd48 <line:34:3, col:40>
    |     |-BinaryOperator 0x5644bab5ccd0 <col:7, col:31> 'int' '&'
    |     | |-ParenExpr 0x5644bab5cbf8 <col:7, col:17> 'int'
    |     | | `-BinaryOperator 0x5644bab5cbd8 <col:8, col:16> 'int' '<'
    |     | |   |-ImplicitCastExpr 0x5644bab5cbc0 <col:8> 'int' <LValueToRValue>
    |     | |   | `-DeclRefExpr 0x5644bab5cb60 <col:8> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    |     | |   `-ParenExpr 0x5644bab5cba0 <col:12, col:16> 'int'
    |     | |     `-IntegerLiteral 0x5644bab5cb80 <col:13> 'int' 100
    |     | `-ParenExpr 0x5644bab5ccb0 <col:21, col:31> 'int'
    |     |   `-BinaryOperator 0x5644bab5cc90 <col:22, col:30> 'int' '<'
    |     |     |-ImplicitCastExpr 0x5644bab5cc78 <col:22> 'int' <LValueToRValue>
    |     |     | `-DeclRefExpr 0x5644bab5cc18 <col:22> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    |     |     `-ParenExpr 0x5644bab5cc58 <col:26, col:30> 'int'
    |     |       `-IntegerLiteral 0x5644bab5cc38 <col:27> 'int' 100
    |     `-CallExpr 0x5644bab5cd28 <col:34, col:40> 'void'
    |       `-ImplicitCastExpr 0x5644bab5cd10 <col:34> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x5644bab5ccf0 <col:34> 'void (void) __attribute__((noreturn))' Function 0x5644bab5b518 'abort' 'void (void) __attribute__((noreturn))'
    |-CallExpr 0x5644bab5cf20 <line:37:3, col:41> 'void'
    | |-ImplicitCastExpr 0x5644bab5cf08 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5644bab5cdb0 <col:3> 'void (int)' Function 0x5644bab5b968 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5644bab5cec0 <col:21, col:38> 'int' '||'
    |   |-BinaryOperator 0x5644bab5ce28 <col:21, col:26> 'int' '=='
    |   | |-ImplicitCastExpr 0x5644bab5ce10 <col:21> 'int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x5644bab5cdd0 <col:21> 'int' lvalue Var 0x5644bab5bc08 'x' 'int'
    |   | `-IntegerLiteral 0x5644bab5cdf0 <col:26> 'int' 100
    |   `-BinaryOperator 0x5644bab5cea0 <col:33, col:38> 'int' '=='
    |     |-ImplicitCastExpr 0x5644bab5ce88 <col:33> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x5644bab5ce48 <col:33> 'int' lvalue Var 0x5644bab5bd20 'y' 'int'
    |     `-IntegerLiteral 0x5644bab5ce68 <col:38> 'int' 100
    `-ReturnStmt 0x5644bab5cf68 <line:38:3, col:10>
      `-IntegerLiteral 0x5644bab5cf48 <col:10> 'int' 0
1 warning generated.
