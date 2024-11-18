./Benchmark/PLDI/SVComp/loop-zilu/benchmark26_linear.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark26_linear.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55a89122cee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55a89122d780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55a89122d480 '__int128'
|-TypedefDecl 0x55a89122d7f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55a89122d4a0 'unsigned __int128'
|-TypedefDecl 0x55a89122daf8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55a89122d8d0 'struct __NSConstantString_tag'
|   `-Record 0x55a89122d848 '__NSConstantString_tag'
|-TypedefDecl 0x55a89122db90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55a89122db50 'char *'
|   `-BuiltinType 0x55a89122cf80 'char'
|-TypedefDecl 0x55a89122de88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55a89122de30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55a89122dc70 'struct __va_list_tag'
|     `-Record 0x55a89122dbe8 '__va_list_tag'
|-FunctionDecl 0x55a89128ce28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark26_linear.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55a89128d0b8 <col:24, col:35>
|   `-CallExpr 0x55a89128d090 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55a89128d078 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55a89128d010 <col:25> 'int ()' Function 0x55a89128cf60 'assert' 'int ()'
|     `-IntegerLiteral 0x55a89128d030 <col:32> 'int' 0
|-FunctionDecl 0x55a89128d1a0 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55a89128d308 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55a89128d488 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55a89128d3c0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55a89128d630 <col:34, line:10:1>
|   `-IfStmt 0x55a89128d618 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55a89128d568 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55a89128d550 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55a89128d530 <col:8> 'int' lvalue ParmVar 0x55a89128d3c0 'cond' 'int'
|     `-CompoundStmt 0x55a89128d600 <col:14, line:9:3>
|       `-CallExpr 0x55a89128d5e0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55a89128d5c8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55a89128d580 <col:5> 'void (void)' Function 0x55a89128ce28 'reach_error' 'void (void)'
`-FunctionDecl 0x55a89128d670 <line:20:1, line:29:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x55a89128dce8 <col:12, line:29:1>
    |-DeclStmt 0x55a89128d810 <line:21:3, col:34>
    | `-VarDecl 0x55a89128d728 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x55a89128d7f0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55a89128d7d8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55a89128d790 <col:11> 'int (void)' Function 0x55a89128d1a0 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55a89128d900 <line:22:3, col:34>
    | `-VarDecl 0x55a89128d840 <col:3, col:33> col:7 used y 'int' cinit
    |   `-CallExpr 0x55a89128d8e0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55a89128d8c8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55a89128d8a8 <col:11> 'int (void)' Function 0x55a89128d1a0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55a89128da10 <line:23:3, col:22>
    | |-UnaryOperator 0x55a89128d9c8 <col:7, col:12> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55a89128d9a8 <col:8, col:12> 'int'
    | |   `-BinaryOperator 0x55a89128d988 <col:9, col:11> 'int' '<'
    | |     |-ImplicitCastExpr 0x55a89128d958 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x55a89128d918 <col:9> 'int' lvalue Var 0x55a89128d728 'x' 'int'
    | |     `-ImplicitCastExpr 0x55a89128d970 <col:11> 'int' <LValueToRValue>
    | |       `-DeclRefExpr 0x55a89128d938 <col:11> 'int' lvalue Var 0x55a89128d840 'y' 'int'
    | `-ReturnStmt 0x55a89128da00 <col:15, col:22>
    |   `-IntegerLiteral 0x55a89128d9e0 <col:22> 'int' 0
    |-WhileStmt 0x55a89128db88 <line:24:3, line:26:3>
    | |-BinaryOperator 0x55a89128da98 <line:24:10, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x55a89128da68 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55a89128da28 <col:10> 'int' lvalue Var 0x55a89128d728 'x' 'int'
    | | `-ImplicitCastExpr 0x55a89128da80 <col:12> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55a89128da48 <col:12> 'int' lvalue Var 0x55a89128d840 'y' 'int'
    | `-CompoundStmt 0x55a89128db70 <col:15, line:26:3>
    |   `-BinaryOperator 0x55a89128db50 <line:25:5, col:9> 'int' '='
    |     |-DeclRefExpr 0x55a89128dab8 <col:5> 'int' lvalue Var 0x55a89128d728 'x' 'int'
    |     `-BinaryOperator 0x55a89128db30 <col:7, col:9> 'int' '+'
    |       |-ImplicitCastExpr 0x55a89128db18 <col:7> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55a89128dad8 <col:7> 'int' lvalue Var 0x55a89128d728 'x' 'int'
    |       `-IntegerLiteral 0x55a89128daf8 <col:9> 'int' 1
    |-CallExpr 0x55a89128dc90 <line:27:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55a89128dc78 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55a89128dba0 <col:3> 'void (int)' Function 0x55a89128d488 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55a89128dc30 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55a89128dc00 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55a89128dbc0 <col:21> 'int' lvalue Var 0x55a89128d728 'x' 'int'
    |   `-ImplicitCastExpr 0x55a89128dc18 <col:24> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x55a89128dbe0 <col:24> 'int' lvalue Var 0x55a89128d840 'y' 'int'
    `-ReturnStmt 0x55a89128dcd8 <line:28:3, col:10>
      `-IntegerLiteral 0x55a89128dcb8 <col:10> 'int' 0
1 warning generated.
