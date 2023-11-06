./Benchmark/PLDI/SVComp/loop-zilu/benchmark33_linear.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark33_linear.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x5561fe959ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5561fe95a780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5561fe95a480 '__int128'
|-TypedefDecl 0x5561fe95a7f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5561fe95a4a0 'unsigned __int128'
|-TypedefDecl 0x5561fe95aaf8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5561fe95a8d0 'struct __NSConstantString_tag'
|   `-Record 0x5561fe95a848 '__NSConstantString_tag'
|-TypedefDecl 0x5561fe95ab90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5561fe95ab50 'char *'
|   `-BuiltinType 0x5561fe959f80 'char'
|-TypedefDecl 0x5561fe95ae88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5561fe95ae30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5561fe95ac70 'struct __va_list_tag'
|     `-Record 0x5561fe95abe8 '__va_list_tag'
|-FunctionDecl 0x5561fe9b9e48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark33_linear.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x5561fe9ba0d8 <col:24, col:35>
|   `-CallExpr 0x5561fe9ba0b0 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x5561fe9ba098 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5561fe9ba030 <col:25> 'int ()' Function 0x5561fe9b9f80 'assert' 'int ()'
|     `-IntegerLiteral 0x5561fe9ba050 <col:32> 'int' 0
|-FunctionDecl 0x5561fe9ba1c0 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x5561fe9ba328 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x5561fe9ba4a8 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5561fe9ba3e0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5561fe9ba650 <col:34, line:10:1>
|   `-IfStmt 0x5561fe9ba638 <line:7:3, line:9:3>
|     |-UnaryOperator 0x5561fe9ba588 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5561fe9ba570 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5561fe9ba550 <col:8> 'int' lvalue ParmVar 0x5561fe9ba3e0 'cond' 'int'
|     `-CompoundStmt 0x5561fe9ba620 <col:14, line:9:3>
|       `-CallExpr 0x5561fe9ba600 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x5561fe9ba5e8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5561fe9ba5a0 <col:5> 'void (void)' Function 0x5561fe9b9e48 'reach_error' 'void (void)'
`-FunctionDecl 0x5561fe9ba690 <line:23:1, line:32:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x5561fe9babe8 <col:12, line:32:1>
    |-DeclStmt 0x5561fe9ba830 <line:24:3, col:34>
    | `-VarDecl 0x5561fe9ba748 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x5561fe9ba810 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5561fe9ba7f8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5561fe9ba7b0 <col:11> 'int (void)' Function 0x5561fe9ba1c0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x5561fe9ba928 <line:26:3, col:23>
    | |-UnaryOperator 0x5561fe9ba8e0 <col:7, col:13> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5561fe9ba8c0 <col:8, col:13> 'int'
    | |   `-BinaryOperator 0x5561fe9ba8a0 <col:9, col:12> 'int' '>='
    | |     |-ImplicitCastExpr 0x5561fe9ba888 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x5561fe9ba848 <col:9> 'int' lvalue Var 0x5561fe9ba748 'x' 'int'
    | |     `-IntegerLiteral 0x5561fe9ba868 <col:12> 'int' 0
    | `-ReturnStmt 0x5561fe9ba918 <col:16, col:23>
    |   `-IntegerLiteral 0x5561fe9ba8f8 <col:23> 'int' 0
    |-WhileStmt 0x5561fe9baaa0 <line:27:3, line:29:3>
    | |-BinaryOperator 0x5561fe9baa30 <line:27:10, col:22> 'int' '&&'
    | | |-BinaryOperator 0x5561fe9ba998 <col:10, col:12> 'int' '<'
    | | | |-ImplicitCastExpr 0x5561fe9ba980 <col:10> 'int' <LValueToRValue>
    | | | | `-DeclRefExpr 0x5561fe9ba940 <col:10> 'int' lvalue Var 0x5561fe9ba748 'x' 'int'
    | | | `-IntegerLiteral 0x5561fe9ba960 <col:12> 'int' 100
    | | `-BinaryOperator 0x5561fe9baa10 <col:19, col:22> 'int' '>='
    | |   |-ImplicitCastExpr 0x5561fe9ba9f8 <col:19> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x5561fe9ba9b8 <col:19> 'int' lvalue Var 0x5561fe9ba748 'x' 'int'
    | |   `-IntegerLiteral 0x5561fe9ba9d8 <col:22> 'int' 0
    | `-CompoundStmt 0x5561fe9baa88 <col:25, line:29:3>
    |   `-UnaryOperator 0x5561fe9baa70 <line:28:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x5561fe9baa50 <col:5> 'int' lvalue Var 0x5561fe9ba748 'x' 'int'
    |-CallExpr 0x5561fe9bab90 <line:30:3, col:27> 'void'
    | |-ImplicitCastExpr 0x5561fe9bab78 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5561fe9baab8 <col:3> 'void (int)' Function 0x5561fe9ba4a8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5561fe9bab30 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x5561fe9bab18 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5561fe9baad8 <col:21> 'int' lvalue Var 0x5561fe9ba748 'x' 'int'
    |   `-IntegerLiteral 0x5561fe9baaf8 <col:24> 'int' 100
    `-ReturnStmt 0x5561fe9babd8 <line:31:3, col:10>
      `-IntegerLiteral 0x5561fe9babb8 <col:10> 'int' 0
1 warning generated.
