./Benchmark/PLDI/SVComp/loop-zilu/benchmark37_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark37_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55d011f06f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55d011f077e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55d011f074e0 '__int128'
|-TypedefDecl 0x55d011f07850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55d011f07500 'unsigned __int128'
|-TypedefDecl 0x55d011f07b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55d011f07930 'struct __NSConstantString_tag'
|   `-Record 0x55d011f078a8 '__NSConstantString_tag'
|-TypedefDecl 0x55d011f07bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55d011f07bb0 'char *'
|   `-BuiltinType 0x55d011f06fe0 'char'
|-TypedefDecl 0x55d011f07ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55d011f07e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55d011f07cd0 'struct __va_list_tag'
|     `-Record 0x55d011f07c48 '__va_list_tag'
|-FunctionDecl 0x55d011f66eb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark37_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55d011f67148 <col:24, col:35>
|   `-CallExpr 0x55d011f67120 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55d011f67108 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55d011f670a0 <col:25> 'int ()' Function 0x55d011f66ff0 'assert' 'int ()'
|     `-IntegerLiteral 0x55d011f670c0 <col:32> 'int' 0
|-FunctionDecl 0x55d011f67230 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55d011f67398 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55d011f67518 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55d011f67450 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55d011f676c0 <col:34, line:10:1>
|   `-IfStmt 0x55d011f676a8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55d011f675f8 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55d011f675e0 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55d011f675c0 <col:8> 'int' lvalue ParmVar 0x55d011f67450 'cond' 'int'
|     `-CompoundStmt 0x55d011f67690 <col:14, line:9:3>
|       `-CallExpr 0x55d011f67670 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55d011f67658 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55d011f67610 <col:5> 'void (void)' Function 0x55d011f66eb8 'reach_error' 'void (void)'
`-FunctionDecl 0x55d011f67700 <line:20:1, line:30:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x55d011f67da8 <col:12, line:30:1>
    |-DeclStmt 0x55d011f678a0 <line:21:3, col:34>
    | `-VarDecl 0x55d011f677b8 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x55d011f67880 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55d011f67868 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55d011f67820 <col:11> 'int (void)' Function 0x55d011f67230 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55d011f67990 <line:22:3, col:34>
    | `-VarDecl 0x55d011f678d0 <col:3, col:33> col:7 used y 'int' cinit
    |   `-CallExpr 0x55d011f67970 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55d011f67958 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55d011f67938 <col:11> 'int (void)' Function 0x55d011f67230 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55d011f67b38 <line:23:3, col:35>
    | |-UnaryOperator 0x55d011f67af0 <col:7, col:25> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55d011f67ad0 <col:8, col:25> 'int'
    | |   `-BinaryOperator 0x55d011f67ab0 <col:9, col:24> 'int' '&&'
    | |     |-BinaryOperator 0x55d011f67a18 <col:9, col:14> 'int' '=='
    | |     | |-ImplicitCastExpr 0x55d011f679e8 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x55d011f679a8 <col:9> 'int' lvalue Var 0x55d011f677b8 'x' 'int'
    | |     | `-ImplicitCastExpr 0x55d011f67a00 <col:14> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x55d011f679c8 <col:14> 'int' lvalue Var 0x55d011f678d0 'y' 'int'
    | |     `-BinaryOperator 0x55d011f67a90 <col:19, col:24> 'int' '>='
    | |       |-ImplicitCastExpr 0x55d011f67a78 <col:19> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x55d011f67a38 <col:19> 'int' lvalue Var 0x55d011f677b8 'x' 'int'
    | |       `-IntegerLiteral 0x55d011f67a58 <col:24> 'int' 0
    | `-ReturnStmt 0x55d011f67b28 <col:28, col:35>
    |   `-IntegerLiteral 0x55d011f67b08 <col:35> 'int' 0
    |-WhileStmt 0x55d011f67c58 <line:24:3, line:27:3>
    | |-BinaryOperator 0x55d011f67ba8 <line:24:10, col:14> 'int' '>'
    | | |-ImplicitCastExpr 0x55d011f67b90 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55d011f67b50 <col:10> 'int' lvalue Var 0x55d011f677b8 'x' 'int'
    | | `-IntegerLiteral 0x55d011f67b70 <col:14> 'int' 0
    | `-CompoundStmt 0x55d011f67c38 <col:17, line:27:3>
    |   |-UnaryOperator 0x55d011f67be8 <line:25:5, col:6> 'int' postfix '--'
    |   | `-DeclRefExpr 0x55d011f67bc8 <col:5> 'int' lvalue Var 0x55d011f677b8 'x' 'int'
    |   `-UnaryOperator 0x55d011f67c20 <line:26:5, col:6> 'int' postfix '--'
    |     `-DeclRefExpr 0x55d011f67c00 <col:5> 'int' lvalue Var 0x55d011f678d0 'y' 'int'
    |-CallExpr 0x55d011f67d50 <line:28:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55d011f67d38 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55d011f67c70 <col:3> 'void (int)' Function 0x55d011f67518 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55d011f67ce8 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x55d011f67cd0 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55d011f67c90 <col:21> 'int' lvalue Var 0x55d011f678d0 'y' 'int'
    |   `-IntegerLiteral 0x55d011f67cb0 <col:24> 'int' 0
    `-ReturnStmt 0x55d011f67d98 <line:29:3, col:10>
      `-IntegerLiteral 0x55d011f67d78 <col:10> 'int' 0
1 warning generated.
