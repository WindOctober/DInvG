./Benchmark/PLDI/SVComp/loop-zilu/benchmark17_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark17_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x558ff24bff48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x558ff24c07e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x558ff24c04e0 '__int128'
|-TypedefDecl 0x558ff24c0850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x558ff24c0500 'unsigned __int128'
|-TypedefDecl 0x558ff24c0b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x558ff24c0930 'struct __NSConstantString_tag'
|   `-Record 0x558ff24c08a8 '__NSConstantString_tag'
|-TypedefDecl 0x558ff24c0bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x558ff24c0bb0 'char *'
|   `-BuiltinType 0x558ff24bffe0 'char'
|-TypedefDecl 0x558ff24c0ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x558ff24c0e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x558ff24c0cd0 'struct __va_list_tag'
|     `-Record 0x558ff24c0c48 '__va_list_tag'
|-FunctionDecl 0x558ff251fef8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark17_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x558ff2520188 <col:24, col:35>
|   `-CallExpr 0x558ff2520160 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x558ff2520148 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x558ff25200e0 <col:25> 'int ()' Function 0x558ff2520030 'assert' 'int ()'
|     `-IntegerLiteral 0x558ff2520100 <col:32> 'int' 0
|-FunctionDecl 0x558ff2520270 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x558ff25203d8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x558ff2520558 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x558ff2520490 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x558ff2520700 <col:34, line:10:1>
|   `-IfStmt 0x558ff25206e8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x558ff2520638 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x558ff2520620 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x558ff2520600 <col:8> 'int' lvalue ParmVar 0x558ff2520490 'cond' 'int'
|     `-CompoundStmt 0x558ff25206d0 <col:14, line:9:3>
|       `-CallExpr 0x558ff25206b0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x558ff2520698 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x558ff2520650 <col:5> 'void (void)' Function 0x558ff251fef8 'reach_error' 'void (void)'
`-FunctionDecl 0x558ff2520740 <line:23:1, line:35:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x558ff25212e8 <col:12, line:35:1>
    |-DeclStmt 0x558ff25208e0 <line:24:3, col:34>
    | `-VarDecl 0x558ff25207f8 <col:3, col:33> col:7 used i 'int' cinit
    |   `-CallExpr 0x558ff25208c0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x558ff25208a8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x558ff2520860 <col:11> 'int (void)' Function 0x558ff2520270 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x558ff25209d0 <line:25:3, col:34>
    | `-VarDecl 0x558ff2520910 <col:3, col:33> col:7 used k 'int' cinit
    |   `-CallExpr 0x558ff25209b0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x558ff2520998 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x558ff2520978 <col:11> 'int (void)' Function 0x558ff2520270 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x558ff2520ac0 <line:26:3, col:34>
    | `-VarDecl 0x558ff2520a00 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x558ff2520aa0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x558ff2520a88 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x558ff2520a68 <col:11> 'int (void)' Function 0x558ff2520270 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x558ff2520c50 <line:28:3, col:31>
    | |-UnaryOperator 0x558ff2520c08 <col:7, col:21> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x558ff2520be8 <col:8, col:21> 'int'
    | |   `-BinaryOperator 0x558ff2520bc8 <col:9, col:20> 'int' '&&'
    | |     |-BinaryOperator 0x558ff2520b30 <col:9, col:12> 'int' '=='
    | |     | |-ImplicitCastExpr 0x558ff2520b18 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x558ff2520ad8 <col:9> 'int' lvalue Var 0x558ff25207f8 'i' 'int'
    | |     | `-IntegerLiteral 0x558ff2520af8 <col:12> 'int' 0
    | |     `-BinaryOperator 0x558ff2520ba8 <col:17, col:20> 'int' '=='
    | |       |-ImplicitCastExpr 0x558ff2520b90 <col:17> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x558ff2520b50 <col:17> 'int' lvalue Var 0x558ff2520910 'k' 'int'
    | |       `-IntegerLiteral 0x558ff2520b70 <col:20> 'int' 0
    | `-ReturnStmt 0x558ff2520c40 <col:24, col:31>
    |   `-IntegerLiteral 0x558ff2520c20 <col:31> 'int' 0
    |-WhileStmt 0x558ff2520d88 <line:29:3, line:32:3>
    | |-BinaryOperator 0x558ff2520cd8 <line:29:10, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x558ff2520ca8 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558ff2520c68 <col:10> 'int' lvalue Var 0x558ff25207f8 'i' 'int'
    | | `-ImplicitCastExpr 0x558ff2520cc0 <col:12> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x558ff2520c88 <col:12> 'int' lvalue Var 0x558ff2520a00 'n' 'int'
    | `-CompoundStmt 0x558ff2520d68 <col:15, line:32:3>
    |   |-UnaryOperator 0x558ff2520d18 <line:30:5, col:6> 'int' postfix '++'
    |   | `-DeclRefExpr 0x558ff2520cf8 <col:5> 'int' lvalue Var 0x558ff25207f8 'i' 'int'
    |   `-UnaryOperator 0x558ff2520d50 <line:31:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x558ff2520d30 <col:5> 'int' lvalue Var 0x558ff2520910 'k' 'int'
    |-CallExpr 0x558ff2521290 <line:33:3, col:25> 'void'
    | |-ImplicitCastExpr 0x558ff2521278 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x558ff2520da0 <col:3> 'void (int)' Function 0x558ff2520558 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x558ff2521230 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x558ff2520e00 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x558ff2520dc0 <col:21> 'int' lvalue Var 0x558ff2520910 'k' 'int'
    |   `-ImplicitCastExpr 0x558ff2520e18 <col:24> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x558ff2520de0 <col:24> 'int' lvalue Var 0x558ff2520a00 'n' 'int'
    `-ReturnStmt 0x558ff25212d8 <line:34:3, col:10>
      `-IntegerLiteral 0x558ff25212b8 <col:10> 'int' 0
1 warning generated.
