./Benchmark/PLDI/SVComp/loop-zilu/benchmark19_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark19_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x562af4702f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x562af47037e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x562af47034e0 '__int128'
|-TypedefDecl 0x562af4703850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562af4703500 'unsigned __int128'
|-TypedefDecl 0x562af4703b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x562af4703930 'struct __NSConstantString_tag'
|   `-Record 0x562af47038a8 '__NSConstantString_tag'
|-TypedefDecl 0x562af4703bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562af4703bb0 'char *'
|   `-BuiltinType 0x562af4702fe0 'char'
|-TypedefDecl 0x562af4703ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562af4703e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562af4703cd0 'struct __va_list_tag'
|     `-Record 0x562af4703c48 '__va_list_tag'
|-FunctionDecl 0x562af4762ef8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark19_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x562af4763188 <col:24, col:35>
|   `-CallExpr 0x562af4763160 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x562af4763148 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x562af47630e0 <col:25> 'int ()' Function 0x562af4763030 'assert' 'int ()'
|     `-IntegerLiteral 0x562af4763100 <col:32> 'int' 0
|-FunctionDecl 0x562af4763270 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x562af47633d8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x562af4763558 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x562af4763490 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x562af4763700 <col:34, line:10:1>
|   `-IfStmt 0x562af47636e8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x562af4763638 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x562af4763620 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x562af4763600 <col:8> 'int' lvalue ParmVar 0x562af4763490 'cond' 'int'
|     `-CompoundStmt 0x562af47636d0 <col:14, line:9:3>
|       `-CallExpr 0x562af47636b0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x562af4763698 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x562af4763650 <col:5> 'void (void)' Function 0x562af4762ef8 'reach_error' 'void (void)'
`-FunctionDecl 0x562af4763740 <line:20:1, line:30:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x562af47644a8 <col:12, line:30:1>
    |-DeclStmt 0x562af47638e0 <line:21:3, col:34>
    | `-VarDecl 0x562af47637f8 <col:3, col:33> col:7 used j 'int' cinit
    |   `-CallExpr 0x562af47638c0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x562af47638a8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562af4763860 <col:11> 'int (void)' Function 0x562af4763270 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x562af47639d0 <line:22:3, col:34>
    | `-VarDecl 0x562af4763910 <col:3, col:33> col:7 used k 'int' cinit
    |   `-CallExpr 0x562af47639b0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x562af4763998 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562af4763978 <col:11> 'int (void)' Function 0x562af4763270 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x562af4763ac0 <line:23:3, col:34>
    | `-VarDecl 0x562af4763a00 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x562af4763aa0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x562af4763a88 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562af4763a68 <col:11> 'int (void)' Function 0x562af4763270 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x562af4763d78 <line:24:3, col:44>
    | |-UnaryOperator 0x562af4763d30 <col:7, col:34> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x562af4763d10 <col:8, col:34> 'int'
    | |   `-BinaryOperator 0x562af4763cf0 <col:9, col:33> 'int' '&&'
    | |     |-BinaryOperator 0x562af4763c38 <col:9, col:24> 'int' '&&'
    | |     | |-ParenExpr 0x562af4763b68 <col:9, col:14> 'int'
    | |     | | `-BinaryOperator 0x562af4763b48 <col:10, col:13> 'int' '=='
    | |     | |   |-ImplicitCastExpr 0x562af4763b18 <col:10> 'int' <LValueToRValue>
    | |     | |   | `-DeclRefExpr 0x562af4763ad8 <col:10> 'int' lvalue Var 0x562af47637f8 'j' 'int'
    | |     | |   `-ImplicitCastExpr 0x562af4763b30 <col:13> 'int' <LValueToRValue>
    | |     | |     `-DeclRefExpr 0x562af4763af8 <col:13> 'int' lvalue Var 0x562af4763a00 'n' 'int'
    | |     | `-ParenExpr 0x562af4763c18 <col:19, col:24> 'int'
    | |     |   `-BinaryOperator 0x562af4763bf8 <col:20, col:23> 'int' '=='
    | |     |     |-ImplicitCastExpr 0x562af4763bc8 <col:20> 'int' <LValueToRValue>
    | |     |     | `-DeclRefExpr 0x562af4763b88 <col:20> 'int' lvalue Var 0x562af4763910 'k' 'int'
    | |     |     `-ImplicitCastExpr 0x562af4763be0 <col:23> 'int' <LValueToRValue>
    | |     |       `-DeclRefExpr 0x562af4763ba8 <col:23> 'int' lvalue Var 0x562af4763a00 'n' 'int'
    | |     `-ParenExpr 0x562af4763cd0 <col:29, col:33> 'int'
    | |       `-BinaryOperator 0x562af4763cb0 <col:30, col:32> 'int' '>'
    | |         |-ImplicitCastExpr 0x562af4763c98 <col:30> 'int' <LValueToRValue>
    | |         | `-DeclRefExpr 0x562af4763c58 <col:30> 'int' lvalue Var 0x562af4763a00 'n' 'int'
    | |         `-IntegerLiteral 0x562af4763c78 <col:32> 'int' 0
    | `-ReturnStmt 0x562af4763d68 <col:37, col:44>
    |   `-IntegerLiteral 0x562af4763d48 <col:44> 'int' 0
    |-WhileStmt 0x562af4764338 <line:25:3, line:27:3>
    | |-BinaryOperator 0x562af4764288 <line:25:10, col:19> 'int' '&&'
    | | |-BinaryOperator 0x562af4763de8 <col:10, col:12> 'int' '>'
    | | | |-ImplicitCastExpr 0x562af4763dd0 <col:10> 'int' <LValueToRValue>
    | | | | `-DeclRefExpr 0x562af4763d90 <col:10> 'int' lvalue Var 0x562af47637f8 'j' 'int'
    | | | `-IntegerLiteral 0x562af4763db0 <col:12> 'int' 0
    | | `-BinaryOperator 0x562af4764268 <col:17, col:19> 'int' '>'
    | |   |-ImplicitCastExpr 0x562af4764250 <col:17> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x562af4763e08 <col:17> 'int' lvalue Var 0x562af4763a00 'n' 'int'
    | |   `-IntegerLiteral 0x562af4764230 <col:19> 'int' 0
    | `-CompoundStmt 0x562af4764318 <col:22, line:27:3>
    |   |-UnaryOperator 0x562af47642c8 <line:26:5, col:6> 'int' postfix '--'
    |   | `-DeclRefExpr 0x562af47642a8 <col:5> 'int' lvalue Var 0x562af47637f8 'j' 'int'
    |   `-UnaryOperator 0x562af4764300 <col:9, col:10> 'int' postfix '--'
    |     `-DeclRefExpr 0x562af47642e0 <col:9> 'int' lvalue Var 0x562af4763910 'k' 'int'
    |-CallExpr 0x562af4764450 <line:28:3, col:29> 'void'
    | |-ImplicitCastExpr 0x562af4764438 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x562af4764350 <col:3> 'void (int)' Function 0x562af4763558 '__VERIFIER_assert' 'void (int)'
    | `-ParenExpr 0x562af47643e8 <col:21, col:28> 'int'
    |   `-BinaryOperator 0x562af47643c8 <col:22, col:27> 'int' '=='
    |     |-ImplicitCastExpr 0x562af47643b0 <col:22> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x562af4764370 <col:22> 'int' lvalue Var 0x562af4763910 'k' 'int'
    |     `-IntegerLiteral 0x562af4764390 <col:27> 'int' 0
    `-ReturnStmt 0x562af4764498 <line:29:3, col:10>
      `-IntegerLiteral 0x562af4764478 <col:10> 'int' 0
1 warning generated.
