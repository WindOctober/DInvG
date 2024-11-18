./Benchmark/PLDI/SVComp/loop-zilu/benchmark05_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark05_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55972dce5f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55972dce67e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55972dce64e0 '__int128'
|-TypedefDecl 0x55972dce6850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55972dce6500 'unsigned __int128'
|-TypedefDecl 0x55972dce6b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55972dce6930 'struct __NSConstantString_tag'
|   `-Record 0x55972dce68a8 '__NSConstantString_tag'
|-TypedefDecl 0x55972dce6bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55972dce6bb0 'char *'
|   `-BuiltinType 0x55972dce5fe0 'char'
|-TypedefDecl 0x55972dce6ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55972dce6e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55972dce6cd0 'struct __va_list_tag'
|     `-Record 0x55972dce6c48 '__va_list_tag'
|-FunctionDecl 0x55972dd45c08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark05_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55972dd45e98 <col:24, col:35>
|   `-CallExpr 0x55972dd45e70 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55972dd45e58 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55972dd45df0 <col:25> 'int ()' Function 0x55972dd45d40 'assert' 'int ()'
|     `-IntegerLiteral 0x55972dd45e10 <col:32> 'int' 0
|-FunctionDecl 0x55972dd45f80 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55972dd460e8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55972dd46268 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55972dd461a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55972dd46410 <col:34, line:10:1>
|   `-IfStmt 0x55972dd463f8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55972dd46348 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55972dd46330 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55972dd46310 <col:8> 'int' lvalue ParmVar 0x55972dd461a0 'cond' 'int'
|     `-CompoundStmt 0x55972dd463e0 <col:14, line:9:3>
|       `-CallExpr 0x55972dd463c0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55972dd463a8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55972dd46360 <col:5> 'void (void)' Function 0x55972dd45c08 'reach_error' 'void (void)'
`-FunctionDecl 0x55972dd46450 <line:23:1, line:35:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x55972dd47338 <col:12, line:35:1>
    |-DeclStmt 0x55972dd465f0 <line:24:3, col:34>
    | `-VarDecl 0x55972dd46508 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x55972dd465d0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55972dd465b8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55972dd46570 <col:11> 'int (void)' Function 0x55972dd45f80 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55972dd466e0 <line:25:3, col:34>
    | `-VarDecl 0x55972dd46620 <col:3, col:33> col:7 used y 'int' cinit
    |   `-CallExpr 0x55972dd466c0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55972dd466a8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55972dd46688 <col:11> 'int (void)' Function 0x55972dd45f80 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55972dd467d0 <line:26:3, col:34>
    | `-VarDecl 0x55972dd46710 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x55972dd467b0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55972dd46798 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55972dd46778 <col:11> 'int (void)' Function 0x55972dd45f80 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55972dd46a28 <line:28:3, col:38>
    | |-UnaryOperator 0x55972dd469e0 <col:7, col:28> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55972dd469c0 <col:8, col:28> 'int'
    | |   `-BinaryOperator 0x55972dd469a0 <col:9, col:27> 'int' '&&'
    | |     |-BinaryOperator 0x55972dd468f0 <col:9, col:20> 'int' '&&'
    | |     | |-BinaryOperator 0x55972dd46840 <col:9, col:12> 'int' '>='
    | |     | | |-ImplicitCastExpr 0x55972dd46828 <col:9> 'int' <LValueToRValue>
    | |     | | | `-DeclRefExpr 0x55972dd467e8 <col:9> 'int' lvalue Var 0x55972dd46508 'x' 'int'
    | |     | | `-IntegerLiteral 0x55972dd46808 <col:12> 'int' 0
    | |     | `-BinaryOperator 0x55972dd468d0 <col:17, col:20> 'int' '<='
    | |     |   |-ImplicitCastExpr 0x55972dd468a0 <col:17> 'int' <LValueToRValue>
    | |     |   | `-DeclRefExpr 0x55972dd46860 <col:17> 'int' lvalue Var 0x55972dd46508 'x' 'int'
    | |     |   `-ImplicitCastExpr 0x55972dd468b8 <col:20> 'int' <LValueToRValue>
    | |     |     `-DeclRefExpr 0x55972dd46880 <col:20> 'int' lvalue Var 0x55972dd46620 'y' 'int'
    | |     `-BinaryOperator 0x55972dd46980 <col:25, col:27> 'int' '<'
    | |       |-ImplicitCastExpr 0x55972dd46950 <col:25> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x55972dd46910 <col:25> 'int' lvalue Var 0x55972dd46620 'y' 'int'
    | |       `-ImplicitCastExpr 0x55972dd46968 <col:27> 'int' <LValueToRValue>
    | |         `-DeclRefExpr 0x55972dd46930 <col:27> 'int' lvalue Var 0x55972dd46710 'n' 'int'
    | `-ReturnStmt 0x55972dd46a18 <col:31, col:38>
    |   `-IntegerLiteral 0x55972dd469f8 <col:38> 'int' 0
    |-WhileStmt 0x55972dd471d0 <line:29:3, line:32:3>
    | |-BinaryOperator 0x55972dd46ab0 <line:29:10, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x55972dd46a80 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55972dd46a40 <col:10> 'int' lvalue Var 0x55972dd46508 'x' 'int'
    | | `-ImplicitCastExpr 0x55972dd46a98 <col:12> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55972dd46a60 <col:12> 'int' lvalue Var 0x55972dd46710 'n' 'int'
    | `-CompoundStmt 0x55972dd471b0 <col:15, line:32:3>
    |   |-UnaryOperator 0x55972dd46af0 <line:30:5, col:6> 'int' postfix '++'
    |   | `-DeclRefExpr 0x55972dd46ad0 <col:5> 'int' lvalue Var 0x55972dd46508 'x' 'int'
    |   `-IfStmt 0x55972dd47198 <line:31:5, col:15>
    |     |-BinaryOperator 0x55972dd47140 <col:9, col:11> 'int' '>'
    |     | |-ImplicitCastExpr 0x55972dd47110 <col:9> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55972dd46b08 <col:9> 'int' lvalue Var 0x55972dd46508 'x' 'int'
    |     | `-ImplicitCastExpr 0x55972dd47128 <col:11> 'int' <LValueToRValue>
    |     |   `-DeclRefExpr 0x55972dd470f0 <col:11> 'int' lvalue Var 0x55972dd46620 'y' 'int'
    |     `-UnaryOperator 0x55972dd47180 <col:14, col:15> 'int' postfix '++'
    |       `-DeclRefExpr 0x55972dd47160 <col:14> 'int' lvalue Var 0x55972dd46620 'y' 'int'
    |-CallExpr 0x55972dd472e0 <line:33:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55972dd472c8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55972dd471e8 <col:3> 'void (int)' Function 0x55972dd46268 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55972dd47278 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55972dd47248 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55972dd47208 <col:21> 'int' lvalue Var 0x55972dd46620 'y' 'int'
    |   `-ImplicitCastExpr 0x55972dd47260 <col:24> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x55972dd47228 <col:24> 'int' lvalue Var 0x55972dd46710 'n' 'int'
    `-ReturnStmt 0x55972dd47328 <line:34:3, col:10>
      `-IntegerLiteral 0x55972dd47308 <col:10> 'int' 0
1 warning generated.
