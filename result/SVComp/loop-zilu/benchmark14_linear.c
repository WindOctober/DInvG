./Benchmark/PLDI/SVComp/loop-zilu/benchmark14_linear.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark14_linear.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x5649a1af3ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5649a1af4780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5649a1af4480 '__int128'
|-TypedefDecl 0x5649a1af47f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5649a1af44a0 'unsigned __int128'
|-TypedefDecl 0x5649a1af4af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5649a1af48d0 'struct __NSConstantString_tag'
|   `-Record 0x5649a1af4848 '__NSConstantString_tag'
|-TypedefDecl 0x5649a1af4b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5649a1af4b50 'char *'
|   `-BuiltinType 0x5649a1af3f80 'char'
|-TypedefDecl 0x5649a1af4e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5649a1af4e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5649a1af4c70 'struct __va_list_tag'
|     `-Record 0x5649a1af4be8 '__va_list_tag'
|-FunctionDecl 0x5649a1b53e48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark14_linear.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x5649a1b540d8 <col:24, col:35>
|   `-CallExpr 0x5649a1b540b0 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x5649a1b54098 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5649a1b54030 <col:25> 'int ()' Function 0x5649a1b53f80 'assert' 'int ()'
|     `-IntegerLiteral 0x5649a1b54050 <col:32> 'int' 0
|-FunctionDecl 0x5649a1b541c0 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x5649a1b54328 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x5649a1b544a8 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5649a1b543e0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5649a1b54650 <col:34, line:10:1>
|   `-IfStmt 0x5649a1b54638 <line:7:3, line:9:3>
|     |-UnaryOperator 0x5649a1b54588 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5649a1b54570 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5649a1b54550 <col:8> 'int' lvalue ParmVar 0x5649a1b543e0 'cond' 'int'
|     `-CompoundStmt 0x5649a1b54620 <col:14, line:9:3>
|       `-CallExpr 0x5649a1b54600 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x5649a1b545e8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5649a1b545a0 <col:5> 'void (void)' Function 0x5649a1b53e48 'reach_error' 'void (void)'
`-FunctionDecl 0x5649a1b54690 <line:23:1, line:32:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x5649a1b54be8 <col:12, line:32:1>
    |-DeclStmt 0x5649a1b54830 <line:24:3, col:34>
    | `-VarDecl 0x5649a1b54748 <col:3, col:33> col:7 used i 'int' cinit
    |   `-CallExpr 0x5649a1b54810 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5649a1b547f8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5649a1b547b0 <col:11> 'int (void)' Function 0x5649a1b541c0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x5649a1b549c0 <line:26:3, col:33>
    | |-UnaryOperator 0x5649a1b54978 <col:7, col:23> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5649a1b54958 <col:8, col:23> 'int'
    | |   `-BinaryOperator 0x5649a1b54938 <col:9, col:20> 'int' '&&'
    | |     |-BinaryOperator 0x5649a1b548a0 <col:9, col:12> 'int' '>='
    | |     | |-ImplicitCastExpr 0x5649a1b54888 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x5649a1b54848 <col:9> 'int' lvalue Var 0x5649a1b54748 'i' 'int'
    | |     | `-IntegerLiteral 0x5649a1b54868 <col:12> 'int' 0
    | |     `-BinaryOperator 0x5649a1b54918 <col:17, col:20> 'int' '<='
    | |       |-ImplicitCastExpr 0x5649a1b54900 <col:17> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5649a1b548c0 <col:17> 'int' lvalue Var 0x5649a1b54748 'i' 'int'
    | |       `-IntegerLiteral 0x5649a1b548e0 <col:20> 'int' 200
    | `-ReturnStmt 0x5649a1b549b0 <col:26, col:33>
    |   `-IntegerLiteral 0x5649a1b54990 <col:33> 'int' 0
    |-WhileStmt 0x5649a1b54aa0 <line:27:3, line:29:3>
    | |-BinaryOperator 0x5649a1b54a30 <line:27:10, col:12> 'int' '>'
    | | |-ImplicitCastExpr 0x5649a1b54a18 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5649a1b549d8 <col:10> 'int' lvalue Var 0x5649a1b54748 'i' 'int'
    | | `-IntegerLiteral 0x5649a1b549f8 <col:12> 'int' 0
    | `-CompoundStmt 0x5649a1b54a88 <col:15, line:29:3>
    |   `-UnaryOperator 0x5649a1b54a70 <line:28:5, col:6> 'int' postfix '--'
    |     `-DeclRefExpr 0x5649a1b54a50 <col:5> 'int' lvalue Var 0x5649a1b54748 'i' 'int'
    |-CallExpr 0x5649a1b54b90 <line:30:3, col:25> 'void'
    | |-ImplicitCastExpr 0x5649a1b54b78 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5649a1b54ab8 <col:3> 'void (int)' Function 0x5649a1b544a8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5649a1b54b30 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x5649a1b54b18 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5649a1b54ad8 <col:21> 'int' lvalue Var 0x5649a1b54748 'i' 'int'
    |   `-IntegerLiteral 0x5649a1b54af8 <col:24> 'int' 0
    `-ReturnStmt 0x5649a1b54bd8 <line:31:3, col:10>
      `-IntegerLiteral 0x5649a1b54bb8 <col:10> 'int' 0
1 warning generated.
