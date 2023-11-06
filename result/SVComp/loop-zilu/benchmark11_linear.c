./Benchmark/PLDI/SVComp/loop-zilu/benchmark11_linear.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark11_linear.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55a70403eee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55a70403f780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55a70403f480 '__int128'
|-TypedefDecl 0x55a70403f7f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55a70403f4a0 'unsigned __int128'
|-TypedefDecl 0x55a70403faf8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55a70403f8d0 'struct __NSConstantString_tag'
|   `-Record 0x55a70403f848 '__NSConstantString_tag'
|-TypedefDecl 0x55a70403fb90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55a70403fb50 'char *'
|   `-BuiltinType 0x55a70403ef80 'char'
|-TypedefDecl 0x55a70403fe88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55a70403fe30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55a70403fc70 'struct __va_list_tag'
|     `-Record 0x55a70403fbe8 '__va_list_tag'
|-FunctionDecl 0x55a70409ee68 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark11_linear.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55a70409f0f8 <col:24, col:35>
|   `-CallExpr 0x55a70409f0d0 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55a70409f0b8 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55a70409f050 <col:25> 'int ()' Function 0x55a70409efa0 'assert' 'int ()'
|     `-IntegerLiteral 0x55a70409f070 <col:32> 'int' 0
|-FunctionDecl 0x55a70409f1e0 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55a70409f348 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55a70409f4c8 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55a70409f400 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55a70409f670 <col:34, line:10:1>
|   `-IfStmt 0x55a70409f658 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55a70409f5a8 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55a70409f590 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55a70409f570 <col:8> 'int' lvalue ParmVar 0x55a70409f400 'cond' 'int'
|     `-CompoundStmt 0x55a70409f640 <col:14, line:9:3>
|       `-CallExpr 0x55a70409f620 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55a70409f608 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55a70409f5c0 <col:5> 'void (void)' Function 0x55a70409ee68 'reach_error' 'void (void)'
`-FunctionDecl 0x55a70409f6b0 <line:23:1, line:33:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x55a70409fd28 <col:12, line:33:1>
    |-DeclStmt 0x55a70409f850 <line:24:3, col:34>
    | `-VarDecl 0x55a70409f768 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x55a70409f830 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55a70409f818 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55a70409f7d0 <col:11> 'int (void)' Function 0x55a70409f1e0 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55a70409f940 <line:25:3, col:34>
    | `-VarDecl 0x55a70409f880 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x55a70409f920 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55a70409f908 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55a70409f8e8 <col:11> 'int (void)' Function 0x55a70409f1e0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55a70409fad0 <line:27:3, col:30>
    | |-UnaryOperator 0x55a70409fa88 <col:7, col:20> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55a70409fa68 <col:8, col:20> 'int'
    | |   `-BinaryOperator 0x55a70409fa48 <col:9, col:19> 'int' '&&'
    | |     |-BinaryOperator 0x55a70409f9b0 <col:9, col:12> 'int' '=='
    | |     | |-ImplicitCastExpr 0x55a70409f998 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x55a70409f958 <col:9> 'int' lvalue Var 0x55a70409f768 'x' 'int'
    | |     | `-IntegerLiteral 0x55a70409f978 <col:12> 'int' 0
    | |     `-BinaryOperator 0x55a70409fa28 <col:17, col:19> 'int' '>'
    | |       |-ImplicitCastExpr 0x55a70409fa10 <col:17> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x55a70409f9d0 <col:17> 'int' lvalue Var 0x55a70409f880 'n' 'int'
    | |       `-IntegerLiteral 0x55a70409f9f0 <col:19> 'int' 0
    | `-ReturnStmt 0x55a70409fac0 <col:23, col:30>
    |   `-IntegerLiteral 0x55a70409faa0 <col:30> 'int' 0
    |-WhileStmt 0x55a70409fbc8 <line:28:3, line:30:3>
    | |-BinaryOperator 0x55a70409fb58 <line:28:10, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x55a70409fb28 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55a70409fae8 <col:10> 'int' lvalue Var 0x55a70409f768 'x' 'int'
    | | `-ImplicitCastExpr 0x55a70409fb40 <col:12> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55a70409fb08 <col:12> 'int' lvalue Var 0x55a70409f880 'n' 'int'
    | `-CompoundStmt 0x55a70409fbb0 <col:15, line:30:3>
    |   `-UnaryOperator 0x55a70409fb98 <line:29:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x55a70409fb78 <col:5> 'int' lvalue Var 0x55a70409f768 'x' 'int'
    |-CallExpr 0x55a70409fcd0 <line:31:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55a70409fcb8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55a70409fbe0 <col:3> 'void (int)' Function 0x55a70409f4c8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55a70409fc70 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55a70409fc40 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55a70409fc00 <col:21> 'int' lvalue Var 0x55a70409f768 'x' 'int'
    |   `-ImplicitCastExpr 0x55a70409fc58 <col:24> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x55a70409fc20 <col:24> 'int' lvalue Var 0x55a70409f880 'n' 'int'
    `-ReturnStmt 0x55a70409fd18 <line:32:3, col:10>
      `-IntegerLiteral 0x55a70409fcf8 <col:10> 'int' 0
1 warning generated.
