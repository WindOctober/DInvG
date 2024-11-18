./Benchmark/PLDI/SVComp/loop-zilu/benchmark25_linear.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark25_linear.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55c2bffaeee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55c2bffaf780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55c2bffaf480 '__int128'
|-TypedefDecl 0x55c2bffaf7f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55c2bffaf4a0 'unsigned __int128'
|-TypedefDecl 0x55c2bffafaf8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55c2bffaf8d0 'struct __NSConstantString_tag'
|   `-Record 0x55c2bffaf848 '__NSConstantString_tag'
|-TypedefDecl 0x55c2bffafb90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55c2bffafb50 'char *'
|   `-BuiltinType 0x55c2bffaef80 'char'
|-TypedefDecl 0x55c2bffafe88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55c2bffafe30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55c2bffafc70 'struct __va_list_tag'
|     `-Record 0x55c2bffafbe8 '__va_list_tag'
|-FunctionDecl 0x55c2c000ee08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark25_linear.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55c2c000f098 <col:24, col:35>
|   `-CallExpr 0x55c2c000f070 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55c2c000f058 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55c2c000eff0 <col:25> 'int ()' Function 0x55c2c000ef40 'assert' 'int ()'
|     `-IntegerLiteral 0x55c2c000f010 <col:32> 'int' 0
|-FunctionDecl 0x55c2c000f180 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55c2c000f2e8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55c2c000f468 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55c2c000f3a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55c2c000f610 <col:34, line:10:1>
|   `-IfStmt 0x55c2c000f5f8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55c2c000f548 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55c2c000f530 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55c2c000f510 <col:8> 'int' lvalue ParmVar 0x55c2c000f3a0 'cond' 'int'
|     `-CompoundStmt 0x55c2c000f5e0 <col:14, line:9:3>
|       `-CallExpr 0x55c2c000f5c0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55c2c000f5a8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55c2c000f560 <col:5> 'void (void)' Function 0x55c2c000ee08 'reach_error' 'void (void)'
`-FunctionDecl 0x55c2c000f650 <line:20:1, line:28:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x55c2c000fb98 <col:12, line:28:1>
    |-DeclStmt 0x55c2c000f7f0 <line:21:3, col:34>
    | `-VarDecl 0x55c2c000f708 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x55c2c000f7d0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55c2c000f7b8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55c2c000f770 <col:11> 'int (void)' Function 0x55c2c000f180 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55c2c000f8e8 <line:22:3, col:22>
    | |-UnaryOperator 0x55c2c000f8a0 <col:7, col:12> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55c2c000f880 <col:8, col:12> 'int'
    | |   `-BinaryOperator 0x55c2c000f860 <col:9, col:11> 'int' '<'
    | |     |-ImplicitCastExpr 0x55c2c000f848 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x55c2c000f808 <col:9> 'int' lvalue Var 0x55c2c000f708 'x' 'int'
    | |     `-IntegerLiteral 0x55c2c000f828 <col:11> 'int' 0
    | `-ReturnStmt 0x55c2c000f8d8 <col:15, col:22>
    |   `-IntegerLiteral 0x55c2c000f8b8 <col:22> 'int' 0
    |-WhileStmt 0x55c2c000fa48 <line:23:3, line:25:3>
    | |-BinaryOperator 0x55c2c000f958 <line:23:10, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x55c2c000f940 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55c2c000f900 <col:10> 'int' lvalue Var 0x55c2c000f708 'x' 'int'
    | | `-IntegerLiteral 0x55c2c000f920 <col:12> 'int' 10
    | `-CompoundStmt 0x55c2c000fa30 <col:16, line:25:3>
    |   `-BinaryOperator 0x55c2c000fa10 <line:24:5, col:9> 'int' '='
    |     |-DeclRefExpr 0x55c2c000f978 <col:5> 'int' lvalue Var 0x55c2c000f708 'x' 'int'
    |     `-BinaryOperator 0x55c2c000f9f0 <col:7, col:9> 'int' '+'
    |       |-ImplicitCastExpr 0x55c2c000f9d8 <col:7> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55c2c000f998 <col:7> 'int' lvalue Var 0x55c2c000f708 'x' 'int'
    |       `-IntegerLiteral 0x55c2c000f9b8 <col:9> 'int' 1
    |-CallExpr 0x55c2c000fb40 <line:26:3, col:26> 'void'
    | |-ImplicitCastExpr 0x55c2c000fb28 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55c2c000fa60 <col:3> 'void (int)' Function 0x55c2c000f468 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55c2c000fad8 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55c2c000fac0 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55c2c000fa80 <col:21> 'int' lvalue Var 0x55c2c000f708 'x' 'int'
    |   `-IntegerLiteral 0x55c2c000faa0 <col:24> 'int' 10
    `-ReturnStmt 0x55c2c000fb88 <line:27:3, col:10>
      `-IntegerLiteral 0x55c2c000fb68 <col:10> 'int' 0
1 warning generated.
