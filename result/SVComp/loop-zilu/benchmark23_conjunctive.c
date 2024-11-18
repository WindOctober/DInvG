./Benchmark/PLDI/SVComp/loop-zilu/benchmark23_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark23_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x5633c53c6f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5633c53c77e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5633c53c74e0 '__int128'
|-TypedefDecl 0x5633c53c7850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5633c53c7500 'unsigned __int128'
|-TypedefDecl 0x5633c53c7b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5633c53c7930 'struct __NSConstantString_tag'
|   `-Record 0x5633c53c78a8 '__NSConstantString_tag'
|-TypedefDecl 0x5633c53c7bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5633c53c7bb0 'char *'
|   `-BuiltinType 0x5633c53c6fe0 'char'
|-TypedefDecl 0x5633c53c7ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5633c53c7e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5633c53c7cd0 'struct __va_list_tag'
|     `-Record 0x5633c53c7c48 '__va_list_tag'
|-FunctionDecl 0x5633c5426ed8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark23_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x5633c5427168 <col:24, col:35>
|   `-CallExpr 0x5633c5427140 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x5633c5427128 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5633c54270c0 <col:25> 'int ()' Function 0x5633c5427010 'assert' 'int ()'
|     `-IntegerLiteral 0x5633c54270e0 <col:32> 'int' 0
|-FunctionDecl 0x5633c5427250 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x5633c54273b8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x5633c5427538 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5633c5427470 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5633c54276e0 <col:34, line:10:1>
|   `-IfStmt 0x5633c54276c8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x5633c5427618 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5633c5427600 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5633c54275e0 <col:8> 'int' lvalue ParmVar 0x5633c5427470 'cond' 'int'
|     `-CompoundStmt 0x5633c54276b0 <col:14, line:9:3>
|       `-CallExpr 0x5633c5427690 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x5633c5427678 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5633c5427630 <col:5> 'void (void)' Function 0x5633c5426ed8 'reach_error' 'void (void)'
`-FunctionDecl 0x5633c5427720 <line:23:1, line:34:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x5633c5428210 <col:12, line:34:1>
    |-DeclStmt 0x5633c54278c0 <line:24:3, col:34>
    | `-VarDecl 0x5633c54277d8 <col:3, col:33> col:7 used i 'int' cinit
    |   `-CallExpr 0x5633c54278a0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5633c5427888 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5633c5427840 <col:11> 'int (void)' Function 0x5633c5427250 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x5633c54279b0 <line:25:3, col:34>
    | `-VarDecl 0x5633c54278f0 <col:3, col:33> col:7 used j 'int' cinit
    |   `-CallExpr 0x5633c5427990 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x5633c5427978 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5633c5427958 <col:11> 'int (void)' Function 0x5633c5427250 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x5633c5427b40 <line:27:3, col:31>
    | |-UnaryOperator 0x5633c5427af8 <col:7, col:21> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5633c5427ad8 <col:8, col:21> 'int'
    | |   `-BinaryOperator 0x5633c5427ab8 <col:9, col:20> 'int' '&&'
    | |     |-BinaryOperator 0x5633c5427a20 <col:9, col:12> 'int' '=='
    | |     | |-ImplicitCastExpr 0x5633c5427a08 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x5633c54279c8 <col:9> 'int' lvalue Var 0x5633c54277d8 'i' 'int'
    | |     | `-IntegerLiteral 0x5633c54279e8 <col:12> 'int' 0
    | |     `-BinaryOperator 0x5633c5427a98 <col:17, col:20> 'int' '=='
    | |       |-ImplicitCastExpr 0x5633c5427a80 <col:17> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5633c5427a40 <col:17> 'int' lvalue Var 0x5633c54278f0 'j' 'int'
    | |       `-IntegerLiteral 0x5633c5427a60 <col:20> 'int' 0
    | `-ReturnStmt 0x5633c5427b30 <col:24, col:31>
    |   `-IntegerLiteral 0x5633c5427b10 <col:31> 'int' 0
    |-WhileStmt 0x5633c5427c98 <line:28:3, line:31:3>
    | |-BinaryOperator 0x5633c5427bb0 <line:28:10, col:12> 'int' '<'
    | | |-ImplicitCastExpr 0x5633c5427b98 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5633c5427b58 <col:10> 'int' lvalue Var 0x5633c54277d8 'i' 'int'
    | | `-IntegerLiteral 0x5633c5427b78 <col:12> 'int' 100
    | `-CompoundStmt 0x5633c5427c78 <col:17, line:31:3>
    |   |-CompoundAssignOperator 0x5633c5427c10 <line:29:5, col:8> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   | |-DeclRefExpr 0x5633c5427bd0 <col:5> 'int' lvalue Var 0x5633c54278f0 'j' 'int'
    |   | `-IntegerLiteral 0x5633c5427bf0 <col:8> 'int' 2
    |   `-UnaryOperator 0x5633c5427c60 <line:30:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x5633c5427c40 <col:5> 'int' lvalue Var 0x5633c54277d8 'i' 'int'
    |-CallExpr 0x5633c5427d90 <line:32:3, col:27> 'void'
    | |-ImplicitCastExpr 0x5633c5427d78 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5633c5427cb0 <col:3> 'void (int)' Function 0x5633c5427538 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5633c5427d28 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x5633c5427d10 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5633c5427cd0 <col:21> 'int' lvalue Var 0x5633c54278f0 'j' 'int'
    |   `-IntegerLiteral 0x5633c5427cf0 <col:24> 'int' 200
    `-ReturnStmt 0x5633c5427dd8 <line:33:3, col:10>
      `-IntegerLiteral 0x5633c5427db8 <col:10> 'int' 0
1 warning generated.
