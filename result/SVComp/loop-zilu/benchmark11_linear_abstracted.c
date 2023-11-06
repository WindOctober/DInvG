./Benchmark/PLDI/SVComp/loop-zilu/benchmark11_linear_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark11_linear_abstracted.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x56533883a028 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x56533883a8c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x56533883a5c0 '__int128'
|-TypedefDecl 0x56533883a930 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x56533883a5e0 'unsigned __int128'
|-TypedefDecl 0x56533883ac38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x56533883aa10 'struct __NSConstantString_tag'
|   `-Record 0x56533883a988 '__NSConstantString_tag'
|-TypedefDecl 0x56533883acd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x56533883ac90 'char *'
|   `-BuiltinType 0x56533883a0c0 'char'
|-TypedefDecl 0x56533883afc8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x56533883af70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x56533883adb0 'struct __va_list_tag'
|     `-Record 0x56533883ad28 '__va_list_tag'
|-FunctionDecl 0x56533889a068 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark11_linear_abstracted.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x56533889a2f8 <col:24, col:35>
|   `-CallExpr 0x56533889a2d0 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x56533889a2b8 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x56533889a250 <col:25> 'int ()' Function 0x56533889a1a0 'assert' 'int ()'
|     `-IntegerLiteral 0x56533889a270 <col:32> 'int' 0
|-FunctionDecl 0x56533889a3d8 <line:2:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56533889a478 prev 0x56533889a3d8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56533889a5e0 <line:4:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x56533889a748 <line:5:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x56533889a8c8 <line:7:1, line:11:1> line:7:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x56533889a800 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x56533889aa70 <col:34, line:11:1>
|   `-IfStmt 0x56533889aa58 <line:8:3, line:10:3>
|     |-UnaryOperator 0x56533889a9a8 <line:8:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x56533889a990 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x56533889a970 <col:8> 'int' lvalue ParmVar 0x56533889a800 'cond' 'int'
|     `-CompoundStmt 0x56533889aa40 <col:14, line:10:3>
|       `-CallExpr 0x56533889aa20 <line:9:5, col:17> 'void'
|         `-ImplicitCastExpr 0x56533889aa08 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x56533889a9c0 <col:5> 'void (void)' Function 0x56533889a068 'reach_error' 'void (void)'
`-FunctionDecl 0x56533889aab0 <line:24:1, line:41:1> line:24:5 main 'int ()'
  `-CompoundStmt 0x56533889b908 <col:12, line:41:1>
    |-DeclStmt 0x56533889ac50 <line:25:3, col:34>
    | `-VarDecl 0x56533889ab68 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x56533889ac30 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x56533889ac18 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x56533889abd0 <col:11> 'int (void)' Function 0x56533889a5e0 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x56533889ad40 <line:26:3, col:34>
    | `-VarDecl 0x56533889ac80 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x56533889ad20 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x56533889ad08 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x56533889ace8 <col:11> 'int (void)' Function 0x56533889a5e0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x56533889aed0 <line:28:3, col:30>
    | |-UnaryOperator 0x56533889ae88 <col:7, col:20> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x56533889ae68 <col:8, col:20> 'int'
    | |   `-BinaryOperator 0x56533889ae48 <col:9, col:19> 'int' '&&'
    | |     |-BinaryOperator 0x56533889adb0 <col:9, col:12> 'int' '=='
    | |     | |-ImplicitCastExpr 0x56533889ad98 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x56533889ad58 <col:9> 'int' lvalue Var 0x56533889ab68 'x' 'int'
    | |     | `-IntegerLiteral 0x56533889ad78 <col:12> 'int' 0
    | |     `-BinaryOperator 0x56533889ae28 <col:17, col:19> 'int' '>'
    | |       |-ImplicitCastExpr 0x56533889ae10 <col:17> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x56533889add0 <col:17> 'int' lvalue Var 0x56533889ac80 'n' 'int'
    | |       `-IntegerLiteral 0x56533889adf0 <col:19> 'int' 0
    | `-ReturnStmt 0x56533889aec0 <col:23, col:30>
    |   `-IntegerLiteral 0x56533889aea0 <col:30> 'int' 0
    |-IfStmt 0x56533889b7a0 <line:30:3, line:37:3>
    | |-BinaryOperator 0x56533889af58 <line:30:7, col:11> 'int' '<'
    | | |-ImplicitCastExpr 0x56533889af28 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x56533889aee8 <col:7> 'int' lvalue Var 0x56533889ab68 'x' 'int'
    | | `-ImplicitCastExpr 0x56533889af40 <col:11> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x56533889af08 <col:11> 'int' lvalue Var 0x56533889ac80 'n' 'int'
    | `-CompoundStmt 0x56533889b770 <col:14, line:37:3>
    |   |-BinaryOperator 0x56533889b3f8 <line:31:3, col:29> 'int' '='
    |   | |-DeclRefExpr 0x56533889af78 <col:3> 'int' lvalue Var 0x56533889ab68 'x' 'int'
    |   | `-CallExpr 0x56533889b3d8 <col:7, col:29> 'int'
    |   |   `-ImplicitCastExpr 0x56533889b3c0 <col:7> 'int (*)(void)' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x56533889b3a0 <col:7> 'int (void)' Function 0x56533889a5e0 '__VERIFIER_nondet_int' 'int (void)'
    |   |-IfStmt 0x56533889b560 <line:32:3, col:23>
    |   | |-UnaryOperator 0x56533889b4c8 <col:7, col:14> 'int' prefix '!' cannot overflow
    |   | | `-ParenExpr 0x56533889b4a8 <col:8, col:14> 'int'
    |   | |   `-BinaryOperator 0x56533889b488 <col:9, col:13> 'int' '<'
    |   | |     |-ImplicitCastExpr 0x56533889b458 <col:9> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x56533889b418 <col:9> 'int' lvalue Var 0x56533889ab68 'x' 'int'
    |   | |     `-ImplicitCastExpr 0x56533889b470 <col:13> 'int' <LValueToRValue>
    |   | |       `-DeclRefExpr 0x56533889b438 <col:13> 'int' lvalue Var 0x56533889ac80 'n' 'int'
    |   | `-CallExpr 0x56533889b540 <col:17, col:23> 'void'
    |   |   `-ImplicitCastExpr 0x56533889b528 <col:17> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x56533889b4e0 <col:17> 'void (void) __attribute__((noreturn))' Function 0x56533889a478 'abort' 'void (void) __attribute__((noreturn))'
    |   |-IfStmt 0x56533889b658 <line:33:3, line:35:5>
    |   | |-BinaryOperator 0x56533889b5e8 <line:33:7, col:9> 'int' '<'
    |   | | |-ImplicitCastExpr 0x56533889b5b8 <col:7> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x56533889b578 <col:7> 'int' lvalue Var 0x56533889ab68 'x' 'int'
    |   | | `-ImplicitCastExpr 0x56533889b5d0 <col:9> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x56533889b598 <col:9> 'int' lvalue Var 0x56533889ac80 'n' 'int'
    |   | `-CompoundStmt 0x56533889b640 <col:12, line:35:5>
    |   |   `-UnaryOperator 0x56533889b628 <line:34:7, col:8> 'int' postfix '++'
    |   |     `-DeclRefExpr 0x56533889b608 <col:7> 'int' lvalue Var 0x56533889ab68 'x' 'int'
    |   `-IfStmt 0x56533889b758 <line:36:3, col:20>
    |     |-BinaryOperator 0x56533889b6e0 <col:7, col:11> 'int' '<'
    |     | |-ImplicitCastExpr 0x56533889b6b0 <col:7> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x56533889b670 <col:7> 'int' lvalue Var 0x56533889ab68 'x' 'int'
    |     | `-ImplicitCastExpr 0x56533889b6c8 <col:11> 'int' <LValueToRValue>
    |     |   `-DeclRefExpr 0x56533889b690 <col:11> 'int' lvalue Var 0x56533889ac80 'n' 'int'
    |     `-CallExpr 0x56533889b738 <col:14, col:20> 'void'
    |       `-ImplicitCastExpr 0x56533889b720 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x56533889b700 <col:14> 'void (void) __attribute__((noreturn))' Function 0x56533889a478 'abort' 'void (void) __attribute__((noreturn))'
    |-CallExpr 0x56533889b8b0 <line:39:3, col:25> 'void'
    | |-ImplicitCastExpr 0x56533889b898 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x56533889b7b8 <col:3> 'void (int)' Function 0x56533889a8c8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x56533889b848 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x56533889b818 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x56533889b7d8 <col:21> 'int' lvalue Var 0x56533889ab68 'x' 'int'
    |   `-ImplicitCastExpr 0x56533889b830 <col:24> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x56533889b7f8 <col:24> 'int' lvalue Var 0x56533889ac80 'n' 'int'
    `-ReturnStmt 0x56533889b8f8 <line:40:3, col:10>
      `-IntegerLiteral 0x56533889b8d8 <col:10> 'int' 0
1 warning generated.
