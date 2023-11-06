./Benchmark/PLDI/SVComp/loops/terminator_03-2_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/terminator_03-2_abstracted.c:2:22: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error() { assert(0); }
                     ^
TranslationUnitDecl 0x55a2a8ac9f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55a2a8aca7e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55a2a8aca4e0 '__int128'
|-TypedefDecl 0x55a2a8aca850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55a2a8aca500 'unsigned __int128'
|-TypedefDecl 0x55a2a8acab58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55a2a8aca930 'struct __NSConstantString_tag'
|   `-Record 0x55a2a8aca8a8 '__NSConstantString_tag'
|-TypedefDecl 0x55a2a8acabf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55a2a8acabb0 'char *'
|   `-BuiltinType 0x55a2a8ac9fe0 'char'
|-TypedefDecl 0x55a2a8acaee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55a2a8acae90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55a2a8acacd0 'struct __va_list_tag'
|     `-Record 0x55a2a8acac48 '__va_list_tag'
|-FunctionDecl 0x55a2a8b29c28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/terminator_03-2_abstracted.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a2a8b29cc8 prev 0x55a2a8b29c28 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a2a8b29db8 <line:2:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55a2a8b2a048 <col:20, col:33>
|   `-CallExpr 0x55a2a8b2a020 <col:22, col:30> 'int'
|     |-ImplicitCastExpr 0x55a2a8b2a008 <col:22> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55a2a8b29fa0 <col:22> 'int ()' Function 0x55a2a8b29ef0 'assert' 'int ()'
|     `-IntegerLiteral 0x55a2a8b29fc0 <col:29> 'int' 0
|-FunctionDecl 0x55a2a8b2a0f8 prev 0x55a2a8b29cc8 <line:3:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55a2a8b2a278 <line:4:1, line:6:1> line:4:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55a2a8b2a1b0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55a2a8b2a420 <col:36, line:6:1>
|   `-IfStmt 0x55a2a8b2a408 <line:5:3, col:22>
|     |-UnaryOperator 0x55a2a8b2a358 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55a2a8b2a340 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55a2a8b2a320 <col:7> 'int' lvalue ParmVar 0x55a2a8b2a1b0 'cond' 'int'
|     `-CompoundStmt 0x55a2a8b2a3f0 <col:13, col:22>
|       `-CallExpr 0x55a2a8b2a3d0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55a2a8b2a3b8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55a2a8b2a370 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55a2a8b2a0f8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55a2a8b2a4e0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55a2a8b2a450 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55a2a8b2a7a0 <col:34, line:13:1>
|   |-IfStmt 0x55a2a8b2a778 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x55a2a8b2a5e0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55a2a8b2a5c8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55a2a8b2a5a8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55a2a8b2a588 <col:9> 'int' lvalue ParmVar 0x55a2a8b2a450 'cond' 'int'
|   | `-CompoundStmt 0x55a2a8b2a760 <col:16, line:11:3>
|   |   `-LabelStmt 0x55a2a8b2a748 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55a2a8b2a6d8 <col:12, col:35>
|   |       |-CallExpr 0x55a2a8b2a660 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55a2a8b2a648 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55a2a8b2a5f8 <col:13> 'void ()' Function 0x55a2a8b29db8 'reach_error' 'void ()'
|   |       `-CallExpr 0x55a2a8b2a6b8 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55a2a8b2a6a0 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55a2a8b2a680 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55a2a8b2a0f8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55a2a8b2a790 <line:12:3>
|-FunctionDecl 0x55a2a8b2a7e8 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x55a2a8b2a8d8 <line:15:1, col:30> col:7 __VERIFIER_nondet_bool '_Bool ()'
`-FunctionDecl 0x55a2a8b2a9a0 <line:19:1, line:36:1> line:19:5 main 'int ()'
  `-CompoundStmt 0x55a2a8b2b868 <col:12, line:36:1>
    |-DeclStmt 0x55a2a8b2ab18 <line:20:5, col:34>
    | `-VarDecl 0x55a2a8b2aa58 <col:5, col:33> col:9 used x 'int' cinit
    |   `-CallExpr 0x55a2a8b2aaf8 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55a2a8b2aae0 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55a2a8b2aac0 <col:11> 'int ()' Function 0x55a2a8b2a7e8 '__VERIFIER_nondet_int' 'int ()'
    |-DeclStmt 0x55a2a8b2b1b8 <line:21:5, col:34>
    | `-VarDecl 0x55a2a8b2b0f8 <col:5, col:33> col:9 used y 'int' cinit
    |   `-CallExpr 0x55a2a8b2b198 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55a2a8b2b180 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55a2a8b2b160 <col:11> 'int ()' Function 0x55a2a8b2a7e8 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x55a2a8b2b2b0 <line:22:5, col:31>
    | |-UnaryOperator 0x55a2a8b2b268 <col:9, col:21> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55a2a8b2b248 <col:10, col:21> 'int'
    | |   `-BinaryOperator 0x55a2a8b2b228 <col:11, line:17:15> 'int' '<='
    | |     |-ImplicitCastExpr 0x55a2a8b2b210 <line:22:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x55a2a8b2b1d0 <col:11> 'int' lvalue Var 0x55a2a8b2b0f8 'y' 'int'
    | |     `-IntegerLiteral 0x55a2a8b2b1f0 <line:17:15> 'int' 1000000
    | `-ReturnStmt 0x55a2a8b2b2a0 <line:22:24, col:31>
    |   `-IntegerLiteral 0x55a2a8b2b280 <col:31> 'int' 0
    |-IfStmt 0x55a2a8b2b5c8 <line:24:5, line:31:5>
    | |-BinaryOperator 0x55a2a8b2b320 <line:24:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55a2a8b2b308 <col:9> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55a2a8b2b2c8 <col:9> 'int' lvalue Var 0x55a2a8b2b0f8 'y' 'int'
    | | `-IntegerLiteral 0x55a2a8b2b2e8 <col:11> 'int' 0
    | `-CompoundStmt 0x55a2a8b2b5a8 <col:14, line:31:5>
    |   |-IfStmt 0x55a2a8b2b488 <line:26:9, line:28:9>
    |   | |-BinaryOperator 0x55a2a8b2b3b8 <line:26:13, col:21> 'int' '<'
    |   | | |-ImplicitCastExpr 0x55a2a8b2b3a0 <col:13> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55a2a8b2b340 <col:13> 'int' lvalue Var 0x55a2a8b2aa58 'x' 'int'
    |   | | `-ParenExpr 0x55a2a8b2b380 <col:17, col:21> 'int'
    |   | |   `-IntegerLiteral 0x55a2a8b2b360 <col:18> 'int' 100
    |   | `-CompoundStmt 0x55a2a8b2b470 <col:24, line:28:9>
    |   |   `-BinaryOperator 0x55a2a8b2b450 <line:27:9, col:35> 'int' '='
    |   |     |-DeclRefExpr 0x55a2a8b2b3d8 <col:9> 'int' lvalue Var 0x55a2a8b2aa58 'x' 'int'
    |   |     `-CallExpr 0x55a2a8b2b430 <col:13, col:35> 'int'
    |   |       `-ImplicitCastExpr 0x55a2a8b2b418 <col:13> 'int (*)()' <FunctionToPointerDecay>
    |   |         `-DeclRefExpr 0x55a2a8b2b3f8 <col:13> 'int ()' Function 0x55a2a8b2a7e8 '__VERIFIER_nondet_int' 'int ()'
    |   `-IfStmt 0x55a2a8b2b590 <line:29:9, col:30>
    |     |-BinaryOperator 0x55a2a8b2b518 <col:13, col:21> 'int' '<'
    |     | |-ImplicitCastExpr 0x55a2a8b2b500 <col:13> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55a2a8b2b4a0 <col:13> 'int' lvalue Var 0x55a2a8b2aa58 'x' 'int'
    |     | `-ParenExpr 0x55a2a8b2b4e0 <col:17, col:21> 'int'
    |     |   `-IntegerLiteral 0x55a2a8b2b4c0 <col:18> 'int' 100
    |     `-CallExpr 0x55a2a8b2b570 <col:24, col:30> 'void'
    |       `-ImplicitCastExpr 0x55a2a8b2b558 <col:24> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x55a2a8b2b538 <col:24> 'void (void) __attribute__((noreturn))' Function 0x55a2a8b2a0f8 'abort' 'void (void) __attribute__((noreturn))'
    |-CallExpr 0x55a2a8b2b810 <line:33:5, col:46> 'void'
    | |-ImplicitCastExpr 0x55a2a8b2b7f8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55a2a8b2b5e0 <col:5> 'void (int)' Function 0x55a2a8b2a4e0 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55a2a8b2b7a8 <col:23, col:45> 'int' '||'
    |   |-BinaryOperator 0x55a2a8b2b658 <col:23, col:26> 'int' '<='
    |   | |-ImplicitCastExpr 0x55a2a8b2b640 <col:23> 'int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x55a2a8b2b600 <col:23> 'int' lvalue Var 0x55a2a8b2b0f8 'y' 'int'
    |   | `-IntegerLiteral 0x55a2a8b2b620 <col:26> 'int' 0
    |   `-ParenExpr 0x55a2a8b2b788 <col:31, col:45> 'int'
    |     `-BinaryOperator 0x55a2a8b2b768 <col:32, col:42> 'int' '&&'
    |       |-BinaryOperator 0x55a2a8b2b6d0 <col:32, col:34> 'int' '>'
    |       | |-ImplicitCastExpr 0x55a2a8b2b6b8 <col:32> 'int' <LValueToRValue>
    |       | | `-DeclRefExpr 0x55a2a8b2b678 <col:32> 'int' lvalue Var 0x55a2a8b2b0f8 'y' 'int'
    |       | `-IntegerLiteral 0x55a2a8b2b698 <col:34> 'int' 0
    |       `-BinaryOperator 0x55a2a8b2b748 <col:39, col:42> 'int' '>='
    |         |-ImplicitCastExpr 0x55a2a8b2b730 <col:39> 'int' <LValueToRValue>
    |         | `-DeclRefExpr 0x55a2a8b2b6f0 <col:39> 'int' lvalue Var 0x55a2a8b2aa58 'x' 'int'
    |         `-IntegerLiteral 0x55a2a8b2b710 <col:42> 'int' 100
    `-ReturnStmt 0x55a2a8b2b858 <line:35:5, col:12>
      `-IntegerLiteral 0x55a2a8b2b838 <col:12> 'int' 0
1 warning generated.
