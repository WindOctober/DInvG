./Benchmark/PLDI/SVComp/loop-zilu/benchmark34_conjunctive.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark34_conjunctive.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55eba0bf8f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55eba0bf97e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55eba0bf94e0 '__int128'
|-TypedefDecl 0x55eba0bf9850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55eba0bf9500 'unsigned __int128'
|-TypedefDecl 0x55eba0bf9b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55eba0bf9930 'struct __NSConstantString_tag'
|   `-Record 0x55eba0bf98a8 '__NSConstantString_tag'
|-TypedefDecl 0x55eba0bf9bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55eba0bf9bb0 'char *'
|   `-BuiltinType 0x55eba0bf8fe0 'char'
|-TypedefDecl 0x55eba0bf9ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55eba0bf9e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55eba0bf9cd0 'struct __va_list_tag'
|     `-Record 0x55eba0bf9c48 '__va_list_tag'
|-FunctionDecl 0x55eba0c58ef8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark34_conjunctive.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55eba0c59188 <col:24, col:35>
|   `-CallExpr 0x55eba0c59160 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55eba0c59148 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55eba0c590e0 <col:25> 'int ()' Function 0x55eba0c59030 'assert' 'int ()'
|     `-IntegerLiteral 0x55eba0c59100 <col:32> 'int' 0
|-FunctionDecl 0x55eba0c59270 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55eba0c593d8 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55eba0c59558 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55eba0c59490 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55eba0c59700 <col:34, line:10:1>
|   `-IfStmt 0x55eba0c596e8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55eba0c59638 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55eba0c59620 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55eba0c59600 <col:8> 'int' lvalue ParmVar 0x55eba0c59490 'cond' 'int'
|     `-CompoundStmt 0x55eba0c596d0 <col:14, line:9:3>
|       `-CallExpr 0x55eba0c596b0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55eba0c59698 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55eba0c59650 <col:5> 'void (void)' Function 0x55eba0c58ef8 'reach_error' 'void (void)'
`-FunctionDecl 0x55eba0c59740 <line:20:1, line:30:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x55eba0c5a4a8 <col:12, line:30:1>
    |-DeclStmt 0x55eba0c598e0 <line:21:3, col:34>
    | `-VarDecl 0x55eba0c597f8 <col:3, col:33> col:7 used j 'int' cinit
    |   `-CallExpr 0x55eba0c598c0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55eba0c598a8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55eba0c59860 <col:11> 'int (void)' Function 0x55eba0c59270 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55eba0c599d0 <line:22:3, col:34>
    | `-VarDecl 0x55eba0c59910 <col:3, col:33> col:7 used k 'int' cinit
    |   `-CallExpr 0x55eba0c599b0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55eba0c59998 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55eba0c59978 <col:11> 'int (void)' Function 0x55eba0c59270 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x55eba0c59ac0 <line:23:3, col:34>
    | `-VarDecl 0x55eba0c59a00 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x55eba0c59aa0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55eba0c59a88 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55eba0c59a68 <col:11> 'int (void)' Function 0x55eba0c59270 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55eba0c59d60 <line:24:3, col:44>
    | |-UnaryOperator 0x55eba0c59d18 <col:7, col:34> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55eba0c59cf8 <col:8, col:34> 'int'
    | |   `-BinaryOperator 0x55eba0c59cd8 <col:9, col:33> 'int' '&&'
    | |     |-BinaryOperator 0x55eba0c59c20 <col:9, col:24> 'int' '&&'
    | |     | |-ParenExpr 0x55eba0c59b50 <col:9, col:14> 'int'
    | |     | | `-BinaryOperator 0x55eba0c59b30 <col:10, col:13> 'int' '=='
    | |     | |   |-ImplicitCastExpr 0x55eba0c59b18 <col:10> 'int' <LValueToRValue>
    | |     | |   | `-DeclRefExpr 0x55eba0c59ad8 <col:10> 'int' lvalue Var 0x55eba0c597f8 'j' 'int'
    | |     | |   `-IntegerLiteral 0x55eba0c59af8 <col:13> 'int' 0
    | |     | `-ParenExpr 0x55eba0c59c00 <col:19, col:24> 'int'
    | |     |   `-BinaryOperator 0x55eba0c59be0 <col:20, col:23> 'int' '=='
    | |     |     |-ImplicitCastExpr 0x55eba0c59bb0 <col:20> 'int' <LValueToRValue>
    | |     |     | `-DeclRefExpr 0x55eba0c59b70 <col:20> 'int' lvalue Var 0x55eba0c59910 'k' 'int'
    | |     |     `-ImplicitCastExpr 0x55eba0c59bc8 <col:23> 'int' <LValueToRValue>
    | |     |       `-DeclRefExpr 0x55eba0c59b90 <col:23> 'int' lvalue Var 0x55eba0c59a00 'n' 'int'
    | |     `-ParenExpr 0x55eba0c59cb8 <col:29, col:33> 'int'
    | |       `-BinaryOperator 0x55eba0c59c98 <col:30, col:32> 'int' '>'
    | |         |-ImplicitCastExpr 0x55eba0c59c80 <col:30> 'int' <LValueToRValue>
    | |         | `-DeclRefExpr 0x55eba0c59c40 <col:30> 'int' lvalue Var 0x55eba0c59a00 'n' 'int'
    | |         `-IntegerLiteral 0x55eba0c59c60 <col:32> 'int' 0
    | `-ReturnStmt 0x55eba0c59d50 <col:37, col:44>
    |   `-IntegerLiteral 0x55eba0c59d30 <col:44> 'int' 0
    |-WhileStmt 0x55eba0c5a338 <line:25:3, line:27:3>
    | |-BinaryOperator 0x55eba0c5a288 <line:25:10, col:19> 'int' '&&'
    | | |-BinaryOperator 0x55eba0c59de8 <col:10, col:12> 'int' '<'
    | | | |-ImplicitCastExpr 0x55eba0c59db8 <col:10> 'int' <LValueToRValue>
    | | | | `-DeclRefExpr 0x55eba0c59d78 <col:10> 'int' lvalue Var 0x55eba0c597f8 'j' 'int'
    | | | `-ImplicitCastExpr 0x55eba0c59dd0 <col:12> 'int' <LValueToRValue>
    | | |   `-DeclRefExpr 0x55eba0c59d98 <col:12> 'int' lvalue Var 0x55eba0c59a00 'n' 'int'
    | | `-BinaryOperator 0x55eba0c5a268 <col:17, col:19> 'int' '>'
    | |   |-ImplicitCastExpr 0x55eba0c5a250 <col:17> 'int' <LValueToRValue>
    | |   | `-DeclRefExpr 0x55eba0c59e08 <col:17> 'int' lvalue Var 0x55eba0c59a00 'n' 'int'
    | |   `-IntegerLiteral 0x55eba0c5a230 <col:19> 'int' 0
    | `-CompoundStmt 0x55eba0c5a318 <col:22, line:27:3>
    |   |-UnaryOperator 0x55eba0c5a2c8 <line:26:5, col:6> 'int' postfix '++'
    |   | `-DeclRefExpr 0x55eba0c5a2a8 <col:5> 'int' lvalue Var 0x55eba0c597f8 'j' 'int'
    |   `-UnaryOperator 0x55eba0c5a300 <col:9, col:10> 'int' postfix '--'
    |     `-DeclRefExpr 0x55eba0c5a2e0 <col:9> 'int' lvalue Var 0x55eba0c59910 'k' 'int'
    |-CallExpr 0x55eba0c5a450 <line:28:3, col:29> 'void'
    | |-ImplicitCastExpr 0x55eba0c5a438 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55eba0c5a350 <col:3> 'void (int)' Function 0x55eba0c59558 '__VERIFIER_assert' 'void (int)'
    | `-ParenExpr 0x55eba0c5a3e8 <col:21, col:28> 'int'
    |   `-BinaryOperator 0x55eba0c5a3c8 <col:22, col:27> 'int' '=='
    |     |-ImplicitCastExpr 0x55eba0c5a3b0 <col:22> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x55eba0c5a370 <col:22> 'int' lvalue Var 0x55eba0c59910 'k' 'int'
    |     `-IntegerLiteral 0x55eba0c5a390 <col:27> 'int' 0
    `-ReturnStmt 0x55eba0c5a498 <line:29:3, col:10>
      `-IntegerLiteral 0x55eba0c5a478 <col:10> 'int' 0
1 warning generated.
