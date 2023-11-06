./Benchmark/PLDI/SVComp/loop-zilu/benchmark51_polynomial.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark51_polynomial.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x55de83f29f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55de83f2a7e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55de83f2a4e0 '__int128'
|-TypedefDecl 0x55de83f2a850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55de83f2a500 'unsigned __int128'
|-TypedefDecl 0x55de83f2ab58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55de83f2a930 'struct __NSConstantString_tag'
|   `-Record 0x55de83f2a8a8 '__NSConstantString_tag'
|-TypedefDecl 0x55de83f2abf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55de83f2abb0 'char *'
|   `-BuiltinType 0x55de83f29fe0 'char'
|-TypedefDecl 0x55de83f2aee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55de83f2ae90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55de83f2acd0 'struct __va_list_tag'
|     `-Record 0x55de83f2ac48 '__va_list_tag'
|-FunctionDecl 0x55de83f89c08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark51_polynomial.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x55de83f89e98 <col:24, col:35>
|   `-CallExpr 0x55de83f89e70 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x55de83f89e58 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55de83f89df0 <col:25> 'int ()' Function 0x55de83f89d40 'assert' 'int ()'
|     `-IntegerLiteral 0x55de83f89e10 <col:32> 'int' 0
|-FunctionDecl 0x55de83f89f80 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x55de83f8a0e8 <line:4:1, col:41> col:14 used __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x55de83f8a268 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55de83f8a1a0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55de83f8a410 <col:34, line:10:1>
|   `-IfStmt 0x55de83f8a3f8 <line:7:3, line:9:3>
|     |-UnaryOperator 0x55de83f8a348 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55de83f8a330 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55de83f8a310 <col:8> 'int' lvalue ParmVar 0x55de83f8a1a0 'cond' 'int'
|     `-CompoundStmt 0x55de83f8a3e0 <col:14, line:9:3>
|       `-CallExpr 0x55de83f8a3c0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x55de83f8a3a8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55de83f8a360 <col:5> 'void (void)' Function 0x55de83f89c08 'reach_error' 'void (void)'
`-FunctionDecl 0x55de83f8a450 <line:22:1, line:33:1> line:22:5 main 'int ()'
  `-CompoundStmt 0x55de83f8b3f8 <col:12, line:33:1>
    |-DeclStmt 0x55de83f8a5f0 <line:23:3, col:34>
    | `-VarDecl 0x55de83f8a508 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x55de83f8a5d0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55de83f8a5b8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55de83f8a570 <col:11> 'int (void)' Function 0x55de83f89f80 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x55de83f8a7c0 <line:25:3, col:36>
    | |-UnaryOperator 0x55de83f8a778 <col:7, col:26> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55de83f8a758 <col:8, col:26> 'int'
    | |   `-BinaryOperator 0x55de83f8a738 <col:9, col:25> 'int' '&&'
    | |     |-ParenExpr 0x55de83f8a680 <col:9, col:14> 'int'
    | |     | `-BinaryOperator 0x55de83f8a660 <col:10, col:13> 'int' '>='
    | |     |   |-ImplicitCastExpr 0x55de83f8a648 <col:10> 'int' <LValueToRValue>
    | |     |   | `-DeclRefExpr 0x55de83f8a608 <col:10> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    | |     |   `-IntegerLiteral 0x55de83f8a628 <col:13> 'int' 0
    | |     `-ParenExpr 0x55de83f8a718 <col:19, col:25> 'int'
    | |       `-BinaryOperator 0x55de83f8a6f8 <col:20, col:23> 'int' '<='
    | |         |-ImplicitCastExpr 0x55de83f8a6e0 <col:20> 'int' <LValueToRValue>
    | |         | `-DeclRefExpr 0x55de83f8a6a0 <col:20> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    | |         `-IntegerLiteral 0x55de83f8a6c0 <col:23> 'int' 50
    | `-ReturnStmt 0x55de83f8a7b0 <col:29, col:36>
    |   `-IntegerLiteral 0x55de83f8a790 <col:36> 'int' 0
    |-WhileStmt 0x55de83f8aa70 <line:26:3, line:30:3>
    | |-CallExpr 0x55de83f8a840 <line:26:10, col:33> '_Bool'
    | | `-ImplicitCastExpr 0x55de83f8a828 <col:10> '_Bool (*)(void)' <FunctionToPointerDecay>
    | |   `-DeclRefExpr 0x55de83f8a7d8 <col:10> '_Bool (void)' Function 0x55de83f8a0e8 '__VERIFIER_nondet_bool' '_Bool (void)'
    | `-CompoundStmt 0x55de83f8aa50 <col:36, line:30:3>
    |   |-IfStmt 0x55de83f8a910 <line:27:5, col:16>
    |   | |-BinaryOperator 0x55de83f8a8b8 <col:9, col:11> 'int' '>'
    |   | | |-ImplicitCastExpr 0x55de83f8a8a0 <col:9> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55de83f8a860 <col:9> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    |   | | `-IntegerLiteral 0x55de83f8a880 <col:11> 'int' 50
    |   | `-UnaryOperator 0x55de83f8a8f8 <col:15, col:16> 'int' postfix '++'
    |   |   `-DeclRefExpr 0x55de83f8a8d8 <col:15> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    |   `-IfStmt 0x55de83f8aa28 <line:28:5, line:29:13> has_else
    |     |-BinaryOperator 0x55de83f8a980 <line:28:9, col:14> 'int' '=='
    |     | |-ImplicitCastExpr 0x55de83f8a968 <col:9> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x55de83f8a928 <col:9> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    |     | `-IntegerLiteral 0x55de83f8a948 <col:14> 'int' 0
    |     |-CompoundStmt 0x55de83f8a9d8 <col:17, line:29:5>
    |     | `-UnaryOperator 0x55de83f8a9c0 <line:28:19, col:21> 'int' postfix '++'
    |     |   `-DeclRefExpr 0x55de83f8a9a0 <col:19> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    |     `-UnaryOperator 0x55de83f8aa10 <line:29:12, col:13> 'int' postfix '--'
    |       `-DeclRefExpr 0x55de83f8a9f0 <col:12> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    |-CallExpr 0x55de83f8b3a0 <line:31:3, col:38> 'void'
    | |-ImplicitCastExpr 0x55de83f8b388 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55de83f8aa88 <col:3> 'void (int)' Function 0x55de83f8a268 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55de83f8b338 <col:21, col:37> 'int' '&&'
    |   |-ParenExpr 0x55de83f8ab20 <col:21, col:26> 'int'
    |   | `-BinaryOperator 0x55de83f8ab00 <col:22, col:25> 'int' '>='
    |   |   |-ImplicitCastExpr 0x55de83f8aae8 <col:22> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55de83f8aaa8 <col:22> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    |   |   `-IntegerLiteral 0x55de83f8aac8 <col:25> 'int' 0
    |   `-ParenExpr 0x55de83f8b318 <col:31, col:37> 'int'
    |     `-BinaryOperator 0x55de83f8b2f8 <col:32, col:35> 'int' '<='
    |       |-ImplicitCastExpr 0x55de83f8b2e0 <col:32> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55de83f8b2a0 <col:32> 'int' lvalue Var 0x55de83f8a508 'x' 'int'
    |       `-IntegerLiteral 0x55de83f8b2c0 <col:35> 'int' 50
    `-ReturnStmt 0x55de83f8b3e8 <line:32:3, col:10>
      `-IntegerLiteral 0x55de83f8b3c8 <col:10> 'int' 0
1 warning generated.
