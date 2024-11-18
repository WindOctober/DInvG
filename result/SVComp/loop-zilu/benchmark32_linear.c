./Benchmark/PLDI/SVComp/loop-zilu/benchmark32_linear.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark32_linear.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x5603770a2ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5603770a3780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5603770a3480 '__int128'
|-TypedefDecl 0x5603770a37f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5603770a34a0 'unsigned __int128'
|-TypedefDecl 0x5603770a3af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5603770a38d0 'struct __NSConstantString_tag'
|   `-Record 0x5603770a3848 '__NSConstantString_tag'
|-TypedefDecl 0x5603770a3b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5603770a3b50 'char *'
|   `-BuiltinType 0x5603770a2f80 'char'
|-TypedefDecl 0x5603770a3e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5603770a3e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5603770a3c70 'struct __va_list_tag'
|     `-Record 0x5603770a3be8 '__va_list_tag'
|-FunctionDecl 0x560377102e88 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark32_linear.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x560377103118 <col:24, col:35>
|   `-CallExpr 0x5603771030f0 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x5603771030d8 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x560377103070 <col:25> 'int ()' Function 0x560377102fc0 'assert' 'int ()'
|     `-IntegerLiteral 0x560377103090 <col:32> 'int' 0
|-FunctionDecl 0x560377103200 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x560377103368 <line:4:1, col:41> col:14 used __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x5603771034e8 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x560377103420 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x560377103690 <col:34, line:10:1>
|   `-IfStmt 0x560377103678 <line:7:3, line:9:3>
|     |-UnaryOperator 0x5603771035c8 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5603771035b0 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x560377103590 <col:8> 'int' lvalue ParmVar 0x560377103420 'cond' 'int'
|     `-CompoundStmt 0x560377103660 <col:14, line:9:3>
|       `-CallExpr 0x560377103640 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x560377103628 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5603771035e0 <col:5> 'void (void)' Function 0x560377102e88 'reach_error' 'void (void)'
`-FunctionDecl 0x5603771036d0 <line:23:1, line:33:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x5603771048d8 <col:12, line:33:1>
    |-DeclStmt 0x560377103870 <line:24:3, col:34>
    | `-VarDecl 0x560377103788 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x560377103850 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x560377103838 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5603771037f0 <col:11> 'int (void)' Function 0x560377103200 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x560377103a00 <line:26:3, col:31>
    | |-UnaryOperator 0x5603771039b8 <col:7, col:21> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x560377103998 <col:8, col:21> 'int'
    | |   `-BinaryOperator 0x560377103978 <col:9, col:20> 'int' '||'
    | |     |-BinaryOperator 0x5603771038e0 <col:9, col:12> 'int' '=='
    | |     | |-ImplicitCastExpr 0x5603771038c8 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x560377103888 <col:9> 'int' lvalue Var 0x560377103788 'x' 'int'
    | |     | `-IntegerLiteral 0x5603771038a8 <col:12> 'int' 1
    | |     `-BinaryOperator 0x560377103958 <col:17, col:20> 'int' '=='
    | |       |-ImplicitCastExpr 0x560377103940 <col:17> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x560377103900 <col:17> 'int' lvalue Var 0x560377103788 'x' 'int'
    | |       `-IntegerLiteral 0x560377103920 <col:20> 'int' 2
    | `-ReturnStmt 0x5603771039f0 <col:24, col:31>
    |   `-IntegerLiteral 0x5603771039d0 <col:31> 'int' 0
    |-WhileStmt 0x560377103ca8 <line:27:3, line:30:3>
    | |-CallExpr 0x560377103a80 <line:27:10, col:33> '_Bool'
    | | `-ImplicitCastExpr 0x560377103a68 <col:10> '_Bool (*)(void)' <FunctionToPointerDecay>
    | |   `-DeclRefExpr 0x560377103a18 <col:10> '_Bool (void)' Function 0x560377103368 '__VERIFIER_nondet_bool' '_Bool (void)'
    | `-CompoundStmt 0x560377103c90 <col:36, line:30:3>
    |   `-IfStmt 0x560377103c68 <line:28:5, line:29:22> has_else
    |     |-BinaryOperator 0x560377103af8 <line:28:8, col:11> 'int' '=='
    |     | |-ImplicitCastExpr 0x560377103ae0 <col:8> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x560377103aa0 <col:8> 'int' lvalue Var 0x560377103788 'x' 'int'
    |     | `-IntegerLiteral 0x560377103ac0 <col:11> 'int' 1
    |     |-BinaryOperator 0x560377103b58 <col:14, col:16> 'int' '='
    |     | |-DeclRefExpr 0x560377103b18 <col:14> 'int' lvalue Var 0x560377103788 'x' 'int'
    |     | `-IntegerLiteral 0x560377103b38 <col:16> 'int' 2
    |     `-IfStmt 0x560377103c50 <line:29:10, col:22>
    |       |-BinaryOperator 0x560377103bd0 <col:14, col:17> 'int' '=='
    |       | |-ImplicitCastExpr 0x560377103bb8 <col:14> 'int' <LValueToRValue>
    |       | | `-DeclRefExpr 0x560377103b78 <col:14> 'int' lvalue Var 0x560377103788 'x' 'int'
    |       | `-IntegerLiteral 0x560377103b98 <col:17> 'int' 2
    |       `-BinaryOperator 0x560377103c30 <col:20, col:22> 'int' '='
    |         |-DeclRefExpr 0x560377103bf0 <col:20> 'int' lvalue Var 0x560377103788 'x' 'int'
    |         `-IntegerLiteral 0x560377103c10 <col:22> 'int' 1
    |-CallExpr 0x560377104880 <line:31:3, col:25> 'void'
    | |-ImplicitCastExpr 0x560377103d88 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x560377103cc0 <col:3> 'void (int)' Function 0x5603771034e8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x560377103d38 <col:21, col:24> 'int' '<='
    |   |-ImplicitCastExpr 0x560377103d20 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x560377103ce0 <col:21> 'int' lvalue Var 0x560377103788 'x' 'int'
    |   `-IntegerLiteral 0x560377103d00 <col:24> 'int' 8
    `-ReturnStmt 0x5603771048c8 <line:32:3, col:10>
      `-IntegerLiteral 0x5603771048a8 <col:10> 'int' 0
1 warning generated.
