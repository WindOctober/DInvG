./Benchmark/PLDI/SVComp/loop-zilu/benchmark35_linear.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark35_linear.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x562f34608ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x562f34609780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x562f34609480 '__int128'
|-TypedefDecl 0x562f346097f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562f346094a0 'unsigned __int128'
|-TypedefDecl 0x562f34609af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x562f346098d0 'struct __NSConstantString_tag'
|   `-Record 0x562f34609848 '__NSConstantString_tag'
|-TypedefDecl 0x562f34609b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562f34609b50 'char *'
|   `-BuiltinType 0x562f34608f80 'char'
|-TypedefDecl 0x562f34609e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562f34609e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562f34609c70 'struct __va_list_tag'
|     `-Record 0x562f34609be8 '__va_list_tag'
|-FunctionDecl 0x562f34668e28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark35_linear.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x562f346690b8 <col:24, col:35>
|   `-CallExpr 0x562f34669090 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x562f34669078 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x562f34669010 <col:25> 'int ()' Function 0x562f34668f60 'assert' 'int ()'
|     `-IntegerLiteral 0x562f34669030 <col:32> 'int' 0
|-FunctionDecl 0x562f346691a0 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x562f34669308 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x562f34669488 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x562f346693c0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x562f34669630 <col:34, line:10:1>
|   `-IfStmt 0x562f34669618 <line:7:3, line:9:3>
|     |-UnaryOperator 0x562f34669568 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x562f34669550 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x562f34669530 <col:8> 'int' lvalue ParmVar 0x562f346693c0 'cond' 'int'
|     `-CompoundStmt 0x562f34669600 <col:14, line:9:3>
|       `-CallExpr 0x562f346695e0 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x562f346695c8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x562f34669580 <col:5> 'void (void)' Function 0x562f34668e28 'reach_error' 'void (void)'
`-FunctionDecl 0x562f34669670 <line:20:1, line:28:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x562f34669c88 <col:12, line:28:1>
    |-DeclStmt 0x562f34669810 <line:21:3, col:34>
    | `-VarDecl 0x562f34669728 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x562f346697f0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x562f346697d8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562f34669790 <col:11> 'int (void)' Function 0x562f346691a0 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x562f34669908 <line:22:3, col:23>
    | |-UnaryOperator 0x562f346698c0 <col:7, col:13> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x562f346698a0 <col:8, col:13> 'int'
    | |   `-BinaryOperator 0x562f34669880 <col:9, col:12> 'int' '>='
    | |     |-ImplicitCastExpr 0x562f34669868 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x562f34669828 <col:9> 'int' lvalue Var 0x562f34669728 'x' 'int'
    | |     `-IntegerLiteral 0x562f34669848 <col:12> 'int' 0
    | `-ReturnStmt 0x562f346698f8 <col:16, col:23>
    |   `-IntegerLiteral 0x562f346698d8 <col:23> 'int' 0
    |-WhileStmt 0x562f34669b40 <line:23:3, line:25:3>
    | |-BinaryOperator 0x562f34669a50 <line:23:10, col:25> 'int' '&&'
    | | |-ParenExpr 0x562f34669998 <col:10, col:15> 'int'
    | | | `-BinaryOperator 0x562f34669978 <col:11, col:14> 'int' '>='
    | | |   |-ImplicitCastExpr 0x562f34669960 <col:11> 'int' <LValueToRValue>
    | | |   | `-DeclRefExpr 0x562f34669920 <col:11> 'int' lvalue Var 0x562f34669728 'x' 'int'
    | | |   `-IntegerLiteral 0x562f34669940 <col:14> 'int' 0
    | | `-ParenExpr 0x562f34669a30 <col:20, col:25> 'int'
    | |   `-BinaryOperator 0x562f34669a10 <col:21, col:23> 'int' '<'
    | |     |-ImplicitCastExpr 0x562f346699f8 <col:21> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x562f346699b8 <col:21> 'int' lvalue Var 0x562f34669728 'x' 'int'
    | |     `-IntegerLiteral 0x562f346699d8 <col:23> 'int' 10
    | `-CompoundStmt 0x562f34669b28 <col:28, line:25:3>
    |   `-BinaryOperator 0x562f34669b08 <line:24:5, col:9> 'int' '='
    |     |-DeclRefExpr 0x562f34669a70 <col:5> 'int' lvalue Var 0x562f34669728 'x' 'int'
    |     `-BinaryOperator 0x562f34669ae8 <col:7, col:9> 'int' '+'
    |       |-ImplicitCastExpr 0x562f34669ad0 <col:7> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x562f34669a90 <col:7> 'int' lvalue Var 0x562f34669728 'x' 'int'
    |       `-IntegerLiteral 0x562f34669ab0 <col:9> 'int' 1
    |-CallExpr 0x562f34669c30 <line:26:3, col:26> 'void'
    | |-ImplicitCastExpr 0x562f34669c18 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x562f34669b58 <col:3> 'void (int)' Function 0x562f34669488 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x562f34669bd0 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x562f34669bb8 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x562f34669b78 <col:21> 'int' lvalue Var 0x562f34669728 'x' 'int'
    |   `-IntegerLiteral 0x562f34669b98 <col:24> 'int' 10
    `-ReturnStmt 0x562f34669c78 <line:27:3, col:10>
      `-IntegerLiteral 0x562f34669c58 <col:10> 'int' 0
1 warning generated.
