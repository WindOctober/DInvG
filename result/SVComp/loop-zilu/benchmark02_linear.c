./Benchmark/PLDI/SVComp/loop-zilu/benchmark02_linear.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark02_linear.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x560cecd38ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x560cecd39780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x560cecd39480 '__int128'
|-TypedefDecl 0x560cecd397f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x560cecd394a0 'unsigned __int128'
|-TypedefDecl 0x560cecd39af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x560cecd398d0 'struct __NSConstantString_tag'
|   `-Record 0x560cecd39848 '__NSConstantString_tag'
|-TypedefDecl 0x560cecd39b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x560cecd39b50 'char *'
|   `-BuiltinType 0x560cecd38f80 'char'
|-TypedefDecl 0x560cecd39e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x560cecd39e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x560cecd39c70 'struct __va_list_tag'
|     `-Record 0x560cecd39be8 '__va_list_tag'
|-FunctionDecl 0x560cecd98e98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark02_linear.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x560cecd99128 <col:24, col:35>
|   `-CallExpr 0x560cecd99100 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x560cecd990e8 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x560cecd99080 <col:25> 'int ()' Function 0x560cecd98fd0 'assert' 'int ()'
|     `-IntegerLiteral 0x560cecd990a0 <col:32> 'int' 0
|-FunctionDecl 0x560cecd99210 <line:3:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x560cecd99378 <line:4:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x560cecd994f8 <line:6:1, line:10:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x560cecd99430 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x560cecd996a0 <col:34, line:10:1>
|   `-IfStmt 0x560cecd99688 <line:7:3, line:9:3>
|     |-UnaryOperator 0x560cecd995d8 <line:7:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x560cecd995c0 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x560cecd995a0 <col:8> 'int' lvalue ParmVar 0x560cecd99430 'cond' 'int'
|     `-CompoundStmt 0x560cecd99670 <col:14, line:9:3>
|       `-CallExpr 0x560cecd99650 <line:8:5, col:17> 'void'
|         `-ImplicitCastExpr 0x560cecd99638 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x560cecd995f0 <col:5> 'void (void)' Function 0x560cecd98e98 'reach_error' 'void (void)'
`-FunctionDecl 0x560cecd996e0 <line:23:1, line:34:1> line:23:5 main 'int ()'
  `-CompoundStmt 0x560cecd9a228 <col:12, line:34:1>
    |-DeclStmt 0x560cecd99880 <line:24:3, col:34>
    | `-VarDecl 0x560cecd99798 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x560cecd99860 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x560cecd99848 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x560cecd99800 <col:11> 'int (void)' Function 0x560cecd99210 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x560cecd99970 <line:25:3, col:34>
    | `-VarDecl 0x560cecd998b0 <col:3, col:33> col:7 used i 'int' cinit
    |   `-CallExpr 0x560cecd99950 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x560cecd99938 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x560cecd99918 <col:11> 'int (void)' Function 0x560cecd99210 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x560cecd99a60 <line:26:3, col:34>
    | `-VarDecl 0x560cecd999a0 <col:3, col:33> col:7 used l 'int' cinit
    |   `-CallExpr 0x560cecd99a40 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x560cecd99a28 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x560cecd99a08 <col:11> 'int (void)' Function 0x560cecd99210 '__VERIFIER_nondet_int' 'int (void)'
    |-BinaryOperator 0x560cecd99ad0 <line:27:3, col:7> 'int' '='
    | |-DeclRefExpr 0x560cecd99a78 <col:3> 'int' lvalue Var 0x560cecd998b0 'i' 'int'
    | `-ImplicitCastExpr 0x560cecd99ab8 <col:7> 'int' <LValueToRValue>
    |   `-DeclRefExpr 0x560cecd99a98 <col:7> 'int' lvalue Var 0x560cecd999a0 'l' 'int'
    |-IfStmt 0x560cecd99bd0 <line:28:3, col:22>
    | |-UnaryOperator 0x560cecd99b88 <col:7, col:12> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x560cecd99b68 <col:8, col:12> 'int'
    | |   `-BinaryOperator 0x560cecd99b48 <col:9, col:11> 'int' '>'
    | |     |-ImplicitCastExpr 0x560cecd99b30 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x560cecd99af0 <col:9> 'int' lvalue Var 0x560cecd999a0 'l' 'int'
    | |     `-IntegerLiteral 0x560cecd99b10 <col:11> 'int' 0
    | `-ReturnStmt 0x560cecd99bc0 <col:15, col:22>
    |   `-IntegerLiteral 0x560cecd99ba0 <col:22> 'int' 0
    |-WhileStmt 0x560cecd99cc8 <line:29:3, line:31:3>
    | |-BinaryOperator 0x560cecd99c58 <line:29:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x560cecd99c28 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x560cecd99be8 <col:10> 'int' lvalue Var 0x560cecd998b0 'i' 'int'
    | | `-ImplicitCastExpr 0x560cecd99c40 <col:14> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x560cecd99c08 <col:14> 'int' lvalue Var 0x560cecd99798 'n' 'int'
    | `-CompoundStmt 0x560cecd99cb0 <col:17, line:31:3>
    |   `-UnaryOperator 0x560cecd99c98 <line:30:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x560cecd99c78 <col:5> 'int' lvalue Var 0x560cecd998b0 'i' 'int'
    |-CallExpr 0x560cecd9a1d0 <line:32:3, col:25> 'void'
    | |-ImplicitCastExpr 0x560cecd99da8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x560cecd99ce0 <col:3> 'void (int)' Function 0x560cecd994f8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x560cecd99d58 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x560cecd99d40 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x560cecd99d00 <col:21> 'int' lvalue Var 0x560cecd999a0 'l' 'int'
    |   `-IntegerLiteral 0x560cecd99d20 <col:24> 'int' 1
    `-ReturnStmt 0x560cecd9a218 <line:33:3, col:10>
      `-IntegerLiteral 0x560cecd9a1f8 <col:10> 'int' 0
1 warning generated.
