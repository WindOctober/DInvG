./Benchmark/PLDI/SVComp/loops-crafted-1/loopv3.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/loopv3.c:6:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x56238271be98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x56238271c730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x56238271c430 '__int128'
|-TypedefDecl 0x56238271c7a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x56238271c450 'unsigned __int128'
|-TypedefDecl 0x56238271caa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x56238271c880 'struct __NSConstantString_tag'
|   `-Record 0x56238271c7f8 '__NSConstantString_tag'
|-TypedefDecl 0x56238271cb40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x56238271cb00 'char *'
|   `-BuiltinType 0x56238271bf30 'char'
|-TypedefDecl 0x56238271ce38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x56238271cde0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x56238271cc20 'struct __va_list_tag'
|     `-Record 0x56238271cb98 '__va_list_tag'
|-VarDecl 0x56238277be08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/loopv3.c:1:1, col:12> col:5 used SIZE 'int' cinit
| `-IntegerLiteral 0x56238277beb8 <col:12> 'int' 50000001
|-FunctionDecl 0x56238277bf30 <line:4:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x56238277c0c8 <line:5:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56238277c168 prev 0x56238277c0c8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56238277c4e8 <line:6:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x56238277c220 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x56238277c2a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x56238277c320 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x56238277c3a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x56238277c5a8 <col:99>
|-FunctionDecl 0x56238277c648 <line:7:1, col:72> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x56238277c978 <col:20, col:72>
|   `-CallExpr 0x56238277c890 <col:22, col:69> 'void'
|     |-ImplicitCastExpr 0x56238277c878 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x56238277c6e8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x56238277c4e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x56238277c8e8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56238277c8d0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56238277c748 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x56238277c918 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56238277c900 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56238277c7a8 <col:41> 'char [9]' lvalue "loopv3.c"
|     |-ImplicitCastExpr 0x56238277c930 <col:53> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x56238277c7c8 <col:53> 'int' 7
|     `-ImplicitCastExpr 0x56238277c960 <col:56> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x56238277c948 <col:56> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x56238277c828 <col:56> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x56238277ca28 prev 0x56238277c168 <line:8:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56238277cba8 <line:9:1, line:11:1> line:9:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x56238277cae0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x56238277cd50 <col:36, line:11:1>
|   `-IfStmt 0x56238277cd38 <line:10:3, col:22>
|     |-UnaryOperator 0x56238277cc88 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x56238277cc70 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x56238277cc50 <col:7> 'int' lvalue ParmVar 0x56238277cae0 'cond' 'int'
|     `-CompoundStmt 0x56238277cd20 <col:13, col:22>
|       `-CallExpr 0x56238277cd00 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x56238277cce8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x56238277cca0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x56238277ca28 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x56238277e668 <line:12:1, line:17:1> line:12:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x56238277cd80 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x56238277e920 <col:34, line:17:1>
|   |-IfStmt 0x56238277e8f8 <line:13:3, line:15:3>
|   | |-UnaryOperator 0x56238277e768 <line:13:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x56238277e750 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x56238277e730 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x56238277e710 <col:9> 'int' lvalue ParmVar 0x56238277cd80 'cond' 'int'
|   | `-CompoundStmt 0x56238277e8e0 <col:16, line:15:3>
|   |   `-LabelStmt 0x56238277e8c8 <line:14:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x56238277e858 <col:12, col:35>
|   |       |-CallExpr 0x56238277e7e0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x56238277e7c8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x56238277e780 <col:13> 'void ()' Function 0x56238277c648 'reach_error' 'void ()'
|   |       `-CallExpr 0x56238277e838 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x56238277e820 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x56238277e800 <col:27> 'void (void) __attribute__((noreturn))' Function 0x56238277ca28 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x56238277e910 <line:16:3>
`-FunctionDecl 0x56238277e968 <line:20:1, line:34:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x56238277f138 <col:12, line:34:1>
    |-DeclStmt 0x56238277eb20 <line:21:3, col:10>
    | |-VarDecl 0x56238277ea20 <col:3, col:7> col:7 used i 'int'
    | `-VarDecl 0x56238277eaa0 <col:3, col:9> col:9 used j 'int'
    |-BinaryOperator 0x56238277eb78 <line:22:3, col:7> 'int' '='
    | |-DeclRefExpr 0x56238277eb38 <col:3> 'int' lvalue Var 0x56238277ea20 'i' 'int'
    | `-IntegerLiteral 0x56238277eb58 <col:7> 'int' 0
    |-BinaryOperator 0x56238277ebd8 <col:10, col:12> 'int' '='
    | |-DeclRefExpr 0x56238277eb98 <col:10> 'int' lvalue Var 0x56238277eaa0 'j' 'int'
    | `-IntegerLiteral 0x56238277ebb8 <col:12> 'int' 0
    |-WhileStmt 0x56238277eec0 <line:23:3, line:30:3>
    | |-BinaryOperator 0x56238277ec68 <line:23:9, col:11> 'int' '<'
    | | |-ImplicitCastExpr 0x56238277ec38 <col:9> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x56238277ebf8 <col:9> 'int' lvalue Var 0x56238277ea20 'i' 'int'
    | | `-ImplicitCastExpr 0x56238277ec50 <col:11> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x56238277ec18 <col:11> 'int' lvalue Var 0x56238277be08 'SIZE' 'int'
    | `-CompoundStmt 0x56238277eea8 <col:16, line:30:3>
    |   `-IfStmt 0x56238277ee80 <line:25:5, line:28:14> has_else
    |     |-CallExpr 0x56238277ecf0 <line:25:8, col:30> 'int'
    |     | `-ImplicitCastExpr 0x56238277ecd8 <col:8> 'int (*)()' <FunctionToPointerDecay>
    |     |   `-DeclRefExpr 0x56238277ec88 <col:8> 'int ()' Function 0x56238277bf30 '__VERIFIER_nondet_int' 'int ()'
    |     |-BinaryOperator 0x56238277eda8 <line:26:7, col:15> 'int' '='
    |     | |-DeclRefExpr 0x56238277ed10 <col:7> 'int' lvalue Var 0x56238277ea20 'i' 'int'
    |     | `-BinaryOperator 0x56238277ed88 <col:11, col:15> 'int' '+'
    |     |   |-ImplicitCastExpr 0x56238277ed70 <col:11> 'int' <LValueToRValue>
    |     |   | `-DeclRefExpr 0x56238277ed30 <col:11> 'int' lvalue Var 0x56238277ea20 'i' 'int'
    |     |   `-IntegerLiteral 0x56238277ed50 <col:15> 'int' 8
    |     `-BinaryOperator 0x56238277ee60 <line:28:6, col:14> 'int' '='
    |       |-DeclRefExpr 0x56238277edc8 <col:6> 'int' lvalue Var 0x56238277ea20 'i' 'int'
    |       `-BinaryOperator 0x56238277ee40 <col:10, col:14> 'int' '+'
    |         |-ImplicitCastExpr 0x56238277ee28 <col:10> 'int' <LValueToRValue>
    |         | `-DeclRefExpr 0x56238277ede8 <col:10> 'int' lvalue Var 0x56238277ea20 'i' 'int'
    |         `-IntegerLiteral 0x56238277ee08 <col:14> 'int' 4
    |-BinaryOperator 0x56238277ef70 <line:31:3, col:9> 'int' '='
    | |-DeclRefExpr 0x56238277eed8 <col:3> 'int' lvalue Var 0x56238277eaa0 'j' 'int'
    | `-BinaryOperator 0x56238277ef50 <col:7, col:9> 'int' '/'
    |   |-ImplicitCastExpr 0x56238277ef38 <col:7> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x56238277eef8 <col:7> 'int' lvalue Var 0x56238277ea20 'i' 'int'
    |   `-IntegerLiteral 0x56238277ef18 <col:9> 'int' 4
    |-CallExpr 0x56238277f0e0 <line:32:5, col:36> 'void'
    | |-ImplicitCastExpr 0x56238277f0c8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x56238277ef90 <col:5> 'void (int)' Function 0x56238277e668 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x56238277f080 <col:24, col:35> 'int' '=='
    |   |-ParenExpr 0x56238277f028 <col:24, col:30> 'int'
    |   | `-BinaryOperator 0x56238277f008 <col:25, col:29> 'int' '*'
    |   |   |-ImplicitCastExpr 0x56238277eff0 <col:25> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x56238277efb0 <col:25> 'int' lvalue Var 0x56238277eaa0 'j' 'int'
    |   |   `-IntegerLiteral 0x56238277efd0 <col:29> 'int' 4
    |   `-ImplicitCastExpr 0x56238277f068 <col:35> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x56238277f048 <col:35> 'int' lvalue Var 0x56238277ea20 'i' 'int'
    `-ReturnStmt 0x56238277f128 <line:33:3, col:10>
      `-IntegerLiteral 0x56238277f108 <col:10> 'int' 0
1 warning generated.
