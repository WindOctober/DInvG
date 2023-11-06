./Benchmark/PLDI/SVComp/loop-zilu/benchmark02_linear_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark02_linear_abstracted.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x5584713e8028 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5584713e88c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5584713e85c0 '__int128'
|-TypedefDecl 0x5584713e8930 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5584713e85e0 'unsigned __int128'
|-TypedefDecl 0x5584713e8c38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5584713e8a10 'struct __NSConstantString_tag'
|   `-Record 0x5584713e8988 '__NSConstantString_tag'
|-TypedefDecl 0x5584713e8cd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5584713e8c90 'char *'
|   `-BuiltinType 0x5584713e80c0 'char'
|-TypedefDecl 0x5584713e8fc8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5584713e8f70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5584713e8db0 'struct __va_list_tag'
|     `-Record 0x5584713e8d28 '__va_list_tag'
|-FunctionDecl 0x558471447ce8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark02_linear_abstracted.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x558471447f78 <col:24, col:35>
|   `-CallExpr 0x558471447f50 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x558471447f38 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x558471447ed0 <col:25> 'int ()' Function 0x558471447e20 'assert' 'int ()'
|     `-IntegerLiteral 0x558471447ef0 <col:32> 'int' 0
|-FunctionDecl 0x558471448058 <line:2:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5584714480f8 prev 0x558471448058 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558471448260 <line:4:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x5584714483c8 <line:5:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x558471448548 <line:7:1, line:11:1> line:7:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x558471448480 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5584714486f0 <col:34, line:11:1>
|   `-IfStmt 0x5584714486d8 <line:8:3, line:10:3>
|     |-UnaryOperator 0x558471448628 <line:8:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x558471448610 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5584714485f0 <col:8> 'int' lvalue ParmVar 0x558471448480 'cond' 'int'
|     `-CompoundStmt 0x5584714486c0 <col:14, line:10:3>
|       `-CallExpr 0x5584714486a0 <line:9:5, col:17> 'void'
|         `-ImplicitCastExpr 0x558471448688 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x558471448640 <col:5> 'void (void)' Function 0x558471447ce8 'reach_error' 'void (void)'
`-FunctionDecl 0x558471448730 <line:24:1, line:38:1> line:24:5 main 'int ()'
  `-CompoundStmt 0x5584714493e8 <col:12, line:38:1>
    |-DeclStmt 0x5584714488d0 <line:25:3, col:34>
    | `-VarDecl 0x5584714487e8 <col:3, col:33> col:7 used n 'int' cinit
    |   `-CallExpr 0x5584714488b0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x558471448898 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x558471448850 <col:11> 'int (void)' Function 0x558471448260 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x5584714489c0 <line:26:3, col:34>
    | `-VarDecl 0x558471448900 <col:3, col:33> col:7 used i 'int' cinit
    |   `-CallExpr 0x5584714489a0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x558471448988 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x558471448968 <col:11> 'int (void)' Function 0x558471448260 '__VERIFIER_nondet_int' 'int (void)'
    |-DeclStmt 0x558471448ab0 <line:27:3, col:34>
    | `-VarDecl 0x5584714489f0 <col:3, col:33> col:7 used l 'int' cinit
    |   `-CallExpr 0x558471448a90 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x558471448a78 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x558471448a58 <col:11> 'int (void)' Function 0x558471448260 '__VERIFIER_nondet_int' 'int (void)'
    |-BinaryOperator 0x558471448b20 <line:28:3, col:7> 'int' '='
    | |-DeclRefExpr 0x558471448ac8 <col:3> 'int' lvalue Var 0x558471448900 'i' 'int'
    | `-ImplicitCastExpr 0x558471448b08 <col:7> 'int' <LValueToRValue>
    |   `-DeclRefExpr 0x558471448ae8 <col:7> 'int' lvalue Var 0x5584714489f0 'l' 'int'
    |-IfStmt 0x558471449020 <line:29:3, col:22>
    | |-UnaryOperator 0x558471448bd8 <col:7, col:12> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x558471448bb8 <col:8, col:12> 'int'
    | |   `-BinaryOperator 0x558471448b98 <col:9, col:11> 'int' '>'
    | |     |-ImplicitCastExpr 0x558471448b80 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x558471448b40 <col:9> 'int' lvalue Var 0x5584714489f0 'l' 'int'
    | |     `-IntegerLiteral 0x558471448b60 <col:11> 'int' 0
    | `-ReturnStmt 0x558471448c10 <col:15, col:22>
    |   `-IntegerLiteral 0x558471448bf0 <col:22> 'int' 0
    |-IfStmt 0x558471449178 <line:31:3, line:33:3>
    | |-BinaryOperator 0x5584714490a8 <line:31:7, col:11> 'int' '<'
    | | |-ImplicitCastExpr 0x558471449078 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558471449038 <col:7> 'int' lvalue Var 0x558471448900 'i' 'int'
    | | `-ImplicitCastExpr 0x558471449090 <col:11> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x558471449058 <col:11> 'int' lvalue Var 0x5584714487e8 'n' 'int'
    | `-CompoundStmt 0x558471449160 <col:14, line:33:3>
    |   `-BinaryOperator 0x558471449140 <line:32:3, col:29> 'int' '='
    |     |-DeclRefExpr 0x5584714490c8 <col:3> 'int' lvalue Var 0x558471448900 'i' 'int'
    |     `-CallExpr 0x558471449120 <col:7, col:29> 'int'
    |       `-ImplicitCastExpr 0x558471449108 <col:7> 'int (*)(void)' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x5584714490e8 <col:7> 'int (void)' Function 0x558471448260 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x5584714492a0 <line:34:3, col:20>
    | |-BinaryOperator 0x558471449200 <col:7, col:11> 'int' '<'
    | | |-ImplicitCastExpr 0x5584714491d0 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558471449190 <col:7> 'int' lvalue Var 0x558471448900 'i' 'int'
    | | `-ImplicitCastExpr 0x5584714491e8 <col:11> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x5584714491b0 <col:11> 'int' lvalue Var 0x5584714487e8 'n' 'int'
    | `-CallExpr 0x558471449280 <col:14, col:20> 'void'
    |   `-ImplicitCastExpr 0x558471449268 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x558471449220 <col:14> 'void (void) __attribute__((noreturn))' Function 0x5584714480f8 'abort' 'void (void) __attribute__((noreturn))'
    |-CallExpr 0x558471449390 <line:36:3, col:25> 'void'
    | |-ImplicitCastExpr 0x558471449378 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5584714492b8 <col:3> 'void (int)' Function 0x558471448548 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x558471449330 <col:21, col:24> 'int' '>='
    |   |-ImplicitCastExpr 0x558471449318 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5584714492d8 <col:21> 'int' lvalue Var 0x5584714489f0 'l' 'int'
    |   `-IntegerLiteral 0x5584714492f8 <col:24> 'int' 1
    `-ReturnStmt 0x5584714493d8 <line:37:3, col:10>
      `-IntegerLiteral 0x5584714493b8 <col:10> 'int' 0
1 warning generated.
