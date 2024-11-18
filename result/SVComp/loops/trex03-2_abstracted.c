./Benchmark/PLDI/SVComp/loops/trex03-2_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex03-2_abstracted.c:12:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x56144e12cee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x56144e12d780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x56144e12d480 '__int128'
|-TypedefDecl 0x56144e12d7f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x56144e12d4a0 'unsigned __int128'
|-TypedefDecl 0x56144e12daf8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x56144e12d8d0 'struct __NSConstantString_tag'
|   `-Record 0x56144e12d848 '__NSConstantString_tag'
|-TypedefDecl 0x56144e12db90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x56144e12db50 'char *'
|   `-BuiltinType 0x56144e12cf80 'char'
|-TypedefDecl 0x56144e12de88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x56144e12de30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x56144e12dc70 'struct __va_list_tag'
|     `-Record 0x56144e12dbe8 '__va_list_tag'
|-FunctionDecl 0x56144e18d218 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex03-2_abstracted.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56144e18d2b8 prev 0x56144e18d218 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56144e18d3b0 <line:2:1, col:34> col:12 __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x56144e18d4e8 <line:3:1, col:37> col:14 used __VERIFIER_nondet_bool '_Bool ()' extern
|-FunctionDecl 0x56144e18d5d8 <line:4:1, col:36> col:13 __VERIFIER_nondet_char 'char ()' extern
|-FunctionDecl 0x56144e18d6d0 <line:5:1, col:40> col:15 __VERIFIER_nondet_double 'double ()' extern
|-FunctionDecl 0x56144e18d7c0 <line:6:1, col:38> col:14 __VERIFIER_nondet_float 'float ()' extern
|-FunctionDecl 0x56144e18d8b0 <line:7:1, col:46> col:22 __VERIFIER_nondet_ulong 'unsigned long ()' extern
|-FunctionDecl 0x56144e18d9a0 <line:8:1, col:55> col:27 __VERIFIER_nondet_ulonglong 'unsigned long long ()' extern
|-FunctionDecl 0x56144e18da90 <line:9:1, col:44> col:21 used __VERIFIER_nondet_uint 'unsigned int ()' extern
|-FunctionDecl 0x56144e18db58 prev 0x56144e18d3b0 <line:10:1, col:34> col:12 __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x56144e18dc90 prev 0x56144e18d2b8 <line:11:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56144e18e008 <line:12:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x56144e18dd48 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x56144e18ddc8 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x56144e18de48 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x56144e18dec8 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x56144e18e0c8 <col:99>
|-FunctionDecl 0x56144e18f188 <line:13:1, col:85> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x56144e18f4c8 <col:20, col:85>
|   `-CallExpr 0x56144e18f3e0 <col:22, col:82> 'void'
|     |-ImplicitCastExpr 0x56144e18f3c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x56144e18f228 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x56144e18e008 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x56144e18f438 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56144e18f420 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56144e18f288 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x56144e18f468 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56144e18f450 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56144e18f2e8 <col:41> 'char [22]' lvalue "trex03-2_abstracted.c"
|     |-ImplicitCastExpr 0x56144e18f480 <col:66> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x56144e18f318 <col:66> 'int' 3
|     `-ImplicitCastExpr 0x56144e18f4b0 <col:69> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x56144e18f498 <col:69> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x56144e18f378 <col:69> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x56144e18f5b8 <line:15:1, line:20:1> line:15:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x56144e18f4f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x56144e18f898 <col:34, line:20:1>
|   |-IfStmt 0x56144e18f870 <line:16:3, line:18:3>
|   | |-UnaryOperator 0x56144e18f6b8 <line:16:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x56144e18f6a0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x56144e18f680 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x56144e18f660 <col:9> 'int' lvalue ParmVar 0x56144e18f4f8 'cond' 'int'
|   | `-CompoundStmt 0x56144e18f858 <col:16, line:18:3>
|   |   `-LabelStmt 0x56144e18f840 <line:17:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x56144e18f7d0 <col:12, col:35>
|   |       |-CallExpr 0x56144e18f730 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x56144e18f718 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x56144e18f6d0 <col:13> 'void ()' Function 0x56144e18f188 'reach_error' 'void ()'
|   |       `-CallExpr 0x56144e18f7b0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x56144e18f798 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x56144e18f750 <col:27> 'void (void) __attribute__((noreturn))' Function 0x56144e18dc90 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x56144e18f888 <line:19:3>
|-FunctionDecl 0x56144e18f8e0 prev 0x56144e18da90 <line:21:1, col:37> col:14 used __VERIFIER_nondet_uint 'unsigned int ()'
|-FunctionDecl 0x56144e18f9a0 prev 0x56144e18d4e8 <line:22:1, col:30> col:7 used __VERIFIER_nondet_bool '_Bool ()'
`-FunctionDecl 0x56144e18fa68 <line:24:1, line:43:1> line:24:5 main 'int ()'
  `-CompoundStmt 0x56144e1926b8 <line:25:1, line:43:1>
    |-DeclStmt 0x56144e18fde0 <line:26:3, col:101>
    | |-VarDecl 0x56144e18fb20 <col:3, col:42> col:16 used x1 'unsigned int' cinit
    | | `-CallExpr 0x56144e18fbf0 <col:19, col:42> 'unsigned int'
    | |   `-ImplicitCastExpr 0x56144e18fbd8 <col:19> 'unsigned int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x56144e18fb88 <col:19> 'unsigned int ()' Function 0x56144e18f8e0 '__VERIFIER_nondet_uint' 'unsigned int ()'
    | |-VarDecl 0x56144e18fc28 <col:3, col:71> col:45 used x2 'unsigned int' cinit
    | | `-CallExpr 0x56144e18fcc8 <col:48, col:71> 'unsigned int'
    | |   `-ImplicitCastExpr 0x56144e18fcb0 <col:48> 'unsigned int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x56144e18fc90 <col:48> 'unsigned int ()' Function 0x56144e18f8e0 '__VERIFIER_nondet_uint' 'unsigned int ()'
    | `-VarDecl 0x56144e18fd00 <col:3, col:100> col:74 used x3 'unsigned int' cinit
    |   `-CallExpr 0x56144e18fda0 <col:77, col:100> 'unsigned int'
    |     `-ImplicitCastExpr 0x56144e18fd88 <col:77> 'unsigned int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x56144e18fd68 <col:77> 'unsigned int ()' Function 0x56144e18f8e0 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |-DeclStmt 0x56144e190040 <line:27:3, col:32>
    | |-VarDecl 0x56144e18fe10 <col:3, col:19> col:16 d1 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x56144e18fe98 <col:19> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x56144e18fe78 <col:19> 'int' 1
    | |-VarDecl 0x56144e18fec8 <col:3, col:25> col:22 d2 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x56144e18ff50 <col:25> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x56144e18ff30 <col:25> 'int' 1
    | `-VarDecl 0x56144e18ff80 <col:3, col:31> col:28 d3 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x56144e190008 <col:31> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x56144e18ffe8 <col:31> 'int' 1
    |-DeclStmt 0x56144e191a98 <line:28:3, col:65>
    | |-VarDecl 0x56144e190068 <col:3, col:35> col:9 used c1 '_Bool' cinit
    | | `-CallExpr 0x56144e191990 <col:12, col:35> '_Bool'
    | |   `-ImplicitCastExpr 0x56144e190118 <col:12> '_Bool (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x56144e1900d0 <col:12> '_Bool ()' Function 0x56144e18f9a0 '__VERIFIER_nondet_bool' '_Bool ()'
    | `-VarDecl 0x56144e1919c0 <col:3, col:64> col:38 used c2 '_Bool' cinit
    |   `-CallExpr 0x56144e191a60 <col:41, col:64> '_Bool'
    |     `-ImplicitCastExpr 0x56144e191a48 <col:41> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x56144e191a28 <col:41> '_Bool ()' Function 0x56144e18f9a0 '__VERIFIER_nondet_bool' '_Bool ()'
    |-IfStmt 0x56144e1920b0 <line:31:3, line:37:3>
    | |-BinaryOperator 0x56144e191d60 <line:31:7, col:44> 'int' '&'
    | | |-ParenExpr 0x56144e191b60 <col:7, col:16> 'int'
    | | | `-BinaryOperator 0x56144e191b40 <col:8, col:15> 'int' '>'
    | | |   |-ImplicitCastExpr 0x56144e191b10 <col:8> 'unsigned int' <LValueToRValue>
    | | |   | `-DeclRefExpr 0x56144e191ab0 <col:8> 'unsigned int' lvalue Var 0x56144e18fd00 'x3' 'unsigned int'
    | | |   `-ImplicitCastExpr 0x56144e191b28 <col:13, col:15> 'unsigned int' <IntegralCast>
    | | |     `-ParenExpr 0x56144e191af0 <col:13, col:15> 'int'
    | | |       `-IntegerLiteral 0x56144e191ad0 <col:14> 'int' 0
    | | `-ParenExpr 0x56144e191d40 <col:20, col:44> 'int'
    | |   `-BinaryOperator 0x56144e191d20 <col:21, col:43> 'int' '&'
    | |     |-ParenExpr 0x56144e191c30 <col:21, col:30> 'int'
    | |     | `-BinaryOperator 0x56144e191c10 <col:22, col:29> 'int' '>'
    | |     |   |-ImplicitCastExpr 0x56144e191be0 <col:22> 'unsigned int' <LValueToRValue>
    | |     |   | `-DeclRefExpr 0x56144e191b80 <col:22> 'unsigned int' lvalue Var 0x56144e18fc28 'x2' 'unsigned int'
    | |     |   `-ImplicitCastExpr 0x56144e191bf8 <col:27, col:29> 'unsigned int' <IntegralCast>
    | |     |     `-ParenExpr 0x56144e191bc0 <col:27, col:29> 'int'
    | |     |       `-IntegerLiteral 0x56144e191ba0 <col:28> 'int' 0
    | |     `-ParenExpr 0x56144e191d00 <col:34, col:43> 'int'
    | |       `-BinaryOperator 0x56144e191ce0 <col:35, col:42> 'int' '>'
    | |         |-ImplicitCastExpr 0x56144e191cb0 <col:35> 'unsigned int' <LValueToRValue>
    | |         | `-DeclRefExpr 0x56144e191c50 <col:35> 'unsigned int' lvalue Var 0x56144e18fb20 'x1' 'unsigned int'
    | |         `-ImplicitCastExpr 0x56144e191cc8 <col:40, col:42> 'unsigned int' <IntegralCast>
    | |           `-ParenExpr 0x56144e191c90 <col:40, col:42> 'int'
    | |             `-IntegerLiteral 0x56144e191c70 <col:41> 'int' 0
    | `-CompoundStmt 0x56144e192078 <col:47, line:37:3>
    |   |-BinaryOperator 0x56144e191df8 <line:32:3, col:31> 'unsigned int' '='
    |   | |-DeclRefExpr 0x56144e191d80 <col:3> 'unsigned int' lvalue Var 0x56144e18fd00 'x3' 'unsigned int'
    |   | `-CallExpr 0x56144e191dd8 <col:8, col:31> 'unsigned int'
    |   |   `-ImplicitCastExpr 0x56144e191dc0 <col:8> 'unsigned int (*)()' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x56144e191da0 <col:8> 'unsigned int ()' Function 0x56144e18f8e0 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |   |-BinaryOperator 0x56144e191e90 <line:33:3, col:31> 'unsigned int' '='
    |   | |-DeclRefExpr 0x56144e191e18 <col:3> 'unsigned int' lvalue Var 0x56144e18fc28 'x2' 'unsigned int'
    |   | `-CallExpr 0x56144e191e70 <col:8, col:31> 'unsigned int'
    |   |   `-ImplicitCastExpr 0x56144e191e58 <col:8> 'unsigned int (*)()' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x56144e191e38 <col:8> 'unsigned int ()' Function 0x56144e18f8e0 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |   |-BinaryOperator 0x56144e191f28 <line:34:3, col:31> 'unsigned int' '='
    |   | |-DeclRefExpr 0x56144e191eb0 <col:3> 'unsigned int' lvalue Var 0x56144e18fb20 'x1' 'unsigned int'
    |   | `-CallExpr 0x56144e191f08 <col:8, col:31> 'unsigned int'
    |   |   `-ImplicitCastExpr 0x56144e191ef0 <col:8> 'unsigned int (*)()' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x56144e191ed0 <col:8> 'unsigned int ()' Function 0x56144e18f8e0 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |   |-BinaryOperator 0x56144e191fc0 <line:35:3, col:31> '_Bool' '='
    |   | |-DeclRefExpr 0x56144e191f48 <col:3> '_Bool' lvalue Var 0x56144e1919c0 'c2' '_Bool'
    |   | `-CallExpr 0x56144e191fa0 <col:8, col:31> '_Bool'
    |   |   `-ImplicitCastExpr 0x56144e191f88 <col:8> '_Bool (*)()' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x56144e191f68 <col:8> '_Bool ()' Function 0x56144e18f9a0 '__VERIFIER_nondet_bool' '_Bool ()'
    |   `-BinaryOperator 0x56144e192058 <line:36:3, col:31> '_Bool' '='
    |     |-DeclRefExpr 0x56144e191fe0 <col:3> '_Bool' lvalue Var 0x56144e190068 'c1' '_Bool'
    |     `-CallExpr 0x56144e192038 <col:8, col:31> '_Bool'
    |       `-ImplicitCastExpr 0x56144e192020 <col:8> '_Bool (*)()' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x56144e192000 <col:8> '_Bool ()' Function 0x56144e18f9a0 '__VERIFIER_nondet_bool' '_Bool ()'
    |-IfStmt 0x56144e1923f0 <line:38:3, col:53>
    | |-BinaryOperator 0x56144e192378 <col:7, col:44> 'int' '&'
    | | |-ParenExpr 0x56144e192178 <col:7, col:16> 'int'
    | | | `-BinaryOperator 0x56144e192158 <col:8, col:15> 'int' '>'
    | | |   |-ImplicitCastExpr 0x56144e192128 <col:8> 'unsigned int' <LValueToRValue>
    | | |   | `-DeclRefExpr 0x56144e1920c8 <col:8> 'unsigned int' lvalue Var 0x56144e18fd00 'x3' 'unsigned int'
    | | |   `-ImplicitCastExpr 0x56144e192140 <col:13, col:15> 'unsigned int' <IntegralCast>
    | | |     `-ParenExpr 0x56144e192108 <col:13, col:15> 'int'
    | | |       `-IntegerLiteral 0x56144e1920e8 <col:14> 'int' 0
    | | `-ParenExpr 0x56144e192358 <col:20, col:44> 'int'
    | |   `-BinaryOperator 0x56144e192338 <col:21, col:43> 'int' '&'
    | |     |-ParenExpr 0x56144e192248 <col:21, col:30> 'int'
    | |     | `-BinaryOperator 0x56144e192228 <col:22, col:29> 'int' '>'
    | |     |   |-ImplicitCastExpr 0x56144e1921f8 <col:22> 'unsigned int' <LValueToRValue>
    | |     |   | `-DeclRefExpr 0x56144e192198 <col:22> 'unsigned int' lvalue Var 0x56144e18fc28 'x2' 'unsigned int'
    | |     |   `-ImplicitCastExpr 0x56144e192210 <col:27, col:29> 'unsigned int' <IntegralCast>
    | |     |     `-ParenExpr 0x56144e1921d8 <col:27, col:29> 'int'
    | |     |       `-IntegerLiteral 0x56144e1921b8 <col:28> 'int' 0
    | |     `-ParenExpr 0x56144e192318 <col:34, col:43> 'int'
    | |       `-BinaryOperator 0x56144e1922f8 <col:35, col:42> 'int' '>'
    | |         |-ImplicitCastExpr 0x56144e1922c8 <col:35> 'unsigned int' <LValueToRValue>
    | |         | `-DeclRefExpr 0x56144e192268 <col:35> 'unsigned int' lvalue Var 0x56144e18fb20 'x1' 'unsigned int'
    | |         `-ImplicitCastExpr 0x56144e1922e0 <col:40, col:42> 'unsigned int' <IntegralCast>
    | |           `-ParenExpr 0x56144e1922a8 <col:40, col:42> 'int'
    | |             `-IntegerLiteral 0x56144e192288 <col:41> 'int' 0
    | `-CallExpr 0x56144e1923d0 <col:47, col:53> 'void'
    |   `-ImplicitCastExpr 0x56144e1923b8 <col:47> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x56144e192398 <col:47> 'void (void) __attribute__((noreturn))' Function 0x56144e18dc90 'abort' 'void (void) __attribute__((noreturn))'
    |-CallExpr 0x56144e192660 <line:41:3, col:44> 'void'
    | |-ImplicitCastExpr 0x56144e192648 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x56144e192408 <col:3> 'void (int)' Function 0x56144e18f5b8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x56144e1925f8 <col:21, col:43> 'int' '||'
    |   |-BinaryOperator 0x56144e192548 <col:21, col:34> 'int' '||'
    |   | |-BinaryOperator 0x56144e192498 <col:21, col:25> 'int' '=='
    |   | | |-ImplicitCastExpr 0x56144e192468 <col:21> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x56144e192428 <col:21> 'unsigned int' lvalue Var 0x56144e18fb20 'x1' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x56144e192480 <col:25> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x56144e192448 <col:25> 'int' 0
    |   | `-BinaryOperator 0x56144e192528 <col:30, col:34> 'int' '=='
    |   |   |-ImplicitCastExpr 0x56144e1924f8 <col:30> 'unsigned int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x56144e1924b8 <col:30> 'unsigned int' lvalue Var 0x56144e18fc28 'x2' 'unsigned int'
    |   |   `-ImplicitCastExpr 0x56144e192510 <col:34> 'unsigned int' <IntegralCast>
    |   |     `-IntegerLiteral 0x56144e1924d8 <col:34> 'int' 0
    |   `-BinaryOperator 0x56144e1925d8 <col:39, col:43> 'int' '=='
    |     |-ImplicitCastExpr 0x56144e1925a8 <col:39> 'unsigned int' <LValueToRValue>
    |     | `-DeclRefExpr 0x56144e192568 <col:39> 'unsigned int' lvalue Var 0x56144e18fd00 'x3' 'unsigned int'
    |     `-ImplicitCastExpr 0x56144e1925c0 <col:43> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x56144e192588 <col:43> 'int' 0
    `-ReturnStmt 0x56144e1926a8 <line:42:3, col:10>
      `-IntegerLiteral 0x56144e192688 <col:10> 'int' 0
1 warning generated.
