./Benchmark/PLDI/SVComp/loops/trex04_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex04_abstracted.c:12:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x559e72be9ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x559e72bea780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x559e72bea480 '__int128'
|-TypedefDecl 0x559e72bea7f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x559e72bea4a0 'unsigned __int128'
|-TypedefDecl 0x559e72beaaf8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x559e72bea8d0 'struct __NSConstantString_tag'
|   `-Record 0x559e72bea848 '__NSConstantString_tag'
|-TypedefDecl 0x559e72beab90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x559e72beab50 'char *'
|   `-BuiltinType 0x559e72be9f80 'char'
|-TypedefDecl 0x559e72beae88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x559e72beae30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x559e72beac70 'struct __va_list_tag'
|     `-Record 0x559e72beabe8 '__va_list_tag'
|-FunctionDecl 0x559e72c4a278 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex04_abstracted.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559e72c4a318 prev 0x559e72c4a278 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559e72c4a410 <line:2:1, col:34> col:12 used __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x559e72c4a548 <line:3:1, col:37> col:14 used __VERIFIER_nondet_bool '_Bool ()' extern
|-FunctionDecl 0x559e72c4a638 <line:4:1, col:36> col:13 __VERIFIER_nondet_char 'char ()' extern
|-FunctionDecl 0x559e72c4a730 <line:5:1, col:40> col:15 __VERIFIER_nondet_double 'double ()' extern
|-FunctionDecl 0x559e72c4a820 <line:6:1, col:38> col:14 __VERIFIER_nondet_float 'float ()' extern
|-FunctionDecl 0x559e72c4a910 <line:7:1, col:46> col:22 __VERIFIER_nondet_ulong 'unsigned long ()' extern
|-FunctionDecl 0x559e72c4aa00 <line:8:1, col:55> col:27 __VERIFIER_nondet_ulonglong 'unsigned long long ()' extern
|-FunctionDecl 0x559e72c4aaf0 <line:9:1, col:44> col:21 __VERIFIER_nondet_uint 'unsigned int ()' extern
|-FunctionDecl 0x559e72c4abb8 prev 0x559e72c4a410 <line:10:1, col:34> col:12 used __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x559e72c4acf0 prev 0x559e72c4a318 <line:11:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559e72c4b068 <line:12:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559e72c4ada8 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x559e72c4ae28 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x559e72c4aea8 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x559e72c4af28 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x559e72c4b128 <col:99>
|-FunctionDecl 0x559e72c4c1e8 <line:13:1, col:83> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x559e72c4c528 <col:20, col:83>
|   `-CallExpr 0x559e72c4c440 <col:22, col:80> 'void'
|     |-ImplicitCastExpr 0x559e72c4c428 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x559e72c4c288 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x559e72c4b068 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x559e72c4c498 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x559e72c4c480 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x559e72c4c2e8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x559e72c4c4c8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x559e72c4c4b0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x559e72c4c348 <col:41> 'char [20]' lvalue "trex04_abstracted.c"
|     |-ImplicitCastExpr 0x559e72c4c4e0 <col:64> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x559e72c4c378 <col:64> 'int' 3
|     `-ImplicitCastExpr 0x559e72c4c510 <col:67> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x559e72c4c4f8 <col:67> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x559e72c4c3d8 <col:67> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x559e72c4c5d8 prev 0x559e72c4acf0 <line:14:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559e72c4c758 <line:15:1, line:17:1> line:15:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x559e72c4c690 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x559e72c4c900 <col:36, line:17:1>
|   `-IfStmt 0x559e72c4c8e8 <line:16:3, col:22>
|     |-UnaryOperator 0x559e72c4c838 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x559e72c4c820 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x559e72c4c800 <col:7> 'int' lvalue ParmVar 0x559e72c4c690 'cond' 'int'
|     `-CompoundStmt 0x559e72c4c8d0 <col:13, col:22>
|       `-CallExpr 0x559e72c4c8b0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x559e72c4c898 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x559e72c4c850 <col:14> 'void (void) __attribute__((noreturn))' Function 0x559e72c4c5d8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x559e72c4c9c0 <line:19:1, line:24:1> line:19:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x559e72c4c930 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x559e72c4cc80 <col:34, line:24:1>
|   |-IfStmt 0x559e72c4cc58 <line:20:3, line:22:3>
|   | |-UnaryOperator 0x559e72c4cac0 <line:20:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x559e72c4caa8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x559e72c4ca88 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x559e72c4ca68 <col:9> 'int' lvalue ParmVar 0x559e72c4c930 'cond' 'int'
|   | `-CompoundStmt 0x559e72c4cc40 <col:16, line:22:3>
|   |   `-LabelStmt 0x559e72c4cc28 <line:21:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x559e72c4cbb8 <col:12, col:35>
|   |       |-CallExpr 0x559e72c4cb40 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x559e72c4cb28 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x559e72c4cad8 <col:13> 'void ()' Function 0x559e72c4c1e8 'reach_error' 'void ()'
|   |       `-CallExpr 0x559e72c4cb98 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x559e72c4cb80 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x559e72c4cb60 <col:27> 'void (void) __attribute__((noreturn))' Function 0x559e72c4c5d8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x559e72c4cc70 <line:23:3>
|-FunctionDecl 0x559e72c4ccc0 prev 0x559e72c4a548 <line:25:1, col:37> col:14 used __VERIFIER_nondet_bool '_Bool ()' extern
|-FunctionDecl 0x559e72c4cd88 prev 0x559e72c4abb8 <line:26:1, col:34> col:12 used __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x559e72c4ce48 <line:28:1, line:35:1> line:28:6 used foo 'void ()'
| `-CompoundStmt 0x559e72c4db70 <line:29:1, line:35:1>
|   |-DeclStmt 0x559e72c4cf88 <line:30:3, col:10>
|   | `-VarDecl 0x559e72c4cf00 <col:3, col:9> col:7 used y 'int' cinit
|   |   `-IntegerLiteral 0x559e72c4cf68 <col:9> 'int' 0
|   |-DeclStmt 0x559e72c4d188 <line:31:3, col:65>
|   | |-VarDecl 0x559e72c4cfb0 <col:3, col:35> col:9 used c1 '_Bool' cinit
|   | | `-CallExpr 0x559e72c4d080 <col:12, col:35> '_Bool'
|   | |   `-ImplicitCastExpr 0x559e72c4d068 <col:12> '_Bool (*)()' <FunctionToPointerDecay>
|   | |     `-DeclRefExpr 0x559e72c4d018 <col:12> '_Bool ()' Function 0x559e72c4ccc0 '__VERIFIER_nondet_bool' '_Bool ()'
|   | `-VarDecl 0x559e72c4d0b0 <col:3, col:64> col:38 used c2 '_Bool' cinit
|   |   `-CallExpr 0x559e72c4d150 <col:41, col:64> '_Bool'
|   |     `-ImplicitCastExpr 0x559e72c4d138 <col:41> '_Bool (*)()' <FunctionToPointerDecay>
|   |       `-DeclRefExpr 0x559e72c4d118 <col:41> '_Bool ()' Function 0x559e72c4ccc0 '__VERIFIER_nondet_bool' '_Bool ()'
|   |-IfStmt 0x559e72c4da50 <line:32:3, col:12>
|   | |-ImplicitCastExpr 0x559e72c4da00 <col:7> '_Bool' <LValueToRValue>
|   | | `-DeclRefExpr 0x559e72c4d9e0 <col:7> '_Bool' lvalue Var 0x559e72c4cfb0 'c1' '_Bool'
|   | `-UnaryOperator 0x559e72c4da38 <col:11, col:12> 'int' postfix '++'
|   |   `-DeclRefExpr 0x559e72c4da18 <col:11> 'int' lvalue Var 0x559e72c4cf00 'y' 'int'
|   `-IfStmt 0x559e72c4db48 <line:33:3, line:34:11> has_else
|     |-ImplicitCastExpr 0x559e72c4da88 <line:33:7> '_Bool' <LValueToRValue>
|     | `-DeclRefExpr 0x559e72c4da68 <col:7> '_Bool' lvalue Var 0x559e72c4d0b0 'c2' '_Bool'
|     |-UnaryOperator 0x559e72c4dac0 <col:11, col:12> 'int' postfix '--'
|     | `-DeclRefExpr 0x559e72c4daa0 <col:11> 'int' lvalue Var 0x559e72c4cf00 'y' 'int'
|     `-CompoundAssignOperator 0x559e72c4db18 <line:34:8, col:11> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
|       |-DeclRefExpr 0x559e72c4dad8 <col:8> 'int' lvalue Var 0x559e72c4cf00 'y' 'int'
|       `-IntegerLiteral 0x559e72c4daf8 <col:11> 'int' 10
`-FunctionDecl 0x559e72c4dbc8 <line:37:1, line:60:1> line:37:5 main 'int ()'
  `-CompoundStmt 0x559e72c4fa00 <line:38:1, line:60:1>
    |-DeclStmt 0x559e72c4dd08 <line:39:3, col:12>
    | `-VarDecl 0x559e72c4dc80 <col:3, col:11> col:7 used d 'int' cinit
    |   `-IntegerLiteral 0x559e72c4dce8 <col:11> 'int' 1
    |-DeclStmt 0x559e72c4de20 <line:40:3, col:34>
    | `-VarDecl 0x559e72c4dd38 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x559e72c4de00 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x559e72c4dde8 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x559e72c4dda0 <col:11> 'int ()' Function 0x559e72c4cd88 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x559e72c4dfc8 <line:41:3, col:48>
    | |-UnaryOperator 0x559e72c4df80 <col:7, col:38> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x559e72c4df60 <col:8, col:38> 'int'
    | |   `-BinaryOperator 0x559e72c4df40 <col:9, col:31> 'int' '&&'
    | |     |-BinaryOperator 0x559e72c4de90 <col:9, col:14> 'int' '<='
    | |     | |-ImplicitCastExpr 0x559e72c4de78 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x559e72c4de38 <col:9> 'int' lvalue Var 0x559e72c4dd38 'x' 'int'
    | |     | `-IntegerLiteral 0x559e72c4de58 <col:14> 'int' 1000000
    | |     `-BinaryOperator 0x559e72c4df20 <col:25, col:31> 'int' '>='
    | |       |-ImplicitCastExpr 0x559e72c4df08 <col:25> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x559e72c4deb0 <col:25> 'int' lvalue Var 0x559e72c4dd38 'x' 'int'
    | |       `-UnaryOperator 0x559e72c4def0 <col:30, col:31> 'int' prefix '-'
    | |         `-IntegerLiteral 0x559e72c4ded0 <col:31> 'int' 1000000
    | `-ReturnStmt 0x559e72c4dfb8 <col:41, col:48>
    |   `-IntegerLiteral 0x559e72c4df98 <col:48> 'int' 0
    |-DeclStmt 0x559e72c4e198 <line:42:3, col:65>
    | |-VarDecl 0x559e72c4dff0 <col:3, col:35> col:9 used c1 '_Bool' cinit
    | | `-CallExpr 0x559e72c4e090 <col:12, col:35> '_Bool'
    | |   `-ImplicitCastExpr 0x559e72c4e078 <col:12> '_Bool (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x559e72c4e058 <col:12> '_Bool ()' Function 0x559e72c4ccc0 '__VERIFIER_nondet_bool' '_Bool ()'
    | `-VarDecl 0x559e72c4e0c0 <col:3, col:64> col:38 used c2 '_Bool' cinit
    |   `-CallExpr 0x559e72c4e160 <col:41, col:64> '_Bool'
    |     `-ImplicitCastExpr 0x559e72c4e148 <col:41> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x559e72c4e128 <col:41> '_Bool ()' Function 0x559e72c4ccc0 '__VERIFIER_nondet_bool' '_Bool ()'
    |-IfStmt 0x559e72c4e2a0 <line:44:3, col:19>
    | |-ImplicitCastExpr 0x559e72c4e1d0 <col:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x559e72c4e1b0 <col:7> '_Bool' lvalue Var 0x559e72c4dff0 'c1' '_Bool'
    | `-BinaryOperator 0x559e72c4e280 <col:11, col:19> 'int' '='
    |   |-DeclRefExpr 0x559e72c4e1e8 <col:11> 'int' lvalue Var 0x559e72c4dc80 'd' 'int'
    |   `-BinaryOperator 0x559e72c4e260 <col:15, col:19> 'int' '-'
    |     |-ImplicitCastExpr 0x559e72c4e248 <col:15> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x559e72c4e208 <col:15> 'int' lvalue Var 0x559e72c4dc80 'd' 'int'
    |     `-IntegerLiteral 0x559e72c4e228 <col:19> 'int' 1
    |-IfStmt 0x559e72c4e348 <line:45:3, col:15>
    | |-ImplicitCastExpr 0x559e72c4e2d8 <col:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x559e72c4e2b8 <col:7> '_Bool' lvalue Var 0x559e72c4e0c0 'c2' '_Bool'
    | `-CallExpr 0x559e72c4e328 <col:11, col:15> 'void'
    |   `-ImplicitCastExpr 0x559e72c4e310 <col:11> 'void (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x559e72c4e2f0 <col:11> 'void ()' Function 0x559e72c4ce48 'foo' 'void ()'
    |-BinaryOperator 0x559e72c4e490 <line:47:3, col:58> '_Bool' ','
    | |-BinaryOperator 0x559e72c4e3d8 <col:3, col:29> '_Bool' '='
    | | |-DeclRefExpr 0x559e72c4e360 <col:3> '_Bool' lvalue Var 0x559e72c4dff0 'c1' '_Bool'
    | | `-CallExpr 0x559e72c4e3b8 <col:6, col:29> '_Bool'
    | |   `-ImplicitCastExpr 0x559e72c4e3a0 <col:6> '_Bool (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x559e72c4e380 <col:6> '_Bool ()' Function 0x559e72c4ccc0 '__VERIFIER_nondet_bool' '_Bool ()'
    | `-BinaryOperator 0x559e72c4e470 <col:32, col:58> '_Bool' '='
    |   |-DeclRefExpr 0x559e72c4e3f8 <col:32> '_Bool' lvalue Var 0x559e72c4e0c0 'c2' '_Bool'
    |   `-CallExpr 0x559e72c4e450 <col:35, col:58> '_Bool'
    |     `-ImplicitCastExpr 0x559e72c4e438 <col:35> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x559e72c4e418 <col:35> '_Bool ()' Function 0x559e72c4ccc0 '__VERIFIER_nondet_bool' '_Bool ()'
    |-IfStmt 0x559e72c4e540 <line:49:3, col:15>
    | |-ImplicitCastExpr 0x559e72c4e4d0 <col:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x559e72c4e4b0 <col:7> '_Bool' lvalue Var 0x559e72c4dff0 'c1' '_Bool'
    | `-CallExpr 0x559e72c4e520 <col:11, col:15> 'void'
    |   `-ImplicitCastExpr 0x559e72c4e508 <col:11> 'void (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x559e72c4e4e8 <col:11> 'void ()' Function 0x559e72c4ce48 'foo' 'void ()'
    |-IfStmt 0x559e72c4e648 <line:50:3, col:19>
    | |-ImplicitCastExpr 0x559e72c4e578 <col:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x559e72c4e558 <col:7> '_Bool' lvalue Var 0x559e72c4e0c0 'c2' '_Bool'
    | `-BinaryOperator 0x559e72c4e628 <col:11, col:19> 'int' '='
    |   |-DeclRefExpr 0x559e72c4e590 <col:11> 'int' lvalue Var 0x559e72c4dc80 'd' 'int'
    |   `-BinaryOperator 0x559e72c4e608 <col:15, col:19> 'int' '-'
    |     |-ImplicitCastExpr 0x559e72c4e5f0 <col:15> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x559e72c4e5b0 <col:15> 'int' lvalue Var 0x559e72c4dc80 'd' 'int'
    |     `-IntegerLiteral 0x559e72c4e5d0 <col:19> 'int' 1
    |-IfStmt 0x559e72c4e7a8 <line:53:3, line:55:3>
    | |-BinaryOperator 0x559e72c4e6d8 <line:53:7, col:13> 'int' '>'
    | | |-ImplicitCastExpr 0x559e72c4e6c0 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x559e72c4e660 <col:7> 'int' lvalue Var 0x559e72c4dd38 'x' 'int'
    | | `-ParenExpr 0x559e72c4e6a0 <col:11, col:13> 'int'
    | |   `-IntegerLiteral 0x559e72c4e680 <col:12> 'int' 0
    | `-CompoundStmt 0x559e72c4e790 <col:16, line:55:3>
    |   `-BinaryOperator 0x559e72c4e770 <line:54:3, col:29> 'int' '='
    |     |-DeclRefExpr 0x559e72c4e6f8 <col:3> 'int' lvalue Var 0x559e72c4dd38 'x' 'int'
    |     `-CallExpr 0x559e72c4e750 <col:7, col:29> 'int'
    |       `-ImplicitCastExpr 0x559e72c4e738 <col:7> 'int (*)()' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x559e72c4e718 <col:7> 'int ()' Function 0x559e72c4cd88 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x559e72c4e8b0 <line:56:3, col:22>
    | |-BinaryOperator 0x559e72c4e838 <col:7, col:13> 'int' '>'
    | | |-ImplicitCastExpr 0x559e72c4e820 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x559e72c4e7c0 <col:7> 'int' lvalue Var 0x559e72c4dd38 'x' 'int'
    | | `-ParenExpr 0x559e72c4e800 <col:11, col:13> 'int'
    | |   `-IntegerLiteral 0x559e72c4e7e0 <col:12> 'int' 0
    | `-CallExpr 0x559e72c4e890 <col:16, col:22> 'void'
    |   `-ImplicitCastExpr 0x559e72c4e878 <col:16> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x559e72c4e858 <col:16> 'void (void) __attribute__((noreturn))' Function 0x559e72c4c5d8 'abort' 'void (void) __attribute__((noreturn))'
    `-CallExpr 0x559e72c4e9a0 <line:59:3, col:25> 'void'
      |-ImplicitCastExpr 0x559e72c4e988 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x559e72c4e8c8 <col:3> 'void (int)' Function 0x559e72c4c9c0 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x559e72c4e940 <col:21, col:24> 'int' '<='
        |-ImplicitCastExpr 0x559e72c4e928 <col:21> 'int' <LValueToRValue>
        | `-DeclRefExpr 0x559e72c4e8e8 <col:21> 'int' lvalue Var 0x559e72c4dd38 'x' 'int'
        `-IntegerLiteral 0x559e72c4e908 <col:24> 'int' 0
1 warning generated.
