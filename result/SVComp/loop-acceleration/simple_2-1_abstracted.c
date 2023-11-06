./Benchmark/PLDI/SVComp/loop-acceleration/simple_2-1_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/simple_2-1_abstracted.c:12:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x562c1e688ff8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x562c1e689890 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x562c1e689590 '__int128'
|-TypedefDecl 0x562c1e689900 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562c1e6895b0 'unsigned __int128'
|-TypedefDecl 0x562c1e689c08 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x562c1e6899e0 'struct __NSConstantString_tag'
|   `-Record 0x562c1e689958 '__NSConstantString_tag'
|-TypedefDecl 0x562c1e689ca0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562c1e689c60 'char *'
|   `-BuiltinType 0x562c1e689090 'char'
|-TypedefDecl 0x562c1e689f98 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562c1e689f40 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562c1e689d80 'struct __va_list_tag'
|     `-Record 0x562c1e689cf8 '__va_list_tag'
|-FunctionDecl 0x562c1e6e91d8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/simple_2-1_abstracted.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562c1e6e9278 prev 0x562c1e6e91d8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562c1e6e9370 <line:2:1, col:34> col:12 __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x562c1e6e94a8 <line:3:1, col:37> col:14 __VERIFIER_nondet_bool '_Bool ()' extern
|-FunctionDecl 0x562c1e6e9598 <line:4:1, col:36> col:13 __VERIFIER_nondet_char 'char ()' extern
|-FunctionDecl 0x562c1e6e9690 <line:5:1, col:40> col:15 __VERIFIER_nondet_double 'double ()' extern
|-FunctionDecl 0x562c1e6e9780 <line:6:1, col:38> col:14 __VERIFIER_nondet_float 'float ()' extern
|-FunctionDecl 0x562c1e6e9870 <line:7:1, col:46> col:22 __VERIFIER_nondet_ulong 'unsigned long ()' extern
|-FunctionDecl 0x562c1e6e9960 <line:8:1, col:55> col:27 __VERIFIER_nondet_ulonglong 'unsigned long long ()' extern
|-FunctionDecl 0x562c1e6e9a50 <line:9:1, col:44> col:21 used __VERIFIER_nondet_uint 'unsigned int ()' extern
|-FunctionDecl 0x562c1e6e9b18 prev 0x562c1e6e9370 <line:10:1, col:34> col:12 __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x562c1e6e9c50 prev 0x562c1e6e9278 <line:11:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562c1e6e9fc8 <line:12:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x562c1e6e9d08 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x562c1e6e9d88 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x562c1e6e9e08 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x562c1e6e9e88 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x562c1e6ea088 <col:99>
|-FunctionDecl 0x562c1e6eb148 <line:13:1, col:87> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x562c1e6eb488 <col:20, col:87>
|   `-CallExpr 0x562c1e6eb3a0 <col:22, col:84> 'void'
|     |-ImplicitCastExpr 0x562c1e6eb388 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x562c1e6eb1e8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x562c1e6e9fc8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x562c1e6eb3f8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x562c1e6eb3e0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x562c1e6eb248 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x562c1e6eb428 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x562c1e6eb410 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x562c1e6eb2a8 <col:41> 'char [24]' lvalue "simple_2-1_abstracted.c"
|     |-ImplicitCastExpr 0x562c1e6eb440 <col:68> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x562c1e6eb2d8 <col:68> 'int' 3
|     `-ImplicitCastExpr 0x562c1e6eb470 <col:71> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x562c1e6eb458 <col:71> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x562c1e6eb338 <col:71> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x562c1e6eb570 prev 0x562c1e6e9a50 <line:14:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x562c1e6eb6e8 <line:16:1, line:21:1> line:16:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x562c1e6eb628 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x562c1e6eb9c8 <col:34, line:21:1>
|   |-IfStmt 0x562c1e6eb9a0 <line:17:3, line:19:3>
|   | |-UnaryOperator 0x562c1e6eb7e8 <line:17:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x562c1e6eb7d0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x562c1e6eb7b0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x562c1e6eb790 <col:9> 'int' lvalue ParmVar 0x562c1e6eb628 'cond' 'int'
|   | `-CompoundStmt 0x562c1e6eb988 <col:16, line:19:3>
|   |   `-LabelStmt 0x562c1e6eb970 <line:18:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x562c1e6eb900 <col:12, col:35>
|   |       |-CallExpr 0x562c1e6eb860 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x562c1e6eb848 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x562c1e6eb800 <col:13> 'void ()' Function 0x562c1e6eb148 'reach_error' 'void ()'
|   |       `-CallExpr 0x562c1e6eb8e0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x562c1e6eb8c8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x562c1e6eb880 <col:27> 'void (void) __attribute__((noreturn))' Function 0x562c1e6e9c50 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x562c1e6eb9b8 <line:20:3>
`-FunctionDecl 0x562c1e6ebab0 <line:23:1, line:34:1> line:23:5 main 'int (void)'
  `-CompoundStmt 0x562c1e6ec048 <col:16, line:34:1>
    |-DeclStmt 0x562c1e6ebc80 <line:24:3, col:44>
    | `-VarDecl 0x562c1e6ebb90 <col:3, col:43> col:16 used x 'unsigned int' cinit
    |   `-CallExpr 0x562c1e6ebc60 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x562c1e6ebc48 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562c1e6ebbf8 <col:20> 'unsigned int (void)' Function 0x562c1e6eb570 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-IfStmt 0x562c1e6ebdf8 <line:27:3, line:29:3>
    | |-BinaryOperator 0x562c1e6ebd28 <line:27:7, col:21> 'int' '<'
    | | |-ImplicitCastExpr 0x562c1e6ebcf8 <col:7> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x562c1e6ebc98 <col:7> 'unsigned int' lvalue Var 0x562c1e6ebb90 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x562c1e6ebd10 <col:11, col:21> 'unsigned int' <IntegralCast>
    | |   `-ParenExpr 0x562c1e6ebcd8 <col:11, col:21> 'int'
    | |     `-IntegerLiteral 0x562c1e6ebcb8 <col:12> 'int' 268435455
    | `-CompoundStmt 0x562c1e6ebde0 <col:24, line:29:3>
    |   `-BinaryOperator 0x562c1e6ebdc0 <line:28:3, col:30> 'unsigned int' '='
    |     |-DeclRefExpr 0x562c1e6ebd48 <col:3> 'unsigned int' lvalue Var 0x562c1e6ebb90 'x' 'unsigned int'
    |     `-CallExpr 0x562c1e6ebda0 <col:7, col:30> 'unsigned int'
    |       `-ImplicitCastExpr 0x562c1e6ebd88 <col:7> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x562c1e6ebd68 <col:7> 'unsigned int (void)' Function 0x562c1e6eb570 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-IfStmt 0x562c1e6ebf18 <line:30:3, col:30>
    | |-BinaryOperator 0x562c1e6ebea0 <col:7, col:21> 'int' '<'
    | | |-ImplicitCastExpr 0x562c1e6ebe70 <col:7> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x562c1e6ebe10 <col:7> 'unsigned int' lvalue Var 0x562c1e6ebb90 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x562c1e6ebe88 <col:11, col:21> 'unsigned int' <IntegralCast>
    | |   `-ParenExpr 0x562c1e6ebe50 <col:11, col:21> 'int'
    | |     `-IntegerLiteral 0x562c1e6ebe30 <col:12> 'int' 268435455
    | `-CallExpr 0x562c1e6ebef8 <col:24, col:30> 'void'
    |   `-ImplicitCastExpr 0x562c1e6ebee0 <col:24> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x562c1e6ebec0 <col:24> 'void (void) __attribute__((noreturn))' Function 0x562c1e6e9c50 'abort' 'void (void) __attribute__((noreturn))'
    `-CallExpr 0x562c1e6ec020 <line:33:3, col:36> 'void'
      |-ImplicitCastExpr 0x562c1e6ec008 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x562c1e6ebf30 <col:3> 'void (int)' Function 0x562c1e6eb6e8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x562c1e6ebfc0 <col:21, col:26> 'int' '>='
        |-ImplicitCastExpr 0x562c1e6ebf90 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x562c1e6ebf50 <col:21> 'unsigned int' lvalue Var 0x562c1e6ebb90 'x' 'unsigned int'
        `-ImplicitCastExpr 0x562c1e6ebfa8 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x562c1e6ebf70 <col:26> 'int' 268435455
1 warning generated.
