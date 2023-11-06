./Benchmark/PLDI/SVComp/loops/count_up_down-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/count_up_down-2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55f45a1d9e18 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55f45a1da6b0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55f45a1da3b0 '__int128'
|-TypedefDecl 0x55f45a1da720 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55f45a1da3d0 'unsigned __int128'
|-TypedefDecl 0x55f45a1daa28 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55f45a1da800 'struct __NSConstantString_tag'
|   `-Record 0x55f45a1da778 '__NSConstantString_tag'
|-TypedefDecl 0x55f45a1daac0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55f45a1daa80 'char *'
|   `-BuiltinType 0x55f45a1d9eb0 'char'
|-TypedefDecl 0x55f45a1dadb8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55f45a1dad60 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55f45a1daba0 'struct __va_list_tag'
|     `-Record 0x55f45a1dab18 '__va_list_tag'
|-FunctionDecl 0x55f45a239dc8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/count_up_down-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f45a239e68 prev 0x55f45a239dc8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f45a23a1e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f45a239f20 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55f45a239fa0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55f45a23a020 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55f45a23a0a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55f45a23a2a8 <col:99>
|-FunctionDecl 0x55f45a23a398 <line:3:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55f45a23a6d8 <col:20, col:81>
|   `-CallExpr 0x55f45a23a5f0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x55f45a23a5d8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55f45a23a438 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55f45a23a1e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55f45a23a648 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55f45a23a630 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55f45a23a498 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55f45a23a678 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55f45a23a660 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55f45a23a4f8 <col:41> 'char [18]' lvalue "count_up_down-2.c"
|     |-ImplicitCastExpr 0x55f45a23a690 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55f45a23a528 <col:62> 'int' 3
|     `-ImplicitCastExpr 0x55f45a23a6c0 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55f45a23a6a8 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55f45a23a588 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55f45a23a7c8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55f45a23a708 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55f45a23aaa8 <col:34, line:10:1>
|   |-IfStmt 0x55f45a23aa80 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55f45a23a8c8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55f45a23a8b0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55f45a23a890 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55f45a23a870 <col:9> 'int' lvalue ParmVar 0x55f45a23a708 'cond' 'int'
|   | `-CompoundStmt 0x55f45a23aa68 <col:16, line:8:3>
|   |   `-LabelStmt 0x55f45a23aa50 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55f45a23a9e0 <col:12, col:35>
|   |       |-CallExpr 0x55f45a23a940 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55f45a23a928 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55f45a23a8e0 <col:13> 'void ()' Function 0x55f45a23a398 'reach_error' 'void ()'
|   |       `-CallExpr 0x55f45a23a9c0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55f45a23a9a8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55f45a23a960 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55f45a239e68 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55f45a23aa98 <line:9:3>
|-FunctionDecl 0x55f45a23ab20 <line:11:1, col:37> col:14 used __VERIFIER_nondet_uint 'unsigned int ()'
`-FunctionDecl 0x55f45a23ac10 <line:13:1, line:23:1> line:13:5 main 'int ()'
  `-CompoundStmt 0x55f45a23cbc8 <line:14:1, line:23:1>
    |-DeclStmt 0x55f45a23c7c0 <line:15:3, col:44>
    | `-VarDecl 0x55f45a23c6d0 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x55f45a23c7a0 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x55f45a23c788 <col:20> 'unsigned int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55f45a23c738 <col:20> 'unsigned int ()' Function 0x55f45a23ab20 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |-DeclStmt 0x55f45a23c960 <line:16:3, col:24>
    | |-VarDecl 0x55f45a23c7f0 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x55f45a23c878 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55f45a23c858 <col:18> 'unsigned int' lvalue Var 0x55f45a23c6d0 'n' 'unsigned int'
    | `-VarDecl 0x55f45a23c8a8 <col:3, col:23> col:21 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55f45a23c930 <col:23> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55f45a23c910 <col:23> 'int' 0
    |-WhileStmt 0x55f45a23ca98 <line:17:3, line:21:3>
    | |-BinaryOperator 0x55f45a23c9e8 <line:17:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55f45a23c9b8 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f45a23c978 <col:9> 'unsigned int' lvalue Var 0x55f45a23c7f0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x55f45a23c9d0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55f45a23c998 <col:11> 'int' 0
    | `-CompoundStmt 0x55f45a23ca78 <line:18:3, line:21:3>
    |   |-UnaryOperator 0x55f45a23ca28 <line:19:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x55f45a23ca08 <col:5> 'unsigned int' lvalue Var 0x55f45a23c7f0 'x' 'unsigned int'
    |   `-UnaryOperator 0x55f45a23ca60 <line:20:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x55f45a23ca40 <col:5> 'unsigned int' lvalue Var 0x55f45a23c8a8 'y' 'unsigned int'
    `-CallExpr 0x55f45a23cba0 <line:22:3, col:25> 'void'
      |-ImplicitCastExpr 0x55f45a23cb88 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55f45a23cab0 <col:3> 'void (int)' Function 0x55f45a23a7c8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55f45a23cb40 <col:21, col:24> 'int' '!='
        |-ImplicitCastExpr 0x55f45a23cb10 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x55f45a23cad0 <col:21> 'unsigned int' lvalue Var 0x55f45a23c8a8 'y' 'unsigned int'
        `-ImplicitCastExpr 0x55f45a23cb28 <col:24> 'unsigned int' <LValueToRValue>
          `-DeclRefExpr 0x55f45a23caf0 <col:24> 'unsigned int' lvalue Var 0x55f45a23c6d0 'n' 'unsigned int'
1 warning generated.
