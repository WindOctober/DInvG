./Benchmark/PLDI/SVComp/loops/while_infinite_loop_1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/while_infinite_loop_1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5564eafb5ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5564eafb6780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5564eafb6480 '__int128'
|-TypedefDecl 0x5564eafb67f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5564eafb64a0 'unsigned __int128'
|-TypedefDecl 0x5564eafb6af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5564eafb68d0 'struct __NSConstantString_tag'
|   `-Record 0x5564eafb6848 '__NSConstantString_tag'
|-TypedefDecl 0x5564eafb6b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5564eafb6b50 'char *'
|   `-BuiltinType 0x5564eafb5f80 'char'
|-TypedefDecl 0x5564eafb6e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5564eafb6e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5564eafb6c70 'struct __va_list_tag'
|     `-Record 0x5564eafb6be8 '__va_list_tag'
|-FunctionDecl 0x5564eb015e48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/while_infinite_loop_1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5564eb015ee8 prev 0x5564eb015e48 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5564eb016268 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5564eb015fa0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5564eb016020 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5564eb0160a0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5564eb016120 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5564eb016328 <col:99>
|-FunctionDecl 0x5564eb016418 <line:3:1, col:87> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5564eb016758 <col:20, col:87>
|   `-CallExpr 0x5564eb016670 <col:22, col:84> 'void'
|     |-ImplicitCastExpr 0x5564eb016658 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5564eb0164b8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5564eb016268 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5564eb0166c8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5564eb0166b0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5564eb016518 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5564eb0166f8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5564eb0166e0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5564eb016578 <col:41> 'char [24]' lvalue "while_infinite_loop_1.c"
|     |-ImplicitCastExpr 0x5564eb016710 <col:68> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5564eb0165a8 <col:68> 'int' 3
|     `-ImplicitCastExpr 0x5564eb016740 <col:71> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5564eb016728 <col:71> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5564eb016608 <col:71> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5564eb016848 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5564eb016788 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5564eb016b28 <col:34, line:10:1>
|   |-IfStmt 0x5564eb016b00 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x5564eb016948 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5564eb016930 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5564eb016910 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5564eb0168f0 <col:9> 'int' lvalue ParmVar 0x5564eb016788 'cond' 'int'
|   | `-CompoundStmt 0x5564eb016ae8 <col:16, line:8:3>
|   |   `-LabelStmt 0x5564eb016ad0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5564eb016a60 <col:12, col:35>
|   |       |-CallExpr 0x5564eb0169c0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5564eb0169a8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5564eb016960 <col:13> 'void ()' Function 0x5564eb016418 'reach_error' 'void ()'
|   |       `-CallExpr 0x5564eb016a40 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5564eb016a28 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5564eb0169e0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5564eb015ee8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5564eb016b18 <line:9:3>
`-FunctionDecl 0x5564eb016ba0 <line:12:1, line:21:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x5564eb018790 <col:12, line:21:1>
    |-DeclStmt 0x5564eb016ce0 <line:13:3, col:10>
    | `-VarDecl 0x5564eb016c58 <col:3, col:9> col:7 used x 'int' cinit
    |   `-IntegerLiteral 0x5564eb016cc0 <col:9> 'int' 0
    |-WhileStmt 0x5564eb0186a0 <line:15:3, line:18:3>
    | |-IntegerLiteral 0x5564eb016cf8 <line:15:9> 'int' 1
    | `-CompoundStmt 0x5564eb018688 <line:16:3, line:18:3>
    |   `-CallExpr 0x5564eb018660 <line:17:5, col:27> 'void'
    |     |-ImplicitCastExpr 0x5564eb018648 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x5564eb016d18 <col:5> 'void (int)' Function 0x5564eb016848 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x5564eb0185f8 <col:23, col:26> 'int' '=='
    |       |-ImplicitCastExpr 0x5564eb0185e0 <col:23> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x5564eb0185a0 <col:23> 'int' lvalue Var 0x5564eb016c58 'x' 'int'
    |       `-IntegerLiteral 0x5564eb0185c0 <col:26> 'int' 0
    `-CallExpr 0x5564eb018768 <line:20:3, col:25> 'void'
      |-ImplicitCastExpr 0x5564eb018750 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x5564eb0186b8 <col:3> 'void (int)' Function 0x5564eb016848 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x5564eb018730 <col:21, col:24> 'int' '!='
        |-ImplicitCastExpr 0x5564eb018718 <col:21> 'int' <LValueToRValue>
        | `-DeclRefExpr 0x5564eb0186d8 <col:21> 'int' lvalue Var 0x5564eb016c58 'x' 'int'
        `-IntegerLiteral 0x5564eb0186f8 <col:24> 'int' 0
1 warning generated.
