./Benchmark/PLDI/SVComp/loop-invariants/linear-inequality-inv-a.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/linear-inequality-inv-a.c:1:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55d24e842018 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55d24e8428b0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55d24e8425b0 '__int128'
|-TypedefDecl 0x55d24e842920 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55d24e8425d0 'unsigned __int128'
|-TypedefDecl 0x55d24e842c28 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55d24e842a00 'struct __NSConstantString_tag'
|   `-Record 0x55d24e842978 '__NSConstantString_tag'
|-TypedefDecl 0x55d24e842cc0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55d24e842c80 'char *'
|   `-BuiltinType 0x55d24e8420b0 'char'
|-TypedefDecl 0x55d24e842fb8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55d24e842f60 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55d24e842da0 'struct __va_list_tag'
|     `-Record 0x55d24e842d18 '__va_list_tag'
|-FunctionDecl 0x55d24e8a2228 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/linear-inequality-inv-a.c:1:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55d24e8a1f68 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55d24e8a1fe8 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55d24e8a2068 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55d24e8a20e8 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55d24e8a22e8 <col:99>
|-FunctionDecl 0x55d24e8a23d8 <line:2:1, col:89> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55d24e8a2718 <col:20, col:89>
|   `-CallExpr 0x55d24e8a2630 <col:22, col:86> 'void'
|     |-ImplicitCastExpr 0x55d24e8a2618 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55d24e8a2478 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55d24e8a2228 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55d24e8a2688 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d24e8a2670 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d24e8a24d8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55d24e8a26b8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d24e8a26a0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d24e8a2538 <col:41> 'char [26]' lvalue "linear-inequality-inv-a.c"
|     |-ImplicitCastExpr 0x55d24e8a26d0 <col:70> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55d24e8a2570 <col:70> 'int' 2
|     `-ImplicitCastExpr 0x55d24e8a2700 <col:73> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55d24e8a26e8 <col:73> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55d24e8a25c8 <col:73> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55d24e8a2800 <line:3:1, col:50> col:22 used __VERIFIER_nondet_uchar 'unsigned char (void)' extern
`-FunctionDecl 0x55d24e8a28f0 <line:4:1, line:26:1> line:4:5 main 'int ()'
  `-CompoundStmt 0x55d24e8a4bc8 <col:12, line:26:1>
    |-DeclStmt 0x55d24e8a2a90 <line:5:3, col:46>
    | `-VarDecl 0x55d24e8a29a8 <col:3, col:45> col:17 used n 'unsigned char' cinit
    |   `-CallExpr 0x55d24e8a2a70 <col:21, col:45> 'unsigned char'
    |     `-ImplicitCastExpr 0x55d24e8a2a58 <col:21> 'unsigned char (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55d24e8a2a10 <col:21> 'unsigned char (void)' Function 0x55d24e8a2800 '__VERIFIER_nondet_uchar' 'unsigned char (void)'
    |-IfStmt 0x55d24e8a2b80 <line:6:3, line:8:3>
    | |-BinaryOperator 0x55d24e8a2b18 <line:6:7, col:12> 'int' '=='
    | | |-ImplicitCastExpr 0x55d24e8a2b00 <col:7> 'int' <IntegralCast>
    | | | `-ImplicitCastExpr 0x55d24e8a2ae8 <col:7> 'unsigned char' <LValueToRValue>
    | | |   `-DeclRefExpr 0x55d24e8a2aa8 <col:7> 'unsigned char' lvalue Var 0x55d24e8a29a8 'n' 'unsigned char'
    | | `-IntegerLiteral 0x55d24e8a2ac8 <col:12> 'int' 0
    | `-CompoundStmt 0x55d24e8a2b68 <col:15, line:8:3>
    |   `-ReturnStmt 0x55d24e8a2b58 <line:7:5, col:12>
    |     `-IntegerLiteral 0x55d24e8a2b38 <col:12> 'int' 0
    |-DeclStmt 0x55d24e8a2c50 <line:9:3, col:22>
    | `-VarDecl 0x55d24e8a2bb0 <col:3, col:21> col:17 used v 'unsigned char' cinit
    |   `-ImplicitCastExpr 0x55d24e8a2c38 <col:21> 'unsigned char' <IntegralCast>
    |     `-IntegerLiteral 0x55d24e8a2c18 <col:21> 'int' 0
    |-DeclStmt 0x55d24e8a2d20 <line:10:3, col:22>
    | `-VarDecl 0x55d24e8a2c80 <col:3, col:21> col:17 used s 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55d24e8a2d08 <col:21> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55d24e8a2ce8 <col:21> 'int' 0
    |-DeclStmt 0x55d24e8a2df0 <line:11:3, col:22>
    | `-VarDecl 0x55d24e8a2d50 <col:3, col:21> col:17 used i 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x55d24e8a2dd8 <col:21> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x55d24e8a2db8 <col:21> 'int' 0
    |-WhileStmt 0x55d24e8a48a0 <line:12:3, line:16:3>
    | |-BinaryOperator 0x55d24e8a2e90 <line:12:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x55d24e8a2e48 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55d24e8a2e08 <col:10> 'unsigned int' lvalue Var 0x55d24e8a2d50 'i' 'unsigned int'
    | | `-ImplicitCastExpr 0x55d24e8a2e78 <col:14> 'unsigned int' <IntegralCast>
    | |   `-ImplicitCastExpr 0x55d24e8a2e60 <col:14> 'unsigned char' <LValueToRValue>
    | |     `-DeclRefExpr 0x55d24e8a2e28 <col:14> 'unsigned char' lvalue Var 0x55d24e8a29a8 'n' 'unsigned char'
    | `-CompoundStmt 0x55d24e8a4878 <col:17, line:16:3>
    |   |-BinaryOperator 0x55d24e8a2f28 <line:13:5, col:33> 'unsigned char' '='
    |   | |-DeclRefExpr 0x55d24e8a2eb0 <col:5> 'unsigned char' lvalue Var 0x55d24e8a2bb0 'v' 'unsigned char'
    |   | `-CallExpr 0x55d24e8a2f08 <col:9, col:33> 'unsigned char'
    |   |   `-ImplicitCastExpr 0x55d24e8a2ef0 <col:9> 'unsigned char (*)(void)' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x55d24e8a2ed0 <col:9> 'unsigned char (void)' Function 0x55d24e8a2800 '__VERIFIER_nondet_uchar' 'unsigned char (void)'
    |   |-CompoundAssignOperator 0x55d24e8a4810 <line:14:5, col:10> 'unsigned int' '+=' ComputeLHSTy='unsigned int' ComputeResultTy='unsigned int'
    |   | |-DeclRefExpr 0x55d24e8a47a0 <col:5> 'unsigned int' lvalue Var 0x55d24e8a2c80 's' 'unsigned int'
    |   | `-ImplicitCastExpr 0x55d24e8a47f8 <col:10> 'unsigned int' <IntegralCast>
    |   |   `-ImplicitCastExpr 0x55d24e8a47e0 <col:10> 'unsigned char' <LValueToRValue>
    |   |     `-DeclRefExpr 0x55d24e8a47c0 <col:10> 'unsigned char' lvalue Var 0x55d24e8a2bb0 'v' 'unsigned char'
    |   `-UnaryOperator 0x55d24e8a4860 <line:15:5, col:7> 'unsigned int' prefix '++'
    |     `-DeclRefExpr 0x55d24e8a4840 <col:7> 'unsigned int' lvalue Var 0x55d24e8a2d50 'i' 'unsigned int'
    |-IfStmt 0x55d24e8a4a30 <line:17:3, line:20:3>
    | |-BinaryOperator 0x55d24e8a4940 <line:17:7, col:11> 'int' '<'
    | | |-ImplicitCastExpr 0x55d24e8a48f8 <col:7> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55d24e8a48b8 <col:7> 'unsigned int' lvalue Var 0x55d24e8a2c80 's' 'unsigned int'
    | | `-ImplicitCastExpr 0x55d24e8a4928 <col:11> 'unsigned int' <IntegralCast>
    | |   `-ImplicitCastExpr 0x55d24e8a4910 <col:11> 'unsigned char' <LValueToRValue>
    | |     `-DeclRefExpr 0x55d24e8a48d8 <col:11> 'unsigned char' lvalue Var 0x55d24e8a2bb0 'v' 'unsigned char'
    | `-CompoundStmt 0x55d24e8a4a10 <col:14, line:20:3>
    |   |-CallExpr 0x55d24e8a49c0 <line:18:5, col:17> 'void'
    |   | `-ImplicitCastExpr 0x55d24e8a49a8 <col:5> 'void (*)()' <FunctionToPointerDecay>
    |   |   `-DeclRefExpr 0x55d24e8a4960 <col:5> 'void ()' Function 0x55d24e8a23d8 'reach_error' 'void ()'
    |   `-ReturnStmt 0x55d24e8a4a00 <line:19:5, col:12>
    |     `-IntegerLiteral 0x55d24e8a49e0 <col:12> 'int' 1
    |-IfStmt 0x55d24e8a4b80 <line:21:3, line:24:3>
    | |-BinaryOperator 0x55d24e8a4ab8 <line:21:7, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55d24e8a4a88 <col:7> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55d24e8a4a48 <col:7> 'unsigned int' lvalue Var 0x55d24e8a2c80 's' 'unsigned int'
    | | `-ImplicitCastExpr 0x55d24e8a4aa0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x55d24e8a4a68 <col:11> 'int' 65025
    | `-CompoundStmt 0x55d24e8a4b60 <col:18, line:24:3>
    |   |-CallExpr 0x55d24e8a4b10 <line:22:5, col:17> 'void'
    |   | `-ImplicitCastExpr 0x55d24e8a4af8 <col:5> 'void (*)()' <FunctionToPointerDecay>
    |   |   `-DeclRefExpr 0x55d24e8a4ad8 <col:5> 'void ()' Function 0x55d24e8a23d8 'reach_error' 'void ()'
    |   `-ReturnStmt 0x55d24e8a4b50 <line:23:5, col:12>
    |     `-IntegerLiteral 0x55d24e8a4b30 <col:12> 'int' 1
    `-ReturnStmt 0x55d24e8a4bb8 <line:25:3, col:10>
      `-IntegerLiteral 0x55d24e8a4b98 <col:10> 'int' 0
1 warning generated.
