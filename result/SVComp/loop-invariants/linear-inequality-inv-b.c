./Benchmark/PLDI/SVComp/loop-invariants/linear-inequality-inv-b.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/linear-inequality-inv-b.c:1:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/linear-inequality-inv-b.c:21:9: warning: result of comparison of constant 65025 with expression of type 'unsigned char' is always false [-Wtautological-constant-out-of-range-compare]
  if (s > 65025) {
      ~ ^ ~~~~~
TranslationUnitDecl 0x561778cf7018 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x561778cf78b0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x561778cf75b0 '__int128'
|-TypedefDecl 0x561778cf7920 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x561778cf75d0 'unsigned __int128'
|-TypedefDecl 0x561778cf7c28 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x561778cf7a00 'struct __NSConstantString_tag'
|   `-Record 0x561778cf7978 '__NSConstantString_tag'
|-TypedefDecl 0x561778cf7cc0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x561778cf7c80 'char *'
|   `-BuiltinType 0x561778cf70b0 'char'
|-TypedefDecl 0x561778cf7fb8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x561778cf7f60 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x561778cf7da0 'struct __va_list_tag'
|     `-Record 0x561778cf7d18 '__va_list_tag'
|-FunctionDecl 0x561778d57228 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/linear-inequality-inv-b.c:1:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x561778d56f68 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x561778d56fe8 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x561778d57068 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x561778d570e8 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x561778d572e8 <col:99>
|-FunctionDecl 0x561778d573d8 <line:2:1, col:89> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x561778d57718 <col:20, col:89>
|   `-CallExpr 0x561778d57630 <col:22, col:86> 'void'
|     |-ImplicitCastExpr 0x561778d57618 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x561778d57478 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x561778d57228 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x561778d57688 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x561778d57670 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x561778d574d8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x561778d576b8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x561778d576a0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x561778d57538 <col:41> 'char [26]' lvalue "linear-inequality-inv-b.c"
|     |-ImplicitCastExpr 0x561778d576d0 <col:70> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x561778d57570 <col:70> 'int' 2
|     `-ImplicitCastExpr 0x561778d57700 <col:73> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x561778d576e8 <col:73> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x561778d575c8 <col:73> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x561778d57800 <line:3:1, col:50> col:22 used __VERIFIER_nondet_uchar 'unsigned char (void)' extern
`-FunctionDecl 0x561778d578f0 <line:4:1, line:26:1> line:4:5 main 'int ()'
  `-CompoundStmt 0x561778d59be8 <col:12, line:26:1>
    |-DeclStmt 0x561778d57a90 <line:5:3, col:46>
    | `-VarDecl 0x561778d579a8 <col:3, col:45> col:17 used n 'unsigned char' cinit
    |   `-CallExpr 0x561778d57a70 <col:21, col:45> 'unsigned char'
    |     `-ImplicitCastExpr 0x561778d57a58 <col:21> 'unsigned char (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x561778d57a10 <col:21> 'unsigned char (void)' Function 0x561778d57800 '__VERIFIER_nondet_uchar' 'unsigned char (void)'
    |-IfStmt 0x561778d57b80 <line:6:3, line:8:3>
    | |-BinaryOperator 0x561778d57b18 <line:6:7, col:12> 'int' '=='
    | | |-ImplicitCastExpr 0x561778d57b00 <col:7> 'int' <IntegralCast>
    | | | `-ImplicitCastExpr 0x561778d57ae8 <col:7> 'unsigned char' <LValueToRValue>
    | | |   `-DeclRefExpr 0x561778d57aa8 <col:7> 'unsigned char' lvalue Var 0x561778d579a8 'n' 'unsigned char'
    | | `-IntegerLiteral 0x561778d57ac8 <col:12> 'int' 0
    | `-CompoundStmt 0x561778d57b68 <col:15, line:8:3>
    |   `-ReturnStmt 0x561778d57b58 <line:7:5, col:12>
    |     `-IntegerLiteral 0x561778d57b38 <col:12> 'int' 0
    |-DeclStmt 0x561778d57c50 <line:9:3, col:22>
    | `-VarDecl 0x561778d57bb0 <col:3, col:21> col:17 used v 'unsigned char' cinit
    |   `-ImplicitCastExpr 0x561778d57c38 <col:21> 'unsigned char' <IntegralCast>
    |     `-IntegerLiteral 0x561778d57c18 <col:21> 'int' 0
    |-DeclStmt 0x561778d57d20 <line:10:3, col:22>
    | `-VarDecl 0x561778d57c80 <col:3, col:21> col:17 used s 'unsigned char' cinit
    |   `-ImplicitCastExpr 0x561778d57d08 <col:21> 'unsigned char' <IntegralCast>
    |     `-IntegerLiteral 0x561778d57ce8 <col:21> 'int' 0
    |-DeclStmt 0x561778d57df0 <line:11:3, col:22>
    | `-VarDecl 0x561778d57d50 <col:3, col:21> col:17 used i 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x561778d57dd8 <col:21> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x561778d57db8 <col:21> 'int' 0
    |-WhileStmt 0x561778d598a0 <line:12:3, line:16:3>
    | |-BinaryOperator 0x561778d57e90 <line:12:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x561778d57e48 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x561778d57e08 <col:10> 'unsigned int' lvalue Var 0x561778d57d50 'i' 'unsigned int'
    | | `-ImplicitCastExpr 0x561778d57e78 <col:14> 'unsigned int' <IntegralCast>
    | |   `-ImplicitCastExpr 0x561778d57e60 <col:14> 'unsigned char' <LValueToRValue>
    | |     `-DeclRefExpr 0x561778d57e28 <col:14> 'unsigned char' lvalue Var 0x561778d579a8 'n' 'unsigned char'
    | `-CompoundStmt 0x561778d59878 <col:17, line:16:3>
    |   |-BinaryOperator 0x561778d57f28 <line:13:5, col:33> 'unsigned char' '='
    |   | |-DeclRefExpr 0x561778d57eb0 <col:5> 'unsigned char' lvalue Var 0x561778d57bb0 'v' 'unsigned char'
    |   | `-CallExpr 0x561778d57f08 <col:9, col:33> 'unsigned char'
    |   |   `-ImplicitCastExpr 0x561778d57ef0 <col:9> 'unsigned char (*)(void)' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x561778d57ed0 <col:9> 'unsigned char (void)' Function 0x561778d57800 '__VERIFIER_nondet_uchar' 'unsigned char (void)'
    |   |-CompoundAssignOperator 0x561778d59810 <line:14:5, col:10> 'unsigned char' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   | |-DeclRefExpr 0x561778d597a0 <col:5> 'unsigned char' lvalue Var 0x561778d57c80 's' 'unsigned char'
    |   | `-ImplicitCastExpr 0x561778d597f8 <col:10> 'int' <IntegralCast>
    |   |   `-ImplicitCastExpr 0x561778d597e0 <col:10> 'unsigned char' <LValueToRValue>
    |   |     `-DeclRefExpr 0x561778d597c0 <col:10> 'unsigned char' lvalue Var 0x561778d57bb0 'v' 'unsigned char'
    |   `-UnaryOperator 0x561778d59860 <line:15:5, col:7> 'unsigned int' prefix '++'
    |     `-DeclRefExpr 0x561778d59840 <col:7> 'unsigned int' lvalue Var 0x561778d57d50 'i' 'unsigned int'
    |-IfStmt 0x561778d59a50 <line:17:3, line:20:3>
    | |-BinaryOperator 0x561778d59958 <line:17:7, col:11> 'int' '<'
    | | |-ImplicitCastExpr 0x561778d59928 <col:7> 'int' <IntegralCast>
    | | | `-ImplicitCastExpr 0x561778d598f8 <col:7> 'unsigned char' <LValueToRValue>
    | | |   `-DeclRefExpr 0x561778d598b8 <col:7> 'unsigned char' lvalue Var 0x561778d57c80 's' 'unsigned char'
    | | `-ImplicitCastExpr 0x561778d59940 <col:11> 'int' <IntegralCast>
    | |   `-ImplicitCastExpr 0x561778d59910 <col:11> 'unsigned char' <LValueToRValue>
    | |     `-DeclRefExpr 0x561778d598d8 <col:11> 'unsigned char' lvalue Var 0x561778d57bb0 'v' 'unsigned char'
    | `-CompoundStmt 0x561778d59a30 <col:14, line:20:3>
    |   |-CallExpr 0x561778d599e0 <line:18:5, col:17> 'void'
    |   | `-ImplicitCastExpr 0x561778d599c8 <col:5> 'void (*)()' <FunctionToPointerDecay>
    |   |   `-DeclRefExpr 0x561778d59978 <col:5> 'void ()' Function 0x561778d573d8 'reach_error' 'void ()'
    |   `-ReturnStmt 0x561778d59a20 <line:19:5, col:12>
    |     `-IntegerLiteral 0x561778d59a00 <col:12> 'int' 1
    |-IfStmt 0x561778d59ba0 <line:21:3, line:24:3>
    | |-BinaryOperator 0x561778d59ad8 <line:21:7, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x561778d59ac0 <col:7> 'int' <IntegralCast>
    | | | `-ImplicitCastExpr 0x561778d59aa8 <col:7> 'unsigned char' <LValueToRValue>
    | | |   `-DeclRefExpr 0x561778d59a68 <col:7> 'unsigned char' lvalue Var 0x561778d57c80 's' 'unsigned char'
    | | `-IntegerLiteral 0x561778d59a88 <col:11> 'int' 65025
    | `-CompoundStmt 0x561778d59b80 <col:18, line:24:3>
    |   |-CallExpr 0x561778d59b30 <line:22:5, col:17> 'void'
    |   | `-ImplicitCastExpr 0x561778d59b18 <col:5> 'void (*)()' <FunctionToPointerDecay>
    |   |   `-DeclRefExpr 0x561778d59af8 <col:5> 'void ()' Function 0x561778d573d8 'reach_error' 'void ()'
    |   `-ReturnStmt 0x561778d59b70 <line:23:5, col:12>
    |     `-IntegerLiteral 0x561778d59b50 <col:12> 'int' 1
    `-ReturnStmt 0x561778d59bd8 <line:25:3, col:10>
      `-IntegerLiteral 0x561778d59bb8 <col:10> 'int' 0
2 warnings generated.
