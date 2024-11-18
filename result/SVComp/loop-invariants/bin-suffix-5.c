./Benchmark/PLDI/SVComp/loop-invariants/bin-suffix-5.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/bin-suffix-5.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5605be62beb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5605be62c750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5605be62c450 '__int128'
|-TypedefDecl 0x5605be62c7c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5605be62c470 'unsigned __int128'
|-TypedefDecl 0x5605be62cac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5605be62c8a0 'struct __NSConstantString_tag'
|   `-Record 0x5605be62c818 '__NSConstantString_tag'
|-TypedefDecl 0x5605be62cb60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5605be62cb20 'char *'
|   `-BuiltinType 0x5605be62bf50 'char'
|-TypedefDecl 0x5605be62ce58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5605be62ce00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5605be62cc40 'struct __va_list_tag'
|     `-Record 0x5605be62cbb8 '__va_list_tag'
|-FunctionDecl 0x5605be68be68 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/bin-suffix-5.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5605be68bf08 prev 0x5605be68be68 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5605be68c288 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5605be68bfc0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5605be68c040 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5605be68c0c0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5605be68c140 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5605be68c348 <col:99>
|-FunctionDecl 0x5605be68c438 <line:3:1, col:78> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5605be68c768 <col:20, col:78>
|   `-CallExpr 0x5605be68c680 <col:22, col:75> 'void'
|     |-ImplicitCastExpr 0x5605be68c668 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5605be68c4d8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5605be68c288 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5605be68c6d8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5605be68c6c0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5605be68c538 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5605be68c708 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5605be68c6f0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5605be68c598 <col:41> 'char [15]' lvalue "bin-suffix-5.c"
|     |-ImplicitCastExpr 0x5605be68c720 <col:59> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5605be68c5c0 <col:59> 'int' 3
|     `-ImplicitCastExpr 0x5605be68c750 <col:62> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5605be68c738 <col:62> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5605be68c618 <col:62> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5605be68c7d0 <line:4:1, col:34> col:12 used __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x5605be68c948 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5605be68c888 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5605be68cc28 <col:34, line:10:1>
|   |-IfStmt 0x5605be68cc00 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x5605be68ca48 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5605be68ca30 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5605be68ca10 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5605be68c9f0 <col:9> 'int' lvalue ParmVar 0x5605be68c888 'cond' 'int'
|   | `-CompoundStmt 0x5605be68cbe8 <col:16, line:8:3>
|   |   `-LabelStmt 0x5605be68cbd0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5605be68cb60 <col:12, col:35>
|   |       |-CallExpr 0x5605be68cac0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5605be68caa8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5605be68ca60 <col:13> 'void ()' Function 0x5605be68c438 'reach_error' 'void ()'
|   |       `-CallExpr 0x5605be68cb40 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5605be68cb28 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5605be68cae0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5605be68bf08 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5605be68cc18 <line:9:3>
`-FunctionDecl 0x5605be68e770 <line:11:1, line:18:1> line:11:5 main 'int (void)'
  `-CompoundStmt 0x5605be68ec08 <col:16, line:18:1>
    |-DeclStmt 0x5605be68e8f0 <line:12:3, col:21>
    | `-VarDecl 0x5605be68e850 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5605be68e8d8 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5605be68e8b8 <col:20> 'int' 5
    |-WhileStmt 0x5605be68ea30 <line:13:3, line:15:3>
    | |-CallExpr 0x5605be68e970 <line:13:10, col:32> 'int'
    | | `-ImplicitCastExpr 0x5605be68e958 <col:10> 'int (*)()' <FunctionToPointerDecay>
    | |   `-DeclRefExpr 0x5605be68e908 <col:10> 'int ()' Function 0x5605be68c7d0 '__VERIFIER_nondet_int' 'int ()'
    | `-CompoundStmt 0x5605be68ea18 <col:35, line:15:3>
    |   `-CompoundAssignOperator 0x5605be68e9e8 <line:14:5, col:10> 'unsigned int' '+=' ComputeLHSTy='unsigned int' ComputeResultTy='unsigned int'
    |     |-DeclRefExpr 0x5605be68e990 <col:5> 'unsigned int' lvalue Var 0x5605be68e850 'x' 'unsigned int'
    |     `-ImplicitCastExpr 0x5605be68e9d0 <col:10> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x5605be68e9b0 <col:10> 'int' 8
    |-CallExpr 0x5605be68ebb0 <line:16:3, col:33> 'void'
    | |-ImplicitCastExpr 0x5605be68eb98 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5605be68ea48 <col:3> 'void (int)' Function 0x5605be68c948 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5605be68eb50 <col:21, col:32> 'int' '=='
    |   |-ParenExpr 0x5605be68eaf8 <col:21, col:27> 'unsigned int'
    |   | `-BinaryOperator 0x5605be68ead8 <col:22, col:26> 'unsigned int' '&'
    |   |   |-ImplicitCastExpr 0x5605be68eaa8 <col:22> 'unsigned int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x5605be68ea68 <col:22> 'unsigned int' lvalue Var 0x5605be68e850 'x' 'unsigned int'
    |   |   `-ImplicitCastExpr 0x5605be68eac0 <col:26> 'unsigned int' <IntegralCast>
    |   |     `-IntegerLiteral 0x5605be68ea88 <col:26> 'int' 5
    |   `-ImplicitCastExpr 0x5605be68eb38 <col:32> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5605be68eb18 <col:32> 'int' 5
    `-ReturnStmt 0x5605be68ebf8 <line:17:3, col:10>
      `-IntegerLiteral 0x5605be68ebd8 <col:10> 'int' 0
1 warning generated.
