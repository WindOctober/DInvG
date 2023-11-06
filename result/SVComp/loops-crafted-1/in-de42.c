./Benchmark/PLDI/SVComp/loops-crafted-1/in-de42.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de42.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x557d2fed5e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x557d2fed6730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x557d2fed6430 '__int128'
|-TypedefDecl 0x557d2fed67a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x557d2fed6450 'unsigned __int128'
|-TypedefDecl 0x557d2fed6aa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x557d2fed6880 'struct __NSConstantString_tag'
|   `-Record 0x557d2fed67f8 '__NSConstantString_tag'
|-TypedefDecl 0x557d2fed6b40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x557d2fed6b00 'char *'
|   `-BuiltinType 0x557d2fed5f30 'char'
|-TypedefDecl 0x557d2fed6e38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x557d2fed6de0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x557d2fed6c20 'struct __va_list_tag'
|     `-Record 0x557d2fed6b98 '__va_list_tag'
|-FunctionDecl 0x557d2ff35ee8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de42.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557d2ff35f88 prev 0x557d2ff35ee8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557d2ff36308 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x557d2ff36040 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x557d2ff360c0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x557d2ff36140 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x557d2ff361c0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x557d2ff363c8 <col:99>
|-FunctionDecl 0x557d2ff364b8 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x557d2ff367e8 <col:20, col:73>
|   `-CallExpr 0x557d2ff36700 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x557d2ff366e8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x557d2ff36558 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x557d2ff36308 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x557d2ff36758 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x557d2ff36740 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x557d2ff365b8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x557d2ff36788 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x557d2ff36770 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x557d2ff36618 <col:41> 'char [10]' lvalue "in-de42.c"
|     |-ImplicitCastExpr 0x557d2ff367a0 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x557d2ff36640 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x557d2ff367d0 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x557d2ff367b8 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x557d2ff36698 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x557d2ff368d0 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x557d2ff36a48 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x557d2ff36988 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x557d2ff36d28 <col:34, line:10:1>
|   |-IfStmt 0x557d2ff36d00 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x557d2ff36b48 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x557d2ff36b30 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x557d2ff36b10 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x557d2ff36af0 <col:9> 'int' lvalue ParmVar 0x557d2ff36988 'cond' 'int'
|   | `-CompoundStmt 0x557d2ff36ce8 <col:16, line:8:3>
|   |   `-LabelStmt 0x557d2ff36cd0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x557d2ff36c60 <col:12, col:35>
|   |       |-CallExpr 0x557d2ff36bc0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x557d2ff36ba8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x557d2ff36b60 <col:13> 'void ()' Function 0x557d2ff364b8 'reach_error' 'void ()'
|   |       `-CallExpr 0x557d2ff36c40 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x557d2ff36c28 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x557d2ff36be0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x557d2ff35f88 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x557d2ff36d18 <line:9:3>
`-FunctionDecl 0x557d2ff387f0 <line:12:1, line:43:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x557d2ff392c8 <line:13:1, line:43:1>
    |-DeclStmt 0x557d2ff38990 <line:14:3, col:44>
    | `-VarDecl 0x557d2ff388a8 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x557d2ff38970 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x557d2ff38958 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x557d2ff38910 <col:20> 'unsigned int (void)' Function 0x557d2ff368d0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x557d2ff38bb8 <line:15:3, col:27>
    | |-VarDecl 0x557d2ff389c0 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x557d2ff38a48 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x557d2ff38a28 <col:18> 'unsigned int' lvalue Var 0x557d2ff388a8 'n' 'unsigned int'
    | |-VarDecl 0x557d2ff38a78 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x557d2ff38b00 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x557d2ff38ae0 <col:23> 'int' 0
    | `-VarDecl 0x557d2ff38b30 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x557d2ff38cf0 <line:16:3, line:20:3>
    | |-BinaryOperator 0x557d2ff38c40 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x557d2ff38c10 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x557d2ff38bd0 <col:9> 'unsigned int' lvalue Var 0x557d2ff389c0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x557d2ff38c28 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x557d2ff38bf0 <col:11> 'int' 0
    | `-CompoundStmt 0x557d2ff38cd0 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x557d2ff38c80 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x557d2ff38c60 <col:5> 'unsigned int' lvalue Var 0x557d2ff389c0 'x' 'unsigned int'
    |   `-UnaryOperator 0x557d2ff38cb8 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x557d2ff38c98 <col:5> 'unsigned int' lvalue Var 0x557d2ff38a78 'y' 'unsigned int'
    |-BinaryOperator 0x557d2ff38d60 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x557d2ff38d08 <col:3> 'unsigned int' lvalue Var 0x557d2ff38b30 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x557d2ff38d48 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x557d2ff38d28 <col:7> 'unsigned int' lvalue Var 0x557d2ff38a78 'y' 'unsigned int'
    |-WhileStmt 0x557d2ff38ea0 <line:23:3, line:27:3>
    | |-BinaryOperator 0x557d2ff38df0 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x557d2ff38dc0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x557d2ff38d80 <col:9> 'unsigned int' lvalue Var 0x557d2ff38b30 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x557d2ff38dd8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x557d2ff38da0 <col:11> 'int' 0
    | `-CompoundStmt 0x557d2ff38e80 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x557d2ff38e30 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x557d2ff38e10 <col:5> 'unsigned int' lvalue Var 0x557d2ff389c0 'x' 'unsigned int'
    |   `-UnaryOperator 0x557d2ff38e68 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x557d2ff38e48 <col:5> 'unsigned int' lvalue Var 0x557d2ff38b30 'z' 'unsigned int'
    |-WhileStmt 0x557d2ff38fd8 <line:29:3, line:33:3>
    | |-BinaryOperator 0x557d2ff38f28 <line:29:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x557d2ff38ef8 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x557d2ff38eb8 <col:9> 'unsigned int' lvalue Var 0x557d2ff38a78 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x557d2ff38f10 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x557d2ff38ed8 <col:11> 'int' 0
    | `-CompoundStmt 0x557d2ff38fb8 <line:30:3, line:33:3>
    |   |-UnaryOperator 0x557d2ff38f68 <line:31:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x557d2ff38f48 <col:5> 'unsigned int' lvalue Var 0x557d2ff38a78 'y' 'unsigned int'
    |   `-UnaryOperator 0x557d2ff38fa0 <line:32:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x557d2ff38f80 <col:5> 'unsigned int' lvalue Var 0x557d2ff38b30 'z' 'unsigned int'
    |-WhileStmt 0x557d2ff39110 <line:35:3, line:39:3>
    | |-BinaryOperator 0x557d2ff39060 <line:35:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x557d2ff39030 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x557d2ff38ff0 <col:9> 'unsigned int' lvalue Var 0x557d2ff389c0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x557d2ff39048 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x557d2ff39010 <col:11> 'int' 0
    | `-CompoundStmt 0x557d2ff390f0 <line:36:3, line:39:3>
    |   |-UnaryOperator 0x557d2ff390a0 <line:37:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x557d2ff39080 <col:5> 'unsigned int' lvalue Var 0x557d2ff389c0 'x' 'unsigned int'
    |   `-UnaryOperator 0x557d2ff390d8 <line:38:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x557d2ff390b8 <col:5> 'unsigned int' lvalue Var 0x557d2ff38b30 'z' 'unsigned int'
    |-CallExpr 0x557d2ff39270 <line:41:3, col:27> 'void'
    | |-ImplicitCastExpr 0x557d2ff39258 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x557d2ff39128 <col:3> 'void (int)' Function 0x557d2ff36a48 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x557d2ff39210 <col:21, col:26> 'int' '=='
    |   |-ImplicitCastExpr 0x557d2ff391f8 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x557d2ff39148 <col:21> 'unsigned int' lvalue Var 0x557d2ff38b30 'z' 'unsigned int'
    |   `-BinaryOperator 0x557d2ff391d8 <col:24, col:26> 'unsigned int' '*'
    |     |-ImplicitCastExpr 0x557d2ff391c0 <col:24> 'unsigned int' <IntegralCast>
    |     | `-IntegerLiteral 0x557d2ff39168 <col:24> 'int' 2
    |     `-ImplicitCastExpr 0x557d2ff391a8 <col:26> 'unsigned int' <LValueToRValue>
    |       `-DeclRefExpr 0x557d2ff39188 <col:26> 'unsigned int' lvalue Var 0x557d2ff388a8 'n' 'unsigned int'
    `-ReturnStmt 0x557d2ff392b8 <line:42:3, col:10>
      `-IntegerLiteral 0x557d2ff39298 <col:10> 'int' 0
1 warning generated.
