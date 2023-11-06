./Benchmark/PLDI/SVComp/loop-acceleration/multivar_1-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/multivar_1-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5623aca39ef8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5623aca3a790 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5623aca3a490 '__int128'
|-TypedefDecl 0x5623aca3a800 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5623aca3a4b0 'unsigned __int128'
|-TypedefDecl 0x5623aca3ab08 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5623aca3a8e0 'struct __NSConstantString_tag'
|   `-Record 0x5623aca3a858 '__NSConstantString_tag'
|-TypedefDecl 0x5623aca3aba0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5623aca3ab60 'char *'
|   `-BuiltinType 0x5623aca39f90 'char'
|-TypedefDecl 0x5623aca3ae98 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5623aca3ae40 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5623aca3ac80 'struct __va_list_tag'
|     `-Record 0x5623aca3abf8 '__va_list_tag'
|-FunctionDecl 0x5623aca99ec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/multivar_1-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5623aca99f68 prev 0x5623aca99ec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5623aca9a2e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5623aca9a020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5623aca9a0a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5623aca9a120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5623aca9a1a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5623aca9a3a8 <col:99>
|-FunctionDecl 0x5623aca9a498 <line:3:1, col:78> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5623aca9a7c8 <col:20, col:78>
|   `-CallExpr 0x5623aca9a6e0 <col:22, col:75> 'void'
|     |-ImplicitCastExpr 0x5623aca9a6c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5623aca9a538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5623aca9a2e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5623aca9a738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5623aca9a720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5623aca9a598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5623aca9a768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5623aca9a750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5623aca9a5f8 <col:41> 'char [15]' lvalue "multivar_1-1.c"
|     |-ImplicitCastExpr 0x5623aca9a780 <col:59> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5623aca9a620 <col:59> 'int' 3
|     `-ImplicitCastExpr 0x5623aca9a7b0 <col:62> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5623aca9a798 <col:62> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5623aca9a678 <col:62> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5623aca9a8b0 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x5623aca9aa28 <line:6:1, line:11:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5623aca9a968 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5623aca9ad08 <col:34, line:11:1>
|   |-IfStmt 0x5623aca9ace0 <line:7:3, line:9:3>
|   | |-UnaryOperator 0x5623aca9ab28 <line:7:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5623aca9ab10 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5623aca9aaf0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5623aca9aad0 <col:9> 'int' lvalue ParmVar 0x5623aca9a968 'cond' 'int'
|   | `-CompoundStmt 0x5623aca9acc8 <col:16, line:9:3>
|   |   `-LabelStmt 0x5623aca9acb0 <line:8:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5623aca9ac40 <col:12, col:35>
|   |       |-CallExpr 0x5623aca9aba0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5623aca9ab88 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5623aca9ab40 <col:13> 'void ()' Function 0x5623aca9a498 'reach_error' 'void ()'
|   |       `-CallExpr 0x5623aca9ac20 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5623aca9ac08 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5623aca9abc0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5623aca99f68 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5623aca9acf8 <line:10:3>
`-FunctionDecl 0x5623aca9c7f8 <line:13:1, line:23:1> line:13:5 main 'int (void)'
  `-CompoundStmt 0x5623aca9cd08 <col:16, line:23:1>
    |-DeclStmt 0x5623aca9c9d0 <line:14:3, col:44>
    | `-VarDecl 0x5623aca9c8e0 <col:3, col:43> col:16 used x 'unsigned int' cinit
    |   `-CallExpr 0x5623aca9c9b0 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x5623aca9c998 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5623aca9c948 <col:20> 'unsigned int (void)' Function 0x5623aca9a8b0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x5623aca9caa0 <line:15:3, col:21>
    | `-VarDecl 0x5623aca9ca00 <col:3, col:20> col:16 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5623aca9ca88 <col:20> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x5623aca9ca68 <col:20> 'unsigned int' lvalue Var 0x5623aca9c8e0 'x' 'unsigned int'
    |-WhileStmt 0x5623aca9cbd8 <line:17:3, line:20:3>
    | |-BinaryOperator 0x5623aca9cb28 <line:17:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x5623aca9caf8 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5623aca9cab8 <col:10> 'unsigned int' lvalue Var 0x5623aca9c8e0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x5623aca9cb10 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5623aca9cad8 <col:14> 'int' 1024
    | `-CompoundStmt 0x5623aca9cbb8 <col:20, line:20:3>
    |   |-UnaryOperator 0x5623aca9cb68 <line:18:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x5623aca9cb48 <col:5> 'unsigned int' lvalue Var 0x5623aca9c8e0 'x' 'unsigned int'
    |   `-UnaryOperator 0x5623aca9cba0 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x5623aca9cb80 <col:5> 'unsigned int' lvalue Var 0x5623aca9ca00 'y' 'unsigned int'
    `-CallExpr 0x5623aca9cce0 <line:22:3, col:27> 'void'
      |-ImplicitCastExpr 0x5623aca9ccc8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x5623aca9cbf0 <col:3> 'void (int)' Function 0x5623aca9aa28 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x5623aca9cc80 <col:21, col:26> 'int' '=='
        |-ImplicitCastExpr 0x5623aca9cc50 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x5623aca9cc10 <col:21> 'unsigned int' lvalue Var 0x5623aca9c8e0 'x' 'unsigned int'
        `-ImplicitCastExpr 0x5623aca9cc68 <col:26> 'unsigned int' <LValueToRValue>
          `-DeclRefExpr 0x5623aca9cc30 <col:26> 'unsigned int' lvalue Var 0x5623aca9ca00 'y' 'unsigned int'
1 warning generated.
