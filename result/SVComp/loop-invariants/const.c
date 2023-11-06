./Benchmark/PLDI/SVComp/loop-invariants/const.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/const.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x563a13325dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x563a13326660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x563a13326360 '__int128'
|-TypedefDecl 0x563a133266d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x563a13326380 'unsigned __int128'
|-TypedefDecl 0x563a133269d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x563a133267b0 'struct __NSConstantString_tag'
|   `-Record 0x563a13326728 '__NSConstantString_tag'
|-TypedefDecl 0x563a13326a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x563a13326a30 'char *'
|   `-BuiltinType 0x563a13325e60 'char'
|-TypedefDecl 0x563a13326d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x563a13326d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x563a13326b50 'struct __va_list_tag'
|     `-Record 0x563a13326ac8 '__va_list_tag'
|-FunctionDecl 0x563a13385da8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invariants/const.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x563a13385e48 prev 0x563a13385da8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x563a133861c8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x563a13385f00 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x563a13385f80 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x563a13386000 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x563a13386080 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x563a13386288 <col:99>
|-FunctionDecl 0x563a13386378 <line:3:1, col:71> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x563a133866a8 <col:20, col:71>
|   `-CallExpr 0x563a133865c0 <col:22, col:68> 'void'
|     |-ImplicitCastExpr 0x563a133865a8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x563a13386418 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x563a133861c8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x563a13386618 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x563a13386600 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x563a13386478 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x563a13386648 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x563a13386630 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x563a133864d8 <col:41> 'char [8]' lvalue "const.c"
|     |-ImplicitCastExpr 0x563a13386660 <col:52> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x563a133864f8 <col:52> 'int' 3
|     `-ImplicitCastExpr 0x563a13386690 <col:55> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x563a13386678 <col:55> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x563a13386558 <col:55> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x563a13386790 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x563a13386908 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x563a13386848 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x563a13386be8 <col:34, line:10:1>
|   |-IfStmt 0x563a13386bc0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x563a13386a08 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x563a133869f0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x563a133869d0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x563a133869b0 <col:9> 'int' lvalue ParmVar 0x563a13386848 'cond' 'int'
|   | `-CompoundStmt 0x563a13386ba8 <col:16, line:8:3>
|   |   `-LabelStmt 0x563a13386b90 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x563a13386b20 <col:12, col:35>
|   |       |-CallExpr 0x563a13386a80 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x563a13386a68 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x563a13386a20 <col:13> 'void ()' Function 0x563a13386378 'reach_error' 'void ()'
|   |       `-CallExpr 0x563a13386b00 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x563a13386ae8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x563a13386aa0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x563a13385e48 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x563a13386bd8 <line:9:3>
`-FunctionDecl 0x563a133886d8 <line:11:1, line:22:1> line:11:5 main 'int (void)'
  `-CompoundStmt 0x563a13388c00 <col:16, line:22:1>
    |-DeclStmt 0x563a13388860 <line:12:3, col:21>
    | `-VarDecl 0x563a133887c0 <col:3, col:20> col:16 used s 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x563a13388848 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x563a13388828 <col:20> 'int' 0
    |-WhileStmt 0x563a13388bb8 <line:13:3, line:20:3>
    | |-CallExpr 0x563a133888e0 <line:13:10, col:33> 'unsigned int'
    | | `-ImplicitCastExpr 0x563a133888c8 <col:10> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    | |   `-DeclRefExpr 0x563a13388878 <col:10> 'unsigned int (void)' Function 0x563a13386790 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    | `-CompoundStmt 0x563a13388b98 <col:36, line:20:3>
    |   |-IfStmt 0x563a133889e0 <line:14:5, line:16:5>
    |   | |-BinaryOperator 0x563a13388970 <line:14:9, col:14> 'int' '!='
    |   | | |-ImplicitCastExpr 0x563a13388940 <col:9> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x563a13388900 <col:9> 'unsigned int' lvalue Var 0x563a133887c0 's' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x563a13388958 <col:14> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x563a13388920 <col:14> 'int' 0
    |   | `-CompoundStmt 0x563a133889c8 <col:17, line:16:5>
    |   |   `-UnaryOperator 0x563a133889b0 <line:15:7, col:9> 'unsigned int' prefix '++'
    |   |     `-DeclRefExpr 0x563a13388990 <col:9> 'unsigned int' lvalue Var 0x563a133887c0 's' 'unsigned int'
    |   `-IfStmt 0x563a13388b80 <line:17:5, line:19:5>
    |     |-CallExpr 0x563a13388a30 <line:17:9, col:32> 'unsigned int'
    |     | `-ImplicitCastExpr 0x563a13388a18 <col:9> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |     |   `-DeclRefExpr 0x563a133889f8 <col:9> 'unsigned int (void)' Function 0x563a13386790 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |     `-CompoundStmt 0x563a13388b68 <col:35, line:19:5>
    |       `-CallExpr 0x563a13388b40 <line:18:7, col:31> 'void'
    |         |-ImplicitCastExpr 0x563a13388b28 <col:7> 'void (*)(int)' <FunctionToPointerDecay>
    |         | `-DeclRefExpr 0x563a13388a50 <col:7> 'void (int)' Function 0x563a13386908 '__VERIFIER_assert' 'void (int)'
    |         `-BinaryOperator 0x563a13388ae0 <col:25, col:30> 'int' '=='
    |           |-ImplicitCastExpr 0x563a13388ab0 <col:25> 'unsigned int' <LValueToRValue>
    |           | `-DeclRefExpr 0x563a13388a70 <col:25> 'unsigned int' lvalue Var 0x563a133887c0 's' 'unsigned int'
    |           `-ImplicitCastExpr 0x563a13388ac8 <col:30> 'unsigned int' <IntegralCast>
    |             `-IntegerLiteral 0x563a13388a90 <col:30> 'int' 0
    `-ReturnStmt 0x563a13388bf0 <line:21:3, col:10>
      `-IntegerLiteral 0x563a13388bd0 <col:10> 'int' 0
1 warning generated.
