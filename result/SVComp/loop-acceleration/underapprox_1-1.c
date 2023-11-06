./Benchmark/PLDI/SVComp/loop-acceleration/underapprox_1-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/underapprox_1-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x555af800ef28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x555af800f7c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x555af800f4c0 '__int128'
|-TypedefDecl 0x555af800f830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x555af800f4e0 'unsigned __int128'
|-TypedefDecl 0x555af800fb38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x555af800f910 'struct __NSConstantString_tag'
|   `-Record 0x555af800f888 '__NSConstantString_tag'
|-TypedefDecl 0x555af800fbd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x555af800fb90 'char *'
|   `-BuiltinType 0x555af800efc0 'char'
|-TypedefDecl 0x555af800fec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x555af800fe70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x555af800fcb0 'struct __va_list_tag'
|     `-Record 0x555af800fc28 '__va_list_tag'
|-FunctionDecl 0x555af806eeb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/underapprox_1-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x555af806ef58 prev 0x555af806eeb8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x555af806f2d8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x555af806f010 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x555af806f090 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x555af806f110 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x555af806f190 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x555af806f398 <col:99>
|-FunctionDecl 0x555af806f488 <line:3:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x555af806f7c8 <col:20, col:81>
|   `-CallExpr 0x555af806f6e0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x555af806f6c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x555af806f528 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x555af806f2d8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x555af806f738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x555af806f720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x555af806f588 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x555af806f768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x555af806f750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x555af806f5e8 <col:41> 'char [18]' lvalue "underapprox_1-1.c"
|     |-ImplicitCastExpr 0x555af806f780 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x555af806f618 <col:62> 'int' 3
|     `-ImplicitCastExpr 0x555af806f7b0 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x555af806f798 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x555af806f678 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x555af806f8b8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x555af806f7f8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x555af806fb98 <col:34, line:10:1>
|   |-IfStmt 0x555af806fb70 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x555af806f9b8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x555af806f9a0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x555af806f980 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x555af806f960 <col:9> 'int' lvalue ParmVar 0x555af806f7f8 'cond' 'int'
|   | `-CompoundStmt 0x555af806fb58 <col:16, line:8:3>
|   |   `-LabelStmt 0x555af806fb40 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x555af806fad0 <col:12, col:35>
|   |       |-CallExpr 0x555af806fa30 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x555af806fa18 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x555af806f9d0 <col:13> 'void ()' Function 0x555af806f488 'reach_error' 'void ()'
|   |       `-CallExpr 0x555af806fab0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x555af806fa98 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x555af806fa50 <col:27> 'void (void) __attribute__((noreturn))' Function 0x555af806ef58 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x555af806fb88 <line:9:3>
`-FunctionDecl 0x555af806fc80 <line:12:1, line:22:1> line:12:5 main 'int (void)'
  `-CompoundStmt 0x555af8071be8 <col:16, line:22:1>
    |-DeclStmt 0x555af8071860 <line:13:3, col:21>
    | `-VarDecl 0x555af80717c0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x555af8071848 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x555af8071828 <col:20> 'int' 0
    |-DeclStmt 0x555af8071930 <line:14:3, col:21>
    | `-VarDecl 0x555af8071890 <col:3, col:20> col:16 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x555af8071918 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x555af80718f8 <col:20> 'int' 1
    |-WhileStmt 0x555af8071ab8 <line:16:3, line:19:3>
    | |-BinaryOperator 0x555af80719b8 <line:16:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x555af8071988 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x555af8071948 <col:10> 'unsigned int' lvalue Var 0x555af80717c0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x555af80719a0 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x555af8071968 <col:14> 'int' 6
    | `-CompoundStmt 0x555af8071a98 <col:17, line:19:3>
    |   |-UnaryOperator 0x555af80719f8 <line:17:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x555af80719d8 <col:5> 'unsigned int' lvalue Var 0x555af80717c0 'x' 'unsigned int'
    |   `-CompoundAssignOperator 0x555af8071a68 <line:18:5, col:10> 'unsigned int' '*=' ComputeLHSTy='unsigned int' ComputeResultTy='unsigned int'
    |     |-DeclRefExpr 0x555af8071a10 <col:5> 'unsigned int' lvalue Var 0x555af8071890 'y' 'unsigned int'
    |     `-ImplicitCastExpr 0x555af8071a50 <col:10> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x555af8071a30 <col:10> 'int' 2
    `-CallExpr 0x555af8071bc0 <line:21:3, col:28> 'void'
      |-ImplicitCastExpr 0x555af8071ba8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x555af8071ad0 <col:3> 'void (int)' Function 0x555af806f8b8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x555af8071b60 <col:21, col:26> 'int' '!='
        |-ImplicitCastExpr 0x555af8071b30 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x555af8071af0 <col:21> 'unsigned int' lvalue Var 0x555af8071890 'y' 'unsigned int'
        `-ImplicitCastExpr 0x555af8071b48 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x555af8071b10 <col:26> 'int' 64
1 warning generated.
