./Benchmark/PLDI/SVComp/loop-acceleration/multivar_1-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/multivar_1-2.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x56546d5c1ef8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x56546d5c2790 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x56546d5c2490 '__int128'
|-TypedefDecl 0x56546d5c2800 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x56546d5c24b0 'unsigned __int128'
|-TypedefDecl 0x56546d5c2b08 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x56546d5c28e0 'struct __NSConstantString_tag'
|   `-Record 0x56546d5c2858 '__NSConstantString_tag'
|-TypedefDecl 0x56546d5c2ba0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x56546d5c2b60 'char *'
|   `-BuiltinType 0x56546d5c1f90 'char'
|-TypedefDecl 0x56546d5c2e98 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x56546d5c2e40 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x56546d5c2c80 'struct __va_list_tag'
|     `-Record 0x56546d5c2bf8 '__va_list_tag'
|-FunctionDecl 0x56546d621ec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-acceleration/multivar_1-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56546d621f68 prev 0x56546d621ec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56546d6222e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x56546d622020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x56546d6220a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x56546d622120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x56546d6221a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x56546d6223a8 <col:99>
|-FunctionDecl 0x56546d622498 <line:3:1, col:78> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x56546d6227c8 <col:20, col:78>
|   `-CallExpr 0x56546d6226e0 <col:22, col:75> 'void'
|     |-ImplicitCastExpr 0x56546d6226c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x56546d622538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x56546d6222e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x56546d622738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56546d622720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56546d622598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x56546d622768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56546d622750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56546d6225f8 <col:41> 'char [15]' lvalue "multivar_1-2.c"
|     |-ImplicitCastExpr 0x56546d622780 <col:59> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x56546d622620 <col:59> 'int' 3
|     `-ImplicitCastExpr 0x56546d6227b0 <col:62> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x56546d622798 <col:62> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x56546d622678 <col:62> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x56546d6228b0 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x56546d622a28 <line:6:1, line:11:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x56546d622968 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x56546d622d08 <col:34, line:11:1>
|   |-IfStmt 0x56546d622ce0 <line:7:3, line:9:3>
|   | |-UnaryOperator 0x56546d622b28 <line:7:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x56546d622b10 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x56546d622af0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x56546d622ad0 <col:9> 'int' lvalue ParmVar 0x56546d622968 'cond' 'int'
|   | `-CompoundStmt 0x56546d622cc8 <col:16, line:9:3>
|   |   `-LabelStmt 0x56546d622cb0 <line:8:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x56546d622c40 <col:12, col:35>
|   |       |-CallExpr 0x56546d622ba0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x56546d622b88 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x56546d622b40 <col:13> 'void ()' Function 0x56546d622498 'reach_error' 'void ()'
|   |       `-CallExpr 0x56546d622c20 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x56546d622c08 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x56546d622bc0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x56546d621f68 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x56546d622cf8 <line:10:3>
`-FunctionDecl 0x56546d6247f8 <line:13:1, line:23:1> line:13:5 main 'int (void)'
  `-CompoundStmt 0x56546d624d68 <col:16, line:23:1>
    |-DeclStmt 0x56546d6249d0 <line:14:3, col:44>
    | `-VarDecl 0x56546d6248e0 <col:3, col:43> col:16 used x 'unsigned int' cinit
    |   `-CallExpr 0x56546d6249b0 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x56546d624998 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x56546d624948 <col:20> 'unsigned int (void)' Function 0x56546d6228b0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x56546d624af8 <line:15:3, col:25>
    | `-VarDecl 0x56546d624a00 <col:3, col:24> col:16 used y 'unsigned int' cinit
    |   `-BinaryOperator 0x56546d624ad8 <col:20, col:24> 'unsigned int' '+'
    |     |-ImplicitCastExpr 0x56546d624aa8 <col:20> 'unsigned int' <LValueToRValue>
    |     | `-DeclRefExpr 0x56546d624a68 <col:20> 'unsigned int' lvalue Var 0x56546d6248e0 'x' 'unsigned int'
    |     `-ImplicitCastExpr 0x56546d624ac0 <col:24> 'unsigned int' <IntegralCast>
    |       `-IntegerLiteral 0x56546d624a88 <col:24> 'int' 1
    |-WhileStmt 0x56546d624c30 <line:17:3, line:20:3>
    | |-BinaryOperator 0x56546d624b80 <line:17:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x56546d624b50 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x56546d624b10 <col:10> 'unsigned int' lvalue Var 0x56546d6248e0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x56546d624b68 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x56546d624b30 <col:14> 'int' 1024
    | `-CompoundStmt 0x56546d624c10 <col:20, line:20:3>
    |   |-UnaryOperator 0x56546d624bc0 <line:18:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x56546d624ba0 <col:5> 'unsigned int' lvalue Var 0x56546d6248e0 'x' 'unsigned int'
    |   `-UnaryOperator 0x56546d624bf8 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x56546d624bd8 <col:5> 'unsigned int' lvalue Var 0x56546d624a00 'y' 'unsigned int'
    `-CallExpr 0x56546d624d40 <line:22:3, col:27> 'void'
      |-ImplicitCastExpr 0x56546d624d28 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x56546d624c48 <col:3> 'void (int)' Function 0x56546d622a28 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x56546d624cd8 <col:21, col:26> 'int' '=='
        |-ImplicitCastExpr 0x56546d624ca8 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x56546d624c68 <col:21> 'unsigned int' lvalue Var 0x56546d6248e0 'x' 'unsigned int'
        `-ImplicitCastExpr 0x56546d624cc0 <col:26> 'unsigned int' <LValueToRValue>
          `-DeclRefExpr 0x56546d624c88 <col:26> 'unsigned int' lvalue Var 0x56546d624a00 'y' 'unsigned int'
1 warning generated.
