./Benchmark/PLDI/SVComp/loops-crafted-1/in-de41.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de41.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x558ccbc78e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x558ccbc79730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x558ccbc79430 '__int128'
|-TypedefDecl 0x558ccbc797a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x558ccbc79450 'unsigned __int128'
|-TypedefDecl 0x558ccbc79aa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x558ccbc79880 'struct __NSConstantString_tag'
|   `-Record 0x558ccbc797f8 '__NSConstantString_tag'
|-TypedefDecl 0x558ccbc79b40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x558ccbc79b00 'char *'
|   `-BuiltinType 0x558ccbc78f30 'char'
|-TypedefDecl 0x558ccbc79e38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x558ccbc79de0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x558ccbc79c20 'struct __va_list_tag'
|     `-Record 0x558ccbc79b98 '__va_list_tag'
|-FunctionDecl 0x558ccbcd8ee8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de41.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558ccbcd8f88 prev 0x558ccbcd8ee8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558ccbcd9308 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x558ccbcd9040 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x558ccbcd90c0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x558ccbcd9140 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x558ccbcd91c0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x558ccbcd93c8 <col:99>
|-FunctionDecl 0x558ccbcd94b8 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x558ccbcd97e8 <col:20, col:73>
|   `-CallExpr 0x558ccbcd9700 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x558ccbcd96e8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x558ccbcd9558 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x558ccbcd9308 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x558ccbcd9758 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x558ccbcd9740 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x558ccbcd95b8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x558ccbcd9788 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x558ccbcd9770 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x558ccbcd9618 <col:41> 'char [10]' lvalue "in-de41.c"
|     |-ImplicitCastExpr 0x558ccbcd97a0 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x558ccbcd9640 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x558ccbcd97d0 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x558ccbcd97b8 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x558ccbcd9698 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x558ccbcd98d0 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x558ccbcd9a48 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x558ccbcd9988 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x558ccbcd9d28 <col:34, line:10:1>
|   |-IfStmt 0x558ccbcd9d00 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x558ccbcd9b48 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x558ccbcd9b30 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x558ccbcd9b10 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x558ccbcd9af0 <col:9> 'int' lvalue ParmVar 0x558ccbcd9988 'cond' 'int'
|   | `-CompoundStmt 0x558ccbcd9ce8 <col:16, line:8:3>
|   |   `-LabelStmt 0x558ccbcd9cd0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x558ccbcd9c60 <col:12, col:35>
|   |       |-CallExpr 0x558ccbcd9bc0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x558ccbcd9ba8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x558ccbcd9b60 <col:13> 'void ()' Function 0x558ccbcd94b8 'reach_error' 'void ()'
|   |       `-CallExpr 0x558ccbcd9c40 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x558ccbcd9c28 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x558ccbcd9be0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x558ccbcd8f88 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x558ccbcd9d18 <line:9:3>
`-FunctionDecl 0x558ccbcdb7f0 <line:12:1, line:43:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x558ccbcdc278 <line:13:1, line:43:1>
    |-DeclStmt 0x558ccbcdb990 <line:14:3, col:44>
    | `-VarDecl 0x558ccbcdb8a8 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x558ccbcdb970 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x558ccbcdb958 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x558ccbcdb910 <col:20> 'unsigned int (void)' Function 0x558ccbcd98d0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x558ccbcdbbb8 <line:15:3, col:27>
    | |-VarDecl 0x558ccbcdb9c0 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x558ccbcdba48 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x558ccbcdba28 <col:18> 'unsigned int' lvalue Var 0x558ccbcdb8a8 'n' 'unsigned int'
    | |-VarDecl 0x558ccbcdba78 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x558ccbcdbb00 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x558ccbcdbae0 <col:23> 'int' 0
    | `-VarDecl 0x558ccbcdbb30 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x558ccbcdbcf0 <line:16:3, line:20:3>
    | |-BinaryOperator 0x558ccbcdbc40 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x558ccbcdbc10 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558ccbcdbbd0 <col:9> 'unsigned int' lvalue Var 0x558ccbcdb9c0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x558ccbcdbc28 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x558ccbcdbbf0 <col:11> 'int' 0
    | `-CompoundStmt 0x558ccbcdbcd0 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x558ccbcdbc80 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x558ccbcdbc60 <col:5> 'unsigned int' lvalue Var 0x558ccbcdb9c0 'x' 'unsigned int'
    |   `-UnaryOperator 0x558ccbcdbcb8 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x558ccbcdbc98 <col:5> 'unsigned int' lvalue Var 0x558ccbcdba78 'y' 'unsigned int'
    |-BinaryOperator 0x558ccbcdbd60 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x558ccbcdbd08 <col:3> 'unsigned int' lvalue Var 0x558ccbcdbb30 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x558ccbcdbd48 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x558ccbcdbd28 <col:7> 'unsigned int' lvalue Var 0x558ccbcdba78 'y' 'unsigned int'
    |-WhileStmt 0x558ccbcdbea0 <line:23:3, line:27:3>
    | |-BinaryOperator 0x558ccbcdbdf0 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x558ccbcdbdc0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558ccbcdbd80 <col:9> 'unsigned int' lvalue Var 0x558ccbcdbb30 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x558ccbcdbdd8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x558ccbcdbda0 <col:11> 'int' 0
    | `-CompoundStmt 0x558ccbcdbe80 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x558ccbcdbe30 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x558ccbcdbe10 <col:5> 'unsigned int' lvalue Var 0x558ccbcdb9c0 'x' 'unsigned int'
    |   `-UnaryOperator 0x558ccbcdbe68 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x558ccbcdbe48 <col:5> 'unsigned int' lvalue Var 0x558ccbcdbb30 'z' 'unsigned int'
    |-WhileStmt 0x558ccbcdbfd8 <line:29:3, line:33:3>
    | |-BinaryOperator 0x558ccbcdbf28 <line:29:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x558ccbcdbef8 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558ccbcdbeb8 <col:9> 'unsigned int' lvalue Var 0x558ccbcdba78 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x558ccbcdbf10 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x558ccbcdbed8 <col:11> 'int' 0
    | `-CompoundStmt 0x558ccbcdbfb8 <line:30:3, line:33:3>
    |   |-UnaryOperator 0x558ccbcdbf68 <line:31:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x558ccbcdbf48 <col:5> 'unsigned int' lvalue Var 0x558ccbcdba78 'y' 'unsigned int'
    |   `-UnaryOperator 0x558ccbcdbfa0 <line:32:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x558ccbcdbf80 <col:5> 'unsigned int' lvalue Var 0x558ccbcdbb30 'z' 'unsigned int'
    |-WhileStmt 0x558ccbcdc110 <line:35:3, line:39:3>
    | |-BinaryOperator 0x558ccbcdc060 <line:35:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x558ccbcdc030 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558ccbcdbff0 <col:9> 'unsigned int' lvalue Var 0x558ccbcdb9c0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x558ccbcdc048 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x558ccbcdc010 <col:11> 'int' 0
    | `-CompoundStmt 0x558ccbcdc0f0 <line:36:3, line:39:3>
    |   |-UnaryOperator 0x558ccbcdc0a0 <line:37:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x558ccbcdc080 <col:5> 'unsigned int' lvalue Var 0x558ccbcdb9c0 'x' 'unsigned int'
    |   `-UnaryOperator 0x558ccbcdc0d8 <line:38:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x558ccbcdc0b8 <col:5> 'unsigned int' lvalue Var 0x558ccbcdba78 'y' 'unsigned int'
    |-CallExpr 0x558ccbcdc220 <line:41:3, col:25> 'void'
    | |-ImplicitCastExpr 0x558ccbcdc208 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x558ccbcdc128 <col:3> 'void (int)' Function 0x558ccbcd9a48 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x558ccbcdc1b8 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x558ccbcdc188 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x558ccbcdc148 <col:21> 'unsigned int' lvalue Var 0x558ccbcdba78 'y' 'unsigned int'
    |   `-ImplicitCastExpr 0x558ccbcdc1a0 <col:24> 'unsigned int' <LValueToRValue>
    |     `-DeclRefExpr 0x558ccbcdc168 <col:24> 'unsigned int' lvalue Var 0x558ccbcdb8a8 'n' 'unsigned int'
    `-ReturnStmt 0x558ccbcdc268 <line:42:3, col:10>
      `-IntegerLiteral 0x558ccbcdc248 <col:10> 'int' 0
1 warning generated.
