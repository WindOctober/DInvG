./Benchmark/PLDI/SVComp/loops-crafted-1/in-de32.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de32.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x560dca93ee98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x560dca93f730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x560dca93f430 '__int128'
|-TypedefDecl 0x560dca93f7a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x560dca93f450 'unsigned __int128'
|-TypedefDecl 0x560dca93faa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x560dca93f880 'struct __NSConstantString_tag'
|   `-Record 0x560dca93f7f8 '__NSConstantString_tag'
|-TypedefDecl 0x560dca93fb40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x560dca93fb00 'char *'
|   `-BuiltinType 0x560dca93ef30 'char'
|-TypedefDecl 0x560dca93fe38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x560dca93fde0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x560dca93fc20 'struct __va_list_tag'
|     `-Record 0x560dca93fb98 '__va_list_tag'
|-FunctionDecl 0x560dca99eec8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/in-de32.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x560dca99ef68 prev 0x560dca99eec8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x560dca99f2e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x560dca99f020 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x560dca99f0a0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x560dca99f120 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x560dca99f1a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x560dca99f3a8 <col:99>
|-FunctionDecl 0x560dca99f498 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x560dca99f7c8 <col:20, col:73>
|   `-CallExpr 0x560dca99f6e0 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x560dca99f6c8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x560dca99f538 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x560dca99f2e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x560dca99f738 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x560dca99f720 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x560dca99f598 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x560dca99f768 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x560dca99f750 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x560dca99f5f8 <col:41> 'char [10]' lvalue "in-de32.c"
|     |-ImplicitCastExpr 0x560dca99f780 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x560dca99f620 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x560dca99f7b0 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x560dca99f798 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x560dca99f678 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x560dca99f8b0 <line:4:1, col:48> col:21 used __VERIFIER_nondet_uint 'unsigned int (void)' extern
|-FunctionDecl 0x560dca99fa28 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x560dca99f968 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x560dca99fd08 <col:34, line:10:1>
|   |-IfStmt 0x560dca99fce0 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x560dca99fb28 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x560dca99fb10 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x560dca99faf0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x560dca99fad0 <col:9> 'int' lvalue ParmVar 0x560dca99f968 'cond' 'int'
|   | `-CompoundStmt 0x560dca99fcc8 <col:16, line:8:3>
|   |   `-LabelStmt 0x560dca99fcb0 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x560dca99fc40 <col:12, col:35>
|   |       |-CallExpr 0x560dca99fba0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x560dca99fb88 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x560dca99fb40 <col:13> 'void ()' Function 0x560dca99f498 'reach_error' 'void ()'
|   |       `-CallExpr 0x560dca99fc20 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x560dca99fc08 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x560dca99fbc0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x560dca99ef68 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x560dca99fcf8 <line:9:3>
`-FunctionDecl 0x560dca9a17d0 <line:12:1, line:37:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x560dca9a2118 <line:13:1, line:37:1>
    |-DeclStmt 0x560dca9a1970 <line:14:3, col:44>
    | `-VarDecl 0x560dca9a1888 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x560dca9a1950 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x560dca9a1938 <col:20> 'unsigned int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x560dca9a18f0 <col:20> 'unsigned int (void)' Function 0x560dca99f8b0 '__VERIFIER_nondet_uint' 'unsigned int (void)'
    |-DeclStmt 0x560dca9a1b98 <line:15:3, col:27>
    | |-VarDecl 0x560dca9a19a0 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x560dca9a1a28 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x560dca9a1a08 <col:18> 'unsigned int' lvalue Var 0x560dca9a1888 'n' 'unsigned int'
    | |-VarDecl 0x560dca9a1a58 <col:3, col:23> col:21 used y 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x560dca9a1ae0 <col:23> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x560dca9a1ac0 <col:23> 'int' 0
    | `-VarDecl 0x560dca9a1b10 <col:3, col:26> col:26 used z 'unsigned int'
    |-WhileStmt 0x560dca9a1cd0 <line:16:3, line:20:3>
    | |-BinaryOperator 0x560dca9a1c20 <line:16:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x560dca9a1bf0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x560dca9a1bb0 <col:9> 'unsigned int' lvalue Var 0x560dca9a19a0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x560dca9a1c08 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x560dca9a1bd0 <col:11> 'int' 0
    | `-CompoundStmt 0x560dca9a1cb0 <line:17:3, line:20:3>
    |   |-UnaryOperator 0x560dca9a1c60 <line:18:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x560dca9a1c40 <col:5> 'unsigned int' lvalue Var 0x560dca9a19a0 'x' 'unsigned int'
    |   `-UnaryOperator 0x560dca9a1c98 <line:19:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x560dca9a1c78 <col:5> 'unsigned int' lvalue Var 0x560dca9a1a58 'y' 'unsigned int'
    |-BinaryOperator 0x560dca9a1d40 <line:22:3, col:7> 'unsigned int' '='
    | |-DeclRefExpr 0x560dca9a1ce8 <col:3> 'unsigned int' lvalue Var 0x560dca9a1b10 'z' 'unsigned int'
    | `-ImplicitCastExpr 0x560dca9a1d28 <col:7> 'unsigned int' <LValueToRValue>
    |   `-DeclRefExpr 0x560dca9a1d08 <col:7> 'unsigned int' lvalue Var 0x560dca9a1a58 'y' 'unsigned int'
    |-WhileStmt 0x560dca9a1e80 <line:23:3, line:27:3>
    | |-BinaryOperator 0x560dca9a1dd0 <line:23:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x560dca9a1da0 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x560dca9a1d60 <col:9> 'unsigned int' lvalue Var 0x560dca9a1b10 'z' 'unsigned int'
    | | `-ImplicitCastExpr 0x560dca9a1db8 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x560dca9a1d80 <col:11> 'int' 0
    | `-CompoundStmt 0x560dca9a1e60 <line:24:3, line:27:3>
    |   |-UnaryOperator 0x560dca9a1e10 <line:25:5, col:6> 'unsigned int' postfix '++'
    |   | `-DeclRefExpr 0x560dca9a1df0 <col:5> 'unsigned int' lvalue Var 0x560dca9a19a0 'x' 'unsigned int'
    |   `-UnaryOperator 0x560dca9a1e48 <line:26:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x560dca9a1e28 <col:5> 'unsigned int' lvalue Var 0x560dca9a1b10 'z' 'unsigned int'
    |-WhileStmt 0x560dca9a1fb8 <line:29:3, line:33:3>
    | |-BinaryOperator 0x560dca9a1f08 <line:29:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x560dca9a1ed8 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x560dca9a1e98 <col:9> 'unsigned int' lvalue Var 0x560dca9a1a58 'y' 'unsigned int'
    | | `-ImplicitCastExpr 0x560dca9a1ef0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x560dca9a1eb8 <col:11> 'int' 0
    | `-CompoundStmt 0x560dca9a1f98 <line:30:3, line:33:3>
    |   |-UnaryOperator 0x560dca9a1f48 <line:31:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x560dca9a1f28 <col:5> 'unsigned int' lvalue Var 0x560dca9a19a0 'x' 'unsigned int'
    |   `-UnaryOperator 0x560dca9a1f80 <line:32:5, col:6> 'unsigned int' postfix '--'
    |     `-DeclRefExpr 0x560dca9a1f60 <col:5> 'unsigned int' lvalue Var 0x560dca9a1a58 'y' 'unsigned int'
    |-CallExpr 0x560dca9a20c0 <line:35:3, col:25> 'void'
    | |-ImplicitCastExpr 0x560dca9a20a8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x560dca9a1fd0 <col:3> 'void (int)' Function 0x560dca99fa28 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x560dca9a2060 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x560dca9a2030 <col:21> 'unsigned int' <LValueToRValue>
    |   | `-DeclRefExpr 0x560dca9a1ff0 <col:21> 'unsigned int' lvalue Var 0x560dca9a19a0 'x' 'unsigned int'
    |   `-ImplicitCastExpr 0x560dca9a2048 <col:24> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x560dca9a2010 <col:24> 'int' 0
    `-ReturnStmt 0x560dca9a2108 <line:36:3, col:10>
      `-IntegerLiteral 0x560dca9a20e8 <col:10> 'int' 0
1 warning generated.
