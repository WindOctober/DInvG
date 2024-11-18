./Benchmark/PLDI/SVComp/loops/for_infinite_loop_1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/for_infinite_loop_1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5614e6057ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5614e6058780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5614e6058480 '__int128'
|-TypedefDecl 0x5614e60587f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5614e60584a0 'unsigned __int128'
|-TypedefDecl 0x5614e6058af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5614e60588d0 'struct __NSConstantString_tag'
|   `-Record 0x5614e6058848 '__NSConstantString_tag'
|-TypedefDecl 0x5614e6058b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5614e6058b50 'char *'
|   `-BuiltinType 0x5614e6057f80 'char'
|-TypedefDecl 0x5614e6058e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5614e6058e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5614e6058c70 'struct __va_list_tag'
|     `-Record 0x5614e6058be8 '__va_list_tag'
|-FunctionDecl 0x5614e60b7f18 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/for_infinite_loop_1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5614e60b7fb8 prev 0x5614e60b7f18 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5614e60b8338 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5614e60b8070 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5614e60b80f0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5614e60b8170 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5614e60b81f0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5614e60b83f8 <col:99>
|-FunctionDecl 0x5614e60b84e8 <line:3:1, col:85> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5614e60b8828 <col:20, col:85>
|   `-CallExpr 0x5614e60b8740 <col:22, col:82> 'void'
|     |-ImplicitCastExpr 0x5614e60b8728 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5614e60b8588 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5614e60b8338 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5614e60b8798 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5614e60b8780 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5614e60b85e8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5614e60b87c8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5614e60b87b0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5614e60b8648 <col:41> 'char [22]' lvalue "for_infinite_loop_1.c"
|     |-ImplicitCastExpr 0x5614e60b87e0 <col:66> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5614e60b8678 <col:66> 'int' 3
|     `-ImplicitCastExpr 0x5614e60b8810 <col:69> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5614e60b87f8 <col:69> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5614e60b86d8 <col:69> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5614e60b88d8 prev 0x5614e60b7fb8 <line:5:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5614e60b8a58 <line:6:1, line:8:1> line:6:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x5614e60b8990 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x5614e60b8c00 <col:36, line:8:1>
|   `-IfStmt 0x5614e60b8be8 <line:7:3, col:22>
|     |-UnaryOperator 0x5614e60b8b38 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5614e60b8b20 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5614e60b8b00 <col:7> 'int' lvalue ParmVar 0x5614e60b8990 'cond' 'int'
|     `-CompoundStmt 0x5614e60b8bd0 <col:13, col:22>
|       `-CallExpr 0x5614e60b8bb0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x5614e60b8b98 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5614e60b8b50 <col:14> 'void (void) __attribute__((noreturn))' Function 0x5614e60b88d8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5614e60b8cc0 <line:9:1, line:14:1> line:9:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5614e60b8c30 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5614e60ba7f0 <col:34, line:14:1>
|   |-IfStmt 0x5614e60ba7c8 <line:10:3, line:12:3>
|   | |-UnaryOperator 0x5614e60b8dc0 <line:10:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5614e60b8da8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5614e60b8d88 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5614e60b8d68 <col:9> 'int' lvalue ParmVar 0x5614e60b8c30 'cond' 'int'
|   | `-CompoundStmt 0x5614e60ba7b0 <col:16, line:12:3>
|   |   `-LabelStmt 0x5614e60ba798 <line:11:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5614e60ba728 <col:12, col:35>
|   |       |-CallExpr 0x5614e60ba6b0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5614e60ba698 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5614e60b8dd8 <col:13> 'void ()' Function 0x5614e60b84e8 'reach_error' 'void ()'
|   |       `-CallExpr 0x5614e60ba708 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5614e60ba6f0 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5614e60ba6d0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5614e60b88d8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5614e60ba7e0 <line:13:3>
|-FunctionDecl 0x5614e60ba860 <line:16:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x5614e60ba928 <line:18:1, line:28:1> line:18:5 main 'int ()'
  `-CompoundStmt 0x5614e60bb120 <col:12, line:28:1>
    |-DeclStmt 0x5614e60baa80 <line:19:3, col:19>
    | `-VarDecl 0x5614e60ba9e0 <col:3, col:18> col:16 used i 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x5614e60baa68 <col:18> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x5614e60baa48 <col:18> 'int' 0
    |-DeclStmt 0x5614e60babf0 <line:20:3, col:15>
    | |-VarDecl 0x5614e60baab0 <col:3, col:9> col:7 used x 'int' cinit
    | | `-IntegerLiteral 0x5614e60bab18 <col:9> 'int' 0
    | `-VarDecl 0x5614e60bab50 <col:3, col:14> col:12 y 'int' cinit
    |   `-IntegerLiteral 0x5614e60babb8 <col:14> 'int' 0
    |-DeclStmt 0x5614e60bad10 <line:21:3, col:32>
    | `-VarDecl 0x5614e60bac20 <col:3, col:31> col:7 used n 'int' cinit
    |   `-CallExpr 0x5614e60bacf0 <col:9, col:31> 'int'
    |     `-ImplicitCastExpr 0x5614e60bacd8 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x5614e60bac88 <col:9> 'int ()' Function 0x5614e60ba860 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x5614e60bae08 <line:22:3, col:22>
    | |-UnaryOperator 0x5614e60badc0 <col:7, col:12> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5614e60bada0 <col:8, col:12> 'int'
    | |   `-BinaryOperator 0x5614e60bad80 <col:9, col:11> 'int' '>'
    | |     |-ImplicitCastExpr 0x5614e60bad68 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x5614e60bad28 <col:9> 'int' lvalue Var 0x5614e60bac20 'n' 'int'
    | |     `-IntegerLiteral 0x5614e60bad48 <col:11> 'int' 0
    | `-ReturnStmt 0x5614e60badf8 <col:15, col:22>
    |   `-IntegerLiteral 0x5614e60badd8 <col:22> 'int' 0
    |-ForStmt 0x5614e60bb010 <line:23:3, line:26:3>
    | |-BinaryOperator 0x5614e60bae78 <line:23:7, col:9> 'unsigned int' '='
    | | |-DeclRefExpr 0x5614e60bae20 <col:7> 'unsigned int' lvalue Var 0x5614e60ba9e0 'i' 'unsigned int'
    | | `-ImplicitCastExpr 0x5614e60bae60 <col:9> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x5614e60bae40 <col:9> 'int' 0
    | |-<<<NULL>>>
    | |-IntegerLiteral 0x5614e60bae98 <col:12> 'int' 1
    | |-UnaryOperator 0x5614e60baed8 <col:15, col:16> 'unsigned int' postfix '++'
    | | `-DeclRefExpr 0x5614e60baeb8 <col:15> 'unsigned int' lvalue Var 0x5614e60ba9e0 'i' 'unsigned int'
    | `-CompoundStmt 0x5614e60baff8 <line:24:3, line:26:3>
    |   `-CallExpr 0x5614e60bafd0 <line:25:5, col:27> 'void'
    |     |-ImplicitCastExpr 0x5614e60bafb8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x5614e60baef0 <col:5> 'void (int)' Function 0x5614e60b8cc0 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x5614e60baf68 <col:23, col:26> 'int' '=='
    |       |-ImplicitCastExpr 0x5614e60baf50 <col:23> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x5614e60baf10 <col:23> 'int' lvalue Var 0x5614e60baab0 'x' 'int'
    |       `-IntegerLiteral 0x5614e60baf30 <col:26> 'int' 0
    `-CallExpr 0x5614e60bb0f8 <line:27:3, col:25> 'void'
      |-ImplicitCastExpr 0x5614e60bb0e0 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x5614e60bb048 <col:3> 'void (int)' Function 0x5614e60b8cc0 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x5614e60bb0c0 <col:21, col:24> 'int' '=='
        |-ImplicitCastExpr 0x5614e60bb0a8 <col:21> 'int' <LValueToRValue>
        | `-DeclRefExpr 0x5614e60bb068 <col:21> 'int' lvalue Var 0x5614e60baab0 'x' 'int'
        `-IntegerLiteral 0x5614e60bb088 <col:24> 'int' 0
1 warning generated.
