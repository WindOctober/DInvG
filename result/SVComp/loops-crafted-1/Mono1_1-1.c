./Benchmark/PLDI/SVComp/loops-crafted-1/Mono1_1-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono1_1-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x557e96e8aeb8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x557e96e8b750 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x557e96e8b450 '__int128'
|-TypedefDecl 0x557e96e8b7c0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x557e96e8b470 'unsigned __int128'
|-TypedefDecl 0x557e96e8bac8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x557e96e8b8a0 'struct __NSConstantString_tag'
|   `-Record 0x557e96e8b818 '__NSConstantString_tag'
|-TypedefDecl 0x557e96e8bb60 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x557e96e8bb20 'char *'
|   `-BuiltinType 0x557e96e8af50 'char'
|-TypedefDecl 0x557e96e8be58 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x557e96e8be00 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x557e96e8bc40 'struct __va_list_tag'
|     `-Record 0x557e96e8bbb8 '__va_list_tag'
|-FunctionDecl 0x557e96eeae58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono1_1-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557e96eeaef8 prev 0x557e96eeae58 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557e96eeb278 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x557e96eeafb0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x557e96eeb030 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x557e96eeb0b0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x557e96eeb130 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x557e96eeb338 <col:99>
|-FunctionDecl 0x557e96eeb428 <line:3:1, col:75> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x557e96eeb728 <col:20, col:75>
|   `-CallExpr 0x557e96eeb640 <col:22, col:72> 'void'
|     |-ImplicitCastExpr 0x557e96eeb628 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x557e96eeb4c8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x557e96eeb278 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x557e96eeb698 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x557e96eeb680 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x557e96eeb528 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x557e96eeb6c8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x557e96eeb6b0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x557e96eeb588 <col:41> 'char [12]' lvalue "Mono1_1-1.c"
|     |-ImplicitCastExpr 0x557e96eeb6e0 <col:56> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x557e96eeb5b0 <col:56> 'int' 3
|     `-ImplicitCastExpr 0x557e96eeb710 <col:59> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x557e96eeb6f8 <col:59> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x557e96eeb5d0 <col:59> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x557e96eeb818 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x557e96eeb758 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x557e96eebae8 <col:34, col:84>
|   `-IfStmt 0x557e96eebad0 <col:36, col:82>
|     |-UnaryOperator 0x557e96eeb918 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x557e96eeb900 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x557e96eeb8e0 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x557e96eeb8c0 <col:41> 'int' lvalue ParmVar 0x557e96eeb758 'cond' 'int'
|     `-CompoundStmt 0x557e96eebab8 <col:48, col:82>
|       `-LabelStmt 0x557e96eebaa0 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x557e96eeba30 <col:57, col:80>
|           |-CallExpr 0x557e96eeb990 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x557e96eeb978 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x557e96eeb930 <col:58> 'void ()' Function 0x557e96eeb428 'reach_error' 'void ()'
|           `-CallExpr 0x557e96eeba10 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x557e96eeb9f8 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x557e96eeb9b0 <col:72> 'void (void) __attribute__((noreturn))' Function 0x557e96eeaef8 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x557e96eebbd0 <line:5:1, line:17:1> line:5:5 main 'int (void)'
  `-CompoundStmt 0x557e96eedaf8 <col:16, line:17:1>
    |-DeclStmt 0x557e96eed760 <line:6:3, col:21>
    | `-VarDecl 0x557e96eebcb0 <col:3, col:20> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x557e96eebd38 <col:20> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x557e96eebd18 <col:20> 'int' 0
    |-WhileStmt 0x557e96eed9c8 <line:8:3, line:14:3>
    | |-BinaryOperator 0x557e96eed7e8 <line:8:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x557e96eed7b8 <col:10> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x557e96eed778 <col:10> 'unsigned int' lvalue Var 0x557e96eebcb0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x557e96eed7d0 <col:14> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x557e96eed798 <col:14> 'int' 100000000
    | `-CompoundStmt 0x557e96eed9b0 <col:25, line:14:3>
    |   `-IfStmt 0x557e96eed988 <line:9:5, line:13:5> has_else
    |     |-BinaryOperator 0x557e96eed878 <line:9:9, col:13> 'int' '<'
    |     | |-ImplicitCastExpr 0x557e96eed848 <col:9> 'unsigned int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x557e96eed808 <col:9> 'unsigned int' lvalue Var 0x557e96eebcb0 'x' 'unsigned int'
    |     | `-ImplicitCastExpr 0x557e96eed860 <col:13> 'unsigned int' <IntegralCast>
    |     |   `-IntegerLiteral 0x557e96eed828 <col:13> 'int' 10000000
    |     |-CompoundStmt 0x557e96eed8d0 <col:23, line:11:5>
    |     | `-UnaryOperator 0x557e96eed8b8 <line:10:7, col:8> 'unsigned int' postfix '++'
    |     |   `-DeclRefExpr 0x557e96eed898 <col:7> 'unsigned int' lvalue Var 0x557e96eebcb0 'x' 'unsigned int'
    |     `-CompoundStmt 0x557e96eed970 <line:11:12, line:13:5>
    |       `-CompoundAssignOperator 0x557e96eed940 <line:12:7, col:12> 'unsigned int' '+=' ComputeLHSTy='unsigned int' ComputeResultTy='unsigned int'
    |         |-DeclRefExpr 0x557e96eed8e8 <col:7> 'unsigned int' lvalue Var 0x557e96eebcb0 'x' 'unsigned int'
    |         `-ImplicitCastExpr 0x557e96eed928 <col:12> 'unsigned int' <IntegralCast>
    |           `-IntegerLiteral 0x557e96eed908 <col:12> 'int' 2
    `-CallExpr 0x557e96eedad0 <line:16:3, col:35> 'void'
      |-ImplicitCastExpr 0x557e96eedab8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x557e96eed9e0 <col:3> 'void (int)' Function 0x557e96eeb818 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x557e96eeda70 <col:21, col:26> 'int' '=='
        |-ImplicitCastExpr 0x557e96eeda40 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x557e96eeda00 <col:21> 'unsigned int' lvalue Var 0x557e96eebcb0 'x' 'unsigned int'
        `-ImplicitCastExpr 0x557e96eeda58 <col:26> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x557e96eeda20 <col:26> 'int' 100000001
1 warning generated.
