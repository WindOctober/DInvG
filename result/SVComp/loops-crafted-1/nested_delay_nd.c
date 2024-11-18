./Benchmark/PLDI/SVComp/loops-crafted-1/nested_delay_nd.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/nested_delay_nd.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55d9f2fcbf28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55d9f2fcc7c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55d9f2fcc4c0 '__int128'
|-TypedefDecl 0x55d9f2fcc830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55d9f2fcc4e0 'unsigned __int128'
|-TypedefDecl 0x55d9f2fccb38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55d9f2fcc910 'struct __NSConstantString_tag'
|   `-Record 0x55d9f2fcc888 '__NSConstantString_tag'
|-TypedefDecl 0x55d9f2fccbd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55d9f2fccb90 'char *'
|   `-BuiltinType 0x55d9f2fcbfc0 'char'
|-TypedefDecl 0x55d9f2fccec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55d9f2fcce70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55d9f2fcccb0 'struct __va_list_tag'
|     `-Record 0x55d9f2fccc28 '__va_list_tag'
|-FunctionDecl 0x55d9f302c078 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/nested_delay_nd.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55d9f302c118 prev 0x55d9f302c078 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55d9f302c498 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55d9f302c1d0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55d9f302c250 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55d9f302c2d0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55d9f302c350 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55d9f302c558 <col:99>
|-FunctionDecl 0x55d9f302c648 <line:3:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55d9f302c988 <col:20, col:81>
|   `-CallExpr 0x55d9f302c8a0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x55d9f302c888 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55d9f302c6e8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55d9f302c498 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55d9f302c8f8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d9f302c8e0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d9f302c748 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55d9f302c928 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d9f302c910 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d9f302c7a8 <col:41> 'char [18]' lvalue "nested_delay_nd.c"
|     |-ImplicitCastExpr 0x55d9f302c940 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55d9f302c7d8 <col:62> 'int' 3
|     `-ImplicitCastExpr 0x55d9f302c970 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55d9f302c958 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55d9f302c838 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55d9f302ca38 prev 0x55d9f302c118 <line:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55d9f302cbb8 <line:5:1, line:7:1> line:5:6 used assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55d9f302caf0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55d9f302cd60 <col:36, line:7:1>
|   `-IfStmt 0x55d9f302cd48 <line:6:3, col:22>
|     |-UnaryOperator 0x55d9f302cc98 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55d9f302cc80 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55d9f302cc60 <col:7> 'int' lvalue ParmVar 0x55d9f302caf0 'cond' 'int'
|     `-CompoundStmt 0x55d9f302cd30 <col:13, col:22>
|       `-CallExpr 0x55d9f302cd10 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55d9f302ccf8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55d9f302ccb0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55d9f302ca38 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55d9f302ce40 <line:8:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-VarDecl 0x55d9f302cef8 <line:9:1, col:5> col:5 used last 'int'
|-FunctionDecl 0x55d9f302e860 <line:10:1, line:15:1> line:10:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55d9f302e7d0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55d9f302eb20 <col:34, line:15:1>
|   |-IfStmt 0x55d9f302eaf8 <line:11:3, line:13:3>
|   | |-UnaryOperator 0x55d9f302e960 <line:11:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55d9f302e948 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55d9f302e928 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55d9f302e908 <col:9> 'int' lvalue ParmVar 0x55d9f302e7d0 'cond' 'int'
|   | `-CompoundStmt 0x55d9f302eae0 <col:16, line:13:3>
|   |   `-LabelStmt 0x55d9f302eac8 <line:12:6, col:36> 'ERROR'
|   |     `-CompoundStmt 0x55d9f302ea58 <col:13, col:36>
|   |       |-CallExpr 0x55d9f302e9e0 <col:14, col:26> 'void'
|   |       | `-ImplicitCastExpr 0x55d9f302e9c8 <col:14> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55d9f302e978 <col:14> 'void ()' Function 0x55d9f302c648 'reach_error' 'void ()'
|   |       `-CallExpr 0x55d9f302ea38 <col:28, col:34> 'void'
|   |         `-ImplicitCastExpr 0x55d9f302ea20 <col:28> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55d9f302ea00 <col:28> 'void (void) __attribute__((noreturn))' Function 0x55d9f302ca38 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55d9f302eb10 <line:14:3>
|-VarDecl 0x55d9f302eb58 <line:18:1, col:12> col:5 used SIZE 'int' cinit
| `-IntegerLiteral 0x55d9f302ebc0 <col:12> 'int' 200000
`-FunctionDecl 0x55d9f302ec30 <line:20:1, line:47:1> line:20:5 main 'int ()'
  `-CompoundStmt 0x55d9f30306e8 <line:21:1, line:47:1>
    |-BinaryOperator 0x55d9f302ed70 <line:22:2, col:31> 'int' '='
    | |-DeclRefExpr 0x55d9f302ecd0 <col:2> 'int' lvalue Var 0x55d9f302cef8 'last' 'int'
    | `-CallExpr 0x55d9f302ed50 <col:9, col:31> 'int'
    |   `-ImplicitCastExpr 0x55d9f302ed38 <col:9> 'int (*)(void)' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55d9f302ecf0 <col:9> 'int (void)' Function 0x55d9f302ce40 '__VERIFIER_nondet_int' 'int (void)'
    |-CallExpr 0x55d9f302ee70 <line:23:2, col:30> 'void'
    | |-ImplicitCastExpr 0x55d9f302ee58 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55d9f302ed90 <col:2> 'void (int)' Function 0x55d9f302cbb8 'assume_abort_if_not' 'void (int)'
    | `-BinaryOperator 0x55d9f302ee08 <col:22, col:29> 'int' '>'
    |   |-ImplicitCastExpr 0x55d9f302edf0 <col:22> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55d9f302edb0 <col:22> 'int' lvalue Var 0x55d9f302cef8 'last' 'int'
    |   `-IntegerLiteral 0x55d9f302edd0 <col:29> 'int' 0
    |-DeclStmt 0x55d9f302f1e8 <line:24:2, col:26>
    | |-VarDecl 0x55d9f302eeb0 <col:2, col:8> col:6 used a 'int' cinit
    | | `-IntegerLiteral 0x55d9f302ef18 <col:8> 'int' 0
    | |-VarDecl 0x55d9f302ef50 <col:2, col:12> col:10 used b 'int' cinit
    | | `-IntegerLiteral 0x55d9f302efb8 <col:12> 'int' 0
    | |-VarDecl 0x55d9f302eff0 <col:2, col:16> col:14 used c 'int' cinit
    | | `-IntegerLiteral 0x55d9f302f058 <col:16> 'int' 0
    | |-VarDecl 0x55d9f302f090 <col:2, col:21> col:18 used st 'int' cinit
    | | `-IntegerLiteral 0x55d9f302f0f8 <col:21> 'int' 0
    | `-VarDecl 0x55d9f302f130 <col:2, col:25> col:23 used d 'int' cinit
    |   `-IntegerLiteral 0x55d9f302f198 <col:25> 'int' 0
    |-WhileStmt 0x55d9f30306a0 <line:25:2, line:45:2>
    | |-IntegerLiteral 0x55d9f302f200 <line:25:8> 'int' 1
    | `-CompoundStmt 0x55d9f3030660 <col:11, line:45:2>
    |   |-BinaryOperator 0x55d9f302f260 <line:26:3, col:6> 'int' '='
    |   | |-DeclRefExpr 0x55d9f302f220 <col:3> 'int' lvalue Var 0x55d9f302f090 'st' 'int'
    |   | `-IntegerLiteral 0x55d9f302f240 <col:6> 'int' 1
    |   |-ForStmt 0x55d9f302f4e0 <line:27:3, line:29:3>
    |   | |-BinaryOperator 0x55d9f302f2c0 <line:27:7, col:9> 'int' '='
    |   | | |-DeclRefExpr 0x55d9f302f280 <col:7> 'int' lvalue Var 0x55d9f302eff0 'c' 'int'
    |   | | `-IntegerLiteral 0x55d9f302f2a0 <col:9> 'int' 0
    |   | |-<<<NULL>>>
    |   | |-BinaryOperator 0x55d9f302f350 <col:11, col:13> 'int' '<'
    |   | | |-ImplicitCastExpr 0x55d9f302f320 <col:11> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55d9f302f2e0 <col:11> 'int' lvalue Var 0x55d9f302eff0 'c' 'int'
    |   | | `-ImplicitCastExpr 0x55d9f302f338 <col:13> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x55d9f302f300 <col:13> 'int' lvalue Var 0x55d9f302eb58 'SIZE' 'int'
    |   | |-UnaryOperator 0x55d9f302f390 <col:18, col:19> 'int' postfix '++'
    |   | | `-DeclRefExpr 0x55d9f302f370 <col:18> 'int' lvalue Var 0x55d9f302eff0 'c' 'int'
    |   | `-CompoundStmt 0x55d9f302f4c8 <col:23, line:29:3>
    |   |   `-IfStmt 0x55d9f302f4b0 <line:28:4, col:28>
    |   |     |-BinaryOperator 0x55d9f302f418 <col:8, col:11> 'int' '>='
    |   |     | |-ImplicitCastExpr 0x55d9f302f3e8 <col:8> 'int' <LValueToRValue>
    |   |     | | `-DeclRefExpr 0x55d9f302f3a8 <col:8> 'int' lvalue Var 0x55d9f302eff0 'c' 'int'
    |   |     | `-ImplicitCastExpr 0x55d9f302f400 <col:11> 'int' <LValueToRValue>
    |   |     |   `-DeclRefExpr 0x55d9f302f3c8 <col:11> 'int' lvalue Var 0x55d9f302cef8 'last' 'int'
    |   |     `-CompoundStmt 0x55d9f302f498 <col:18, col:28>
    |   |       `-BinaryOperator 0x55d9f302f478 <col:20, col:25> 'int' '='
    |   |         |-DeclRefExpr 0x55d9f302f438 <col:20> 'int' lvalue Var 0x55d9f302f090 'st' 'int'
    |   |         `-IntegerLiteral 0x55d9f302f458 <col:25> 'int' 0
    |   |-IfStmt 0x55d9f302ff60 <line:30:3, line:32:22> has_else
    |   | |-BinaryOperator 0x55d9f302f660 <line:30:6, col:23> 'int' '&&'
    |   | | |-BinaryOperator 0x55d9f302f570 <col:6, col:10> 'int' '=='
    |   | | | |-ImplicitCastExpr 0x55d9f302f558 <col:6> 'int' <LValueToRValue>
    |   | | | | `-DeclRefExpr 0x55d9f302f518 <col:6> 'int' lvalue Var 0x55d9f302f090 'st' 'int'
    |   | | | `-IntegerLiteral 0x55d9f302f538 <col:10> 'int' 0
    |   | | `-BinaryOperator 0x55d9f302f640 <col:15, col:23> 'int' '=='
    |   | |   |-ImplicitCastExpr 0x55d9f302f628 <col:15> 'int' <LValueToRValue>
    |   | |   | `-DeclRefExpr 0x55d9f302f590 <col:15> 'int' lvalue Var 0x55d9f302eff0 'c' 'int'
    |   | |   `-BinaryOperator 0x55d9f302f608 <col:18, col:23> 'int' '+'
    |   | |     |-ImplicitCastExpr 0x55d9f302f5f0 <col:18> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x55d9f302f5b0 <col:18> 'int' lvalue Var 0x55d9f302cef8 'last' 'int'
    |   | |     `-IntegerLiteral 0x55d9f302f5d0 <col:23> 'int' 1
    |   | |-CompoundStmt 0x55d9f302f760 <col:25, line:31:15>
    |   | | |-CompoundAssignOperator 0x55d9f302f6c0 <col:4, col:7> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   | | | |-DeclRefExpr 0x55d9f302f680 <col:4> 'int' lvalue Var 0x55d9f302eeb0 'a' 'int'
    |   | | | `-IntegerLiteral 0x55d9f302f6a0 <col:7> 'int' 3
    |   | | `-CompoundAssignOperator 0x55d9f302f730 <col:10, col:13> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   | |   |-DeclRefExpr 0x55d9f302f6f0 <col:10> 'int' lvalue Var 0x55d9f302ef50 'b' 'int'
    |   | |   `-IntegerLiteral 0x55d9f302f710 <col:13> 'int' 3
    |   | `-CompoundStmt 0x55d9f302ff40 <line:32:8, col:22>
    |   |   |-CompoundAssignOperator 0x55d9f302fea0 <col:10, col:13> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   |   | |-DeclRefExpr 0x55d9f302f780 <col:10> 'int' lvalue Var 0x55d9f302eeb0 'a' 'int'
    |   |   | `-IntegerLiteral 0x55d9f302f7a0 <col:13> 'int' 2
    |   |   `-CompoundAssignOperator 0x55d9f302ff10 <col:16, col:19> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
    |   |     |-DeclRefExpr 0x55d9f302fed0 <col:16> 'int' lvalue Var 0x55d9f302ef50 'b' 'int'
    |   |     `-IntegerLiteral 0x55d9f302fef0 <col:19> 'int' 2
    |   |-IfStmt 0x55d9f3030310 <line:33:3, line:38:3> has_else
    |   | |-BinaryOperator 0x55d9f3030090 <line:33:6, col:21> 'int' '&&'
    |   | | |-BinaryOperator 0x55d9f302fff8 <col:6, col:9> 'int' '=='
    |   | | | |-ImplicitCastExpr 0x55d9f302ffc8 <col:6> 'int' <LValueToRValue>
    |   | | | | `-DeclRefExpr 0x55d9f302ff88 <col:6> 'int' lvalue Var 0x55d9f302eff0 'c' 'int'
    |   | | | `-ImplicitCastExpr 0x55d9f302ffe0 <col:9> 'int' <LValueToRValue>
    |   | | |   `-DeclRefExpr 0x55d9f302ffa8 <col:9> 'int' lvalue Var 0x55d9f302cef8 'last' 'int'
    |   | | `-BinaryOperator 0x55d9f3030070 <col:17, col:21> 'int' '=='
    |   | |   |-ImplicitCastExpr 0x55d9f3030058 <col:17> 'int' <LValueToRValue>
    |   | |   | `-DeclRefExpr 0x55d9f3030018 <col:17> 'int' lvalue Var 0x55d9f302f090 'st' 'int'
    |   | |   `-IntegerLiteral 0x55d9f3030038 <col:21> 'int' 0
    |   | |-CompoundStmt 0x55d9f3030168 <col:24, line:35:3>
    |   | | `-BinaryOperator 0x55d9f3030148 <line:34:4, col:10> 'int' '='
    |   | |   |-DeclRefExpr 0x55d9f30300b0 <col:4> 'int' lvalue Var 0x55d9f302eeb0 'a' 'int'
    |   | |   `-BinaryOperator 0x55d9f3030128 <col:8, col:10> 'int' '+'
    |   | |     |-ImplicitCastExpr 0x55d9f3030110 <col:8> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x55d9f30300d0 <col:8> 'int' lvalue Var 0x55d9f302eeb0 'a' 'int'
    |   | |     `-IntegerLiteral 0x55d9f30300f0 <col:10> 'int' 1
    |   | `-IfStmt 0x55d9f30302f8 <line:36:8, line:38:3>
    |   |   |-BinaryOperator 0x55d9f3030288 <line:36:11, col:25> 'int' '&&'
    |   |   | |-BinaryOperator 0x55d9f30301d8 <col:11, col:15> 'int' '=='
    |   |   | | |-ImplicitCastExpr 0x55d9f30301c0 <col:11> 'int' <LValueToRValue>
    |   |   | | | `-DeclRefExpr 0x55d9f3030180 <col:11> 'int' lvalue Var 0x55d9f302f090 'st' 'int'
    |   |   | | `-IntegerLiteral 0x55d9f30301a0 <col:15> 'int' 1
    |   |   | `-BinaryOperator 0x55d9f3030268 <col:20, col:25> 'int' '<'
    |   |   |   |-ImplicitCastExpr 0x55d9f3030238 <col:20> 'int' <LValueToRValue>
    |   |   |   | `-DeclRefExpr 0x55d9f30301f8 <col:20> 'int' lvalue Var 0x55d9f302cef8 'last' 'int'
    |   |   |   `-ImplicitCastExpr 0x55d9f3030250 <col:25> 'int' <LValueToRValue>
    |   |   |     `-DeclRefExpr 0x55d9f3030218 <col:25> 'int' lvalue Var 0x55d9f302eb58 'SIZE' 'int'
    |   |   `-CompoundStmt 0x55d9f30302e0 <col:31, line:38:3>
    |   |     `-UnaryOperator 0x55d9f30302c8 <line:37:4, col:5> 'int' postfix '++'
    |   |       `-DeclRefExpr 0x55d9f30302a8 <col:4> 'int' lvalue Var 0x55d9f302f130 'd' 'int'
    |   |-IfStmt 0x55d9f30304a8 <line:39:3, line:42:3>
    |   | |-BinaryOperator 0x55d9f30303a8 <line:39:6, col:11> 'int' '=='
    |   | | |-ImplicitCastExpr 0x55d9f3030378 <col:6> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55d9f3030338 <col:6> 'int' lvalue Var 0x55d9f302f130 'd' 'int'
    |   | | `-ImplicitCastExpr 0x55d9f3030390 <col:11> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x55d9f3030358 <col:11> 'int' lvalue Var 0x55d9f302eb58 'SIZE' 'int'
    |   | `-CompoundStmt 0x55d9f3030488 <col:17, line:42:3>
    |   |   |-BinaryOperator 0x55d9f3030408 <line:40:4, col:8> 'int' '='
    |   |   | |-DeclRefExpr 0x55d9f30303c8 <col:4> 'int' lvalue Var 0x55d9f302eeb0 'a' 'int'
    |   |   | `-IntegerLiteral 0x55d9f30303e8 <col:8> 'int' 0
    |   |   `-BinaryOperator 0x55d9f3030468 <line:41:4, col:8> 'int' '='
    |   |     |-DeclRefExpr 0x55d9f3030428 <col:4> 'int' lvalue Var 0x55d9f302ef50 'b' 'int'
    |   |     `-IntegerLiteral 0x55d9f3030448 <col:8> 'int' 1
    |   `-CallExpr 0x55d9f3030638 <line:44:3, col:36> 'void'
    |     |-ImplicitCastExpr 0x55d9f3030620 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x55d9f30304c0 <col:3> 'void (int)' Function 0x55d9f302e860 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x55d9f3030600 <col:21, col:32> 'int' '&&'
    |       |-BinaryOperator 0x55d9f3030550 <col:21, col:24> 'int' '=='
    |       | |-ImplicitCastExpr 0x55d9f3030520 <col:21> 'int' <LValueToRValue>
    |       | | `-DeclRefExpr 0x55d9f30304e0 <col:21> 'int' lvalue Var 0x55d9f302eeb0 'a' 'int'
    |       | `-ImplicitCastExpr 0x55d9f3030538 <col:24> 'int' <LValueToRValue>
    |       |   `-DeclRefExpr 0x55d9f3030500 <col:24> 'int' lvalue Var 0x55d9f302ef50 'b' 'int'
    |       `-BinaryOperator 0x55d9f30305e0 <col:29, col:32> 'int' '=='
    |         |-ImplicitCastExpr 0x55d9f30305b0 <col:29> 'int' <LValueToRValue>
    |         | `-DeclRefExpr 0x55d9f3030570 <col:29> 'int' lvalue Var 0x55d9f302eff0 'c' 'int'
    |         `-ImplicitCastExpr 0x55d9f30305c8 <col:32> 'int' <LValueToRValue>
    |           `-DeclRefExpr 0x55d9f3030590 <col:32> 'int' lvalue Var 0x55d9f302eb58 'SIZE' 'int'
    `-ReturnStmt 0x55d9f30306d8 <line:46:2, col:9>
      `-IntegerLiteral 0x55d9f30306b8 <col:9> 'int' 0
1 warning generated.
