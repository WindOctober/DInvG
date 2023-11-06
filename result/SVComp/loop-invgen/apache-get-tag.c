./Benchmark/PLDI/SVComp/loop-invgen/apache-get-tag.c
[info] Using default compilation options.
TranslationUnitDecl 0x564f14080ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x564f14081780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x564f14081480 '__int128'
|-TypedefDecl 0x564f140817f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x564f140814a0 'unsigned __int128'
|-TypedefDecl 0x564f14081af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x564f140818d0 'struct __NSConstantString_tag'
|   `-Record 0x564f14081848 '__NSConstantString_tag'
|-TypedefDecl 0x564f14081b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x564f14081b50 'char *'
|   `-BuiltinType 0x564f14080f80 'char'
|-TypedefDecl 0x564f14081e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x564f14081e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x564f14081c70 'struct __va_list_tag'
|     `-Record 0x564f14081be8 '__va_list_tag'
|-FunctionDecl 0x564f140e11f8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564f140e1298 prev 0x564f140e11f8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564f140e1618 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564f140e1350 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x564f140e13d0 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x564f140e1450 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x564f140e14d0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x564f140e16d8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564f140e1a58 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564f140e1790 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x564f140e1810 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x564f140e1890 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x564f140e1910 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x564f140e1b18 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564f140e1da8 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564f140e1b88 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x564f140e1c08 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x564f140e1c88 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x564f140e1e60 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564f140e1f08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x564f140fd758 <col:20, col:33>
|   `-ParenExpr 0x564f140fd738 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x564f140fd718 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x564f140e20a8 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x564f140e2078 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x564f140e2058 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x564f140e2028 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x564f140e1fc8 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x564f140e1fa8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x564f140e1fe8 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x564f140e2008 <col:32> 'int' 0
|       `-UnaryOperator 0x564f140fd700 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x564f140fd6e0 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x564f140fd6c8 <line:108:51, line:113:5>
|             `-IfStmt 0x564f140fd6a0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x564f140e20d0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x564f140e20f0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x564f140fd5d0 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x564f140fd5b8 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x564f140fd350 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x564f140e1618 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x564f140fd628 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x564f140fd610 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x564f140fd3a8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x564f140fd658 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x564f140fd640 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x564f140fd408 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x564f140fd670 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x564f140fd488 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x564f140fd688 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x564f140fd570 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x564f140fd558 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x564f140fd528 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x564f140fd808 prev 0x564f140e1298 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564f140fd988 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x564f140fd8c0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x564f140fdb30 <col:36, line:7:1>
|   `-IfStmt 0x564f140fdb18 <line:6:3, col:22>
|     |-UnaryOperator 0x564f140fda68 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x564f140fda50 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x564f140fda30 <col:7> 'int' lvalue ParmVar 0x564f140fd8c0 'cond' 'int'
|     `-CompoundStmt 0x564f140fdb00 <col:13, col:22>
|       `-CallExpr 0x564f140fdae0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x564f140fdac8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x564f140fda80 <col:14> 'void (void) __attribute__((noreturn))' Function 0x564f140fd808 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x564f140fdbf0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x564f140fdb60 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x564f140fdeb0 <col:34, line:13:1>
|   |-IfStmt 0x564f140fde88 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x564f140fdcf0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x564f140fdcd8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x564f140fdcb8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x564f140fdc98 <col:9> 'int' lvalue ParmVar 0x564f140fdb60 'cond' 'int'
|   | `-CompoundStmt 0x564f140fde70 <col:16, line:11:3>
|   |   `-LabelStmt 0x564f140fde58 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x564f140fdde8 <col:12, col:35>
|   |       |-CallExpr 0x564f140fdd70 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x564f140fdd58 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x564f140fdd08 <col:13> 'void ()' Function 0x564f140e1f08 'reach_error' 'void ()'
|   |       `-CallExpr 0x564f140fddc8 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x564f140fddb0 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x564f140fdd90 <col:27> 'void (void) __attribute__((noreturn))' Function 0x564f140fd808 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x564f140fdea0 <line:12:3>
|-FunctionDecl 0x564f140fdf20 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x564f140fdfe8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/apache-get-tag.c:2:1, line:69:1> line:2:5 main 'int ()'
  `-CompoundStmt 0x564f14100240 <line:3:1, line:69:1>
    |-DeclStmt 0x564f140fe108 <line:4:3, col:17>
    | `-VarDecl 0x564f140fe0a0 <col:3, col:7> col:7 used tagbuf_len 'int'
    |-DeclStmt 0x564f140fe1a0 <line:5:3, col:8>
    | `-VarDecl 0x564f140fe138 <col:3, col:7> col:7 used t 'int'
    |-BinaryOperator 0x564f140fe260 <line:7:3, col:38> 'int' '='
    | |-DeclRefExpr 0x564f140fe1b8 <col:3> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    | `-CallExpr 0x564f140fe240 <col:16, col:38> 'int'
    |   `-ImplicitCastExpr 0x564f140fe228 <col:16> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x564f140fe1d8 <col:16> 'int ()' Function 0x564f140fdf20 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x564f140fe378 <line:8:3, col:34> has_else
    | |-BinaryOperator 0x564f140fe2d8 <col:6, col:20> 'int' '>='
    | | |-ImplicitCastExpr 0x564f140fe2c0 <col:6> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x564f140fe280 <col:6> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    | | `-IntegerLiteral 0x564f140fe2a0 <col:20> 'int' 1
    | |-NullStmt 0x564f140fe2f8 <col:22>
    | `-GotoStmt 0x564f140fe360 <col:29, col:34> 'END' 0x564f140fe300
    |-BinaryOperator 0x564f140fe3e0 <line:10:3, col:7> 'int' '='
    | |-DeclRefExpr 0x564f140fe3a0 <col:3> 'int' lvalue Var 0x564f140fe138 't' 'int'
    | `-IntegerLiteral 0x564f140fe3c0 <col:7> 'int' 0
    |-UnaryOperator 0x564f140fe420 <line:12:3, col:5> 'int' prefix '--'
    | `-DeclRefExpr 0x564f140fe400 <col:5> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |-WhileStmt 0x564f140fe9f8 <line:14:3, line:27:3>
    | |-IntegerLiteral 0x564f140fe438 <line:14:10> 'int' 1
    | `-CompoundStmt 0x564f140fe9c0 <col:13, line:27:3>
    |   |-IfStmt 0x564f140fe718 <line:15:5, line:20:5>
    |   | |-BinaryOperator 0x564f140fe4c8 <line:15:9, col:14> 'int' '=='
    |   | | |-ImplicitCastExpr 0x564f140fe498 <col:9> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x564f140fe458 <col:9> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   | | `-ImplicitCastExpr 0x564f140fe4b0 <col:14> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x564f140fe478 <col:14> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   | `-CompoundStmt 0x564f140fe6f0 <col:26, line:20:5>
    |   |   |-CallExpr 0x564f140fe5c0 <line:16:7, col:31> 'void'
    |   |   | |-ImplicitCastExpr 0x564f140fe5a8 <col:7> 'void (*)(int)' <FunctionToPointerDecay>
    |   |   | | `-DeclRefExpr 0x564f140fe4e8 <col:7> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   |   | `-BinaryOperator 0x564f140fe560 <col:25, col:30> 'int' '<='
    |   |   |   |-IntegerLiteral 0x564f140fe508 <col:25> 'int' 0
    |   |   |   `-ImplicitCastExpr 0x564f140fe548 <col:30> 'int' <LValueToRValue>
    |   |   |     `-DeclRefExpr 0x564f140fe528 <col:30> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   |   |-CallExpr 0x564f140fe6b0 <line:17:7, col:40> 'void'
    |   |   | |-ImplicitCastExpr 0x564f140fe698 <col:7> 'void (*)(int)' <FunctionToPointerDecay>
    |   |   | | `-DeclRefExpr 0x564f140fe5e8 <col:7> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   |   | `-BinaryOperator 0x564f140fe678 <col:25, col:30> 'int' '<='
    |   |   |   |-ImplicitCastExpr 0x564f140fe648 <col:25> 'int' <LValueToRValue>
    |   |   |   | `-DeclRefExpr 0x564f140fe608 <col:25> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   |   |   `-ImplicitCastExpr 0x564f140fe660 <col:30> 'int' <LValueToRValue>
    |   |   |     `-DeclRefExpr 0x564f140fe628 <col:30> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   |   `-GotoStmt 0x564f140fe6d8 <line:19:7, col:12> 'END' 0x564f140fe300
    |   |-IfStmt 0x564f140fe7a8 <line:21:5, line:23:5>
    |   | |-CallExpr 0x564f140fe768 <line:21:9, col:31> 'int'
    |   | | `-ImplicitCastExpr 0x564f140fe750 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |   | |   `-DeclRefExpr 0x564f140fe730 <col:9> 'int ()' Function 0x564f140fdf20 '__VERIFIER_nondet_int' 'int ()'
    |   | `-CompoundStmt 0x564f140fe790 <col:34, line:23:5>
    |   |   `-BreakStmt 0x564f140fe788 <line:22:7>
    |   |-CallExpr 0x564f140fe870 <line:24:6, col:30> 'void'
    |   | |-ImplicitCastExpr 0x564f140fe858 <col:6> 'void (*)(int)' <FunctionToPointerDecay>
    |   | | `-DeclRefExpr 0x564f140fe7c0 <col:6> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   | `-BinaryOperator 0x564f140fe838 <col:24, col:29> 'int' '<='
    |   |   |-IntegerLiteral 0x564f140fe7e0 <col:24> 'int' 0
    |   |   `-ImplicitCastExpr 0x564f140fe820 <col:29> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x564f140fe800 <col:29> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   |-CallExpr 0x564f140fe960 <line:25:6, col:39> 'void'
    |   | |-ImplicitCastExpr 0x564f140fe948 <col:6> 'void (*)(int)' <FunctionToPointerDecay>
    |   | | `-DeclRefExpr 0x564f140fe898 <col:6> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   | `-BinaryOperator 0x564f140fe928 <col:24, col:29> 'int' '<='
    |   |   |-ImplicitCastExpr 0x564f140fe8f8 <col:24> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x564f140fe8b8 <col:24> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   |   `-ImplicitCastExpr 0x564f140fe910 <col:29> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x564f140fe8d8 <col:29> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   `-UnaryOperator 0x564f140fe9a8 <line:26:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x564f140fe988 <col:5> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |-CallExpr 0x564f140feac0 <line:29:4, col:28> 'void'
    | |-ImplicitCastExpr 0x564f140feaa8 <col:4> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x564f140fea10 <col:4> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x564f140fea88 <col:22, col:27> 'int' '<='
    |   |-IntegerLiteral 0x564f140fea30 <col:22> 'int' 0
    |   `-ImplicitCastExpr 0x564f140fea70 <col:27> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x564f140fea50 <col:27> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |-CallExpr 0x564f140febb0 <line:30:4, col:37> 'void'
    | |-ImplicitCastExpr 0x564f140feb98 <col:4> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x564f140feae8 <col:4> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x564f140feb78 <col:22, col:27> 'int' '<='
    |   |-ImplicitCastExpr 0x564f140feb48 <col:22> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x564f140feb08 <col:22> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   `-ImplicitCastExpr 0x564f140feb60 <col:27> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x564f140feb28 <col:27> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |-UnaryOperator 0x564f140febf8 <line:31:3, col:4> 'int' postfix '++'
    | `-DeclRefExpr 0x564f140febd8 <col:3> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |-WhileStmt 0x564f14100018 <line:33:3, line:62:3>
    | |-IntegerLiteral 0x564f140fec10 <line:33:10> 'int' 1
    | `-CompoundStmt 0x564f140fffe0 <col:13, line:62:3>
    |   |-IfStmt 0x564f140feec8 <line:35:5, line:39:5>
    |   | |-BinaryOperator 0x564f140feca0 <line:35:9, col:14> 'int' '=='
    |   | | |-ImplicitCastExpr 0x564f140fec70 <col:9> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x564f140fec30 <col:9> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   | | `-ImplicitCastExpr 0x564f140fec88 <col:14> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x564f140fec50 <col:14> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   | `-CompoundStmt 0x564f140feea0 <col:26, line:39:5>
    |   |   |-CallExpr 0x564f140fed70 <line:36:7, col:31> 'void'
    |   |   | |-ImplicitCastExpr 0x564f140fed58 <col:7> 'void (*)(int)' <FunctionToPointerDecay>
    |   |   | | `-DeclRefExpr 0x564f140fecc0 <col:7> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   |   | `-BinaryOperator 0x564f140fed38 <col:25, col:30> 'int' '<='
    |   |   |   |-IntegerLiteral 0x564f140fece0 <col:25> 'int' 0
    |   |   |   `-ImplicitCastExpr 0x564f140fed20 <col:30> 'int' <LValueToRValue>
    |   |   |     `-DeclRefExpr 0x564f140fed00 <col:30> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   |   |-CallExpr 0x564f140fee60 <line:37:7, col:40> 'void'
    |   |   | |-ImplicitCastExpr 0x564f140fee48 <col:7> 'void (*)(int)' <FunctionToPointerDecay>
    |   |   | | `-DeclRefExpr 0x564f140fed98 <col:7> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   |   | `-BinaryOperator 0x564f140fee28 <col:25, col:30> 'int' '<='
    |   |   |   |-ImplicitCastExpr 0x564f140fedf8 <col:25> 'int' <LValueToRValue>
    |   |   |   | `-DeclRefExpr 0x564f140fedb8 <col:25> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   |   |   `-ImplicitCastExpr 0x564f140fee10 <col:30> 'int' <LValueToRValue>
    |   |   |     `-DeclRefExpr 0x564f140fedd8 <col:30> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   |   `-GotoStmt 0x564f140fee88 <line:38:7, col:12> 'END' 0x564f140fe300
    |   |-IfStmt 0x564f140ffdb8 <line:41:5, line:55:5> has_else
    |   | |-CallExpr 0x564f140fef18 <line:41:9, col:31> 'int'
    |   | | `-ImplicitCastExpr 0x564f140fef00 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |   | |   `-DeclRefExpr 0x564f140feee0 <col:9> 'int ()' Function 0x564f140fdf20 '__VERIFIER_nondet_int' 'int ()'
    |   | |-CompoundStmt 0x564f140ffd10 <col:34, line:52:5>
    |   | | `-IfStmt 0x564f140ffcf8 <line:42:7, line:51:7>
    |   | |   |-CallExpr 0x564f140fef70 <line:42:12, col:34> 'int'
    |   | |   | `-ImplicitCastExpr 0x564f140fef58 <col:12> 'int (*)()' <FunctionToPointerDecay>
    |   | |   |   `-DeclRefExpr 0x564f140fef38 <col:12> 'int ()' Function 0x564f140fdf20 '__VERIFIER_nondet_int' 'int ()'
    |   | |   `-CompoundStmt 0x564f140ffcc8 <col:37, line:51:7>
    |   | |     |-CallExpr 0x564f140ff040 <line:43:3, col:27> 'void'
    |   | |     | |-ImplicitCastExpr 0x564f140ff028 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    |   | |     | | `-DeclRefExpr 0x564f140fef90 <col:3> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   | |     | `-BinaryOperator 0x564f140ff008 <col:21, col:26> 'int' '<='
    |   | |     |   |-IntegerLiteral 0x564f140fefb0 <col:21> 'int' 0
    |   | |     |   `-ImplicitCastExpr 0x564f140feff0 <col:26> 'int' <LValueToRValue>
    |   | |     |     `-DeclRefExpr 0x564f140fefd0 <col:26> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   | |     |-CallExpr 0x564f140ff130 <line:44:2, col:35> 'void'
    |   | |     | |-ImplicitCastExpr 0x564f140ff118 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    |   | |     | | `-DeclRefExpr 0x564f140ff068 <col:2> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   | |     | `-BinaryOperator 0x564f140ff0f8 <col:20, col:25> 'int' '<='
    |   | |     |   |-ImplicitCastExpr 0x564f140ff0c8 <col:20> 'int' <LValueToRValue>
    |   | |     |   | `-DeclRefExpr 0x564f140ff088 <col:20> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   | |     |   `-ImplicitCastExpr 0x564f140ff0e0 <col:25> 'int' <LValueToRValue>
    |   | |     |     `-DeclRefExpr 0x564f140ff0a8 <col:25> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   | |     |-UnaryOperator 0x564f140ff178 <line:45:9, col:10> 'int' postfix '++'
    |   | |     | `-DeclRefExpr 0x564f140ff158 <col:9> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   | |     `-IfStmt 0x564f140ffcb0 <line:46:9, line:50:9>
    |   | |       |-BinaryOperator 0x564f140ff200 <line:46:13, col:18> 'int' '=='
    |   | |       | |-ImplicitCastExpr 0x564f140ff1d0 <col:13> 'int' <LValueToRValue>
    |   | |       | | `-DeclRefExpr 0x564f140ff190 <col:13> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   | |       | `-ImplicitCastExpr 0x564f140ff1e8 <col:18> 'int' <LValueToRValue>
    |   | |       |   `-DeclRefExpr 0x564f140ff1b0 <col:18> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   | |       `-CompoundStmt 0x564f140ffc88 <col:30, line:50:9>
    |   | |         |-CallExpr 0x564f140ff2d0 <line:47:4, col:28> 'void'
    |   | |         | |-ImplicitCastExpr 0x564f140ff2b8 <col:4> 'void (*)(int)' <FunctionToPointerDecay>
    |   | |         | | `-DeclRefExpr 0x564f140ff220 <col:4> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   | |         | `-BinaryOperator 0x564f140ff298 <col:22, col:27> 'int' '<='
    |   | |         |   |-IntegerLiteral 0x564f140ff240 <col:22> 'int' 0
    |   | |         |   `-ImplicitCastExpr 0x564f140ff280 <col:27> 'int' <LValueToRValue>
    |   | |         |     `-DeclRefExpr 0x564f140ff260 <col:27> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   | |         |-CallExpr 0x564f140ffc48 <line:48:4, col:37> 'void'
    |   | |         | |-ImplicitCastExpr 0x564f140ffc30 <col:4> 'void (*)(int)' <FunctionToPointerDecay>
    |   | |         | | `-DeclRefExpr 0x564f140ff2f8 <col:4> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   | |         | `-BinaryOperator 0x564f140ffc10 <col:22, col:27> 'int' '<='
    |   | |         |   |-ImplicitCastExpr 0x564f140ffbe0 <col:22> 'int' <LValueToRValue>
    |   | |         |   | `-DeclRefExpr 0x564f140ff318 <col:22> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   | |         |   `-ImplicitCastExpr 0x564f140ffbf8 <col:27> 'int' <LValueToRValue>
    |   | |         |     `-DeclRefExpr 0x564f140ff338 <col:27> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   | |         `-GotoStmt 0x564f140ffc70 <line:49:11, col:16> 'END' 0x564f140fe300
    |   | `-IfStmt 0x564f140ffda0 <line:53:10, line:55:5>
    |   |   |-CallExpr 0x564f140ffd60 <line:53:15, col:37> 'int'
    |   |   | `-ImplicitCastExpr 0x564f140ffd48 <col:15> 'int (*)()' <FunctionToPointerDecay>
    |   |   |   `-DeclRefExpr 0x564f140ffd28 <col:15> 'int ()' Function 0x564f140fdf20 '__VERIFIER_nondet_int' 'int ()'
    |   |   `-CompoundStmt 0x564f140ffd88 <col:40, line:55:5>
    |   |     `-BreakStmt 0x564f140ffd80 <line:54:7>
    |   |-CallExpr 0x564f140ffe90 <line:58:5, col:29> 'void'
    |   | |-ImplicitCastExpr 0x564f140ffe78 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |   | | `-DeclRefExpr 0x564f140ffde0 <col:5> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   | `-BinaryOperator 0x564f140ffe58 <col:23, col:28> 'int' '<='
    |   |   |-IntegerLiteral 0x564f140ffe00 <col:23> 'int' 0
    |   |   `-ImplicitCastExpr 0x564f140ffe40 <col:28> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x564f140ffe20 <col:28> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   |-CallExpr 0x564f140fff80 <line:59:5, col:38> 'void'
    |   | |-ImplicitCastExpr 0x564f140fff68 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |   | | `-DeclRefExpr 0x564f140ffeb8 <col:5> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    |   | `-BinaryOperator 0x564f140fff48 <col:23, col:28> 'int' '<='
    |   |   |-ImplicitCastExpr 0x564f140fff18 <col:23> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x564f140ffed8 <col:23> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   |   `-ImplicitCastExpr 0x564f140fff30 <col:28> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x564f140ffef8 <col:28> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    |   `-UnaryOperator 0x564f140fffc8 <line:60:5, col:6> 'int' postfix '++'
    |     `-DeclRefExpr 0x564f140fffa8 <col:5> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |-CallExpr 0x564f141000e0 <line:64:3, col:27> 'void'
    | |-ImplicitCastExpr 0x564f141000c8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x564f14100030 <col:3> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x564f141000a8 <col:21, col:26> 'int' '<='
    |   |-IntegerLiteral 0x564f14100050 <col:21> 'int' 0
    |   `-ImplicitCastExpr 0x564f14100090 <col:26> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x564f14100070 <col:26> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |-CallExpr 0x564f141001d0 <line:65:3, col:36> 'void'
    | |-ImplicitCastExpr 0x564f141001b8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x564f14100108 <col:3> 'void (int)' Function 0x564f140fdbf0 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x564f14100198 <col:21, col:26> 'int' '<='
    |   |-ImplicitCastExpr 0x564f14100168 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x564f14100128 <col:21> 'int' lvalue Var 0x564f140fe138 't' 'int'
    |   `-ImplicitCastExpr 0x564f14100180 <col:26> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x564f14100148 <col:26> 'int' lvalue Var 0x564f140fe0a0 'tagbuf_len' 'int'
    `-LabelStmt 0x564f14100228 <line:67:2, line:68:10> 'END'
      `-ReturnStmt 0x564f14100218 <col:3, col:10>
        `-IntegerLiteral 0x564f141001f8 <col:10> 'int' 0
