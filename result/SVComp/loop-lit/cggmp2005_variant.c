./Benchmark/PLDI/SVComp/loop-lit/cggmp2005_variant.c
[info] Using default compilation options.
TranslationUnitDecl 0x556ba23e7ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x556ba23e8780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x556ba23e8480 '__int128'
|-TypedefDecl 0x556ba23e87f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x556ba23e84a0 'unsigned __int128'
|-TypedefDecl 0x556ba23e8af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x556ba23e88d0 'struct __NSConstantString_tag'
|   `-Record 0x556ba23e8848 '__NSConstantString_tag'
|-TypedefDecl 0x556ba23e8b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x556ba23e8b50 'char *'
|   `-BuiltinType 0x556ba23e7f80 'char'
|-TypedefDecl 0x556ba23e8e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x556ba23e8e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x556ba23e8c70 'struct __va_list_tag'
|     `-Record 0x556ba23e8be8 '__va_list_tag'
|-FunctionDecl 0x556ba2447e68 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556ba2447f08 prev 0x556ba2447e68 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556ba2448288 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556ba2447fc0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x556ba2448040 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x556ba24480c0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556ba2448140 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556ba2448348 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556ba24486c8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556ba2448400 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x556ba2448480 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x556ba2448500 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556ba2448580 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556ba2448788 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556ba2448a18 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556ba24487f8 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x556ba2448878 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x556ba24488f8 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x556ba2448ad0 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556ba2448b78 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x556ba24643c8 <col:20, col:33>
|   `-ParenExpr 0x556ba24643a8 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x556ba2464388 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x556ba2448d18 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x556ba2448ce8 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x556ba2448cc8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x556ba2448c98 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x556ba2448c38 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x556ba2448c18 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x556ba2448c58 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x556ba2448c78 <col:32> 'int' 0
|       `-UnaryOperator 0x556ba2464370 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x556ba2464350 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x556ba2464338 <line:108:51, line:113:5>
|             `-IfStmt 0x556ba2464310 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x556ba2448d40 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x556ba2448d60 </usr/include/assert.h:110:9>
|               `-CallExpr 0x556ba2464240 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x556ba2464228 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x556ba2463fc0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x556ba2448288 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x556ba2464298 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556ba2464280 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556ba2464018 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x556ba24642c8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556ba24642b0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556ba2464078 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x556ba24642e0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x556ba24640f8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x556ba24642f8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x556ba24641e0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x556ba24641c8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x556ba2464198 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x556ba2464478 prev 0x556ba2447f08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556ba24645f8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x556ba2464530 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x556ba24647a0 <col:36, line:7:1>
|   `-IfStmt 0x556ba2464788 <line:6:3, col:22>
|     |-UnaryOperator 0x556ba24646d8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x556ba24646c0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x556ba24646a0 <col:7> 'int' lvalue ParmVar 0x556ba2464530 'cond' 'int'
|     `-CompoundStmt 0x556ba2464770 <col:13, col:22>
|       `-CallExpr 0x556ba2464750 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x556ba2464738 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x556ba24646f0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x556ba2464478 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x556ba2464860 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x556ba24647d0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x556ba2464b20 <col:34, line:13:1>
|   |-IfStmt 0x556ba2464af8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x556ba2464960 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x556ba2464948 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x556ba2464928 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x556ba2464908 <col:9> 'int' lvalue ParmVar 0x556ba24647d0 'cond' 'int'
|   | `-CompoundStmt 0x556ba2464ae0 <col:16, line:11:3>
|   |   `-LabelStmt 0x556ba2464ac8 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x556ba2464a58 <col:14, col:37>
|   |       |-CallExpr 0x556ba24649e0 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x556ba24649c8 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x556ba2464978 <col:15> 'void ()' Function 0x556ba2448b78 'reach_error' 'void ()'
|   |       `-CallExpr 0x556ba2464a38 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x556ba2464a20 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x556ba2464a00 <col:29> 'void (void) __attribute__((noreturn))' Function 0x556ba2464478 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x556ba2464b10 <line:12:3>
|-FunctionDecl 0x556ba2464b90 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x556ba2464c58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/cggmp2005_variant.c:7:1, line:21:1> line:7:5 main 'int ()'
  `-CompoundStmt 0x556ba2465668 <col:12, line:21:1>
    |-DeclStmt 0x556ba2464e98 <line:8:5, col:20>
    | |-VarDecl 0x556ba2464d10 <col:5, col:9> col:9 used lo 'int'
    | |-VarDecl 0x556ba2464d90 <col:5, col:13> col:13 used mid 'int'
    | `-VarDecl 0x556ba2464e10 <col:5, col:18> col:18 used hi 'int'
    |-BinaryOperator 0x556ba2464ef0 <line:9:5, col:10> 'int' '='
    | |-DeclRefExpr 0x556ba2464eb0 <col:5> 'int' lvalue Var 0x556ba2464d10 'lo' 'int'
    | `-IntegerLiteral 0x556ba2464ed0 <col:10> 'int' 0
    |-BinaryOperator 0x556ba2464fd0 <line:10:5, col:33> 'int' '='
    | |-DeclRefExpr 0x556ba2464f10 <col:5> 'int' lvalue Var 0x556ba2464d90 'mid' 'int'
    | `-CallExpr 0x556ba2464f90 <col:11, col:33> 'int'
    |   `-ImplicitCastExpr 0x556ba2464f78 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x556ba2464f30 <col:11> 'int ()' Function 0x556ba2464b90 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x556ba2465168 <line:11:5, col:48>
    | |-UnaryOperator 0x556ba2465120 <col:9, col:38> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x556ba2465100 <col:10, col:38> 'int'
    | |   `-BinaryOperator 0x556ba24650e0 <col:11, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '&&'
    | |     |-BinaryOperator 0x556ba2465048 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/cggmp2005_variant.c:11:11, col:17> 'int' '>'
    | |     | |-ImplicitCastExpr 0x556ba2465030 <col:11> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x556ba2464ff0 <col:11> 'int' lvalue Var 0x556ba2464d90 'mid' 'int'
    | |     | `-IntegerLiteral 0x556ba2465010 <col:17> 'int' 0
    | |     `-BinaryOperator 0x556ba24650c0 <col:22, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '<='
    | |       |-ImplicitCastExpr 0x556ba24650a8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/cggmp2005_variant.c:11:22> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x556ba2465068 <col:22> 'int' lvalue Var 0x556ba2464d90 'mid' 'int'
    | |       `-IntegerLiteral 0x556ba2465088 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' 1000000
    | `-ReturnStmt 0x556ba2465158 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/cggmp2005_variant.c:11:41, col:48>
    |   `-IntegerLiteral 0x556ba2465138 <col:48> 'int' 0
    |-BinaryOperator 0x556ba2465218 <line:12:5, col:12> 'int' '='
    | |-DeclRefExpr 0x556ba2465180 <col:5> 'int' lvalue Var 0x556ba2464e10 'hi' 'int'
    | `-BinaryOperator 0x556ba24651f8 <col:10, col:12> 'int' '*'
    |   |-IntegerLiteral 0x556ba24651a0 <col:10> 'int' 2
    |   `-ImplicitCastExpr 0x556ba24651e0 <col:12> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x556ba24651c0 <col:12> 'int' lvalue Var 0x556ba2464d90 'mid' 'int'
    |-WhileStmt 0x556ba2465500 <line:14:5, line:18:5>
    | |-BinaryOperator 0x556ba2465290 <line:14:12, col:18> 'int' '>'
    | | |-ImplicitCastExpr 0x556ba2465278 <col:12> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x556ba2465238 <col:12> 'int' lvalue Var 0x556ba2464d90 'mid' 'int'
    | | `-IntegerLiteral 0x556ba2465258 <col:18> 'int' 0
    | `-CompoundStmt 0x556ba24654d8 <col:21, line:18:5>
    |   |-BinaryOperator 0x556ba2465348 <line:15:9, col:19> 'int' '='
    |   | |-DeclRefExpr 0x556ba24652b0 <col:9> 'int' lvalue Var 0x556ba2464d10 'lo' 'int'
    |   | `-BinaryOperator 0x556ba2465328 <col:14, col:19> 'int' '+'
    |   |   |-ImplicitCastExpr 0x556ba2465310 <col:14> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x556ba24652d0 <col:14> 'int' lvalue Var 0x556ba2464d10 'lo' 'int'
    |   |   `-IntegerLiteral 0x556ba24652f0 <col:19> 'int' 1
    |   |-BinaryOperator 0x556ba2465400 <line:16:9, col:19> 'int' '='
    |   | |-DeclRefExpr 0x556ba2465368 <col:9> 'int' lvalue Var 0x556ba2464e10 'hi' 'int'
    |   | `-BinaryOperator 0x556ba24653e0 <col:14, col:19> 'int' '-'
    |   |   |-ImplicitCastExpr 0x556ba24653c8 <col:14> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x556ba2465388 <col:14> 'int' lvalue Var 0x556ba2464e10 'hi' 'int'
    |   |   `-IntegerLiteral 0x556ba24653a8 <col:19> 'int' 1
    |   `-BinaryOperator 0x556ba24654b8 <line:17:9, col:21> 'int' '='
    |     |-DeclRefExpr 0x556ba2465420 <col:9> 'int' lvalue Var 0x556ba2464d90 'mid' 'int'
    |     `-BinaryOperator 0x556ba2465498 <col:15, col:21> 'int' '-'
    |       |-ImplicitCastExpr 0x556ba2465480 <col:15> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x556ba2465440 <col:15> 'int' lvalue Var 0x556ba2464d90 'mid' 'int'
    |       `-IntegerLiteral 0x556ba2465460 <col:21> 'int' 1
    |-CallExpr 0x556ba2465610 <line:19:5, col:31> 'void'
    | |-ImplicitCastExpr 0x556ba24655f8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x556ba2465518 <col:5> 'void (int)' Function 0x556ba2464860 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x556ba24655a8 <col:23, col:29> 'int' '=='
    |   |-ImplicitCastExpr 0x556ba2465578 <col:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x556ba2465538 <col:23> 'int' lvalue Var 0x556ba2464d10 'lo' 'int'
    |   `-ImplicitCastExpr 0x556ba2465590 <col:29> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x556ba2465558 <col:29> 'int' lvalue Var 0x556ba2464e10 'hi' 'int'
    `-ReturnStmt 0x556ba2465658 <line:20:5, col:12>
      `-IntegerLiteral 0x556ba2465638 <col:12> 'int' 0
