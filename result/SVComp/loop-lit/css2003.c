./Benchmark/PLDI/SVComp/loop-lit/css2003.c
[info] Using default compilation options.
TranslationUnitDecl 0x55f2aff96dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55f2aff97660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55f2aff97360 '__int128'
|-TypedefDecl 0x55f2aff976d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55f2aff97380 'unsigned __int128'
|-TypedefDecl 0x55f2aff979d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55f2aff977b0 'struct __NSConstantString_tag'
|   `-Record 0x55f2aff97728 '__NSConstantString_tag'
|-TypedefDecl 0x55f2aff97a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55f2aff97a30 'char *'
|   `-BuiltinType 0x55f2aff96e60 'char'
|-TypedefDecl 0x55f2aff97d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55f2aff97d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55f2aff97b50 'struct __va_list_tag'
|     `-Record 0x55f2aff97ac8 '__va_list_tag'
|-FunctionDecl 0x55f2afff6cf8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f2afff6d98 prev 0x55f2afff6cf8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f2afff7118 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f2afff6e50 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x55f2afff6ed0 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x55f2afff6f50 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55f2afff6fd0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55f2afff71d8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55f2afff7558 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f2afff7290 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x55f2afff7310 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x55f2afff7390 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55f2afff7410 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55f2afff7618 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55f2afff78a8 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f2afff7688 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x55f2afff7708 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x55f2afff7788 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x55f2afff7960 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55f2afff7a08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55f2b0013308 <col:20, col:33>
|   `-ParenExpr 0x55f2b00132e8 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x55f2b00132c8 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x55f2afff7ba8 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x55f2afff7b78 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x55f2afff7b58 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x55f2afff7b28 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x55f2afff7ac8 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x55f2afff7aa8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x55f2afff7ae8 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x55f2afff7b08 <col:32> 'int' 0
|       `-UnaryOperator 0x55f2b00132b0 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x55f2b0013290 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x55f2b0013278 <line:108:51, line:113:5>
|             `-IfStmt 0x55f2b0013250 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x55f2afff7bd0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x55f2afff7bf0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x55f2b0013180 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x55f2b0013168 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x55f2b0012f00 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55f2afff7118 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x55f2b00131d8 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55f2b00131c0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55f2b0012f58 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x55f2b0013208 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55f2b00131f0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55f2b0012fb8 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x55f2b0013220 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x55f2b0013038 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x55f2b0013238 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x55f2b0013120 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x55f2b0013108 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x55f2b00130d8 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x55f2b00133b8 prev 0x55f2afff6d98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f2b0013538 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55f2b0013470 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55f2b00136e0 <col:36, line:7:1>
|   `-IfStmt 0x55f2b00136c8 <line:6:3, col:22>
|     |-UnaryOperator 0x55f2b0013618 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55f2b0013600 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55f2b00135e0 <col:7> 'int' lvalue ParmVar 0x55f2b0013470 'cond' 'int'
|     `-CompoundStmt 0x55f2b00136b0 <col:13, col:22>
|       `-CallExpr 0x55f2b0013690 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55f2b0013678 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55f2b0013630 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55f2b00133b8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55f2b00137a0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55f2b0013710 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55f2b0013a60 <col:34, line:13:1>
|   |-IfStmt 0x55f2b0013a38 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x55f2b00138a0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55f2b0013888 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55f2b0013868 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55f2b0013848 <col:9> 'int' lvalue ParmVar 0x55f2b0013710 'cond' 'int'
|   | `-CompoundStmt 0x55f2b0013a20 <col:16, line:11:3>
|   |   `-LabelStmt 0x55f2b0013a08 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x55f2b0013998 <col:14, col:37>
|   |       |-CallExpr 0x55f2b0013920 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x55f2b0013908 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55f2b00138b8 <col:15> 'void ()' Function 0x55f2afff7a08 'reach_error' 'void ()'
|   |       `-CallExpr 0x55f2b0013978 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x55f2b0013960 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55f2b0013940 <col:29> 'void (void) __attribute__((noreturn))' Function 0x55f2b00133b8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55f2b0013a50 <line:12:3>
|-FunctionDecl 0x55f2b0013ad0 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x55f2b0013b98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/css2003.c:5:1, line:18:1> line:5:5 main 'int ()'
  `-CompoundStmt 0x55f2b0014730 <col:12, line:18:1>
    |-DeclStmt 0x55f2b0013dd8 <line:6:5, col:14>
    | |-VarDecl 0x55f2b0013c50 <col:5, col:9> col:9 used i 'int'
    | |-VarDecl 0x55f2b0013cd0 <col:5, col:11> col:11 used j 'int'
    | `-VarDecl 0x55f2b0013d50 <col:5, col:13> col:13 used k 'int'
    |-BinaryOperator 0x55f2b0013e30 <line:7:5, col:9> 'int' '='
    | |-DeclRefExpr 0x55f2b0013df0 <col:5> 'int' lvalue Var 0x55f2b0013c50 'i' 'int'
    | `-IntegerLiteral 0x55f2b0013e10 <col:9> 'int' 1
    |-BinaryOperator 0x55f2b0013e90 <line:8:5, col:9> 'int' '='
    | |-DeclRefExpr 0x55f2b0013e50 <col:5> 'int' lvalue Var 0x55f2b0013cd0 'j' 'int'
    | `-IntegerLiteral 0x55f2b0013e70 <col:9> 'int' 1
    |-BinaryOperator 0x55f2b0013f70 <line:9:5, col:31> 'int' '='
    | |-DeclRefExpr 0x55f2b0013eb0 <col:5> 'int' lvalue Var 0x55f2b0013d50 'k' 'int'
    | `-CallExpr 0x55f2b0013f50 <col:9, col:31> 'int'
    |   `-ImplicitCastExpr 0x55f2b0013f38 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55f2b0013ed0 <col:9> 'int ()' Function 0x55f2b0013ad0 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x55f2b0014108 <line:10:5, col:37>
    | |-UnaryOperator 0x55f2b00140c0 <col:9, col:27> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55f2b00140a0 <col:10, col:27> 'int'
    | |   `-BinaryOperator 0x55f2b0014080 <col:11, col:26> 'int' '&&'
    | |     |-BinaryOperator 0x55f2b0013fe8 <col:11, col:16> 'int' '<='
    | |     | |-IntegerLiteral 0x55f2b0013f90 <col:11> 'int' 0
    | |     | `-ImplicitCastExpr 0x55f2b0013fd0 <col:16> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x55f2b0013fb0 <col:16> 'int' lvalue Var 0x55f2b0013d50 'k' 'int'
    | |     `-BinaryOperator 0x55f2b0014060 <col:21, col:26> 'int' '<='
    | |       |-ImplicitCastExpr 0x55f2b0014048 <col:21> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x55f2b0014008 <col:21> 'int' lvalue Var 0x55f2b0013d50 'k' 'int'
    | |       `-IntegerLiteral 0x55f2b0014028 <col:26> 'int' 1
    | `-ReturnStmt 0x55f2b00140f8 <col:30, col:37>
    |   `-IntegerLiteral 0x55f2b00140d8 <col:37> 'int' 0
    |-WhileStmt 0x55f2b00146e8 <line:11:5, line:16:5>
    | |-BinaryOperator 0x55f2b0014178 <line:11:12, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '<'
    | | |-ImplicitCastExpr 0x55f2b0014160 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/css2003.c:11:12> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f2b0014120 <col:12> 'int' lvalue Var 0x55f2b0013c50 'i' 'int'
    | | `-IntegerLiteral 0x55f2b0014140 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' 1000000
    | `-CompoundStmt 0x55f2b00146b8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/css2003.c:11:27, line:16:5>
    |   |-BinaryOperator 0x55f2b0014230 <line:12:2, col:10> 'int' '='
    |   | |-DeclRefExpr 0x55f2b0014198 <col:2> 'int' lvalue Var 0x55f2b0013c50 'i' 'int'
    |   | `-BinaryOperator 0x55f2b0014210 <col:6, col:10> 'int' '+'
    |   |   |-ImplicitCastExpr 0x55f2b00141f8 <col:6> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55f2b00141b8 <col:6> 'int' lvalue Var 0x55f2b0013c50 'i' 'int'
    |   |   `-IntegerLiteral 0x55f2b00141d8 <col:10> 'int' 1
    |   |-BinaryOperator 0x55f2b0014300 <line:13:2, col:10> 'int' '='
    |   | |-DeclRefExpr 0x55f2b0014250 <col:2> 'int' lvalue Var 0x55f2b0013cd0 'j' 'int'
    |   | `-BinaryOperator 0x55f2b00142e0 <col:6, col:10> 'int' '+'
    |   |   |-ImplicitCastExpr 0x55f2b00142b0 <col:6> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55f2b0014270 <col:6> 'int' lvalue Var 0x55f2b0013cd0 'j' 'int'
    |   |   `-ImplicitCastExpr 0x55f2b00142c8 <col:10> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x55f2b0014290 <col:10> 'int' lvalue Var 0x55f2b0013d50 'k' 'int'
    |   |-BinaryOperator 0x55f2b00143b8 <line:14:2, col:10> 'int' '='
    |   | |-DeclRefExpr 0x55f2b0014320 <col:2> 'int' lvalue Var 0x55f2b0013d50 'k' 'int'
    |   | `-BinaryOperator 0x55f2b0014398 <col:6, col:10> 'int' '-'
    |   |   |-ImplicitCastExpr 0x55f2b0014380 <col:6> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55f2b0014340 <col:6> 'int' lvalue Var 0x55f2b0013d50 'k' 'int'
    |   |   `-IntegerLiteral 0x55f2b0014360 <col:10> 'int' 1
    |   `-CallExpr 0x55f2b0014690 <line:15:2, col:54> 'void'
    |     |-ImplicitCastExpr 0x55f2b0014678 <col:2> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x55f2b00143d8 <col:2> 'void (int)' Function 0x55f2b00137a0 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x55f2b0014630 <col:20, col:53> 'int' '&&'
    |       |-BinaryOperator 0x55f2b0014598 <col:20, col:43> 'int' '&&'
    |       | |-BinaryOperator 0x55f2b00144a8 <col:20, col:29> 'int' '<='
    |       | | |-IntegerLiteral 0x55f2b00143f8 <col:20> 'int' 1
    |       | | `-BinaryOperator 0x55f2b0014488 <col:25, col:29> 'int' '+'
    |       | |   |-ImplicitCastExpr 0x55f2b0014458 <col:25> 'int' <LValueToRValue>
    |       | |   | `-DeclRefExpr 0x55f2b0014418 <col:25> 'int' lvalue Var 0x55f2b0013c50 'i' 'int'
    |       | |   `-ImplicitCastExpr 0x55f2b0014470 <col:29> 'int' <LValueToRValue>
    |       | |     `-DeclRefExpr 0x55f2b0014438 <col:29> 'int' lvalue Var 0x55f2b0013d50 'k' 'int'
    |       | `-BinaryOperator 0x55f2b0014578 <col:34, col:43> 'int' '<='
    |       |   |-BinaryOperator 0x55f2b0014538 <col:34, col:38> 'int' '+'
    |       |   | |-ImplicitCastExpr 0x55f2b0014508 <col:34> 'int' <LValueToRValue>
    |       |   | | `-DeclRefExpr 0x55f2b00144c8 <col:34> 'int' lvalue Var 0x55f2b0013c50 'i' 'int'
    |       |   | `-ImplicitCastExpr 0x55f2b0014520 <col:38> 'int' <LValueToRValue>
    |       |   |   `-DeclRefExpr 0x55f2b00144e8 <col:38> 'int' lvalue Var 0x55f2b0013d50 'k' 'int'
    |       |   `-IntegerLiteral 0x55f2b0014558 <col:43> 'int' 2
    |       `-BinaryOperator 0x55f2b0014610 <col:48, col:53> 'int' '>='
    |         |-ImplicitCastExpr 0x55f2b00145f8 <col:48> 'int' <LValueToRValue>
    |         | `-DeclRefExpr 0x55f2b00145b8 <col:48> 'int' lvalue Var 0x55f2b0013c50 'i' 'int'
    |         `-IntegerLiteral 0x55f2b00145d8 <col:53> 'int' 1
    `-ReturnStmt 0x55f2b0014720 <line:17:5, col:12>
      `-IntegerLiteral 0x55f2b0014700 <col:12> 'int' 0
