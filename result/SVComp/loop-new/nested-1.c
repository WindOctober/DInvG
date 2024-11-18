./Benchmark/PLDI/SVComp/loop-new/nested-1.c
[info] Using default compilation options.
TranslationUnitDecl 0x556c37e31dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x556c37e32660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x556c37e32360 '__int128'
|-TypedefDecl 0x556c37e326d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x556c37e32380 'unsigned __int128'
|-TypedefDecl 0x556c37e329d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x556c37e327b0 'struct __NSConstantString_tag'
|   `-Record 0x556c37e32728 '__NSConstantString_tag'
|-TypedefDecl 0x556c37e32a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x556c37e32a30 'char *'
|   `-BuiltinType 0x556c37e31e60 'char'
|-TypedefDecl 0x556c37e32d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x556c37e32d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x556c37e32b50 'struct __va_list_tag'
|     `-Record 0x556c37e32ac8 '__va_list_tag'
|-FunctionDecl 0x556c37e91ca8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556c37e91d48 prev 0x556c37e91ca8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556c37e920c8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556c37e91e00 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x556c37e91e80 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x556c37e91f00 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556c37e91f80 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556c37e92188 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556c37e92508 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556c37e92240 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x556c37e922c0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x556c37e92340 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556c37e923c0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556c37e925c8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556c37e92858 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556c37e92638 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x556c37e926b8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x556c37e92738 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x556c37e92910 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556c37e929b8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x556c37eae0a8 <col:20, col:33>
|   `-ParenExpr 0x556c37eae088 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x556c37eae068 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x556c37e92b58 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x556c37e92b28 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x556c37e92b08 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x556c37e92ad8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x556c37e92a78 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x556c37e92a58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x556c37e92a98 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x556c37e92ab8 <col:32> 'int' 0
|       `-UnaryOperator 0x556c37eae050 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x556c37eae030 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x556c37eae018 <line:108:51, line:113:5>
|             `-IfStmt 0x556c37eadff0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x556c37e92b80 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:29> 'int' 0
|               |-NullStmt 0x556c37e92ba0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x556c37eadf20 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x556c37eadf08 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x556c37eadca0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x556c37e920c8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x556c37eadf78 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556c37eadf60 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556c37eadcf8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x556c37eadfa8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556c37eadf90 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556c37eadd58 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h"
|                 |-ImplicitCastExpr 0x556c37eadfc0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x556c37eaddd8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x556c37eadfd8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x556c37eadec0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x556c37eadea8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x556c37eade78 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x556c37eae158 prev 0x556c37e91d48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556c37eae2d8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x556c37eae210 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x556c37eae480 <col:36, line:7:1>
|   `-IfStmt 0x556c37eae468 <line:6:3, col:22>
|     |-UnaryOperator 0x556c37eae3b8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x556c37eae3a0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x556c37eae380 <col:7> 'int' lvalue ParmVar 0x556c37eae210 'cond' 'int'
|     `-CompoundStmt 0x556c37eae450 <col:13, col:22>
|       `-CallExpr 0x556c37eae430 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x556c37eae418 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x556c37eae3d0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x556c37eae158 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x556c37eae540 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x556c37eae4b0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x556c37eae800 <col:34, line:13:1>
|   |-IfStmt 0x556c37eae7d8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x556c37eae640 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x556c37eae628 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x556c37eae608 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x556c37eae5e8 <col:9> 'int' lvalue ParmVar 0x556c37eae4b0 'cond' 'int'
|   | `-CompoundStmt 0x556c37eae7c0 <col:16, line:11:3>
|   |   `-LabelStmt 0x556c37eae7a8 <line:10:3, col:33> 'ERROR'
|   |     `-CompoundStmt 0x556c37eae738 <col:10, col:33>
|   |       |-CallExpr 0x556c37eae6c0 <col:11, col:23> 'void'
|   |       | `-ImplicitCastExpr 0x556c37eae6a8 <col:11> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x556c37eae658 <col:11> 'void ()' Function 0x556c37e929b8 'reach_error' 'void ()'
|   |       `-CallExpr 0x556c37eae718 <col:25, col:31> 'void'
|   |         `-ImplicitCastExpr 0x556c37eae700 <col:25> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x556c37eae6e0 <col:25> 'void (void) __attribute__((noreturn))' Function 0x556c37eae158 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x556c37eae7f0 <line:12:3>
|-FunctionDecl 0x556c37eae870 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x556c37eae938 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/nested-1.c:2:1, line:16:1> line:2:5 main 'int ()'
  `-CompoundStmt 0x556c37eaf558 <col:12, line:16:1>
    |-DeclStmt 0x556c37eaeae0 <line:3:5, col:36>
    | `-VarDecl 0x556c37eae9f0 <col:5, col:35> col:9 used n 'int' cinit
    |   `-CallExpr 0x556c37eaeac0 <col:13, col:35> 'int'
    |     `-ImplicitCastExpr 0x556c37eaeaa8 <col:13> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x556c37eaea58 <col:13> 'int ()' Function 0x556c37eae870 '__VERIFIER_nondet_int' 'int ()'
    |-DeclStmt 0x556c37eaebd0 <line:4:5, col:36>
    | `-VarDecl 0x556c37eaeb10 <col:5, col:35> col:9 used m 'int' cinit
    |   `-CallExpr 0x556c37eaebb0 <col:13, col:35> 'int'
    |     `-ImplicitCastExpr 0x556c37eaeb98 <col:13> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x556c37eaeb78 <col:13> 'int ()' Function 0x556c37eae870 '__VERIFIER_nondet_int' 'int ()'
    |-DeclStmt 0x556c37eaec88 <line:5:5, col:14>
    | `-VarDecl 0x556c37eaec00 <col:5, col:13> col:9 used k 'int' cinit
    |   `-IntegerLiteral 0x556c37eaec68 <col:13> 'int' 0
    |-DeclStmt 0x556c37eaedc8 <line:6:5, col:12>
    | |-VarDecl 0x556c37eaecc8 <col:5, col:9> col:9 used i 'int'
    | `-VarDecl 0x556c37eaed48 <col:5, col:11> col:11 used j 'int'
    |-IfStmt 0x556c37eaef58 <line:7:5, col:42>
    | |-UnaryOperator 0x556c37eaef10 <col:9, col:32> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x556c37eaeef0 <col:10, col:32> 'int'
    | |   `-BinaryOperator 0x556c37eaeed0 <col:11, col:27> 'int' '&&'
    | |     |-BinaryOperator 0x556c37eaee38 <col:11, col:17> 'int' '<='
    | |     | |-IntegerLiteral 0x556c37eaede0 <col:11> 'int' 10
    | |     | `-ImplicitCastExpr 0x556c37eaee20 <col:17> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x556c37eaee00 <col:17> 'int' lvalue Var 0x556c37eae9f0 'n' 'int'
    | |     `-BinaryOperator 0x556c37eaeeb0 <col:22, col:27> 'int' '<='
    | |       |-ImplicitCastExpr 0x556c37eaee98 <col:22> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x556c37eaee58 <col:22> 'int' lvalue Var 0x556c37eae9f0 'n' 'int'
    | |       `-IntegerLiteral 0x556c37eaee78 <col:27> 'int' 10000
    | `-ReturnStmt 0x556c37eaef48 <col:35, col:42>
    |   `-IntegerLiteral 0x556c37eaef28 <col:42> 'int' 0
    |-IfStmt 0x556c37eaf0e8 <line:8:5, col:42>
    | |-UnaryOperator 0x556c37eaf0a0 <col:9, col:32> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x556c37eaf080 <col:10, col:32> 'int'
    | |   `-BinaryOperator 0x556c37eaf060 <col:11, col:27> 'int' '&&'
    | |     |-BinaryOperator 0x556c37eaefc8 <col:11, col:17> 'int' '<='
    | |     | |-IntegerLiteral 0x556c37eaef70 <col:11> 'int' 10
    | |     | `-ImplicitCastExpr 0x556c37eaefb0 <col:17> 'int' <LValueToRValue>
    | |     |   `-DeclRefExpr 0x556c37eaef90 <col:17> 'int' lvalue Var 0x556c37eaeb10 'm' 'int'
    | |     `-BinaryOperator 0x556c37eaf040 <col:22, col:27> 'int' '<='
    | |       |-ImplicitCastExpr 0x556c37eaf028 <col:22> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x556c37eaefe8 <col:22> 'int' lvalue Var 0x556c37eaeb10 'm' 'int'
    | |       `-IntegerLiteral 0x556c37eaf008 <col:27> 'int' 10000
    | `-ReturnStmt 0x556c37eaf0d8 <col:35, col:42>
    |   `-IntegerLiteral 0x556c37eaf0b8 <col:42> 'int' 0
    |-ForStmt 0x556c37eaf3f0 <line:9:5, line:13:5>
    | |-BinaryOperator 0x556c37eaf140 <line:9:10, col:14> 'int' '='
    | | |-DeclRefExpr 0x556c37eaf100 <col:10> 'int' lvalue Var 0x556c37eaecc8 'i' 'int'
    | | `-IntegerLiteral 0x556c37eaf120 <col:14> 'int' 0
    | |-<<<NULL>>>
    | |-BinaryOperator 0x556c37eaf1d0 <col:17, col:21> 'int' '<'
    | | |-ImplicitCastExpr 0x556c37eaf1a0 <col:17> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x556c37eaf160 <col:17> 'int' lvalue Var 0x556c37eaecc8 'i' 'int'
    | | `-ImplicitCastExpr 0x556c37eaf1b8 <col:21> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x556c37eaf180 <col:21> 'int' lvalue Var 0x556c37eae9f0 'n' 'int'
    | |-UnaryOperator 0x556c37eaf210 <col:24, col:25> 'int' postfix '++'
    | | `-DeclRefExpr 0x556c37eaf1f0 <col:24> 'int' lvalue Var 0x556c37eaecc8 'i' 'int'
    | `-CompoundStmt 0x556c37eaf3d8 <col:29, line:13:5>
    |   `-ForStmt 0x556c37eaf3a0 <line:10:2, line:12:2>
    |     |-BinaryOperator 0x556c37eaf268 <line:10:7, col:11> 'int' '='
    |     | |-DeclRefExpr 0x556c37eaf228 <col:7> 'int' lvalue Var 0x556c37eaed48 'j' 'int'
    |     | `-IntegerLiteral 0x556c37eaf248 <col:11> 'int' 0
    |     |-<<<NULL>>>
    |     |-BinaryOperator 0x556c37eaf2f8 <col:14, col:18> 'int' '<'
    |     | |-ImplicitCastExpr 0x556c37eaf2c8 <col:14> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x556c37eaf288 <col:14> 'int' lvalue Var 0x556c37eaed48 'j' 'int'
    |     | `-ImplicitCastExpr 0x556c37eaf2e0 <col:18> 'int' <LValueToRValue>
    |     |   `-DeclRefExpr 0x556c37eaf2a8 <col:18> 'int' lvalue Var 0x556c37eaeb10 'm' 'int'
    |     |-UnaryOperator 0x556c37eaf338 <col:21, col:22> 'int' postfix '++'
    |     | `-DeclRefExpr 0x556c37eaf318 <col:21> 'int' lvalue Var 0x556c37eaed48 'j' 'int'
    |     `-CompoundStmt 0x556c37eaf388 <col:26, line:12:2>
    |       `-UnaryOperator 0x556c37eaf370 <line:11:6, col:8> 'int' postfix '++'
    |         `-DeclRefExpr 0x556c37eaf350 <col:6> 'int' lvalue Var 0x556c37eaec00 'k' 'int'
    |-CallExpr 0x556c37eaf500 <line:14:5, col:31> 'void'
    | |-ImplicitCastExpr 0x556c37eaf4e8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x556c37eaf428 <col:5> 'void (int)' Function 0x556c37eae540 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x556c37eaf4a0 <col:23, col:28> 'int' '>='
    |   |-ImplicitCastExpr 0x556c37eaf488 <col:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x556c37eaf448 <col:23> 'int' lvalue Var 0x556c37eaec00 'k' 'int'
    |   `-IntegerLiteral 0x556c37eaf468 <col:28> 'int' 100
    `-ReturnStmt 0x556c37eaf548 <line:15:5, col:12>
      `-IntegerLiteral 0x556c37eaf528 <col:12> 'int' 0
