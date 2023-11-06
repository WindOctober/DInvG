./Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c
[info] Using default compilation options.
TranslationUnitDecl 0x556ac9ca4ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x556ac9ca5780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x556ac9ca5480 '__int128'
|-TypedefDecl 0x556ac9ca57f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x556ac9ca54a0 'unsigned __int128'
|-TypedefDecl 0x556ac9ca5af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x556ac9ca58d0 'struct __NSConstantString_tag'
|   `-Record 0x556ac9ca5848 '__NSConstantString_tag'
|-TypedefDecl 0x556ac9ca5b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x556ac9ca5b50 'char *'
|   `-BuiltinType 0x556ac9ca4f80 'char'
|-TypedefDecl 0x556ac9ca5e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x556ac9ca5e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x556ac9ca5c70 'struct __va_list_tag'
|     `-Record 0x556ac9ca5be8 '__va_list_tag'
|-FunctionDecl 0x556ac9d04d88 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556ac9d04e28 prev 0x556ac9d04d88 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556ac9d051a8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556ac9d04ee0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x556ac9d04f60 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x556ac9d04fe0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556ac9d05060 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556ac9d05268 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556ac9d055e8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556ac9d05320 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x556ac9d053a0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x556ac9d05420 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x556ac9d054a0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x556ac9d056a8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556ac9d05938 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556ac9d05718 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x556ac9d05798 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x556ac9d05818 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x556ac9d059f0 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x556ac9d05a98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x556ac9d210e8 <col:20, col:33>
|   `-ParenExpr 0x556ac9d210c8 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x556ac9d210a8 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x556ac9d05c38 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x556ac9d05c08 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x556ac9d05be8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x556ac9d05bb8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x556ac9d05b58 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x556ac9d05b38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x556ac9d05b78 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x556ac9d05b98 <col:32> 'int' 0
|       `-UnaryOperator 0x556ac9d21090 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x556ac9d21070 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x556ac9d21058 <line:108:51, line:113:5>
|             `-IfStmt 0x556ac9d21030 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x556ac9d05c60 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:29> 'int' 0
|               |-NullStmt 0x556ac9d05c80 </usr/include/assert.h:110:9>
|               `-CallExpr 0x556ac9d20f60 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x556ac9d20f48 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x556ac9d20ce0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x556ac9d051a8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x556ac9d20fb8 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556ac9d20fa0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556ac9d20d38 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x556ac9d20fe8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x556ac9d20fd0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x556ac9d20d98 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h"
|                 |-ImplicitCastExpr 0x556ac9d21000 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x556ac9d20e18 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x556ac9d21018 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x556ac9d20f00 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x556ac9d20ee8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x556ac9d20eb8 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x556ac9d21198 prev 0x556ac9d04e28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556ac9d21318 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x556ac9d21250 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x556ac9d214c0 <col:36, line:7:1>
|   `-IfStmt 0x556ac9d214a8 <line:6:3, col:22>
|     |-UnaryOperator 0x556ac9d213f8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x556ac9d213e0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x556ac9d213c0 <col:7> 'int' lvalue ParmVar 0x556ac9d21250 'cond' 'int'
|     `-CompoundStmt 0x556ac9d21490 <col:13, col:22>
|       `-CallExpr 0x556ac9d21470 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x556ac9d21458 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x556ac9d21410 <col:14> 'void (void) __attribute__((noreturn))' Function 0x556ac9d21198 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x556ac9d21580 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x556ac9d214f0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x556ac9d21840 <col:34, line:13:1>
|   |-IfStmt 0x556ac9d21818 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x556ac9d21680 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x556ac9d21668 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x556ac9d21648 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x556ac9d21628 <col:9> 'int' lvalue ParmVar 0x556ac9d214f0 'cond' 'int'
|   | `-CompoundStmt 0x556ac9d21800 <col:16, line:11:3>
|   |   `-LabelStmt 0x556ac9d217e8 <line:10:3, col:33> 'ERROR'
|   |     `-CompoundStmt 0x556ac9d21778 <col:10, col:33>
|   |       |-CallExpr 0x556ac9d21700 <col:11, col:23> 'void'
|   |       | `-ImplicitCastExpr 0x556ac9d216e8 <col:11> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x556ac9d21698 <col:11> 'void ()' Function 0x556ac9d05a98 'reach_error' 'void ()'
|   |       `-CallExpr 0x556ac9d21758 <col:25, col:31> 'void'
|   |         `-ImplicitCastExpr 0x556ac9d21740 <col:25> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x556ac9d21720 <col:25> 'void (void) __attribute__((noreturn))' Function 0x556ac9d21198 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x556ac9d21830 <line:12:3>
|-FunctionDecl 0x556ac9d218b0 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x556ac9d21978 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c:2:1, line:13:1> line:2:5 main 'int ()'
  `-CompoundStmt 0x556ac9d22138 <col:12, line:13:1>
    |-DeclStmt 0x556ac9d21ab8 <line:3:5, col:14>
    | `-VarDecl 0x556ac9d21a30 <col:5, col:13> col:9 used i 'int' cinit
    |   `-IntegerLiteral 0x556ac9d21a98 <col:13> 'int' 0
    |-DeclStmt 0x556ac9d21b70 <line:4:5, col:14>
    | `-VarDecl 0x556ac9d21ae8 <col:5, col:13> col:9 used k 'int' cinit
    |   `-IntegerLiteral 0x556ac9d21b50 <col:13> 'int' 0
    |-WhileStmt 0x556ac9d21ff0 <line:5:5, line:10:5>
    | |-BinaryOperator 0x556ac9d21be0 <line:5:11, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:15:19> 'int' '<'
    | | |-ImplicitCastExpr 0x556ac9d21bc8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c:5:11> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x556ac9d21b88 <col:11> 'int' lvalue Var 0x556ac9d21a30 'i' 'int'
    | | `-IntegerLiteral 0x556ac9d21ba8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:15:19> 'int' 1000000
    | `-CompoundStmt 0x556ac9d21fc0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c:5:26, line:10:5>
    |   |-DeclStmt 0x556ac9d21d10 <line:6:9, col:40>
    |   | `-VarDecl 0x556ac9d21c18 <col:9, col:39> col:13 used j 'int' cinit
    |   |   `-CallExpr 0x556ac9d21cf0 <col:17, col:39> 'int'
    |   |     `-ImplicitCastExpr 0x556ac9d21cc8 <col:17> 'int (*)()' <FunctionToPointerDecay>
    |   |       `-DeclRefExpr 0x556ac9d21c80 <col:17> 'int ()' Function 0x556ac9d218b0 '__VERIFIER_nondet_int' 'int ()'
    |   |-IfStmt 0x556ac9d21ea0 <line:7:9, col:48>
    |   | |-UnaryOperator 0x556ac9d21e58 <col:13, col:38> 'int' prefix '!' cannot overflow
    |   | | `-ParenExpr 0x556ac9d21e38 <col:14, col:38> 'int'
    |   | |   `-BinaryOperator 0x556ac9d21e18 <col:15, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:15:19> 'int' '&&'
    |   | |     |-BinaryOperator 0x556ac9d21d80 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c:7:15, col:20> 'int' '<='
    |   | |     | |-IntegerLiteral 0x556ac9d21d28 <col:15> 'int' 1
    |   | |     | `-ImplicitCastExpr 0x556ac9d21d68 <col:20> 'int' <LValueToRValue>
    |   | |     |   `-DeclRefExpr 0x556ac9d21d48 <col:20> 'int' lvalue Var 0x556ac9d21c18 'j' 'int'
    |   | |     `-BinaryOperator 0x556ac9d21df8 <col:25, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:15:19> 'int' '<'
    |   | |       |-ImplicitCastExpr 0x556ac9d21de0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c:7:25> 'int' <LValueToRValue>
    |   | |       | `-DeclRefExpr 0x556ac9d21da0 <col:25> 'int' lvalue Var 0x556ac9d21c18 'j' 'int'
    |   | |       `-IntegerLiteral 0x556ac9d21dc0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:15:19> 'int' 1000000
    |   | `-ReturnStmt 0x556ac9d21e90 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c:7:41, col:48>
    |   |   `-IntegerLiteral 0x556ac9d21e70 <col:48> 'int' 0
    |   |-BinaryOperator 0x556ac9d21f68 <line:8:9, col:17> 'int' '='
    |   | |-DeclRefExpr 0x556ac9d21eb8 <col:9> 'int' lvalue Var 0x556ac9d21a30 'i' 'int'
    |   | `-BinaryOperator 0x556ac9d21f48 <col:13, col:17> 'int' '+'
    |   |   |-ImplicitCastExpr 0x556ac9d21f18 <col:13> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x556ac9d21ed8 <col:13> 'int' lvalue Var 0x556ac9d21a30 'i' 'int'
    |   |   `-ImplicitCastExpr 0x556ac9d21f30 <col:17> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x556ac9d21ef8 <col:17> 'int' lvalue Var 0x556ac9d21c18 'j' 'int'
    |   `-UnaryOperator 0x556ac9d21fa8 <line:9:9, col:11> 'int' postfix '++'
    |     `-DeclRefExpr 0x556ac9d21f88 <col:9> 'int' lvalue Var 0x556ac9d21ae8 'k' 'int'
    |-CallExpr 0x556ac9d220e0 <line:11:5, col:37> 'void'
    | |-ImplicitCastExpr 0x556ac9d220c8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x556ac9d22008 <col:5> 'void (int)' Function 0x556ac9d21580 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x556ac9d22080 <col:23, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:15:19> 'int' '<='
    |   |-ImplicitCastExpr 0x556ac9d22068 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c:11:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x556ac9d22028 <col:23> 'int' lvalue Var 0x556ac9d21ae8 'k' 'int'
    |   `-IntegerLiteral 0x556ac9d22048 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:15:19> 'int' 1000000
    `-ReturnStmt 0x556ac9d22128 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/count_by_nondet.c:12:5, col:12>
      `-IntegerLiteral 0x556ac9d22108 <col:12> 'int' 0
