./Benchmark/PLDI/SVComp/loop-lit/bhmr2007.c
[info] Using default compilation options.
TranslationUnitDecl 0x558c09513dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x558c09514660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x558c09514360 '__int128'
|-TypedefDecl 0x558c095146d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x558c09514380 'unsigned __int128'
|-TypedefDecl 0x558c095149d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x558c095147b0 'struct __NSConstantString_tag'
|   `-Record 0x558c09514728 '__NSConstantString_tag'
|-TypedefDecl 0x558c09514a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x558c09514a30 'char *'
|   `-BuiltinType 0x558c09513e60 'char'
|-TypedefDecl 0x558c09514d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x558c09514d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x558c09514b50 'struct __va_list_tag'
|     `-Record 0x558c09514ac8 '__va_list_tag'
|-FunctionDecl 0x558c09573d58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558c09573df8 prev 0x558c09573d58 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558c09574178 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x558c09573eb0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x558c09573f30 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x558c09573fb0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x558c09574030 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x558c09574238 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x558c095745b8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x558c095742f0 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x558c09574370 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x558c095743f0 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x558c09574470 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x558c09574678 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x558c09574908 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x558c095746e8 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x558c09574768 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x558c095747e8 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x558c095749c0 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x558c09574a68 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x558c09590368 <col:20, col:33>
|   `-ParenExpr 0x558c09590348 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x558c09590328 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x558c09574c08 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x558c09574bd8 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x558c09574bb8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x558c09574b88 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x558c09574b28 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x558c09574b08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x558c09574b48 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x558c09574b68 <col:32> 'int' 0
|       `-UnaryOperator 0x558c09590310 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x558c095902f0 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x558c095902d8 <line:108:51, line:113:5>
|             `-IfStmt 0x558c095902b0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x558c09574c30 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x558c09574c50 </usr/include/assert.h:110:9>
|               `-CallExpr 0x558c095901e0 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x558c095901c8 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x558c0958ff60 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x558c09574178 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x558c09590238 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x558c09590220 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x558c0958ffb8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x558c09590268 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x558c09590250 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x558c09590018 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x558c09590280 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x558c09590098 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x558c09590298 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x558c09590180 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x558c09590168 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x558c09590138 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x558c09590418 prev 0x558c09573df8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x558c09590598 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x558c095904d0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x558c09590740 <col:36, line:7:1>
|   `-IfStmt 0x558c09590728 <line:6:3, col:22>
|     |-UnaryOperator 0x558c09590678 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x558c09590660 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x558c09590640 <col:7> 'int' lvalue ParmVar 0x558c095904d0 'cond' 'int'
|     `-CompoundStmt 0x558c09590710 <col:13, col:22>
|       `-CallExpr 0x558c095906f0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x558c095906d8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x558c09590690 <col:14> 'void (void) __attribute__((noreturn))' Function 0x558c09590418 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x558c09590800 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x558c09590770 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x558c09590ac0 <col:34, line:13:1>
|   |-IfStmt 0x558c09590a98 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x558c09590900 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x558c095908e8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x558c095908c8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x558c095908a8 <col:9> 'int' lvalue ParmVar 0x558c09590770 'cond' 'int'
|   | `-CompoundStmt 0x558c09590a80 <col:16, line:11:3>
|   |   `-LabelStmt 0x558c09590a68 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x558c095909f8 <col:14, col:37>
|   |       |-CallExpr 0x558c09590980 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x558c09590968 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x558c09590918 <col:15> 'void ()' Function 0x558c09574a68 'reach_error' 'void ()'
|   |       `-CallExpr 0x558c095909d8 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x558c095909c0 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x558c095909a0 <col:29> 'void (void) __attribute__((noreturn))' Function 0x558c09590418 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x558c09590ab0 <line:12:3>
|-FunctionDecl 0x558c09590b30 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x558c09590bf8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/bhmr2007.c:5:1, line:21:1> line:5:5 main 'int ()'
  `-CompoundStmt 0x558c09591968 <col:12, line:21:1>
    |-DeclStmt 0x558c09590ec0 <line:6:5, col:19>
    | |-VarDecl 0x558c09590cb0 <col:5, col:9> col:9 used i 'int'
    | |-VarDecl 0x558c09590d30 <col:5, col:12> col:12 used n 'int'
    | |-VarDecl 0x558c09590db0 <col:5, col:15> col:15 used a 'int'
    | `-VarDecl 0x558c09590e30 <col:5, col:18> col:18 used b 'int'
    |-BinaryOperator 0x558c09590f18 <line:7:5, col:9> 'int' '='
    | |-DeclRefExpr 0x558c09590ed8 <col:5> 'int' lvalue Var 0x558c09590cb0 'i' 'int'
    | `-IntegerLiteral 0x558c09590ef8 <col:9> 'int' 0
    |-BinaryOperator 0x558c09590f90 <col:12, col:16> 'int' '='
    | |-DeclRefExpr 0x558c09590f38 <col:12> 'int' lvalue Var 0x558c09590db0 'a' 'int'
    | `-IntegerLiteral 0x558c09590f70 <col:16> 'int' 0
    |-BinaryOperator 0x558c09590ff0 <col:19, col:23> 'int' '='
    | |-DeclRefExpr 0x558c09590fb0 <col:19> 'int' lvalue Var 0x558c09590e30 'b' 'int'
    | `-IntegerLiteral 0x558c09590fd0 <col:23> 'int' 0
    |-BinaryOperator 0x558c095910b0 <col:26, col:52> 'int' '='
    | |-DeclRefExpr 0x558c09591010 <col:26> 'int' lvalue Var 0x558c09590d30 'n' 'int'
    | `-CallExpr 0x558c09591090 <col:30, col:52> 'int'
    |   `-ImplicitCastExpr 0x558c09591078 <col:30> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x558c09591030 <col:30> 'int ()' Function 0x558c09590b30 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x558c09591248 <line:8:5, col:45>
    | |-UnaryOperator 0x558c09591200 <col:9, col:35> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x558c095911e0 <col:10, col:35> 'int'
    | |   `-BinaryOperator 0x558c095911c0 <col:11, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '&&'
    | |     |-BinaryOperator 0x558c09591128 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/bhmr2007.c:8:11, col:16> 'int' '>='
    | |     | |-ImplicitCastExpr 0x558c09591110 <col:11> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x558c095910d0 <col:11> 'int' lvalue Var 0x558c09590d30 'n' 'int'
    | |     | `-IntegerLiteral 0x558c095910f0 <col:16> 'int' 0
    | |     `-BinaryOperator 0x558c095911a0 <col:21, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '<='
    | |       |-ImplicitCastExpr 0x558c09591188 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/bhmr2007.c:8:21> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x558c09591148 <col:21> 'int' lvalue Var 0x558c09590d30 'n' 'int'
    | |       `-IntegerLiteral 0x558c09591168 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' 1000000
    | `-ReturnStmt 0x558c09591238 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/bhmr2007.c:8:38, col:45>
    |   `-IntegerLiteral 0x558c09591218 <col:45> 'int' 0
    |-WhileStmt 0x558c09591768 <line:9:5, line:18:5>
    | |-BinaryOperator 0x558c095912d0 <line:9:12, col:16> 'int' '<'
    | | |-ImplicitCastExpr 0x558c095912a0 <col:12> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x558c09591260 <col:12> 'int' lvalue Var 0x558c09590cb0 'i' 'int'
    | | `-ImplicitCastExpr 0x558c095912b8 <col:16> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x558c09591280 <col:16> 'int' lvalue Var 0x558c09590d30 'n' 'int'
    | `-CompoundStmt 0x558c09591748 <col:19, line:18:5>
    |   |-IfStmt 0x558c09591668 <line:10:9, line:16:9> has_else
    |   | |-CallExpr 0x558c09591328 <line:10:13, col:35> 'int'
    |   | | `-ImplicitCastExpr 0x558c09591310 <col:13> 'int (*)()' <FunctionToPointerDecay>
    |   | |   `-DeclRefExpr 0x558c095912f0 <col:13> 'int ()' Function 0x558c09590b30 '__VERIFIER_nondet_int' 'int ()'
    |   | |-CompoundStmt 0x558c095914b8 <col:38, line:13:9>
    |   | | |-BinaryOperator 0x558c095913e0 <line:11:13, col:21> 'int' '='
    |   | | | |-DeclRefExpr 0x558c09591348 <col:13> 'int' lvalue Var 0x558c09590db0 'a' 'int'
    |   | | | `-BinaryOperator 0x558c095913c0 <col:17, col:21> 'int' '+'
    |   | | |   |-ImplicitCastExpr 0x558c095913a8 <col:17> 'int' <LValueToRValue>
    |   | | |   | `-DeclRefExpr 0x558c09591368 <col:17> 'int' lvalue Var 0x558c09590db0 'a' 'int'
    |   | | |   `-IntegerLiteral 0x558c09591388 <col:21> 'int' 1
    |   | | `-BinaryOperator 0x558c09591498 <line:12:13, col:21> 'int' '='
    |   | |   |-DeclRefExpr 0x558c09591400 <col:13> 'int' lvalue Var 0x558c09590e30 'b' 'int'
    |   | |   `-BinaryOperator 0x558c09591478 <col:17, col:21> 'int' '+'
    |   | |     |-ImplicitCastExpr 0x558c09591460 <col:17> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x558c09591420 <col:17> 'int' lvalue Var 0x558c09590e30 'b' 'int'
    |   | |     `-IntegerLiteral 0x558c09591440 <col:21> 'int' 2
    |   | `-CompoundStmt 0x558c09591648 <line:13:16, line:16:9>
    |   |   |-BinaryOperator 0x558c09591570 <line:14:13, col:21> 'int' '='
    |   |   | |-DeclRefExpr 0x558c095914d8 <col:13> 'int' lvalue Var 0x558c09590db0 'a' 'int'
    |   |   | `-BinaryOperator 0x558c09591550 <col:17, col:21> 'int' '+'
    |   |   |   |-ImplicitCastExpr 0x558c09591538 <col:17> 'int' <LValueToRValue>
    |   |   |   | `-DeclRefExpr 0x558c095914f8 <col:17> 'int' lvalue Var 0x558c09590db0 'a' 'int'
    |   |   |   `-IntegerLiteral 0x558c09591518 <col:21> 'int' 2
    |   |   `-BinaryOperator 0x558c09591628 <line:15:13, col:21> 'int' '='
    |   |     |-DeclRefExpr 0x558c09591590 <col:13> 'int' lvalue Var 0x558c09590e30 'b' 'int'
    |   |     `-BinaryOperator 0x558c09591608 <col:17, col:21> 'int' '+'
    |   |       |-ImplicitCastExpr 0x558c095915f0 <col:17> 'int' <LValueToRValue>
    |   |       | `-DeclRefExpr 0x558c095915b0 <col:17> 'int' lvalue Var 0x558c09590e30 'b' 'int'
    |   |       `-IntegerLiteral 0x558c095915d0 <col:21> 'int' 1
    |   `-BinaryOperator 0x558c09591728 <line:17:9, col:17> 'int' '='
    |     |-DeclRefExpr 0x558c09591690 <col:9> 'int' lvalue Var 0x558c09590cb0 'i' 'int'
    |     `-BinaryOperator 0x558c09591708 <col:13, col:17> 'int' '+'
    |       |-ImplicitCastExpr 0x558c095916f0 <col:13> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x558c095916b0 <col:13> 'int' lvalue Var 0x558c09590cb0 'i' 'int'
    |       `-IntegerLiteral 0x558c095916d0 <col:17> 'int' 1
    |-CallExpr 0x558c09591910 <line:19:5, col:35> 'void'
    | |-ImplicitCastExpr 0x558c095918f8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x558c09591780 <col:5> 'void (int)' Function 0x558c09590800 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x558c095918a8 <col:23, col:34> 'int' '=='
    |   |-BinaryOperator 0x558c09591810 <col:23, col:27> 'int' '+'
    |   | |-ImplicitCastExpr 0x558c095917e0 <col:23> 'int' <LValueToRValue>
    |   | | `-DeclRefExpr 0x558c095917a0 <col:23> 'int' lvalue Var 0x558c09590db0 'a' 'int'
    |   | `-ImplicitCastExpr 0x558c095917f8 <col:27> 'int' <LValueToRValue>
    |   |   `-DeclRefExpr 0x558c095917c0 <col:27> 'int' lvalue Var 0x558c09590e30 'b' 'int'
    |   `-BinaryOperator 0x558c09591888 <col:32, col:34> 'int' '*'
    |     |-IntegerLiteral 0x558c09591830 <col:32> 'int' 3
    |     `-ImplicitCastExpr 0x558c09591870 <col:34> 'int' <LValueToRValue>
    |       `-DeclRefExpr 0x558c09591850 <col:34> 'int' lvalue Var 0x558c09590d30 'n' 'int'
    `-ReturnStmt 0x558c09591958 <line:20:5, col:12>
      `-IntegerLiteral 0x558c09591938 <col:12> 'int' 0
