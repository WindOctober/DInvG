./Benchmark/PLDI/SVComp/loop-invgen/nest-if3.c
[info] Using default compilation options.
TranslationUnitDecl 0x5610804eedc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5610804ef660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5610804ef360 '__int128'
|-TypedefDecl 0x5610804ef6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5610804ef380 'unsigned __int128'
|-TypedefDecl 0x5610804ef9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5610804ef7b0 'struct __NSConstantString_tag'
|   `-Record 0x5610804ef728 '__NSConstantString_tag'
|-TypedefDecl 0x5610804efa70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5610804efa30 'char *'
|   `-BuiltinType 0x5610804eee60 'char'
|-TypedefDecl 0x5610804efd68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5610804efd10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5610804efb50 'struct __va_list_tag'
|     `-Record 0x5610804efac8 '__va_list_tag'
|-FunctionDecl 0x56108054ec98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56108054ed38 prev 0x56108054ec98 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56108054f0b8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x56108054edf0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x56108054ee70 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x56108054eef0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x56108054ef70 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x56108054f178 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x56108054f4f8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x56108054f230 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x56108054f2b0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x56108054f330 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x56108054f3b0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x56108054f5b8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x56108054f848 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x56108054f628 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x56108054f6a8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x56108054f728 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x56108054f900 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x56108054f9a8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x56108056b2a8 <col:20, col:33>
|   `-ParenExpr 0x56108056b288 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x56108056b268 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x56108054fb48 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x56108054fb18 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x56108054faf8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x56108054fac8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x56108054fa68 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x56108054fa48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x56108054fa88 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x56108054faa8 <col:32> 'int' 0
|       `-UnaryOperator 0x56108056b250 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x56108056b230 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x56108056b218 <line:108:51, line:113:5>
|             `-IfStmt 0x56108056b1f0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x56108054fb70 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x56108054fb90 </usr/include/assert.h:110:9>
|               `-CallExpr 0x56108056b120 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x56108056b108 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x56108056aea0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x56108054f0b8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x56108056b178 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x56108056b160 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x56108056aef8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x56108056b1a8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x56108056b190 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x56108056af58 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x56108056b1c0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x56108056afd8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x56108056b1d8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x56108056b0c0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x56108056b0a8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x56108056b078 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x56108056b358 prev 0x56108054ed38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56108056b4d8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x56108056b410 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x56108056b680 <col:36, line:7:1>
|   `-IfStmt 0x56108056b668 <line:6:3, col:22>
|     |-UnaryOperator 0x56108056b5b8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x56108056b5a0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x56108056b580 <col:7> 'int' lvalue ParmVar 0x56108056b410 'cond' 'int'
|     `-CompoundStmt 0x56108056b650 <col:13, col:22>
|       `-CallExpr 0x56108056b630 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x56108056b618 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x56108056b5d0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x56108056b358 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x56108056b740 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x56108056b6b0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x56108056ba00 <col:34, line:13:1>
|   |-IfStmt 0x56108056b9d8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x56108056b840 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x56108056b828 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x56108056b808 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x56108056b7e8 <col:9> 'int' lvalue ParmVar 0x56108056b6b0 'cond' 'int'
|   | `-CompoundStmt 0x56108056b9c0 <col:16, line:11:3>
|   |   `-LabelStmt 0x56108056b9a8 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x56108056b938 <col:12, col:35>
|   |       |-CallExpr 0x56108056b8c0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x56108056b8a8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x56108056b858 <col:13> 'void ()' Function 0x56108054f9a8 'reach_error' 'void ()'
|   |       `-CallExpr 0x56108056b918 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x56108056b900 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x56108056b8e0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x56108056b358 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x56108056b9f0 <line:12:3>
|-FunctionDecl 0x56108056ba70 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x56108056bb38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/nest-if3.c:2:1, line:17:2> line:2:5 main 'int ()'
  `-CompoundStmt 0x56108056c7a8 <col:12, line:17:2>
    |-DeclStmt 0x56108056be00 <line:3:3, col:14>
    | |-VarDecl 0x56108056bbf0 <col:3, col:7> col:7 used i 'int'
    | |-VarDecl 0x56108056bc70 <col:3, col:9> col:9 used k 'int'
    | |-VarDecl 0x56108056bcf0 <col:3, col:11> col:11 used n 'int'
    | `-VarDecl 0x56108056bd70 <col:3, col:13> col:13 used l 'int'
    |-BinaryOperator 0x56108056bed0 <line:5:3, col:29> 'int' '='
    | |-DeclRefExpr 0x56108056be18 <col:3> 'int' lvalue Var 0x56108056bcf0 'n' 'int'
    | `-CallExpr 0x56108056beb0 <col:7, col:29> 'int'
    |   `-ImplicitCastExpr 0x56108056be88 <col:7> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x56108056be38 <col:7> 'int ()' Function 0x56108056ba70 '__VERIFIER_nondet_int' 'int ()'
    |-BinaryOperator 0x56108056bf68 <line:6:3, col:29> 'int' '='
    | |-DeclRefExpr 0x56108056bef0 <col:3> 'int' lvalue Var 0x56108056bd70 'l' 'int'
    | `-CallExpr 0x56108056bf48 <col:7, col:29> 'int'
    |   `-ImplicitCastExpr 0x56108056bf30 <col:7> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x56108056bf10 <col:7> 'int ()' Function 0x56108056ba70 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x56108056c068 <line:7:3, col:22>
    | |-UnaryOperator 0x56108056c020 <col:7, col:12> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x56108056c000 <col:8, col:12> 'int'
    | |   `-BinaryOperator 0x56108056bfe0 <col:9, col:11> 'int' '>'
    | |     |-ImplicitCastExpr 0x56108056bfc8 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x56108056bf88 <col:9> 'int' lvalue Var 0x56108056bd70 'l' 'int'
    | |     `-IntegerLiteral 0x56108056bfa8 <col:11> 'int' 0
    | `-ReturnStmt 0x56108056c058 <col:15, col:22>
    |   `-IntegerLiteral 0x56108056c038 <col:22> 'int' 0
    |-IfStmt 0x56108056c160 <line:8:3, col:32>
    | |-UnaryOperator 0x56108056c118 <col:7, col:22> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x56108056c0f8 <col:8, col:22> 'int'
    | |   `-BinaryOperator 0x56108056c0d8 <col:9, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '<'
    | |     |-ImplicitCastExpr 0x56108056c0c0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/nest-if3.c:8:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x56108056c080 <col:9> 'int' lvalue Var 0x56108056bd70 'l' 'int'
    | |     `-IntegerLiteral 0x56108056c0a0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' 1000000
    | `-ReturnStmt 0x56108056c150 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/nest-if3.c:8:25, col:32>
    |   `-IntegerLiteral 0x56108056c130 <col:32> 'int' 0
    |-IfStmt 0x56108056c258 <line:9:3, col:32>
    | |-UnaryOperator 0x56108056c210 <col:7, col:22> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x56108056c1f0 <col:8, col:22> 'int'
    | |   `-BinaryOperator 0x56108056c1d0 <col:9, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '<'
    | |     |-ImplicitCastExpr 0x56108056c1b8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/nest-if3.c:9:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x56108056c178 <col:9> 'int' lvalue Var 0x56108056bcf0 'n' 'int'
    | |     `-IntegerLiteral 0x56108056c198 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' 1000000
    | `-ReturnStmt 0x56108056c248 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/nest-if3.c:9:25, col:32>
    |   `-IntegerLiteral 0x56108056c228 <col:32> 'int' 0
    `-ForStmt 0x56108056c770 <line:10:3, line:16:3>
      |-BinaryOperator 0x56108056c2b0 <line:10:8, col:10> 'int' '='
      | |-DeclRefExpr 0x56108056c270 <col:8> 'int' lvalue Var 0x56108056bc70 'k' 'int'
      | `-IntegerLiteral 0x56108056c290 <col:10> 'int' 1
      |-<<<NULL>>>
      |-BinaryOperator 0x56108056c340 <col:12, col:14> 'int' '<'
      | |-ImplicitCastExpr 0x56108056c310 <col:12> 'int' <LValueToRValue>
      | | `-DeclRefExpr 0x56108056c2d0 <col:12> 'int' lvalue Var 0x56108056bc70 'k' 'int'
      | `-ImplicitCastExpr 0x56108056c328 <col:14> 'int' <LValueToRValue>
      |   `-DeclRefExpr 0x56108056c2f0 <col:14> 'int' lvalue Var 0x56108056bcf0 'n' 'int'
      |-UnaryOperator 0x56108056c380 <col:16, col:17> 'int' postfix '++'
      | `-DeclRefExpr 0x56108056c360 <col:16> 'int' lvalue Var 0x56108056bc70 'k' 'int'
      `-CompoundStmt 0x56108056c750 <col:20, line:16:3>
        |-ForStmt 0x56108056c5f0 <line:11:5, line:13:5>
        | |-BinaryOperator 0x56108056c3f0 <line:11:10, col:12> 'int' '='
        | | |-DeclRefExpr 0x56108056c398 <col:10> 'int' lvalue Var 0x56108056bbf0 'i' 'int'
        | | `-ImplicitCastExpr 0x56108056c3d8 <col:12> 'int' <LValueToRValue>
        | |   `-DeclRefExpr 0x56108056c3b8 <col:12> 'int' lvalue Var 0x56108056bd70 'l' 'int'
        | |-<<<NULL>>>
        | |-BinaryOperator 0x56108056c480 <col:14, col:16> 'int' '<'
        | | |-ImplicitCastExpr 0x56108056c450 <col:14> 'int' <LValueToRValue>
        | | | `-DeclRefExpr 0x56108056c410 <col:14> 'int' lvalue Var 0x56108056bbf0 'i' 'int'
        | | `-ImplicitCastExpr 0x56108056c468 <col:16> 'int' <LValueToRValue>
        | |   `-DeclRefExpr 0x56108056c430 <col:16> 'int' lvalue Var 0x56108056bcf0 'n' 'int'
        | |-UnaryOperator 0x56108056c4c0 <col:18, col:19> 'int' postfix '++'
        | | `-DeclRefExpr 0x56108056c4a0 <col:18> 'int' lvalue Var 0x56108056bbf0 'i' 'int'
        | `-CompoundStmt 0x56108056c5d8 <col:22, line:13:5>
        |   `-CallExpr 0x56108056c5b0 <line:12:7, col:29> 'void'
        |     |-ImplicitCastExpr 0x56108056c598 <col:7> 'void (*)(int)' <FunctionToPointerDecay>
        |     | `-DeclRefExpr 0x56108056c4d8 <col:7> 'void (int)' Function 0x56108056b740 '__VERIFIER_assert' 'void (int)'
        |     `-BinaryOperator 0x56108056c550 <col:25, col:28> 'int' '<='
        |       |-IntegerLiteral 0x56108056c4f8 <col:25> 'int' 1
        |       `-ImplicitCastExpr 0x56108056c538 <col:28> 'int' <LValueToRValue>
        |         `-DeclRefExpr 0x56108056c518 <col:28> 'int' lvalue Var 0x56108056bbf0 'i' 'int'
        `-IfStmt 0x56108056c738 <line:14:5, line:15:15>
          |-CallExpr 0x56108056c660 <line:14:8, col:30> 'int'
          | `-ImplicitCastExpr 0x56108056c648 <col:8> 'int (*)()' <FunctionToPointerDecay>
          |   `-DeclRefExpr 0x56108056c628 <col:8> 'int ()' Function 0x56108056ba70 '__VERIFIER_nondet_int' 'int ()'
          `-BinaryOperator 0x56108056c718 <line:15:7, col:15> 'int' '='
            |-DeclRefExpr 0x56108056c680 <col:7> 'int' lvalue Var 0x56108056bd70 'l' 'int'
            `-BinaryOperator 0x56108056c6f8 <col:11, col:15> 'int' '+'
              |-ImplicitCastExpr 0x56108056c6e0 <col:11> 'int' <LValueToRValue>
              | `-DeclRefExpr 0x56108056c6a0 <col:11> 'int' lvalue Var 0x56108056bd70 'l' 'int'
              `-IntegerLiteral 0x56108056c6c0 <col:15> 'int' 1
