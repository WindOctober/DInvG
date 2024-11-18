./Benchmark/PLDI/SVComp/loop-invgen/up.c
[info] Using default compilation options.
TranslationUnitDecl 0x564556d0adc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x564556d0b660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x564556d0b360 '__int128'
|-TypedefDecl 0x564556d0b6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x564556d0b380 'unsigned __int128'
|-TypedefDecl 0x564556d0b9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x564556d0b7b0 'struct __NSConstantString_tag'
|   `-Record 0x564556d0b728 '__NSConstantString_tag'
|-TypedefDecl 0x564556d0ba70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x564556d0ba30 'char *'
|   `-BuiltinType 0x564556d0ae60 'char'
|-TypedefDecl 0x564556d0bd68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x564556d0bd10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x564556d0bb50 'struct __va_list_tag'
|     `-Record 0x564556d0bac8 '__va_list_tag'
|-FunctionDecl 0x564556d6aab8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564556d6ab58 prev 0x564556d6aab8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564556d6aed8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564556d6ac10 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x564556d6ac90 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x564556d6ad10 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x564556d6ad90 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x564556d6af98 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564556d6b318 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564556d6b050 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x564556d6b0d0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x564556d6b150 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x564556d6b1d0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x564556d6b3d8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564556d6b668 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x564556d6b448 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x564556d6b4c8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x564556d6b548 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x564556d6b720 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x564556d6b7c8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x564556d870c8 <col:20, col:33>
|   `-ParenExpr 0x564556d870a8 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x564556d87088 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x564556d6b968 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x564556d6b938 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x564556d6b918 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x564556d6b8e8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x564556d6b888 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x564556d6b868 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x564556d6b8a8 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x564556d6b8c8 <col:32> 'int' 0
|       `-UnaryOperator 0x564556d87070 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x564556d87050 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x564556d87038 <line:108:51, line:113:5>
|             `-IfStmt 0x564556d87010 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x564556d6b990 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x564556d6b9b0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x564556d86f40 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x564556d86f28 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x564556d86cc0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x564556d6aed8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x564556d86f98 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x564556d86f80 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x564556d86d18 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x564556d86fc8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x564556d86fb0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x564556d86d78 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x564556d86fe0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x564556d86df8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x564556d86ff8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x564556d86ee0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x564556d86ec8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x564556d86e98 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x564556d87178 prev 0x564556d6ab58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x564556d872f8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x564556d87230 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x564556d874a0 <col:36, line:7:1>
|   `-IfStmt 0x564556d87488 <line:6:3, col:22>
|     |-UnaryOperator 0x564556d873d8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x564556d873c0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x564556d873a0 <col:7> 'int' lvalue ParmVar 0x564556d87230 'cond' 'int'
|     `-CompoundStmt 0x564556d87470 <col:13, col:22>
|       `-CallExpr 0x564556d87450 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x564556d87438 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x564556d873f0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x564556d87178 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x564556d87560 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x564556d874d0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x564556d87820 <col:34, line:13:1>
|   |-IfStmt 0x564556d877f8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x564556d87660 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x564556d87648 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x564556d87628 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x564556d87608 <col:9> 'int' lvalue ParmVar 0x564556d874d0 'cond' 'int'
|   | `-CompoundStmt 0x564556d877e0 <col:16, line:11:3>
|   |   `-LabelStmt 0x564556d877c8 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x564556d87758 <col:12, col:35>
|   |       |-CallExpr 0x564556d876e0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x564556d876c8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x564556d87678 <col:13> 'void ()' Function 0x564556d6b7c8 'reach_error' 'void ()'
|   |       `-CallExpr 0x564556d87738 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x564556d87720 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x564556d87700 <col:27> 'void (void) __attribute__((noreturn))' Function 0x564556d87178 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x564556d87810 <line:12:3>
|-FunctionDecl 0x564556d87890 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x564556d87958 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/up.c:3:1, line:18:1> line:3:5 main 'int ()'
  `-CompoundStmt 0x564556d88108 <col:12, line:18:1>
    |-DeclStmt 0x564556d87a78 <line:4:3, col:8>
    | `-VarDecl 0x564556d87a10 <col:3, col:7> col:7 used n 'int'
    |-DeclStmt 0x564556d87b30 <line:5:3, col:12>
    | `-VarDecl 0x564556d87aa8 <col:3, col:11> col:7 used i 'int' cinit
    |   `-IntegerLiteral 0x564556d87b10 <col:11> 'int' 0
    |-DeclStmt 0x564556d87be8 <line:6:3, col:12>
    | `-VarDecl 0x564556d87b60 <col:3, col:11> col:7 used k 'int' cinit
    |   `-IntegerLiteral 0x564556d87bc8 <col:11> 'int' 0
    |-BinaryOperator 0x564556d87ca0 <line:7:3, col:29> 'int' '='
    | |-DeclRefExpr 0x564556d87c00 <col:3> 'int' lvalue Var 0x564556d87a10 'n' 'int'
    | `-CallExpr 0x564556d87c80 <col:7, col:29> 'int'
    |   `-ImplicitCastExpr 0x564556d87c68 <col:7> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x564556d87c20 <col:7> 'int ()' Function 0x564556d87890 '__VERIFIER_nondet_int' 'int ()'
    |-WhileStmt 0x564556d87df0 <line:8:3, line:11:3>
    | |-BinaryOperator 0x564556d87d40 <line:8:10, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x564556d87d10 <col:10> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x564556d87cd0 <col:10> 'int' lvalue Var 0x564556d87aa8 'i' 'int'
    | | `-ImplicitCastExpr 0x564556d87d28 <col:14> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x564556d87cf0 <col:14> 'int' lvalue Var 0x564556d87a10 'n' 'int'
    | `-CompoundStmt 0x564556d87dd0 <col:18, line:11:3>
    |   |-UnaryOperator 0x564556d87d80 <line:9:2, col:3> 'int' postfix '++'
    |   | `-DeclRefExpr 0x564556d87d60 <col:2> 'int' lvalue Var 0x564556d87aa8 'i' 'int'
    |   `-UnaryOperator 0x564556d87db8 <line:10:2, col:3> 'int' postfix '++'
    |     `-DeclRefExpr 0x564556d87d98 <col:2> 'int' lvalue Var 0x564556d87b60 'k' 'int'
    |-DeclStmt 0x564556d87ea8 <line:12:3, col:12>
    | `-VarDecl 0x564556d87e20 <col:3, col:11> col:7 used j 'int' cinit
    |   `-IntegerLiteral 0x564556d87e88 <col:11> 'int' 0
    `-WhileStmt 0x564556d880f0 <line:13:3, line:17:3>
      |-BinaryOperator 0x564556d87f30 <line:13:10, col:14> 'int' '<'
      | |-ImplicitCastExpr 0x564556d87f00 <col:10> 'int' <LValueToRValue>
      | | `-DeclRefExpr 0x564556d87ec0 <col:10> 'int' lvalue Var 0x564556d87e20 'j' 'int'
      | `-ImplicitCastExpr 0x564556d87f18 <col:14> 'int' <LValueToRValue>
      |   `-DeclRefExpr 0x564556d87ee0 <col:14> 'int' lvalue Var 0x564556d87a10 'n' 'int'
      `-CompoundStmt 0x564556d880c8 <col:18, line:17:3>
        |-CallExpr 0x564556d88030 <line:14:5, col:29> 'void'
        | |-ImplicitCastExpr 0x564556d88018 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
        | | `-DeclRefExpr 0x564556d87f50 <col:5> 'void (int)' Function 0x564556d87560 '__VERIFIER_assert' 'void (int)'
        | `-BinaryOperator 0x564556d87fc8 <col:24, col:28> 'int' '>'
        |   |-ImplicitCastExpr 0x564556d87fb0 <col:24> 'int' <LValueToRValue>
        |   | `-DeclRefExpr 0x564556d87f70 <col:24> 'int' lvalue Var 0x564556d87b60 'k' 'int'
        |   `-IntegerLiteral 0x564556d87f90 <col:28> 'int' 0
        |-UnaryOperator 0x564556d88078 <line:15:5, col:6> 'int' postfix '++'
        | `-DeclRefExpr 0x564556d88058 <col:5> 'int' lvalue Var 0x564556d87e20 'j' 'int'
        `-UnaryOperator 0x564556d880b0 <line:16:5, col:6> 'int' postfix '--'
          `-DeclRefExpr 0x564556d88090 <col:5> 'int' lvalue Var 0x564556d87b60 'k' 'int'
