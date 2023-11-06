./Benchmark/PLDI/SVComp/loop-invgen/string_concat-noarr.c
[info] Using default compilation options.
TranslationUnitDecl 0x55f9da9edf28 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55f9da9ee7c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55f9da9ee4c0 '__int128'
|-TypedefDecl 0x55f9da9ee830 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55f9da9ee4e0 'unsigned __int128'
|-TypedefDecl 0x55f9da9eeb38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55f9da9ee910 'struct __NSConstantString_tag'
|   `-Record 0x55f9da9ee888 '__NSConstantString_tag'
|-TypedefDecl 0x55f9da9eebd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55f9da9eeb90 'char *'
|   `-BuiltinType 0x55f9da9edfc0 'char'
|-TypedefDecl 0x55f9da9eeec8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55f9da9eee70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55f9da9eecb0 'struct __va_list_tag'
|     `-Record 0x55f9da9eec28 '__va_list_tag'
|-FunctionDecl 0x55f9daa4de58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f9daa4def8 prev 0x55f9daa4de58 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f9daa4e278 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f9daa4dfb0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x55f9daa4e030 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x55f9daa4e0b0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55f9daa4e130 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55f9daa4e338 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55f9daa4e6b8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f9daa4e3f0 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x55f9daa4e470 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x55f9daa4e4f0 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55f9daa4e570 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55f9daa4e778 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55f9daa4ea08 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55f9daa4e7e8 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x55f9daa4e868 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x55f9daa4e8e8 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x55f9daa4eac0 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55f9daa4eb68 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55f9daa6a3b8 <col:20, col:33>
|   `-ParenExpr 0x55f9daa6a398 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x55f9daa6a378 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x55f9daa4ed08 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x55f9daa4ecd8 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x55f9daa4ecb8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x55f9daa4ec88 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x55f9daa4ec28 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x55f9daa4ec08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x55f9daa4ec48 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x55f9daa4ec68 <col:32> 'int' 0
|       `-UnaryOperator 0x55f9daa6a360 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x55f9daa6a340 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x55f9daa6a328 <line:108:51, line:113:5>
|             `-IfStmt 0x55f9daa6a300 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x55f9daa4ed30 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x55f9daa4ed50 </usr/include/assert.h:110:9>
|               `-CallExpr 0x55f9daa6a230 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x55f9daa6a218 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x55f9daa69fb0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55f9daa4e278 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x55f9daa6a288 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55f9daa6a270 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55f9daa6a008 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x55f9daa6a2b8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55f9daa6a2a0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55f9daa6a068 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x55f9daa6a2d0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x55f9daa6a0e8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x55f9daa6a2e8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x55f9daa6a1d0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x55f9daa6a1b8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x55f9daa6a188 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x55f9daa6a468 prev 0x55f9daa4def8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55f9daa6a5e8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55f9daa6a520 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55f9daa6a790 <col:36, line:7:1>
|   `-IfStmt 0x55f9daa6a778 <line:6:3, col:22>
|     |-UnaryOperator 0x55f9daa6a6c8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55f9daa6a6b0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55f9daa6a690 <col:7> 'int' lvalue ParmVar 0x55f9daa6a520 'cond' 'int'
|     `-CompoundStmt 0x55f9daa6a760 <col:13, col:22>
|       `-CallExpr 0x55f9daa6a740 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55f9daa6a728 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55f9daa6a6e0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55f9daa6a468 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55f9daa6a850 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55f9daa6a7c0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55f9daa6ab10 <col:34, line:13:1>
|   |-IfStmt 0x55f9daa6aae8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x55f9daa6a950 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55f9daa6a938 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55f9daa6a918 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55f9daa6a8f8 <col:9> 'int' lvalue ParmVar 0x55f9daa6a7c0 'cond' 'int'
|   | `-CompoundStmt 0x55f9daa6aad0 <col:16, line:11:3>
|   |   `-LabelStmt 0x55f9daa6aab8 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55f9daa6aa48 <col:12, col:35>
|   |       |-CallExpr 0x55f9daa6a9d0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55f9daa6a9b8 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55f9daa6a968 <col:13> 'void ()' Function 0x55f9daa4eb68 'reach_error' 'void ()'
|   |       `-CallExpr 0x55f9daa6aa28 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55f9daa6aa10 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55f9daa6a9f0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55f9daa6a468 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55f9daa6ab00 <line:12:3>
|-FunctionDecl 0x55f9daa6ab80 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x55f9daa6acf0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/string_concat-noarr.c:3:1, line:23:1> line:3:5 main 'int (void)'
  `-CompoundStmt 0x55f9daa6b6f8 <col:16, line:23:1>
    |-DeclStmt 0x55f9daa6aed0 <line:4:3, col:11>
    | |-VarDecl 0x55f9daa6add0 <col:3, col:7> col:7 used i 'int'
    | `-VarDecl 0x55f9daa6ae50 <col:3, col:10> col:10 used j 'int'
    |-LabelStmt 0x55f9daa6af98 <line:6:2, line:7:7> 'L0'
    | `-BinaryOperator 0x55f9daa6af28 <col:3, col:7> 'int' '='
    |   |-DeclRefExpr 0x55f9daa6aee8 <col:3> 'int' lvalue Var 0x55f9daa6add0 'i' 'int'
    |   `-IntegerLiteral 0x55f9daa6af08 <col:7> 'int' 0
    |-LabelStmt 0x55f9daa6b190 <line:8:2, line:12:3> 'L1'
    | `-WhileStmt 0x55f9daa6b128 <line:9:3, line:12:3>
    |   |-BinaryOperator 0x55f9daa6b0b8 <line:9:10, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '&&'
    |   | |-CallExpr 0x55f9daa6b020 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/string_concat-noarr.c:9:10, col:32> 'int'
    |   | | `-ImplicitCastExpr 0x55f9daa6b008 <col:10> 'int (*)()' <FunctionToPointerDecay>
    |   | |   `-DeclRefExpr 0x55f9daa6afc0 <col:10> 'int ()' Function 0x55f9daa6ab80 '__VERIFIER_nondet_int' 'int ()'
    |   | `-BinaryOperator 0x55f9daa6b098 <col:37, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '<'
    |   |   |-ImplicitCastExpr 0x55f9daa6b080 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/string_concat-noarr.c:9:37> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55f9daa6b040 <col:37> 'int' lvalue Var 0x55f9daa6add0 'i' 'int'
    |   |   `-IntegerLiteral 0x55f9daa6b060 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' 1000000
    |   `-CompoundStmt 0x55f9daa6b110 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/string_concat-noarr.c:9:51, line:12:3>
    |     `-UnaryOperator 0x55f9daa6b0f8 <line:11:5, col:6> 'int' postfix '++'
    |       `-DeclRefExpr 0x55f9daa6b0d8 <col:5> 'int' lvalue Var 0x55f9daa6add0 'i' 'int'
    |-IfStmt 0x55f9daa6b2a0 <line:13:3, col:28>
    | |-BinaryOperator 0x55f9daa6b200 <col:6, col:11> 'int' '>='
    | | |-ImplicitCastExpr 0x55f9daa6b1e8 <col:6> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f9daa6b1a8 <col:6> 'int' lvalue Var 0x55f9daa6add0 'i' 'int'
    | | `-IntegerLiteral 0x55f9daa6b1c8 <col:11> 'int' 100
    | `-LabelStmt 0x55f9daa6b288 <col:16, col:28> 'STUCK'
    |   `-GotoStmt 0x55f9daa6b270 <col:23, col:28> 'STUCK' 0x55f9daa6b220
    |-BinaryOperator 0x55f9daa6b2f8 <line:14:3, col:7> 'int' '='
    | |-DeclRefExpr 0x55f9daa6b2b8 <col:3> 'int' lvalue Var 0x55f9daa6ae50 'j' 'int'
    | `-IntegerLiteral 0x55f9daa6b2d8 <col:7> 'int' 0
    |-LabelStmt 0x55f9daa6b500 <line:15:2, line:19:3> 'L2'
    | `-WhileStmt 0x55f9daa6b498 <line:16:3, line:19:3>
    |   |-BinaryOperator 0x55f9daa6b3e8 <line:16:10, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '&&'
    |   | |-CallExpr 0x55f9daa6b350 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/string_concat-noarr.c:16:10, col:32> 'int'
    |   | | `-ImplicitCastExpr 0x55f9daa6b338 <col:10> 'int (*)()' <FunctionToPointerDecay>
    |   | |   `-DeclRefExpr 0x55f9daa6b318 <col:10> 'int ()' Function 0x55f9daa6ab80 '__VERIFIER_nondet_int' 'int ()'
    |   | `-BinaryOperator 0x55f9daa6b3c8 <col:37, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' '<'
    |   |   |-ImplicitCastExpr 0x55f9daa6b3b0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/string_concat-noarr.c:16:37> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55f9daa6b370 <col:37> 'int' lvalue Var 0x55f9daa6add0 'i' 'int'
    |   |   `-IntegerLiteral 0x55f9daa6b390 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:15:19> 'int' 1000000
    |   `-CompoundStmt 0x55f9daa6b478 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/string_concat-noarr.c:16:52, line:19:3>
    |     |-UnaryOperator 0x55f9daa6b428 <line:17:5, col:6> 'int' postfix '++'
    |     | `-DeclRefExpr 0x55f9daa6b408 <col:5> 'int' lvalue Var 0x55f9daa6add0 'i' 'int'
    |     `-UnaryOperator 0x55f9daa6b460 <line:18:5, col:6> 'int' postfix '++'
    |       `-DeclRefExpr 0x55f9daa6b440 <col:5> 'int' lvalue Var 0x55f9daa6ae50 'j' 'int'
    |-IfStmt 0x55f9daa6b5a8 <line:20:3, col:21>
    | |-BinaryOperator 0x55f9daa6b570 <col:6, col:11> 'int' '>='
    | | |-ImplicitCastExpr 0x55f9daa6b558 <col:6> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55f9daa6b518 <col:6> 'int' lvalue Var 0x55f9daa6ae50 'j' 'int'
    | | `-IntegerLiteral 0x55f9daa6b538 <col:11> 'int' 100
    | `-GotoStmt 0x55f9daa6b590 <col:16, col:21> 'STUCK' 0x55f9daa6b220
    |-CallExpr 0x55f9daa6b6a0 <line:21:3, col:30> 'void'
    | |-ImplicitCastExpr 0x55f9daa6b688 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55f9daa6b5c0 <col:3> 'void (int)' Function 0x55f9daa6a850 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55f9daa6b638 <col:22, col:26> 'int' '<'
    |   |-ImplicitCastExpr 0x55f9daa6b620 <col:22> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55f9daa6b5e0 <col:22> 'int' lvalue Var 0x55f9daa6add0 'i' 'int'
    |   `-IntegerLiteral 0x55f9daa6b600 <col:26> 'int' 200
    `-ReturnStmt 0x55f9daa6b6e8 <line:22:3, col:10>
      `-IntegerLiteral 0x55f9daa6b6c8 <col:10> 'int' 0
