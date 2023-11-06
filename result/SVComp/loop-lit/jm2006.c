./Benchmark/PLDI/SVComp/loop-lit/jm2006.c
[info] Using default compilation options.
TranslationUnitDecl 0x5622edd58dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5622edd59660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5622edd59360 '__int128'
|-TypedefDecl 0x5622edd596d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5622edd59380 'unsigned __int128'
|-TypedefDecl 0x5622edd599d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5622edd597b0 'struct __NSConstantString_tag'
|   `-Record 0x5622edd59728 '__NSConstantString_tag'
|-TypedefDecl 0x5622edd59a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5622edd59a30 'char *'
|   `-BuiltinType 0x5622edd58e60 'char'
|-TypedefDecl 0x5622edd59d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5622edd59d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5622edd59b50 'struct __va_list_tag'
|     `-Record 0x5622edd59ac8 '__va_list_tag'
|-FunctionDecl 0x5622eddb8d18 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5622eddb8db8 prev 0x5622eddb8d18 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5622eddb9138 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5622eddb8e70 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x5622eddb8ef0 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x5622eddb8f70 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x5622eddb8ff0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x5622eddb91f8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x5622eddb9578 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5622eddb92b0 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x5622eddb9330 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x5622eddb93b0 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x5622eddb9430 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x5622eddb9638 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x5622eddb98c8 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5622eddb96a8 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x5622eddb9728 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x5622eddb97a8 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x5622eddb9980 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x5622eddb9a28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5622eddd5328 <col:20, col:33>
|   `-ParenExpr 0x5622eddd5308 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x5622eddd52e8 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x5622eddb9bc8 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x5622eddb9b98 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x5622eddb9b78 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x5622eddb9b48 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x5622eddb9ae8 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x5622eddb9ac8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x5622eddb9b08 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x5622eddb9b28 <col:32> 'int' 0
|       `-UnaryOperator 0x5622eddd52d0 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x5622eddd52b0 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x5622eddd5298 <line:108:51, line:113:5>
|             `-IfStmt 0x5622eddd5270 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x5622eddb9bf0 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x5622eddb9c10 </usr/include/assert.h:110:9>
|               `-CallExpr 0x5622eddd51a0 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x5622eddd5188 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x5622eddd4f20 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5622eddb9138 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x5622eddd51f8 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x5622eddd51e0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x5622eddd4f78 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x5622eddd5228 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x5622eddd5210 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x5622eddd4fd8 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x5622eddd5240 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x5622eddd5058 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x5622eddd5258 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x5622eddd5140 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x5622eddd5128 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x5622eddd50f8 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x5622eddd53d8 prev 0x5622eddb8db8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5622eddd5558 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x5622eddd5490 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x5622eddd5700 <col:36, line:7:1>
|   `-IfStmt 0x5622eddd56e8 <line:6:3, col:22>
|     |-UnaryOperator 0x5622eddd5638 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5622eddd5620 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5622eddd5600 <col:7> 'int' lvalue ParmVar 0x5622eddd5490 'cond' 'int'
|     `-CompoundStmt 0x5622eddd56d0 <col:13, col:22>
|       `-CallExpr 0x5622eddd56b0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x5622eddd5698 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5622eddd5650 <col:14> 'void (void) __attribute__((noreturn))' Function 0x5622eddd53d8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5622eddd57c0 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5622eddd5730 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5622eddd5a80 <col:34, line:13:1>
|   |-IfStmt 0x5622eddd5a58 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x5622eddd58c0 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5622eddd58a8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5622eddd5888 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5622eddd5868 <col:9> 'int' lvalue ParmVar 0x5622eddd5730 'cond' 'int'
|   | `-CompoundStmt 0x5622eddd5a40 <col:16, line:11:3>
|   |   `-LabelStmt 0x5622eddd5a28 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x5622eddd59b8 <col:14, col:37>
|   |       |-CallExpr 0x5622eddd5940 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x5622eddd5928 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5622eddd58d8 <col:15> 'void ()' Function 0x5622eddb9a28 'reach_error' 'void ()'
|   |       `-CallExpr 0x5622eddd5998 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x5622eddd5980 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5622eddd5960 <col:29> 'void (void) __attribute__((noreturn))' Function 0x5622eddd53d8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5622eddd5a70 <line:12:3>
|-FunctionDecl 0x5622eddd5af0 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x5622eddd5bb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/jm2006.c:7:1, line:23:1> line:7:5 main 'int ()'
  `-CompoundStmt 0x5622eddd6558 <col:12, line:23:1>
    |-DeclStmt 0x5622eddd5d70 <line:8:5, col:13>
    | |-VarDecl 0x5622eddd5c70 <col:5, col:9> col:9 used i 'int'
    | `-VarDecl 0x5622eddd5cf0 <col:5, col:12> col:12 used j 'int'
    |-BinaryOperator 0x5622eddd5e30 <line:9:5, col:31> 'int' '='
    | |-DeclRefExpr 0x5622eddd5d88 <col:5> 'int' lvalue Var 0x5622eddd5c70 'i' 'int'
    | `-CallExpr 0x5622eddd5e10 <col:9, col:31> 'int'
    |   `-ImplicitCastExpr 0x5622eddd5df8 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x5622eddd5da8 <col:9> 'int ()' Function 0x5622eddd5af0 '__VERIFIER_nondet_int' 'int ()'
    |-BinaryOperator 0x5622eddd5ec8 <line:10:5, col:31> 'int' '='
    | |-DeclRefExpr 0x5622eddd5e50 <col:5> 'int' lvalue Var 0x5622eddd5cf0 'j' 'int'
    | `-CallExpr 0x5622eddd5ea8 <col:9, col:31> 'int'
    |   `-ImplicitCastExpr 0x5622eddd5e90 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x5622eddd5e70 <col:9> 'int ()' Function 0x5622eddd5af0 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x5622eddd6088 <line:11:5, col:37>
    | |-UnaryOperator 0x5622eddd6040 <col:9, col:27> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x5622eddd6020 <col:10, col:27> 'int'
    | |   `-BinaryOperator 0x5622eddd6000 <col:11, col:26> 'int' '&&'
    | |     |-BinaryOperator 0x5622eddd5f68 <col:11, col:16> 'int' '>='
    | |     | |-ImplicitCastExpr 0x5622eddd5f50 <col:11> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x5622eddd5ee8 <col:11> 'int' lvalue Var 0x5622eddd5c70 'i' 'int'
    | |     | `-IntegerLiteral 0x5622eddd5f30 <col:16> 'int' 0
    | |     `-BinaryOperator 0x5622eddd5fe0 <col:21, col:26> 'int' '>='
    | |       |-ImplicitCastExpr 0x5622eddd5fc8 <col:21> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x5622eddd5f88 <col:21> 'int' lvalue Var 0x5622eddd5cf0 'j' 'int'
    | |       `-IntegerLiteral 0x5622eddd5fa8 <col:26> 'int' 0
    | `-ReturnStmt 0x5622eddd6078 <col:30, col:37>
    |   `-IntegerLiteral 0x5622eddd6058 <col:37> 'int' 0
    |-DeclStmt 0x5622eddd6158 <line:12:5, col:14>
    | `-VarDecl 0x5622eddd60b8 <col:5, col:13> col:9 used x 'int' cinit
    |   `-ImplicitCastExpr 0x5622eddd6140 <col:13> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x5622eddd6120 <col:13> 'int' lvalue Var 0x5622eddd5c70 'i' 'int'
    |-DeclStmt 0x5622eddd6228 <line:13:5, col:14>
    | `-VarDecl 0x5622eddd6188 <col:5, col:13> col:9 used y 'int' cinit
    |   `-ImplicitCastExpr 0x5622eddd6210 <col:13> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x5622eddd61f0 <col:13> 'int' lvalue Var 0x5622eddd5cf0 'j' 'int'
    |-WhileStmt 0x5622eddd6348 <line:14:5, line:17:5>
    | |-BinaryOperator 0x5622eddd6298 <line:14:11, col:16> 'int' '!='
    | | |-ImplicitCastExpr 0x5622eddd6280 <col:11> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5622eddd6240 <col:11> 'int' lvalue Var 0x5622eddd60b8 'x' 'int'
    | | `-IntegerLiteral 0x5622eddd6260 <col:16> 'int' 0
    | `-CompoundStmt 0x5622eddd6328 <col:19, line:17:5>
    |   |-UnaryOperator 0x5622eddd62d8 <line:15:9, col:10> 'int' postfix '--'
    |   | `-DeclRefExpr 0x5622eddd62b8 <col:9> 'int' lvalue Var 0x5622eddd60b8 'x' 'int'
    |   `-UnaryOperator 0x5622eddd6310 <line:16:9, col:10> 'int' postfix '--'
    |     `-DeclRefExpr 0x5622eddd62f0 <col:9> 'int' lvalue Var 0x5622eddd6188 'y' 'int'
    |-IfStmt 0x5622eddd6510 <line:19:5, line:21:5>
    | |-BinaryOperator 0x5622eddd63d0 <line:19:9, col:14> 'int' '=='
    | | |-ImplicitCastExpr 0x5622eddd63a0 <col:9> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5622eddd6360 <col:9> 'int' lvalue Var 0x5622eddd5c70 'i' 'int'
    | | `-ImplicitCastExpr 0x5622eddd63b8 <col:14> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x5622eddd6380 <col:14> 'int' lvalue Var 0x5622eddd5cf0 'j' 'int'
    | `-CompoundStmt 0x5622eddd64f8 <col:17, line:21:5>
    |   `-CallExpr 0x5622eddd64d0 <line:20:9, col:33> 'void'
    |     |-ImplicitCastExpr 0x5622eddd64b8 <col:9> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x5622eddd63f0 <col:9> 'void (int)' Function 0x5622eddd57c0 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x5622eddd6468 <col:27, col:32> 'int' '=='
    |       |-ImplicitCastExpr 0x5622eddd6450 <col:27> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x5622eddd6410 <col:27> 'int' lvalue Var 0x5622eddd6188 'y' 'int'
    |       `-IntegerLiteral 0x5622eddd6430 <col:32> 'int' 0
    `-ReturnStmt 0x5622eddd6548 <line:22:5, col:12>
      `-IntegerLiteral 0x5622eddd6528 <col:12> 'int' 0
