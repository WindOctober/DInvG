./Benchmark/PLDI/SVComp/loop-lit/jm2006_variant.c
[info] Using default compilation options.
TranslationUnitDecl 0x557df58d6ee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x557df58d7780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x557df58d7480 '__int128'
|-TypedefDecl 0x557df58d77f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x557df58d74a0 'unsigned __int128'
|-TypedefDecl 0x557df58d7af8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x557df58d78d0 'struct __NSConstantString_tag'
|   `-Record 0x557df58d7848 '__NSConstantString_tag'
|-TypedefDecl 0x557df58d7b90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x557df58d7b50 'char *'
|   `-BuiltinType 0x557df58d6f80 'char'
|-TypedefDecl 0x557df58d7e88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x557df58d7e30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x557df58d7c70 'struct __va_list_tag'
|     `-Record 0x557df58d7be8 '__va_list_tag'
|-FunctionDecl 0x557df5936e98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557df5936f38 prev 0x557df5936e98 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557df59372b8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x557df5936ff0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x557df5937070 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x557df59370f0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x557df5937170 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x557df5937378 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x557df59376f8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x557df5937430 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x557df59374b0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x557df5937530 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x557df59375b0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x557df59377b8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x557df5937a48 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x557df5937828 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x557df59378a8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x557df5937928 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x557df5937b00 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x557df5937ba8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x557df59533f8 <col:20, col:33>
|   `-ParenExpr 0x557df59533d8 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x557df59533b8 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x557df5937d48 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x557df5937d18 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x557df5937cf8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x557df5937cc8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x557df5937c68 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x557df5937c48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x557df5937c88 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x557df5937ca8 <col:32> 'int' 0
|       `-UnaryOperator 0x557df59533a0 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x557df5953380 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x557df5953368 <line:108:51, line:113:5>
|             `-IfStmt 0x557df5953340 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x557df5937d70 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x557df5937d90 </usr/include/assert.h:110:9>
|               `-CallExpr 0x557df5953270 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x557df5953258 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x557df5952ff0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x557df59372b8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x557df59532c8 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x557df59532b0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x557df5953048 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x557df59532f8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x557df59532e0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x557df59530a8 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x557df5953310 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x557df5953128 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x557df5953328 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x557df5953210 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x557df59531f8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x557df59531c8 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x557df59534a8 prev 0x557df5936f38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x557df5953628 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x557df5953560 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x557df59537d0 <col:36, line:7:1>
|   `-IfStmt 0x557df59537b8 <line:6:3, col:22>
|     |-UnaryOperator 0x557df5953708 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x557df59536f0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x557df59536d0 <col:7> 'int' lvalue ParmVar 0x557df5953560 'cond' 'int'
|     `-CompoundStmt 0x557df59537a0 <col:13, col:22>
|       `-CallExpr 0x557df5953780 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x557df5953768 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x557df5953720 <col:14> 'void (void) __attribute__((noreturn))' Function 0x557df59534a8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x557df5953890 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x557df5953800 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x557df5953b50 <col:34, line:13:1>
|   |-IfStmt 0x557df5953b28 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x557df5953990 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x557df5953978 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x557df5953958 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x557df5953938 <col:9> 'int' lvalue ParmVar 0x557df5953800 'cond' 'int'
|   | `-CompoundStmt 0x557df5953b10 <col:16, line:11:3>
|   |   `-LabelStmt 0x557df5953af8 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x557df5953a88 <col:14, col:37>
|   |       |-CallExpr 0x557df5953a10 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x557df59539f8 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x557df59539a8 <col:15> 'void ()' Function 0x557df5937ba8 'reach_error' 'void ()'
|   |       `-CallExpr 0x557df5953a68 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x557df5953a50 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x557df5953a30 <col:29> 'void (void) __attribute__((noreturn))' Function 0x557df59534a8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x557df5953b40 <line:12:3>
|-FunctionDecl 0x557df5953bc0 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x557df5953c88 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/jm2006_variant.c:7:1, line:26:1> line:7:5 main 'int ()'
  `-CompoundStmt 0x557df5954878 <col:12, line:26:1>
    |-DeclStmt 0x557df5953e40 <line:8:5, col:13>
    | |-VarDecl 0x557df5953d40 <col:5, col:9> col:9 used i 'int'
    | `-VarDecl 0x557df5953dc0 <col:5, col:12> col:12 used j 'int'
    |-BinaryOperator 0x557df5953f00 <line:9:5, col:31> 'int' '='
    | |-DeclRefExpr 0x557df5953e58 <col:5> 'int' lvalue Var 0x557df5953d40 'i' 'int'
    | `-CallExpr 0x557df5953ee0 <col:9, col:31> 'int'
    |   `-ImplicitCastExpr 0x557df5953ec8 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x557df5953e78 <col:9> 'int ()' Function 0x557df5953bc0 '__VERIFIER_nondet_int' 'int ()'
    |-BinaryOperator 0x557df5953f98 <line:10:5, col:31> 'int' '='
    | |-DeclRefExpr 0x557df5953f20 <col:5> 'int' lvalue Var 0x557df5953dc0 'j' 'int'
    | `-CallExpr 0x557df5953f78 <col:9, col:31> 'int'
    |   `-ImplicitCastExpr 0x557df5953f60 <col:9> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x557df5953f40 <col:9> 'int ()' Function 0x557df5953bc0 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x557df5954158 <line:12:5, col:45>
    | |-UnaryOperator 0x557df5954110 <col:9, col:35> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x557df59540f0 <col:10, col:35> 'int'
    | |   `-BinaryOperator 0x557df59540d0 <col:11, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '&&'
    | |     |-BinaryOperator 0x557df5954038 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/jm2006_variant.c:12:11, col:16> 'int' '>='
    | |     | |-ImplicitCastExpr 0x557df5954020 <col:11> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x557df5953fb8 <col:11> 'int' lvalue Var 0x557df5953d40 'i' 'int'
    | |     | `-IntegerLiteral 0x557df5954000 <col:16> 'int' 0
    | |     `-BinaryOperator 0x557df59540b0 <col:21, /home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' '<='
    | |       |-ImplicitCastExpr 0x557df5954098 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/jm2006_variant.c:12:21> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x557df5954058 <col:21> 'int' lvalue Var 0x557df5953d40 'i' 'int'
    | |       `-IntegerLiteral 0x557df5954078 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:15:19> 'int' 1000000
    | `-ReturnStmt 0x557df5954148 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/jm2006_variant.c:12:38, col:45>
    |   `-IntegerLiteral 0x557df5954128 <col:45> 'int' 0
    |-IfStmt 0x557df5954250 <line:13:5, col:27>
    | |-UnaryOperator 0x557df5954208 <col:9, col:17> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x557df59541e8 <col:10, col:17> 'int'
    | |   `-BinaryOperator 0x557df59541c8 <col:11, col:16> 'int' '>='
    | |     |-ImplicitCastExpr 0x557df59541b0 <col:11> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x557df5954170 <col:11> 'int' lvalue Var 0x557df5953dc0 'j' 'int'
    | |     `-IntegerLiteral 0x557df5954190 <col:16> 'int' 0
    | `-ReturnStmt 0x557df5954240 <col:20, col:27>
    |   `-IntegerLiteral 0x557df5954220 <col:27> 'int' 0
    |-DeclStmt 0x557df5954320 <line:14:5, col:14>
    | `-VarDecl 0x557df5954280 <col:5, col:13> col:9 used x 'int' cinit
    |   `-ImplicitCastExpr 0x557df5954308 <col:13> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x557df59542e8 <col:13> 'int' lvalue Var 0x557df5953d40 'i' 'int'
    |-DeclStmt 0x557df59543f0 <line:15:5, col:14>
    | `-VarDecl 0x557df5954350 <col:5, col:13> col:9 used y 'int' cinit
    |   `-ImplicitCastExpr 0x557df59543d8 <col:13> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x557df59543b8 <col:13> 'int' lvalue Var 0x557df5953dc0 'j' 'int'
    |-DeclStmt 0x557df59544a8 <line:16:5, col:14>
    | `-VarDecl 0x557df5954420 <col:5, col:13> col:9 used z 'int' cinit
    |   `-IntegerLiteral 0x557df5954488 <col:13> 'int' 0
    |-WhileStmt 0x557df5954640 <line:17:5, line:21:5>
    | |-BinaryOperator 0x557df5954518 <line:17:11, col:16> 'int' '!='
    | | |-ImplicitCastExpr 0x557df5954500 <col:11> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x557df59544c0 <col:11> 'int' lvalue Var 0x557df5954280 'x' 'int'
    | | `-IntegerLiteral 0x557df59544e0 <col:16> 'int' 0
    | `-CompoundStmt 0x557df5954618 <col:19, line:21:5>
    |   |-UnaryOperator 0x557df5954558 <line:18:9, col:11> 'int' postfix '--'
    |   | `-DeclRefExpr 0x557df5954538 <col:9> 'int' lvalue Var 0x557df5954280 'x' 'int'
    |   |-CompoundAssignOperator 0x557df59545b0 <line:19:9, col:14> 'int' '-=' ComputeLHSTy='int' ComputeResultTy='int'
    |   | |-DeclRefExpr 0x557df5954570 <col:9> 'int' lvalue Var 0x557df5954350 'y' 'int'
    |   | `-IntegerLiteral 0x557df5954590 <col:14> 'int' 2
    |   `-UnaryOperator 0x557df5954600 <line:20:9, col:11> 'int' postfix '++'
    |     `-DeclRefExpr 0x557df59545e0 <col:9> 'int' lvalue Var 0x557df5954420 'z' 'int'
    |-IfStmt 0x557df5954830 <line:22:5, line:24:5>
    | |-BinaryOperator 0x557df59546c8 <line:22:9, col:14> 'int' '=='
    | | |-ImplicitCastExpr 0x557df5954698 <col:9> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x557df5954658 <col:9> 'int' lvalue Var 0x557df5953d40 'i' 'int'
    | | `-ImplicitCastExpr 0x557df59546b0 <col:14> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x557df5954678 <col:14> 'int' lvalue Var 0x557df5953dc0 'j' 'int'
    | `-CompoundStmt 0x557df5954818 <col:17, line:24:5>
    |   `-CallExpr 0x557df59547f0 <line:23:9, col:34> 'void'
    |     |-ImplicitCastExpr 0x557df59547d8 <col:9> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x557df59546e8 <col:9> 'void (int)' Function 0x557df5953890 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x557df5954790 <col:27, col:33> 'int' '=='
    |       |-ImplicitCastExpr 0x557df5954778 <col:27> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x557df5954708 <col:27> 'int' lvalue Var 0x557df5954350 'y' 'int'
    |       `-UnaryOperator 0x557df5954760 <col:32, col:33> 'int' prefix '-'
    |         `-ImplicitCastExpr 0x557df5954748 <col:33> 'int' <LValueToRValue>
    |           `-DeclRefExpr 0x557df5954728 <col:33> 'int' lvalue Var 0x557df5954420 'z' 'int'
    `-ReturnStmt 0x557df5954868 <line:25:5, col:12>
      `-IntegerLiteral 0x557df5954848 <col:12> 'int' 0
