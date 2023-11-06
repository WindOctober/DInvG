./Benchmark/PLDI/SVComp/loop-lit/gr2006.c
[info] Using default compilation options.
TranslationUnitDecl 0x561b33d4edc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x561b33d4f660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x561b33d4f360 '__int128'
|-TypedefDecl 0x561b33d4f6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x561b33d4f380 'unsigned __int128'
|-TypedefDecl 0x561b33d4f9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x561b33d4f7b0 'struct __NSConstantString_tag'
|   `-Record 0x561b33d4f728 '__NSConstantString_tag'
|-TypedefDecl 0x561b33d4fa70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x561b33d4fa30 'char *'
|   `-BuiltinType 0x561b33d4ee60 'char'
|-TypedefDecl 0x561b33d4fd68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x561b33d4fd10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x561b33d4fb50 'struct __va_list_tag'
|     `-Record 0x561b33d4fac8 '__va_list_tag'
|-FunctionDecl 0x561b33daec98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x561b33daed38 prev 0x561b33daec98 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x561b33daf0b8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x561b33daedf0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x561b33daee70 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x561b33daeef0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x561b33daef70 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x561b33daf178 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x561b33daf4f8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x561b33daf230 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x561b33daf2b0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x561b33daf330 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x561b33daf3b0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x561b33daf5b8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x561b33daf848 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x561b33daf628 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x561b33daf6a8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x561b33daf728 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x561b33daf900 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x561b33daf9a8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x561b33dcb2a8 <col:20, col:33>
|   `-ParenExpr 0x561b33dcb288 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x561b33dcb268 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x561b33dafb48 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x561b33dafb18 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x561b33dafaf8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x561b33dafac8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x561b33dafa68 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x561b33dafa48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x561b33dafa88 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x561b33dafaa8 <col:32> 'int' 0
|       `-UnaryOperator 0x561b33dcb250 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x561b33dcb230 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x561b33dcb218 <line:108:51, line:113:5>
|             `-IfStmt 0x561b33dcb1f0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x561b33dafb70 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x561b33dafb90 </usr/include/assert.h:110:9>
|               `-CallExpr 0x561b33dcb120 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x561b33dcb108 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x561b33dcaea0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x561b33daf0b8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x561b33dcb178 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x561b33dcb160 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x561b33dcaef8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x561b33dcb1a8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x561b33dcb190 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x561b33dcaf58 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x561b33dcb1c0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x561b33dcafd8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x561b33dcb1d8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x561b33dcb0c0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x561b33dcb0a8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x561b33dcb078 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x561b33dcb358 prev 0x561b33daed38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x561b33dcb4d8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x561b33dcb410 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x561b33dcb680 <col:36, line:7:1>
|   `-IfStmt 0x561b33dcb668 <line:6:3, col:22>
|     |-UnaryOperator 0x561b33dcb5b8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x561b33dcb5a0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x561b33dcb580 <col:7> 'int' lvalue ParmVar 0x561b33dcb410 'cond' 'int'
|     `-CompoundStmt 0x561b33dcb650 <col:13, col:22>
|       `-CallExpr 0x561b33dcb630 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x561b33dcb618 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x561b33dcb5d0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x561b33dcb358 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x561b33dcb740 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x561b33dcb6b0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x561b33dcba00 <col:34, line:13:1>
|   |-IfStmt 0x561b33dcb9d8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x561b33dcb840 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x561b33dcb828 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x561b33dcb808 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x561b33dcb7e8 <col:9> 'int' lvalue ParmVar 0x561b33dcb6b0 'cond' 'int'
|   | `-CompoundStmt 0x561b33dcb9c0 <col:16, line:11:3>
|   |   `-LabelStmt 0x561b33dcb9a8 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x561b33dcb938 <col:14, col:37>
|   |       |-CallExpr 0x561b33dcb8c0 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x561b33dcb8a8 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x561b33dcb858 <col:15> 'void ()' Function 0x561b33daf9a8 'reach_error' 'void ()'
|   |       `-CallExpr 0x561b33dcb918 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x561b33dcb900 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x561b33dcb8e0 <col:29> 'void (void) __attribute__((noreturn))' Function 0x561b33dcb358 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x561b33dcb9f0 <line:12:3>
|-FunctionDecl 0x561b33dcba70 <line:14:1, col:27> col:5 __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x561b33dcbb38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gr2006.c:5:1, line:20:1> line:5:5 main 'int ()'
  `-CompoundStmt 0x561b33dcc338 <col:12, line:20:1>
    |-DeclStmt 0x561b33dcbcf0 <line:6:5, col:12>
    | |-VarDecl 0x561b33dcbbf0 <col:5, col:9> col:9 used x 'int'
    | `-VarDecl 0x561b33dcbc70 <col:5, col:11> col:11 used y 'int'
    |-BinaryOperator 0x561b33dcbd48 <line:7:5, col:9> 'int' '='
    | |-DeclRefExpr 0x561b33dcbd08 <col:5> 'int' lvalue Var 0x561b33dcbbf0 'x' 'int'
    | `-IntegerLiteral 0x561b33dcbd28 <col:9> 'int' 0
    |-BinaryOperator 0x561b33dcbda8 <line:8:5, col:9> 'int' '='
    | |-DeclRefExpr 0x561b33dcbd68 <col:5> 'int' lvalue Var 0x561b33dcbc70 'y' 'int'
    | `-IntegerLiteral 0x561b33dcbd88 <col:9> 'int' 0
    |-WhileStmt 0x561b33dcc1e8 <line:9:5, line:17:5>
    | |-IntegerLiteral 0x561b33dcbdc8 <line:9:12> 'int' 1
    | `-CompoundStmt 0x561b33dcc1c0 <col:15, line:17:5>
    |   |-IfStmt 0x561b33dcc0c8 <line:10:9, line:14:9> has_else
    |   | |-BinaryOperator 0x561b33dcbe40 <line:10:13, col:17> 'int' '<'
    |   | | |-ImplicitCastExpr 0x561b33dcbe28 <col:13> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x561b33dcbde8 <col:13> 'int' lvalue Var 0x561b33dcbbf0 'x' 'int'
    |   | | `-IntegerLiteral 0x561b33dcbe08 <col:17> 'int' 50
    |   | |-CompoundStmt 0x561b33dcc060 <col:21, line:12:9>
    |   | | `-UnaryOperator 0x561b33dcbe80 <line:11:13, col:14> 'int' postfix '++'
    |   | |   `-DeclRefExpr 0x561b33dcbe60 <col:13> 'int' lvalue Var 0x561b33dcbc70 'y' 'int'
    |   | `-CompoundStmt 0x561b33dcc0b0 <line:12:16, line:14:9>
    |   |   `-UnaryOperator 0x561b33dcc098 <line:13:13, col:14> 'int' postfix '--'
    |   |     `-DeclRefExpr 0x561b33dcc078 <col:13> 'int' lvalue Var 0x561b33dcbc70 'y' 'int'
    |   |-IfStmt 0x561b33dcc170 <line:15:9, col:20>
    |   | |-BinaryOperator 0x561b33dcc148 <col:13, col:17> 'int' '<'
    |   | | |-ImplicitCastExpr 0x561b33dcc130 <col:13> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x561b33dcc0f0 <col:13> 'int' lvalue Var 0x561b33dcbc70 'y' 'int'
    |   | | `-IntegerLiteral 0x561b33dcc110 <col:17> 'int' 0
    |   | `-BreakStmt 0x561b33dcc168 <col:20>
    |   `-UnaryOperator 0x561b33dcc1a8 <line:16:9, col:10> 'int' postfix '++'
    |     `-DeclRefExpr 0x561b33dcc188 <col:9> 'int' lvalue Var 0x561b33dcbbf0 'x' 'int'
    |-CallExpr 0x561b33dcc2e0 <line:18:5, col:31> 'void'
    | |-ImplicitCastExpr 0x561b33dcc2c8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x561b33dcc200 <col:5> 'void (int)' Function 0x561b33dcb740 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x561b33dcc278 <col:23, col:28> 'int' '=='
    |   |-ImplicitCastExpr 0x561b33dcc260 <col:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x561b33dcc220 <col:23> 'int' lvalue Var 0x561b33dcbbf0 'x' 'int'
    |   `-IntegerLiteral 0x561b33dcc240 <col:28> 'int' 100
    `-ReturnStmt 0x561b33dcc328 <line:19:5, col:12>
      `-IntegerLiteral 0x561b33dcc308 <col:12> 'int' 0
