./Benchmark/PLDI/SVComp/loop-lit/afnp2014.c
[info] Using default compilation options.
TranslationUnitDecl 0x55be1539bdc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55be1539c660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55be1539c360 '__int128'
|-TypedefDecl 0x55be1539c6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55be1539c380 'unsigned __int128'
|-TypedefDecl 0x55be1539c9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55be1539c7b0 'struct __NSConstantString_tag'
|   `-Record 0x55be1539c728 '__NSConstantString_tag'
|-TypedefDecl 0x55be1539ca70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55be1539ca30 'char *'
|   `-BuiltinType 0x55be1539be60 'char'
|-TypedefDecl 0x55be1539cd68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55be1539cd10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55be1539cb50 'struct __va_list_tag'
|     `-Record 0x55be1539cac8 '__va_list_tag'
|-FunctionDecl 0x55be153fbab8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55be153fbb58 prev 0x55be153fbab8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55be153fbed8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55be153fbc10 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x55be153fbc90 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x55be153fbd10 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55be153fbd90 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55be153fbf98 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55be153fc318 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55be153fc050 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x55be153fc0d0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x55be153fc150 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55be153fc1d0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55be153fc3d8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55be153fc668 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55be153fc448 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x55be153fc4c8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x55be153fc548 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x55be153fc720 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55be153fc7c8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55be154180c8 <col:20, col:33>
|   `-ParenExpr 0x55be154180a8 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x55be15418088 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x55be153fc968 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x55be153fc938 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x55be153fc918 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x55be153fc8e8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x55be153fc888 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x55be153fc868 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x55be153fc8a8 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x55be153fc8c8 <col:32> 'int' 0
|       `-UnaryOperator 0x55be15418070 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x55be15418050 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x55be15418038 <line:108:51, line:113:5>
|             `-IfStmt 0x55be15418010 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x55be153fc990 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x55be153fc9b0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x55be15417f40 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x55be15417f28 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x55be15417cc0 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55be153fbed8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x55be15417f98 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55be15417f80 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55be15417d18 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x55be15417fc8 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55be15417fb0 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55be15417d78 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x55be15417fe0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x55be15417df8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x55be15417ff8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x55be15417ee0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x55be15417ec8 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x55be15417e98 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x55be15418178 prev 0x55be153fbb58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55be154182f8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55be15418230 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55be154184a0 <col:36, line:7:1>
|   `-IfStmt 0x55be15418488 <line:6:3, col:22>
|     |-UnaryOperator 0x55be154183d8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55be154183c0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55be154183a0 <col:7> 'int' lvalue ParmVar 0x55be15418230 'cond' 'int'
|     `-CompoundStmt 0x55be15418470 <col:13, col:22>
|       `-CallExpr 0x55be15418450 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55be15418438 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55be154183f0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55be15418178 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55be15418560 <line:8:1, line:13:1> line:8:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55be154184d0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55be15418820 <col:34, line:13:1>
|   |-IfStmt 0x55be154187f8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x55be15418660 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55be15418648 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55be15418628 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55be15418608 <col:9> 'int' lvalue ParmVar 0x55be154184d0 'cond' 'int'
|   | `-CompoundStmt 0x55be154187e0 <col:16, line:11:3>
|   |   `-LabelStmt 0x55be154187c8 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x55be15418758 <col:14, col:37>
|   |       |-CallExpr 0x55be154186e0 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x55be154186c8 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55be15418678 <col:15> 'void ()' Function 0x55be153fc7c8 'reach_error' 'void ()'
|   |       `-CallExpr 0x55be15418738 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x55be15418720 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55be15418700 <col:29> 'void (void) __attribute__((noreturn))' Function 0x55be15418178 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55be15418810 <line:12:3>
|-FunctionDecl 0x55be15418890 <line:14:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
`-FunctionDecl 0x55be15418958 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/afnp2014.c:7:1, line:16:1> line:7:5 main 'int ()'
  `-CompoundStmt 0x55be15418f98 <col:12, line:16:1>
    |-DeclStmt 0x55be15418a98 <line:8:5, col:14>
    | `-VarDecl 0x55be15418a10 <col:5, col:13> col:9 used x 'int' cinit
    |   `-IntegerLiteral 0x55be15418a78 <col:13> 'int' 1
    |-DeclStmt 0x55be15418b50 <line:9:5, col:14>
    | `-VarDecl 0x55be15418ac8 <col:5, col:13> col:9 used y 'int' cinit
    |   `-IntegerLiteral 0x55be15418b30 <col:13> 'int' 0
    |-WhileStmt 0x55be15418e38 <line:10:5, line:13:5>
    | |-BinaryOperator 0x55be15418c60 <line:10:12, col:46> 'int' '&&'
    | | |-BinaryOperator 0x55be15418bc0 <col:12, col:16> 'int' '<'
    | | | |-ImplicitCastExpr 0x55be15418ba8 <col:12> 'int' <LValueToRValue>
    | | | | `-DeclRefExpr 0x55be15418b68 <col:12> 'int' lvalue Var 0x55be15418ac8 'y' 'int'
    | | | `-IntegerLiteral 0x55be15418b88 <col:16> 'int' 1000
    | | `-CallExpr 0x55be15418c40 <col:24, col:46> 'int'
    | |   `-ImplicitCastExpr 0x55be15418c28 <col:24> 'int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55be15418be0 <col:24> 'int ()' Function 0x55be15418890 '__VERIFIER_nondet_int' 'int ()'
    | `-CompoundStmt 0x55be15418e18 <col:49, line:13:5>
    |   |-BinaryOperator 0x55be15418d40 <line:11:9, col:17> 'int' '='
    |   | |-DeclRefExpr 0x55be15418c80 <col:9> 'int' lvalue Var 0x55be15418a10 'x' 'int'
    |   | `-BinaryOperator 0x55be15418d20 <col:13, col:17> 'int' '+'
    |   |   |-ImplicitCastExpr 0x55be15418cf0 <col:13> 'int' <LValueToRValue>
    |   |   | `-DeclRefExpr 0x55be15418ca0 <col:13> 'int' lvalue Var 0x55be15418a10 'x' 'int'
    |   |   `-ImplicitCastExpr 0x55be15418d08 <col:17> 'int' <LValueToRValue>
    |   |     `-DeclRefExpr 0x55be15418cd0 <col:17> 'int' lvalue Var 0x55be15418ac8 'y' 'int'
    |   `-BinaryOperator 0x55be15418df8 <line:12:9, col:17> 'int' '='
    |     |-DeclRefExpr 0x55be15418d60 <col:9> 'int' lvalue Var 0x55be15418ac8 'y' 'int'
    |     `-BinaryOperator 0x55be15418dd8 <col:13, col:17> 'int' '+'
    |       |-ImplicitCastExpr 0x55be15418dc0 <col:13> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55be15418d80 <col:13> 'int' lvalue Var 0x55be15418ac8 'y' 'int'
    |       `-IntegerLiteral 0x55be15418da0 <col:17> 'int' 1
    |-CallExpr 0x55be15418f40 <line:14:5, col:29> 'void'
    | |-ImplicitCastExpr 0x55be15418f28 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55be15418e50 <col:5> 'void (int)' Function 0x55be15418560 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55be15418ee0 <col:23, col:28> 'int' '>='
    |   |-ImplicitCastExpr 0x55be15418eb0 <col:23> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55be15418e70 <col:23> 'int' lvalue Var 0x55be15418a10 'x' 'int'
    |   `-ImplicitCastExpr 0x55be15418ec8 <col:28> 'int' <LValueToRValue>
    |     `-DeclRefExpr 0x55be15418e90 <col:28> 'int' lvalue Var 0x55be15418ac8 'y' 'int'
    `-ReturnStmt 0x55be15418f88 <line:15:5, col:12>
      `-IntegerLiteral 0x55be15418f68 <col:12> 'int' 0
