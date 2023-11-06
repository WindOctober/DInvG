./Benchmark/PLDI/SVComp/loop-invgen/assert.h
[info] Using default compilation options.
TranslationUnitDecl 0x55ee99b6ddc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55ee99b6e660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55ee99b6e360 '__int128'
|-TypedefDecl 0x55ee99b6e6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55ee99b6e380 'unsigned __int128'
|-TypedefDecl 0x55ee99b6e9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55ee99b6e7b0 'struct __NSConstantString_tag'
|   `-Record 0x55ee99b6e728 '__NSConstantString_tag'
|-TypedefDecl 0x55ee99b6ea70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55ee99b6ea30 'char *'
|   `-BuiltinType 0x55ee99b6de60 'char'
|-TypedefDecl 0x55ee99b6ed68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55ee99b6ed10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55ee99b6eb50 'struct __va_list_tag'
|     `-Record 0x55ee99b6eac8 '__va_list_tag'
|-FunctionDecl 0x55ee99bcdc98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ee99bcdd38 prev 0x55ee99bcdc98 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ee99bce0b8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55ee99bcddf0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x55ee99bcde70 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x55ee99bcdef0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55ee99bcdf70 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55ee99bce178 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55ee99bce4f8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55ee99bce230 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x55ee99bce2b0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x55ee99bce330 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x55ee99bce3b0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x55ee99bce5b8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55ee99bce848 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55ee99bce628 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x55ee99bce6a8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x55ee99bce728 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x55ee99bce900 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x55ee99bce9a8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55ee99be9d78 <col:20, col:33>
|   `-ParenExpr 0x55ee99be9d58 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x55ee99be9d38 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x55ee99bceb48 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x55ee99bceb18 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x55ee99bceaf8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x55ee99bceac8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x55ee99bcea68 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x55ee99bcea48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x55ee99bcea88 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x55ee99bceaa8 <col:32> 'int' 0
|       `-UnaryOperator 0x55ee99be9d20 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x55ee99be9d00 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x55ee99be9ce8 <line:108:51, line:113:5>
|             `-IfStmt 0x55ee99be9cc0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x55ee99bceb70 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:3:29> 'int' 0
|               |-NullStmt 0x55ee99bceb90 </usr/include/assert.h:110:9>
|               `-CallExpr 0x55ee99be9bf0 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x55ee99be9bd8 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x55ee99be9970 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55ee99bce0b8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x55ee99be9c48 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55ee99be9c30 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55ee99be99c8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x55ee99be9c78 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x55ee99be9c60 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x55ee99be9a28 <col:1> 'char [101]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h"
|                 |-ImplicitCastExpr 0x55ee99be9c90 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x55ee99be9aa8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x55ee99be9ca8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x55ee99be9b90 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x55ee99be9b78 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x55ee99be9b48 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x55ee99be9e28 prev 0x55ee99bcdd38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-invgen/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55ee99be9fa8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55ee99be9ee0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55ee99bea150 <col:36, line:7:1>
|   `-IfStmt 0x55ee99bea138 <line:6:3, col:22>
|     |-UnaryOperator 0x55ee99bea088 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55ee99bea070 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55ee99bea050 <col:7> 'int' lvalue ParmVar 0x55ee99be9ee0 'cond' 'int'
|     `-CompoundStmt 0x55ee99bea120 <col:13, col:22>
|       `-CallExpr 0x55ee99bea100 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55ee99bea0e8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55ee99bea0a0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55ee99be9e28 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55ee99bea210 <line:8:1, line:13:1> line:8:6 __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55ee99bea180 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55ee99bea4d0 <col:34, line:13:1>
|   |-IfStmt 0x55ee99bea4a8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x55ee99bea310 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55ee99bea2f8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55ee99bea2d8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55ee99bea2b8 <col:9> 'int' lvalue ParmVar 0x55ee99bea180 'cond' 'int'
|   | `-CompoundStmt 0x55ee99bea490 <col:16, line:11:3>
|   |   `-LabelStmt 0x55ee99bea478 <line:10:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55ee99bea408 <col:12, col:35>
|   |       |-CallExpr 0x55ee99bea390 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55ee99bea378 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55ee99bea328 <col:13> 'void ()' Function 0x55ee99bce9a8 'reach_error' 'void ()'
|   |       `-CallExpr 0x55ee99bea3e8 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55ee99bea3d0 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55ee99bea3b0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55ee99be9e28 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55ee99bea4c0 <line:12:3>
`-FunctionDecl 0x55ee99bea540 <line:14:1, col:27> col:5 __VERIFIER_nondet_int 'int ()'
