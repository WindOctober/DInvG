./Benchmark/PLDI/SVComp/loop-new/assert.h
[info] Using default compilation options.
TranslationUnitDecl 0x559ac6e7ddc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x559ac6e7e660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x559ac6e7e360 '__int128'
|-TypedefDecl 0x559ac6e7e6d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x559ac6e7e380 'unsigned __int128'
|-TypedefDecl 0x559ac6e7e9d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x559ac6e7e7b0 'struct __NSConstantString_tag'
|   `-Record 0x559ac6e7e728 '__NSConstantString_tag'
|-TypedefDecl 0x559ac6e7ea70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x559ac6e7ea30 'char *'
|   `-BuiltinType 0x559ac6e7de60 'char'
|-TypedefDecl 0x559ac6e7ed68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x559ac6e7ed10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x559ac6e7eb50 'struct __va_list_tag'
|     `-Record 0x559ac6e7eac8 '__va_list_tag'
|-FunctionDecl 0x559ac6eddab8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559ac6eddb58 prev 0x559ac6eddab8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559ac6edded8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559ac6eddc10 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x559ac6eddc90 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x559ac6eddd10 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x559ac6eddd90 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x559ac6eddf98 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x559ac6ede318 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559ac6ede050 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x559ac6ede0d0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x559ac6ede150 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x559ac6ede1d0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x559ac6ede3d8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x559ac6ede668 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559ac6ede448 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x559ac6ede4c8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x559ac6ede548 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x559ac6ede720 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x559ac6ede7c8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x559ac6ef9b98 <col:20, col:33>
|   `-ParenExpr 0x559ac6ef9b78 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x559ac6ef9b58 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x559ac6ede968 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x559ac6ede938 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x559ac6ede918 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x559ac6ede8e8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x559ac6ede888 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x559ac6ede868 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x559ac6ede8a8 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x559ac6ede8c8 <col:32> 'int' 0
|       `-UnaryOperator 0x559ac6ef9b40 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x559ac6ef9b20 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x559ac6ef9b08 <line:108:51, line:113:5>
|             `-IfStmt 0x559ac6ef9ae0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x559ac6ede990 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:3:29> 'int' 0
|               |-NullStmt 0x559ac6ede9b0 </usr/include/assert.h:110:9>
|               `-CallExpr 0x559ac6ef9a10 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x559ac6ef99f8 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x559ac6ef9790 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x559ac6edded8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x559ac6ef9a68 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x559ac6ef9a50 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x559ac6ef97e8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x559ac6ef9a98 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x559ac6ef9a80 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x559ac6ef9848 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h"
|                 |-ImplicitCastExpr 0x559ac6ef9ab0 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x559ac6ef98c8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x559ac6ef9ac8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x559ac6ef99b0 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x559ac6ef9998 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x559ac6ef9968 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x559ac6ef9c48 prev 0x559ac6eddb58 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-new/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559ac6ef9dc8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x559ac6ef9d00 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x559ac6ef9f70 <col:36, line:7:1>
|   `-IfStmt 0x559ac6ef9f58 <line:6:3, col:22>
|     |-UnaryOperator 0x559ac6ef9ea8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x559ac6ef9e90 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x559ac6ef9e70 <col:7> 'int' lvalue ParmVar 0x559ac6ef9d00 'cond' 'int'
|     `-CompoundStmt 0x559ac6ef9f40 <col:13, col:22>
|       `-CallExpr 0x559ac6ef9f20 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x559ac6ef9f08 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x559ac6ef9ec0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x559ac6ef9c48 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x559ac6efa030 <line:8:1, line:13:1> line:8:6 __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x559ac6ef9fa0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x559ac6efa2f0 <col:34, line:13:1>
|   |-IfStmt 0x559ac6efa2c8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x559ac6efa130 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x559ac6efa118 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x559ac6efa0f8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x559ac6efa0d8 <col:9> 'int' lvalue ParmVar 0x559ac6ef9fa0 'cond' 'int'
|   | `-CompoundStmt 0x559ac6efa2b0 <col:16, line:11:3>
|   |   `-LabelStmt 0x559ac6efa298 <line:10:3, col:33> 'ERROR'
|   |     `-CompoundStmt 0x559ac6efa228 <col:10, col:33>
|   |       |-CallExpr 0x559ac6efa1b0 <col:11, col:23> 'void'
|   |       | `-ImplicitCastExpr 0x559ac6efa198 <col:11> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x559ac6efa148 <col:11> 'void ()' Function 0x559ac6ede7c8 'reach_error' 'void ()'
|   |       `-CallExpr 0x559ac6efa208 <col:25, col:31> 'void'
|   |         `-ImplicitCastExpr 0x559ac6efa1f0 <col:25> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x559ac6efa1d0 <col:25> 'void (void) __attribute__((noreturn))' Function 0x559ac6ef9c48 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x559ac6efa2e0 <line:12:3>
`-FunctionDecl 0x559ac6efa360 <line:14:1, col:27> col:5 __VERIFIER_nondet_int 'int ()'
