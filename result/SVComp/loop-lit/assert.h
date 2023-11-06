./Benchmark/PLDI/SVComp/loop-lit/assert.h
[info] Using default compilation options.
TranslationUnitDecl 0x559bd2f84dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x559bd2f85660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x559bd2f85360 '__int128'
|-TypedefDecl 0x559bd2f856d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x559bd2f85380 'unsigned __int128'
|-TypedefDecl 0x559bd2f859d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x559bd2f857b0 'struct __NSConstantString_tag'
|   `-Record 0x559bd2f85728 '__NSConstantString_tag'
|-TypedefDecl 0x559bd2f85a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x559bd2f85a30 'char *'
|   `-BuiltinType 0x559bd2f84e60 'char'
|-TypedefDecl 0x559bd2f85d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x559bd2f85d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x559bd2f85b50 'struct __va_list_tag'
|     `-Record 0x559bd2f85ac8 '__va_list_tag'
|-FunctionDecl 0x559bd2fe4c98 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559bd2fe4d38 prev 0x559bd2fe4c98 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559bd2fe50b8 </usr/include/assert.h:69:1, line:71:43> line:69:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559bd2fe4df0 <col:28, col:40> col:40 __assertion 'const char *'
| |-ParmVarDecl 0x559bd2fe4e70 <col:53, col:65> col:65 __file 'const char *'
| |-ParmVarDecl 0x559bd2fe4ef0 <line:70:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x559bd2fe4f70 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x559bd2fe5178 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x559bd2fe54f8 </usr/include/assert.h:74:1, line:76:43> line:74:13 __assert_perror_fail 'void (int, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559bd2fe5230 <col:35, col:39> col:39 __errnum 'int'
| |-ParmVarDecl 0x559bd2fe52b0 <col:49, col:61> col:61 __file 'const char *'
| |-ParmVarDecl 0x559bd2fe5330 <line:75:7, col:20> col:20 __line 'unsigned int'
| |-ParmVarDecl 0x559bd2fe53b0 <col:28, col:40> col:40 __function 'const char *'
| `-NoThrowAttr 0x559bd2fe55b8 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x559bd2fe5848 </usr/include/assert.h:81:1, line:82:43> line:81:13 __assert 'void (const char *, const char *, int) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x559bd2fe5628 <col:23, col:35> col:35 __assertion 'const char *'
| |-ParmVarDecl 0x559bd2fe56a8 <col:48, col:60> col:60 __file 'const char *'
| |-ParmVarDecl 0x559bd2fe5728 <col:68, col:72> col:72 __line 'int'
| `-NoThrowAttr 0x559bd2fe5900 </usr/include/x86_64-linux-gnu/sys/cdefs.h:55:35>
|-FunctionDecl 0x559bd2fe59a8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x559bd3000d78 <col:20, col:33>
|   `-ParenExpr 0x559bd3000d58 </usr/include/assert.h:108:3, line:113:7> 'void'
|     `-BinaryOperator 0x559bd3000d38 <line:108:4, line:113:6> 'void' ','
|       |-CStyleCastExpr 0x559bd2fe5b48 <line:108:4, col:33> 'void' <ToVoid>
|       | `-UnaryExprOrTypeTraitExpr 0x559bd2fe5b18 <col:11, col:33> 'unsigned long' sizeof
|       |   `-ParenExpr 0x559bd2fe5af8 <col:18, col:33> 'int'
|       |     `-ConditionalOperator 0x559bd2fe5ac8 <col:19, col:32> 'int'
|       |       |-ParenExpr 0x559bd2fe5a68 <col:19, col:24> 'int'
|       |       | `-IntegerLiteral 0x559bd2fe5a48 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|       |       |-IntegerLiteral 0x559bd2fe5a88 </usr/include/assert.h:108:28> 'int' 1
|       |       `-IntegerLiteral 0x559bd2fe5aa8 <col:32> 'int' 0
|       `-UnaryOperator 0x559bd3000d20 <col:36, line:113:6> 'void' prefix '__extension__' cannot overflow
|         `-StmtExpr 0x559bd3000d00 <line:108:50, line:113:6> 'void'
|           `-CompoundStmt 0x559bd3000ce8 <line:108:51, line:113:5>
|             `-IfStmt 0x559bd3000cc0 <line:109:7, line:112:68> has_else
|               |-IntegerLiteral 0x559bd2fe5b70 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:3:29> 'int' 0
|               |-NullStmt 0x559bd2fe5b90 </usr/include/assert.h:110:9>
|               `-CallExpr 0x559bd3000bf0 <line:112:9, col:68> 'void'
|                 |-ImplicitCastExpr 0x559bd3000bd8 <col:9> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|                 | `-DeclRefExpr 0x559bd3000970 <col:9> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x559bd2fe50b8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|                 |-ImplicitCastExpr 0x559bd3000c48 <<scratch space>:4:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x559bd3000c30 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x559bd30009c8 <col:1> 'char [2]' lvalue "0"
|                 |-ImplicitCastExpr 0x559bd3000c78 <line:5:1> 'const char *' <NoOp>
|                 | `-ImplicitCastExpr 0x559bd3000c60 <col:1> 'char *' <ArrayToPointerDecay>
|                 |   `-StringLiteral 0x559bd3000a28 <col:1> 'char [98]' lvalue "/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h"
|                 |-ImplicitCastExpr 0x559bd3000c90 <line:6:1> 'unsigned int' <IntegralCast>
|                 | `-IntegerLiteral 0x559bd3000aa8 <col:1> 'int' 3
|                 `-ImplicitCastExpr 0x559bd3000ca8 </usr/include/assert.h:129:30, col:44> 'const char *' <ArrayToPointerDecay>
|                   `-UnaryOperator 0x559bd3000b90 <col:30, col:44> 'const char [19]' lvalue prefix '__extension__' cannot overflow
|                     `-PredefinedExpr 0x559bd3000b78 <col:44> 'const char [19]' lvalue __PRETTY_FUNCTION__
|                       `-StringLiteral 0x559bd3000b48 <col:44> 'const char [19]' lvalue "void reach_error()"
|-FunctionDecl 0x559bd3000e28 prev 0x559bd2fe4d38 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/assert.h:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x559bd3000fa8 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x559bd3000ee0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x559bd3001150 <col:36, line:7:1>
|   `-IfStmt 0x559bd3001138 <line:6:3, col:22>
|     |-UnaryOperator 0x559bd3001088 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x559bd3001070 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x559bd3001050 <col:7> 'int' lvalue ParmVar 0x559bd3000ee0 'cond' 'int'
|     `-CompoundStmt 0x559bd3001120 <col:13, col:22>
|       `-CallExpr 0x559bd3001100 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x559bd30010e8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x559bd30010a0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x559bd3000e28 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x559bd3001210 <line:8:1, line:13:1> line:8:6 __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x559bd3001180 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x559bd30014d0 <col:34, line:13:1>
|   |-IfStmt 0x559bd30014a8 <line:9:3, line:11:3>
|   | |-UnaryOperator 0x559bd3001310 <line:9:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x559bd30012f8 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x559bd30012d8 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x559bd30012b8 <col:9> 'int' lvalue ParmVar 0x559bd3001180 'cond' 'int'
|   | `-CompoundStmt 0x559bd3001490 <col:16, line:11:3>
|   |   `-LabelStmt 0x559bd3001478 <line:10:7, col:37> 'ERROR'
|   |     `-CompoundStmt 0x559bd3001408 <col:14, col:37>
|   |       |-CallExpr 0x559bd3001390 <col:15, col:27> 'void'
|   |       | `-ImplicitCastExpr 0x559bd3001378 <col:15> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x559bd3001328 <col:15> 'void ()' Function 0x559bd2fe59a8 'reach_error' 'void ()'
|   |       `-CallExpr 0x559bd30013e8 <col:29, col:35> 'void'
|   |         `-ImplicitCastExpr 0x559bd30013d0 <col:29> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x559bd30013b0 <col:29> 'void (void) __attribute__((noreturn))' Function 0x559bd3000e28 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x559bd30014c0 <line:12:3>
`-FunctionDecl 0x559bd3001540 <line:14:1, col:27> col:5 __VERIFIER_nondet_int 'int ()'
