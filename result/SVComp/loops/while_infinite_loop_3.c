./Benchmark/PLDI/SVComp/loops/while_infinite_loop_3.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/while_infinite_loop_3.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5606d2a2cee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5606d2a2d780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5606d2a2d480 '__int128'
|-TypedefDecl 0x5606d2a2d7f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5606d2a2d4a0 'unsigned __int128'
|-TypedefDecl 0x5606d2a2daf8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5606d2a2d8d0 'struct __NSConstantString_tag'
|   `-Record 0x5606d2a2d848 '__NSConstantString_tag'
|-TypedefDecl 0x5606d2a2db90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5606d2a2db50 'char *'
|   `-BuiltinType 0x5606d2a2cf80 'char'
|-TypedefDecl 0x5606d2a2de88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5606d2a2de30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5606d2a2dc70 'struct __va_list_tag'
|     `-Record 0x5606d2a2dbe8 '__va_list_tag'
|-FunctionDecl 0x5606d2a8cea8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/while_infinite_loop_3.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5606d2a8cf48 prev 0x5606d2a8cea8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5606d2a8d2c8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5606d2a8d000 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5606d2a8d080 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5606d2a8d100 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5606d2a8d180 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5606d2a8d388 <col:99>
|-FunctionDecl 0x5606d2a8d478 <line:3:1, col:87> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5606d2a8d7b8 <col:20, col:87>
|   `-CallExpr 0x5606d2a8d6d0 <col:22, col:84> 'void'
|     |-ImplicitCastExpr 0x5606d2a8d6b8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5606d2a8d518 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5606d2a8d2c8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5606d2a8d728 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5606d2a8d710 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5606d2a8d578 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5606d2a8d758 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5606d2a8d740 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5606d2a8d5d8 <col:41> 'char [24]' lvalue "while_infinite_loop_3.c"
|     |-ImplicitCastExpr 0x5606d2a8d770 <col:68> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5606d2a8d608 <col:68> 'int' 3
|     `-ImplicitCastExpr 0x5606d2a8d7a0 <col:71> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5606d2a8d788 <col:71> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5606d2a8d668 <col:71> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5606d2a8d8a8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x5606d2a8d7e8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x5606d2a8db88 <col:34, line:10:1>
|   |-IfStmt 0x5606d2a8db60 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x5606d2a8d9a8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x5606d2a8d990 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x5606d2a8d970 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x5606d2a8d950 <col:9> 'int' lvalue ParmVar 0x5606d2a8d7e8 'cond' 'int'
|   | `-CompoundStmt 0x5606d2a8db48 <col:16, line:8:3>
|   |   `-LabelStmt 0x5606d2a8db30 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x5606d2a8dac0 <col:12, col:35>
|   |       |-CallExpr 0x5606d2a8da20 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x5606d2a8da08 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x5606d2a8d9c0 <col:13> 'void ()' Function 0x5606d2a8d478 'reach_error' 'void ()'
|   |       `-CallExpr 0x5606d2a8daa0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x5606d2a8da88 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x5606d2a8da40 <col:27> 'void (void) __attribute__((noreturn))' Function 0x5606d2a8cf48 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x5606d2a8db78 <line:9:3>
|-VarDecl 0x5606d2a8dbc0 <line:12:1, col:7> col:5 used x 'int' cinit
| `-IntegerLiteral 0x5606d2a8dc28 <col:7> 'int' 0
|-FunctionDecl 0x5606d2a8dce0 <line:14:1, line:21:1> line:14:6 used eval 'void (void)'
| `-CompoundStmt 0x5606d2a8f6b0 <line:15:1, line:21:1>
|   |-WhileStmt 0x5606d2a8f688 <line:16:3, line:19:3>
|   | |-IntegerLiteral 0x5606d2a8dd80 <line:16:10> 'int' 1
|   | `-CompoundStmt 0x5606d2a8f668 <col:13, line:19:3>
|   |   |-BinaryOperator 0x5606d2a8f640 <line:17:7, col:9> 'int' '='
|   |   | |-DeclRefExpr 0x5606d2a8f600 <col:7> 'int' lvalue Var 0x5606d2a8dbc0 'x' 'int'
|   |   | `-IntegerLiteral 0x5606d2a8f620 <col:9> 'int' 0
|   |   `-BreakStmt 0x5606d2a8f660 <line:18:7>
|   `-ReturnStmt 0x5606d2a8f6a0 <line:20:3>
`-FunctionDecl 0x5606d2a8f720 <line:24:1, line:35:1> line:24:5 main 'int ()'
  `-CompoundStmt 0x5606d2a8faa8 <col:12, line:35:1>
    |-WhileStmt 0x5606d2a8f988 <line:26:3, line:30:3>
    | |-IntegerLiteral 0x5606d2a8f7c0 <line:26:9> 'int' 1
    | `-CompoundStmt 0x5606d2a8f968 <line:27:3, line:30:3>
    |   |-CallExpr 0x5606d2a8f840 <line:28:5, col:10> 'void'
    |   | `-ImplicitCastExpr 0x5606d2a8f828 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
    |   |   `-DeclRefExpr 0x5606d2a8f7e0 <col:5> 'void (void)' Function 0x5606d2a8dce0 'eval' 'void (void)'
    |   `-CallExpr 0x5606d2a8f940 <line:29:5, col:27> 'void'
    |     |-ImplicitCastExpr 0x5606d2a8f928 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x5606d2a8f860 <col:5> 'void (int)' Function 0x5606d2a8d8a8 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x5606d2a8f8d8 <col:23, col:26> 'int' '=='
    |       |-ImplicitCastExpr 0x5606d2a8f8c0 <col:23> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x5606d2a8f880 <col:23> 'int' lvalue Var 0x5606d2a8dbc0 'x' 'int'
    |       `-IntegerLiteral 0x5606d2a8f8a0 <col:26> 'int' 0
    |-CallExpr 0x5606d2a8fa50 <line:32:3, col:25> 'void'
    | |-ImplicitCastExpr 0x5606d2a8fa38 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5606d2a8f9a0 <col:3> 'void (int)' Function 0x5606d2a8d8a8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x5606d2a8fa18 <col:21, col:24> 'int' '!='
    |   |-ImplicitCastExpr 0x5606d2a8fa00 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x5606d2a8f9c0 <col:21> 'int' lvalue Var 0x5606d2a8dbc0 'x' 'int'
    |   `-IntegerLiteral 0x5606d2a8f9e0 <col:24> 'int' 0
    `-ReturnStmt 0x5606d2a8fa98 <line:34:3, col:10>
      `-IntegerLiteral 0x5606d2a8fa78 <col:10> 'int' 0
1 warning generated.
