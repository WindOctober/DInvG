./Benchmark/PLDI/SVComp/loops/while_infinite_loop_4.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/while_infinite_loop_4.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55af8233cee8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55af8233d780 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55af8233d480 '__int128'
|-TypedefDecl 0x55af8233d7f0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55af8233d4a0 'unsigned __int128'
|-TypedefDecl 0x55af8233daf8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55af8233d8d0 'struct __NSConstantString_tag'
|   `-Record 0x55af8233d848 '__NSConstantString_tag'
|-TypedefDecl 0x55af8233db90 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55af8233db50 'char *'
|   `-BuiltinType 0x55af8233cf80 'char'
|-TypedefDecl 0x55af8233de88 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55af8233de30 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55af8233dc70 'struct __va_list_tag'
|     `-Record 0x55af8233dbe8 '__va_list_tag'
|-FunctionDecl 0x55af8239cea8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/while_infinite_loop_4.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55af8239cf48 prev 0x55af8239cea8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55af8239d2c8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55af8239d000 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55af8239d080 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55af8239d100 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55af8239d180 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55af8239d388 <col:99>
|-FunctionDecl 0x55af8239d478 <line:3:1, col:87> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55af8239d7b8 <col:20, col:87>
|   `-CallExpr 0x55af8239d6d0 <col:22, col:84> 'void'
|     |-ImplicitCastExpr 0x55af8239d6b8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55af8239d518 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55af8239d2c8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55af8239d728 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55af8239d710 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55af8239d578 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55af8239d758 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55af8239d740 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55af8239d5d8 <col:41> 'char [24]' lvalue "while_infinite_loop_4.c"
|     |-ImplicitCastExpr 0x55af8239d770 <col:68> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55af8239d608 <col:68> 'int' 3
|     `-ImplicitCastExpr 0x55af8239d7a0 <col:71> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55af8239d788 <col:71> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55af8239d668 <col:71> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55af8239d8a8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55af8239d7e8 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55af8239db88 <col:34, line:10:1>
|   |-IfStmt 0x55af8239db60 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x55af8239d9a8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55af8239d990 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55af8239d970 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55af8239d950 <col:9> 'int' lvalue ParmVar 0x55af8239d7e8 'cond' 'int'
|   | `-CompoundStmt 0x55af8239db48 <col:16, line:8:3>
|   |   `-LabelStmt 0x55af8239db30 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55af8239dac0 <col:12, col:35>
|   |       |-CallExpr 0x55af8239da20 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55af8239da08 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55af8239d9c0 <col:13> 'void ()' Function 0x55af8239d478 'reach_error' 'void ()'
|   |       `-CallExpr 0x55af8239daa0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55af8239da88 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55af8239da40 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55af8239cf48 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55af8239db78 <line:9:3>
|-VarDecl 0x55af8239dbc0 <line:12:1, col:7> col:5 used x 'int' cinit
| `-IntegerLiteral 0x55af8239dc28 <col:7> 'int' 0
|-FunctionDecl 0x55af8239dce0 <line:14:1, line:21:1> line:14:6 used eval 'void (void)'
| `-CompoundStmt 0x55af8239f6b0 <line:15:1, line:21:1>
|   |-WhileStmt 0x55af8239f688 <line:16:3, line:19:3>
|   | |-IntegerLiteral 0x55af8239dd80 <line:16:10> 'int' 1
|   | `-CompoundStmt 0x55af8239f668 <col:13, line:19:3>
|   |   |-BinaryOperator 0x55af8239f640 <line:17:7, col:9> 'int' '='
|   |   | |-DeclRefExpr 0x55af8239f600 <col:7> 'int' lvalue Var 0x55af8239dbc0 'x' 'int'
|   |   | `-IntegerLiteral 0x55af8239f620 <col:9> 'int' 1
|   |   `-BreakStmt 0x55af8239f660 <line:18:7>
|   `-ReturnStmt 0x55af8239f6a0 <line:20:3>
`-FunctionDecl 0x55af8239f720 <line:24:1, line:35:1> line:24:5 main 'int ()'
  `-CompoundStmt 0x55af8239faa8 <col:12, line:35:1>
    |-WhileStmt 0x55af8239f988 <line:26:3, line:30:3>
    | |-IntegerLiteral 0x55af8239f7c0 <line:26:9> 'int' 1
    | `-CompoundStmt 0x55af8239f968 <line:27:3, line:30:3>
    |   |-CallExpr 0x55af8239f840 <line:28:5, col:10> 'void'
    |   | `-ImplicitCastExpr 0x55af8239f828 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
    |   |   `-DeclRefExpr 0x55af8239f7e0 <col:5> 'void (void)' Function 0x55af8239dce0 'eval' 'void (void)'
    |   `-CallExpr 0x55af8239f940 <line:29:5, col:27> 'void'
    |     |-ImplicitCastExpr 0x55af8239f928 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
    |     | `-DeclRefExpr 0x55af8239f860 <col:5> 'void (int)' Function 0x55af8239d8a8 '__VERIFIER_assert' 'void (int)'
    |     `-BinaryOperator 0x55af8239f8d8 <col:23, col:26> 'int' '=='
    |       |-ImplicitCastExpr 0x55af8239f8c0 <col:23> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55af8239f880 <col:23> 'int' lvalue Var 0x55af8239dbc0 'x' 'int'
    |       `-IntegerLiteral 0x55af8239f8a0 <col:26> 'int' 0
    |-CallExpr 0x55af8239fa50 <line:32:3, col:25> 'void'
    | |-ImplicitCastExpr 0x55af8239fa38 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55af8239f9a0 <col:3> 'void (int)' Function 0x55af8239d8a8 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x55af8239fa18 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x55af8239fa00 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x55af8239f9c0 <col:21> 'int' lvalue Var 0x55af8239dbc0 'x' 'int'
    |   `-IntegerLiteral 0x55af8239f9e0 <col:24> 'int' 0
    `-ReturnStmt 0x55af8239fa98 <line:34:3, col:10>
      `-IntegerLiteral 0x55af8239fa78 <col:10> 'int' 0
1 warning generated.
