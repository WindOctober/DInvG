./Benchmark/PLDI/SVComp/loops/trex04.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex04.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55e16ecd9d88 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55e16ecda620 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55e16ecda320 '__int128'
|-TypedefDecl 0x55e16ecda690 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55e16ecda340 'unsigned __int128'
|-TypedefDecl 0x55e16ecda998 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55e16ecda770 'struct __NSConstantString_tag'
|   `-Record 0x55e16ecda6e8 '__NSConstantString_tag'
|-TypedefDecl 0x55e16ecdaa30 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55e16ecda9f0 'char *'
|   `-BuiltinType 0x55e16ecd9e20 'char'
|-TypedefDecl 0x55e16ecdad28 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55e16ecdacd0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55e16ecdab10 'struct __va_list_tag'
|     `-Record 0x55e16ecdaa88 '__va_list_tag'
|-FunctionDecl 0x55e16ed39f18 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/trex04.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55e16ed39fb8 prev 0x55e16ed39f18 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55e16ed3a338 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55e16ed3a070 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55e16ed3a0f0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55e16ed3a170 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55e16ed3a1f0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55e16ed3a3f8 <col:99>
|-FunctionDecl 0x55e16ed3a4e8 <line:3:1, col:72> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55e16ed3a818 <col:20, col:72>
|   `-CallExpr 0x55e16ed3a730 <col:22, col:69> 'void'
|     |-ImplicitCastExpr 0x55e16ed3a718 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55e16ed3a588 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55e16ed3a338 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55e16ed3a788 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55e16ed3a770 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55e16ed3a5e8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55e16ed3a7b8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55e16ed3a7a0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55e16ed3a648 <col:41> 'char [9]' lvalue "trex04.c"
|     |-ImplicitCastExpr 0x55e16ed3a7d0 <col:53> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55e16ed3a668 <col:53> 'int' 3
|     `-ImplicitCastExpr 0x55e16ed3a800 <col:56> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55e16ed3a7e8 <col:56> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55e16ed3a6c8 <col:56> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55e16ed3a8c8 prev 0x55e16ed39fb8 <line:4:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55e16ed3aa48 <line:5:1, line:7:1> line:5:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55e16ed3a980 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55e16ed3abf0 <col:36, line:7:1>
|   `-IfStmt 0x55e16ed3abd8 <line:6:3, col:22>
|     |-UnaryOperator 0x55e16ed3ab28 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55e16ed3ab10 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55e16ed3aaf0 <col:7> 'int' lvalue ParmVar 0x55e16ed3a980 'cond' 'int'
|     `-CompoundStmt 0x55e16ed3abc0 <col:13, col:22>
|       `-CallExpr 0x55e16ed3aba0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55e16ed3ab88 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55e16ed3ab40 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55e16ed3a8c8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55e16ed3acb0 <line:9:1, line:14:1> line:9:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55e16ed3ac20 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55e16ed3c978 <col:34, line:14:1>
|   |-IfStmt 0x55e16ed3c950 <line:10:3, line:12:3>
|   | |-UnaryOperator 0x55e16ed3adb0 <line:10:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55e16ed3ad98 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55e16ed3ad78 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55e16ed3ad58 <col:9> 'int' lvalue ParmVar 0x55e16ed3ac20 'cond' 'int'
|   | `-CompoundStmt 0x55e16ed3c938 <col:16, line:12:3>
|   |   `-LabelStmt 0x55e16ed3c920 <line:11:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55e16ed3c8b0 <col:12, col:35>
|   |       |-CallExpr 0x55e16ed3c838 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55e16ed3c820 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55e16ed3adc8 <col:13> 'void ()' Function 0x55e16ed3a4e8 'reach_error' 'void ()'
|   |       `-CallExpr 0x55e16ed3c890 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55e16ed3c878 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55e16ed3c858 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55e16ed3a8c8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55e16ed3c968 <line:13:3>
|-FunctionDecl 0x55e16ed3c9e8 <line:15:1, col:37> col:14 used __VERIFIER_nondet_bool '_Bool ()' extern
|-FunctionDecl 0x55e16ed3cae0 <line:16:1, col:34> col:12 used __VERIFIER_nondet_int 'int ()' extern
|-FunctionDecl 0x55e16ed3cba0 <line:18:1, line:25:1> line:18:6 used foo 'void ()'
| `-CompoundStmt 0x55e16ed3d080 <line:19:1, line:25:1>
|   |-DeclStmt 0x55e16ed3cce0 <line:20:3, col:10>
|   | `-VarDecl 0x55e16ed3cc58 <col:3, col:9> col:7 used y 'int' cinit
|   |   `-IntegerLiteral 0x55e16ed3ccc0 <col:9> 'int' 0
|   |-DeclStmt 0x55e16ed3ced8 <line:21:3, col:65>
|   | |-VarDecl 0x55e16ed3cd08 <col:3, col:35> col:9 used c1 '_Bool' cinit
|   | | `-CallExpr 0x55e16ed3cdd0 <col:12, col:35> '_Bool'
|   | |   `-ImplicitCastExpr 0x55e16ed3cdb8 <col:12> '_Bool (*)()' <FunctionToPointerDecay>
|   | |     `-DeclRefExpr 0x55e16ed3cd70 <col:12> '_Bool ()' Function 0x55e16ed3c9e8 '__VERIFIER_nondet_bool' '_Bool ()'
|   | `-VarDecl 0x55e16ed3ce00 <col:3, col:64> col:38 used c2 '_Bool' cinit
|   |   `-CallExpr 0x55e16ed3cea0 <col:41, col:64> '_Bool'
|   |     `-ImplicitCastExpr 0x55e16ed3ce88 <col:41> '_Bool (*)()' <FunctionToPointerDecay>
|   |       `-DeclRefExpr 0x55e16ed3ce68 <col:41> '_Bool ()' Function 0x55e16ed3c9e8 '__VERIFIER_nondet_bool' '_Bool ()'
|   |-IfStmt 0x55e16ed3cf60 <line:22:3, col:12>
|   | |-ImplicitCastExpr 0x55e16ed3cf10 <col:7> '_Bool' <LValueToRValue>
|   | | `-DeclRefExpr 0x55e16ed3cef0 <col:7> '_Bool' lvalue Var 0x55e16ed3cd08 'c1' '_Bool'
|   | `-UnaryOperator 0x55e16ed3cf48 <col:11, col:12> 'int' postfix '++'
|   |   `-DeclRefExpr 0x55e16ed3cf28 <col:11> 'int' lvalue Var 0x55e16ed3cc58 'y' 'int'
|   `-IfStmt 0x55e16ed3d058 <line:23:3, line:24:11> has_else
|     |-ImplicitCastExpr 0x55e16ed3cf98 <line:23:7> '_Bool' <LValueToRValue>
|     | `-DeclRefExpr 0x55e16ed3cf78 <col:7> '_Bool' lvalue Var 0x55e16ed3ce00 'c2' '_Bool'
|     |-UnaryOperator 0x55e16ed3cfd0 <col:11, col:12> 'int' postfix '--'
|     | `-DeclRefExpr 0x55e16ed3cfb0 <col:11> 'int' lvalue Var 0x55e16ed3cc58 'y' 'int'
|     `-CompoundAssignOperator 0x55e16ed3d028 <line:24:8, col:11> 'int' '+=' ComputeLHSTy='int' ComputeResultTy='int'
|       |-DeclRefExpr 0x55e16ed3cfe8 <col:8> 'int' lvalue Var 0x55e16ed3cc58 'y' 'int'
|       `-IntegerLiteral 0x55e16ed3d008 <col:11> 'int' 10
`-FunctionDecl 0x55e16ed3d0d8 <line:27:1, line:48:1> line:27:5 main 'int ()'
  `-CompoundStmt 0x55e16ed3ddf8 <line:28:1, line:48:1>
    |-DeclStmt 0x55e16ed3d218 <line:29:3, col:12>
    | `-VarDecl 0x55e16ed3d190 <col:3, col:11> col:7 used d 'int' cinit
    |   `-IntegerLiteral 0x55e16ed3d1f8 <col:11> 'int' 1
    |-DeclStmt 0x55e16ed3d330 <line:30:3, col:34>
    | `-VarDecl 0x55e16ed3d248 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x55e16ed3d310 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x55e16ed3d2f8 <col:11> 'int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55e16ed3d2b0 <col:11> 'int ()' Function 0x55e16ed3cae0 '__VERIFIER_nondet_int' 'int ()'
    |-IfStmt 0x55e16ed3d4d8 <line:31:3, col:48>
    | |-UnaryOperator 0x55e16ed3d490 <col:7, col:38> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55e16ed3d470 <col:8, col:38> 'int'
    | |   `-BinaryOperator 0x55e16ed3d450 <col:9, col:31> 'int' '&&'
    | |     |-BinaryOperator 0x55e16ed3d3a0 <col:9, col:14> 'int' '<='
    | |     | |-ImplicitCastExpr 0x55e16ed3d388 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x55e16ed3d348 <col:9> 'int' lvalue Var 0x55e16ed3d248 'x' 'int'
    | |     | `-IntegerLiteral 0x55e16ed3d368 <col:14> 'int' 1000000
    | |     `-BinaryOperator 0x55e16ed3d430 <col:25, col:31> 'int' '>='
    | |       |-ImplicitCastExpr 0x55e16ed3d418 <col:25> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x55e16ed3d3c0 <col:25> 'int' lvalue Var 0x55e16ed3d248 'x' 'int'
    | |       `-UnaryOperator 0x55e16ed3d400 <col:30, col:31> 'int' prefix '-'
    | |         `-IntegerLiteral 0x55e16ed3d3e0 <col:31> 'int' 1000000
    | `-ReturnStmt 0x55e16ed3d4c8 <col:41, col:48>
    |   `-IntegerLiteral 0x55e16ed3d4a8 <col:48> 'int' 0
    |-DeclStmt 0x55e16ed3d6a8 <line:32:3, col:65>
    | |-VarDecl 0x55e16ed3d500 <col:3, col:35> col:9 used c1 '_Bool' cinit
    | | `-CallExpr 0x55e16ed3d5a0 <col:12, col:35> '_Bool'
    | |   `-ImplicitCastExpr 0x55e16ed3d588 <col:12> '_Bool (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55e16ed3d568 <col:12> '_Bool ()' Function 0x55e16ed3c9e8 '__VERIFIER_nondet_bool' '_Bool ()'
    | `-VarDecl 0x55e16ed3d5d0 <col:3, col:64> col:38 used c2 '_Bool' cinit
    |   `-CallExpr 0x55e16ed3d670 <col:41, col:64> '_Bool'
    |     `-ImplicitCastExpr 0x55e16ed3d658 <col:41> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55e16ed3d638 <col:41> '_Bool ()' Function 0x55e16ed3c9e8 '__VERIFIER_nondet_bool' '_Bool ()'
    |-IfStmt 0x55e16ed3d7b0 <line:34:3, col:19>
    | |-ImplicitCastExpr 0x55e16ed3d6e0 <col:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x55e16ed3d6c0 <col:7> '_Bool' lvalue Var 0x55e16ed3d500 'c1' '_Bool'
    | `-BinaryOperator 0x55e16ed3d790 <col:11, col:19> 'int' '='
    |   |-DeclRefExpr 0x55e16ed3d6f8 <col:11> 'int' lvalue Var 0x55e16ed3d190 'd' 'int'
    |   `-BinaryOperator 0x55e16ed3d770 <col:15, col:19> 'int' '-'
    |     |-ImplicitCastExpr 0x55e16ed3d758 <col:15> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x55e16ed3d718 <col:15> 'int' lvalue Var 0x55e16ed3d190 'd' 'int'
    |     `-IntegerLiteral 0x55e16ed3d738 <col:19> 'int' 1
    |-IfStmt 0x55e16ed3d868 <line:35:3, col:15>
    | |-ImplicitCastExpr 0x55e16ed3d7e8 <col:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x55e16ed3d7c8 <col:7> '_Bool' lvalue Var 0x55e16ed3d5d0 'c2' '_Bool'
    | `-CallExpr 0x55e16ed3d848 <col:11, col:15> 'void'
    |   `-ImplicitCastExpr 0x55e16ed3d830 <col:11> 'void (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55e16ed3d800 <col:11> 'void ()' Function 0x55e16ed3cba0 'foo' 'void ()'
    |-BinaryOperator 0x55e16ed3d9b0 <line:37:3, col:58> '_Bool' ','
    | |-BinaryOperator 0x55e16ed3d8f8 <col:3, col:29> '_Bool' '='
    | | |-DeclRefExpr 0x55e16ed3d880 <col:3> '_Bool' lvalue Var 0x55e16ed3d500 'c1' '_Bool'
    | | `-CallExpr 0x55e16ed3d8d8 <col:6, col:29> '_Bool'
    | |   `-ImplicitCastExpr 0x55e16ed3d8c0 <col:6> '_Bool (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55e16ed3d8a0 <col:6> '_Bool ()' Function 0x55e16ed3c9e8 '__VERIFIER_nondet_bool' '_Bool ()'
    | `-BinaryOperator 0x55e16ed3d990 <col:32, col:58> '_Bool' '='
    |   |-DeclRefExpr 0x55e16ed3d918 <col:32> '_Bool' lvalue Var 0x55e16ed3d5d0 'c2' '_Bool'
    |   `-CallExpr 0x55e16ed3d970 <col:35, col:58> '_Bool'
    |     `-ImplicitCastExpr 0x55e16ed3d958 <col:35> '_Bool (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x55e16ed3d938 <col:35> '_Bool ()' Function 0x55e16ed3c9e8 '__VERIFIER_nondet_bool' '_Bool ()'
    |-IfStmt 0x55e16ed3da60 <line:39:3, col:15>
    | |-ImplicitCastExpr 0x55e16ed3d9f0 <col:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x55e16ed3d9d0 <col:7> '_Bool' lvalue Var 0x55e16ed3d500 'c1' '_Bool'
    | `-CallExpr 0x55e16ed3da40 <col:11, col:15> 'void'
    |   `-ImplicitCastExpr 0x55e16ed3da28 <col:11> 'void (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55e16ed3da08 <col:11> 'void ()' Function 0x55e16ed3cba0 'foo' 'void ()'
    |-IfStmt 0x55e16ed3db68 <line:40:3, col:19>
    | |-ImplicitCastExpr 0x55e16ed3da98 <col:7> '_Bool' <LValueToRValue>
    | | `-DeclRefExpr 0x55e16ed3da78 <col:7> '_Bool' lvalue Var 0x55e16ed3d5d0 'c2' '_Bool'
    | `-BinaryOperator 0x55e16ed3db48 <col:11, col:19> 'int' '='
    |   |-DeclRefExpr 0x55e16ed3dab0 <col:11> 'int' lvalue Var 0x55e16ed3d190 'd' 'int'
    |   `-BinaryOperator 0x55e16ed3db28 <col:15, col:19> 'int' '-'
    |     |-ImplicitCastExpr 0x55e16ed3db10 <col:15> 'int' <LValueToRValue>
    |     | `-DeclRefExpr 0x55e16ed3dad0 <col:15> 'int' lvalue Var 0x55e16ed3d190 'd' 'int'
    |     `-IntegerLiteral 0x55e16ed3daf0 <col:19> 'int' 1
    |-WhileStmt 0x55e16ed3dce0 <line:42:3, line:45:3>
    | |-BinaryOperator 0x55e16ed3dbd8 <line:42:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x55e16ed3dbc0 <col:9> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55e16ed3db80 <col:9> 'int' lvalue Var 0x55e16ed3d248 'x' 'int'
    | | `-IntegerLiteral 0x55e16ed3dba0 <col:11> 'int' 0
    | `-CompoundStmt 0x55e16ed3dcc8 <line:43:3, line:45:3>
    |   `-BinaryOperator 0x55e16ed3dca8 <line:44:5, col:9> 'int' '='
    |     |-DeclRefExpr 0x55e16ed3dbf8 <col:5> 'int' lvalue Var 0x55e16ed3d248 'x' 'int'
    |     `-BinaryOperator 0x55e16ed3dc88 <col:7, col:9> 'int' '-'
    |       |-ImplicitCastExpr 0x55e16ed3dc58 <col:7> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55e16ed3dc18 <col:7> 'int' lvalue Var 0x55e16ed3d248 'x' 'int'
    |       `-ImplicitCastExpr 0x55e16ed3dc70 <col:9> 'int' <LValueToRValue>
    |         `-DeclRefExpr 0x55e16ed3dc38 <col:9> 'int' lvalue Var 0x55e16ed3d190 'd' 'int'
    `-CallExpr 0x55e16ed3ddd0 <line:47:3, col:25> 'void'
      |-ImplicitCastExpr 0x55e16ed3ddb8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55e16ed3dcf8 <col:3> 'void (int)' Function 0x55e16ed3acb0 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55e16ed3dd70 <col:21, col:24> 'int' '<='
        |-ImplicitCastExpr 0x55e16ed3dd58 <col:21> 'int' <LValueToRValue>
        | `-DeclRefExpr 0x55e16ed3dd18 <col:21> 'int' lvalue Var 0x55e16ed3d248 'x' 'int'
        `-IntegerLiteral 0x55e16ed3dd38 <col:24> 'int' 0
1 warning generated.
