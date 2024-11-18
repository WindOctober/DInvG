./Benchmark/PLDI/SVComp/loops/sum01_bug02.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/sum01_bug02.c:2:22: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error() { assert(0); }
                     ^
TranslationUnitDecl 0x55af74ef6dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55af74ef7660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55af74ef7360 '__int128'
|-TypedefDecl 0x55af74ef76d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55af74ef7380 'unsigned __int128'
|-TypedefDecl 0x55af74ef79d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55af74ef77b0 'struct __NSConstantString_tag'
|   `-Record 0x55af74ef7728 '__NSConstantString_tag'
|-TypedefDecl 0x55af74ef7a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55af74ef7a30 'char *'
|   `-BuiltinType 0x55af74ef6e60 'char'
|-TypedefDecl 0x55af74ef7d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55af74ef7d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55af74ef7b50 'struct __va_list_tag'
|     `-Record 0x55af74ef7ac8 '__va_list_tag'
|-FunctionDecl 0x55af74f56d08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/sum01_bug02.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55af74f56da8 prev 0x55af74f56d08 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55af74f56e98 <line:2:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55af74f57128 <col:20, col:33>
|   `-CallExpr 0x55af74f57100 <col:22, col:30> 'int'
|     |-ImplicitCastExpr 0x55af74f570e8 <col:22> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55af74f57080 <col:22> 'int ()' Function 0x55af74f56fd0 'assert' 'int ()'
|     `-IntegerLiteral 0x55af74f570a0 <col:29> 'int' 0
|-FunctionDecl 0x55af74f57218 <line:4:1, line:9:1> line:4:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55af74f57158 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55af74f574f8 <col:34, line:9:1>
|   |-IfStmt 0x55af74f574d0 <line:5:3, line:7:3>
|   | |-UnaryOperator 0x55af74f57318 <line:5:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55af74f57300 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55af74f572e0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55af74f572c0 <col:9> 'int' lvalue ParmVar 0x55af74f57158 'cond' 'int'
|   | `-CompoundStmt 0x55af74f574b8 <col:16, line:7:3>
|   |   `-LabelStmt 0x55af74f574a0 <line:6:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55af74f57430 <col:12, col:35>
|   |       |-CallExpr 0x55af74f57390 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55af74f57378 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55af74f57330 <col:13> 'void ()' Function 0x55af74f56e98 'reach_error' 'void ()'
|   |       `-CallExpr 0x55af74f57410 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55af74f573f8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55af74f573b0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55af74f56da8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55af74f574e8 <line:8:3>
|-FunctionDecl 0x55af74f57570 <line:11:1, col:44> col:21 used __VERIFIER_nondet_uint 'unsigned int ()' extern
`-FunctionDecl 0x55af74f57638 <line:12:1, line:23:1> line:12:5 main 'int ()'
  `-CompoundStmt 0x55af74f58678 <col:12, line:23:1>
    |-DeclStmt 0x55af74f579e0 <line:13:3, col:48>
    | |-VarDecl 0x55af74f576f0 <col:3, col:7> col:7 used i 'int'
    | |-VarDecl 0x55af74f57770 <col:3, col:12> col:10 used j 'int' cinit
    | | `-IntegerLiteral 0x55af74f577d8 <col:12> 'int' 10
    | |-VarDecl 0x55af74f57810 <col:3, col:41> col:16 used n 'int' cinit
    | | `-ImplicitCastExpr 0x55af74f57900 <col:18, col:41> 'int' <IntegralCast>
    | |   `-CallExpr 0x55af74f578e0 <col:18, col:41> 'unsigned int'
    | |     `-ImplicitCastExpr 0x55af74f578c8 <col:18> 'unsigned int (*)()' <FunctionToPointerDecay>
    | |       `-DeclRefExpr 0x55af74f57878 <col:18> 'unsigned int ()' Function 0x55af74f57570 '__VERIFIER_nondet_uint' 'unsigned int ()'
    | `-VarDecl 0x55af74f57930 <col:3, col:47> col:44 used sn 'int' cinit
    |   `-IntegerLiteral 0x55af74f57998 <col:47> 'int' 0
    |-IfStmt 0x55af74f57ab8 <line:14:3, line:16:3>
    | |-BinaryOperator 0x55af74f57a50 <line:14:7, col:10> 'int' '=='
    | | |-ImplicitCastExpr 0x55af74f57a38 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55af74f579f8 <col:7> 'int' lvalue Var 0x55af74f57810 'n' 'int'
    | | `-IntegerLiteral 0x55af74f57a18 <col:10> 'int' 2147483647
    | `-CompoundStmt 0x55af74f57aa0 <col:22, line:16:3>
    |   `-ReturnStmt 0x55af74f57a90 <line:15:5, col:12>
    |     `-IntegerLiteral 0x55af74f57a70 <col:12> 'int' 0
    |-ForStmt 0x55af74f58398 <line:17:3, line:21:3>
    | |-BinaryOperator 0x55af74f57b10 <line:17:7, col:9> 'int' '='
    | | |-DeclRefExpr 0x55af74f57ad0 <col:7> 'int' lvalue Var 0x55af74f576f0 'i' 'int'
    | | `-IntegerLiteral 0x55af74f57af0 <col:9> 'int' 1
    | |-<<<NULL>>>
    | |-BinaryOperator 0x55af74f57ba0 <col:12, col:15> 'int' '<='
    | | |-ImplicitCastExpr 0x55af74f57b70 <col:12> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55af74f57b30 <col:12> 'int' lvalue Var 0x55af74f576f0 'i' 'int'
    | | `-ImplicitCastExpr 0x55af74f57b88 <col:15> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55af74f57b50 <col:15> 'int' lvalue Var 0x55af74f57810 'n' 'int'
    | |-UnaryOperator 0x55af74f57be0 <col:18, col:19> 'int' postfix '++'
    | | `-DeclRefExpr 0x55af74f57bc0 <col:18> 'int' lvalue Var 0x55af74f576f0 'i' 'int'
    | `-CompoundStmt 0x55af74f58378 <col:23, line:21:3>
    |   |-IfStmt 0x55af74f58328 <line:18:5, line:10:13>
    |   | |-BinaryOperator 0x55af74f58230 <line:18:9, col:11> 'int' '<'
    |   | | |-ImplicitCastExpr 0x55af74f58200 <col:9> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x55af74f581c0 <col:9> 'int' lvalue Var 0x55af74f576f0 'i' 'int'
    |   | | `-ImplicitCastExpr 0x55af74f58218 <col:11> 'int' <LValueToRValue>
    |   | |   `-DeclRefExpr 0x55af74f581e0 <col:11> 'int' lvalue Var 0x55af74f57770 'j' 'int'
    |   | `-BinaryOperator 0x55af74f58308 <line:19:5, line:10:13> 'int' '='
    |   |   |-DeclRefExpr 0x55af74f58250 <line:19:5> 'int' lvalue Var 0x55af74f57930 'sn' 'int'
    |   |   `-BinaryOperator 0x55af74f582e8 <col:10, line:10:13> 'int' '+'
    |   |     |-ImplicitCastExpr 0x55af74f582d0 <line:19:10> 'int' <LValueToRValue>
    |   |     | `-DeclRefExpr 0x55af74f58270 <col:10> 'int' lvalue Var 0x55af74f57930 'sn' 'int'
    |   |     `-ParenExpr 0x55af74f582b0 <line:10:11, col:13> 'int'
    |   |       `-IntegerLiteral 0x55af74f58290 <col:12> 'int' 2
    |   `-UnaryOperator 0x55af74f58360 <line:20:5, col:6> 'int' postfix '--'
    |     `-DeclRefExpr 0x55af74f58340 <col:5> 'int' lvalue Var 0x55af74f57770 'j' 'int'
    `-CallExpr 0x55af74f58650 <line:22:3, col:53> 'void'
      |-ImplicitCastExpr 0x55af74f58638 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55af74f583d0 <col:3> 'void (int)' Function 0x55af74f57218 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55af74f585e8 <col:21, col:52> 'int' '||'
        |-BinaryOperator 0x55af74f58550 <col:21, line:10:13> 'int' '=='
        | |-ImplicitCastExpr 0x55af74f58538 <line:22:21> 'long long' <IntegralCast>
        | | `-ImplicitCastExpr 0x55af74f58520 <col:21> 'int' <LValueToRValue>
        | |   `-DeclRefExpr 0x55af74f583f0 <col:21> 'int' lvalue Var 0x55af74f57930 'sn' 'int'
        | `-BinaryOperator 0x55af74f58500 <col:25, line:10:13> 'long long' '*'
        |   |-ParenExpr 0x55af74f58488 <line:22:25, col:39> 'long long'
        |   | `-CStyleCastExpr 0x55af74f58460 <col:26, col:38> 'long long' <IntegralCast>
        |   |   `-ImplicitCastExpr 0x55af74f58448 <col:38> 'int' <LValueToRValue> part_of_explicit_cast
        |   |     `-DeclRefExpr 0x55af74f58410 <col:38> 'int' lvalue Var 0x55af74f57810 'n' 'int'
        |   `-ImplicitCastExpr 0x55af74f584e8 <line:10:11, col:13> 'long long' <IntegralCast>
        |     `-ParenExpr 0x55af74f584c8 <col:11, col:13> 'int'
        |       `-IntegerLiteral 0x55af74f584a8 <col:12> 'int' 2
        `-BinaryOperator 0x55af74f585c8 <line:22:46, col:52> 'int' '=='
          |-ImplicitCastExpr 0x55af74f585b0 <col:46> 'int' <LValueToRValue>
          | `-DeclRefExpr 0x55af74f58570 <col:46> 'int' lvalue Var 0x55af74f57930 'sn' 'int'
          `-IntegerLiteral 0x55af74f58590 <col:52> 'int' 0
1 warning generated.
