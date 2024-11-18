./Benchmark/PLDI/SVComp/loops/sum01-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/sum01-2.c:2:22: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error() { assert(0); }
                     ^
TranslationUnitDecl 0x55b7b2f45d88 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55b7b2f46620 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55b7b2f46320 '__int128'
|-TypedefDecl 0x55b7b2f46690 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55b7b2f46340 'unsigned __int128'
|-TypedefDecl 0x55b7b2f46998 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55b7b2f46770 'struct __NSConstantString_tag'
|   `-Record 0x55b7b2f466e8 '__NSConstantString_tag'
|-TypedefDecl 0x55b7b2f46a30 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55b7b2f469f0 'char *'
|   `-BuiltinType 0x55b7b2f45e20 'char'
|-TypedefDecl 0x55b7b2f46d28 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55b7b2f46cd0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55b7b2f46b10 'struct __va_list_tag'
|     `-Record 0x55b7b2f46a88 '__va_list_tag'
|-FunctionDecl 0x55b7b2fa5cc8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/sum01-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b7b2fa5d68 prev 0x55b7b2fa5cc8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55b7b2fa5e58 <line:2:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55b7b2fa60e8 <col:20, col:33>
|   `-CallExpr 0x55b7b2fa60c0 <col:22, col:30> 'int'
|     |-ImplicitCastExpr 0x55b7b2fa60a8 <col:22> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55b7b2fa6040 <col:22> 'int ()' Function 0x55b7b2fa5f90 'assert' 'int ()'
|     `-IntegerLiteral 0x55b7b2fa6060 <col:29> 'int' 0
|-FunctionDecl 0x55b7b2fa61d8 <line:4:1, col:39> col:13 used __VERIFIER_assert 'void (int)' extern
| `-ParmVarDecl 0x55b7b2fa6118 <col:31, col:35> col:35 cond 'int'
|-FunctionDecl 0x55b7b2fa6328 prev 0x55b7b2fa61d8 <line:6:1, line:11:1> line:6:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55b7b2fa6298 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55b7b2fa6608 <col:34, line:11:1>
|   |-IfStmt 0x55b7b2fa65e0 <line:7:3, line:9:3>
|   | |-UnaryOperator 0x55b7b2fa6428 <line:7:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55b7b2fa6410 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55b7b2fa63f0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55b7b2fa63d0 <col:9> 'int' lvalue ParmVar 0x55b7b2fa6298 'cond' 'int'
|   | `-CompoundStmt 0x55b7b2fa65c8 <col:16, line:9:3>
|   |   `-LabelStmt 0x55b7b2fa65b0 <line:8:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55b7b2fa6540 <col:12, col:35>
|   |       |-CallExpr 0x55b7b2fa64a0 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55b7b2fa6488 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55b7b2fa6440 <col:13> 'void ()' Function 0x55b7b2fa5e58 'reach_error' 'void ()'
|   |       `-CallExpr 0x55b7b2fa6520 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55b7b2fa6508 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55b7b2fa64c0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55b7b2fa5d68 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55b7b2fa65f8 <line:10:3>
|-FunctionDecl 0x55b7b2fa6650 <line:13:1, col:34> col:12 used __VERIFIER_nondet_int 'int ()' extern
`-FunctionDecl 0x55b7b2fa6718 <line:14:1, line:21:1> line:14:5 main 'int ()'
  `-CompoundStmt 0x55b7b2fa75a8 <col:12, line:21:1>
    |-DeclStmt 0x55b7b2fa69d0 <line:15:3, col:41>
    | |-VarDecl 0x55b7b2fa67d0 <col:3, col:7> col:7 used i 'int'
    | |-VarDecl 0x55b7b2fa6850 <col:3, col:34> col:10 used n 'int' cinit
    | | `-CallExpr 0x55b7b2fa68f0 <col:12, col:34> 'int'
    | |   `-ImplicitCastExpr 0x55b7b2fa68d8 <col:12> 'int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x55b7b2fa68b8 <col:12> 'int ()' Function 0x55b7b2fa6650 '__VERIFIER_nondet_int' 'int ()'
    | `-VarDecl 0x55b7b2fa6928 <col:3, col:40> col:37 used sn 'int' cinit
    |   `-IntegerLiteral 0x55b7b2fa6990 <col:40> 'int' 0
    |-IfStmt 0x55b7b2fa6b78 <line:16:3, col:41>
    | |-UnaryOperator 0x55b7b2fa6b30 <col:7, col:31> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x55b7b2fa6b10 <col:8, col:31> 'int'
    | |   `-BinaryOperator 0x55b7b2fa6af0 <col:9, col:27> 'int' '&&'
    | |     |-BinaryOperator 0x55b7b2fa6a40 <col:9, col:13> 'int' '<'
    | |     | |-ImplicitCastExpr 0x55b7b2fa6a28 <col:9> 'int' <LValueToRValue>
    | |     | | `-DeclRefExpr 0x55b7b2fa69e8 <col:9> 'int' lvalue Var 0x55b7b2fa6850 'n' 'int'
    | |     | `-IntegerLiteral 0x55b7b2fa6a08 <col:13> 'int' 1000
    | |     `-BinaryOperator 0x55b7b2fa6ad0 <col:21, col:27> 'int' '>='
    | |       |-ImplicitCastExpr 0x55b7b2fa6ab8 <col:21> 'int' <LValueToRValue>
    | |       | `-DeclRefExpr 0x55b7b2fa6a60 <col:21> 'int' lvalue Var 0x55b7b2fa6850 'n' 'int'
    | |       `-UnaryOperator 0x55b7b2fa6aa0 <col:26, col:27> 'int' prefix '-'
    | |         `-IntegerLiteral 0x55b7b2fa6a80 <col:27> 'int' 1000
    | `-ReturnStmt 0x55b7b2fa6b68 <col:34, col:41>
    |   `-IntegerLiteral 0x55b7b2fa6b48 <col:41> 'int' 0
    |-ForStmt 0x55b7b2fa7358 <line:17:3, line:19:3>
    | |-BinaryOperator 0x55b7b2fa7180 <line:17:7, col:9> 'int' '='
    | | |-DeclRefExpr 0x55b7b2fa6b90 <col:7> 'int' lvalue Var 0x55b7b2fa67d0 'i' 'int'
    | | `-IntegerLiteral 0x55b7b2fa6bb0 <col:9> 'int' 1
    | |-<<<NULL>>>
    | |-BinaryOperator 0x55b7b2fa7210 <col:12, col:15> 'int' '<='
    | | |-ImplicitCastExpr 0x55b7b2fa71e0 <col:12> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x55b7b2fa71a0 <col:12> 'int' lvalue Var 0x55b7b2fa67d0 'i' 'int'
    | | `-ImplicitCastExpr 0x55b7b2fa71f8 <col:15> 'int' <LValueToRValue>
    | |   `-DeclRefExpr 0x55b7b2fa71c0 <col:15> 'int' lvalue Var 0x55b7b2fa6850 'n' 'int'
    | |-UnaryOperator 0x55b7b2fa7250 <col:18, col:19> 'int' postfix '++'
    | | `-DeclRefExpr 0x55b7b2fa7230 <col:18> 'int' lvalue Var 0x55b7b2fa67d0 'i' 'int'
    | `-CompoundStmt 0x55b7b2fa7340 <col:23, line:19:3>
    |   `-BinaryOperator 0x55b7b2fa7320 <line:18:5, line:12:13> 'int' '='
    |     |-DeclRefExpr 0x55b7b2fa7268 <line:18:5> 'int' lvalue Var 0x55b7b2fa6928 'sn' 'int'
    |     `-BinaryOperator 0x55b7b2fa7300 <col:10, line:12:13> 'int' '+'
    |       |-ImplicitCastExpr 0x55b7b2fa72e8 <line:18:10> 'int' <LValueToRValue>
    |       | `-DeclRefExpr 0x55b7b2fa7288 <col:10> 'int' lvalue Var 0x55b7b2fa6928 'sn' 'int'
    |       `-ParenExpr 0x55b7b2fa72c8 <line:12:11, col:13> 'int'
    |         `-IntegerLiteral 0x55b7b2fa72a8 <col:12> 'int' 2
    `-CallExpr 0x55b7b2fa7580 <line:20:3, col:39> 'void'
      |-ImplicitCastExpr 0x55b7b2fa7568 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x55b7b2fa7390 <col:3> 'void (int)' Function 0x55b7b2fa6328 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x55b7b2fa7518 <col:21, col:38> 'int' '||'
        |-BinaryOperator 0x55b7b2fa7480 <col:21, line:12:13> 'int' '=='
        | |-ImplicitCastExpr 0x55b7b2fa7468 <line:20:21> 'int' <LValueToRValue>
        | | `-DeclRefExpr 0x55b7b2fa73b0 <col:21> 'int' lvalue Var 0x55b7b2fa6928 'sn' 'int'
        | `-BinaryOperator 0x55b7b2fa7448 <col:25, line:12:13> 'int' '*'
        |   |-ImplicitCastExpr 0x55b7b2fa7430 <line:20:25> 'int' <LValueToRValue>
        |   | `-DeclRefExpr 0x55b7b2fa73d0 <col:25> 'int' lvalue Var 0x55b7b2fa6850 'n' 'int'
        |   `-ParenExpr 0x55b7b2fa7410 <line:12:11, col:13> 'int'
        |     `-IntegerLiteral 0x55b7b2fa73f0 <col:12> 'int' 2
        `-BinaryOperator 0x55b7b2fa74f8 <line:20:32, col:38> 'int' '=='
          |-ImplicitCastExpr 0x55b7b2fa74e0 <col:32> 'int' <LValueToRValue>
          | `-DeclRefExpr 0x55b7b2fa74a0 <col:32> 'int' lvalue Var 0x55b7b2fa6928 'sn' 'int'
          `-IntegerLiteral 0x55b7b2fa74c0 <col:38> 'int' 0
1 warning generated.
