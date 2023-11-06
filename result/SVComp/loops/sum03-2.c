./Benchmark/PLDI/SVComp/loops/sum03-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/sum03-2.c:2:22: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error() { assert(0); }
                     ^
TranslationUnitDecl 0x562f2a9fcd88 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x562f2a9fd620 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x562f2a9fd320 '__int128'
|-TypedefDecl 0x562f2a9fd690 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x562f2a9fd340 'unsigned __int128'
|-TypedefDecl 0x562f2a9fd998 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x562f2a9fd770 'struct __NSConstantString_tag'
|   `-Record 0x562f2a9fd6e8 '__NSConstantString_tag'
|-TypedefDecl 0x562f2a9fda30 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x562f2a9fd9f0 'char *'
|   `-BuiltinType 0x562f2a9fce20 'char'
|-TypedefDecl 0x562f2a9fdd28 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x562f2a9fdcd0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x562f2a9fdb10 'struct __va_list_tag'
|     `-Record 0x562f2a9fda88 '__va_list_tag'
|-FunctionDecl 0x562f2aa5ccb8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/sum03-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562f2aa5cd58 prev 0x562f2aa5ccb8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x562f2aa5ce48 <line:2:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x562f2aa5d0d8 <col:20, col:33>
|   `-CallExpr 0x562f2aa5d0b0 <col:22, col:30> 'int'
|     |-ImplicitCastExpr 0x562f2aa5d098 <col:22> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x562f2aa5d030 <col:22> 'int ()' Function 0x562f2aa5cf80 'assert' 'int ()'
|     `-IntegerLiteral 0x562f2aa5d050 <col:29> 'int' 0
|-FunctionDecl 0x562f2aa5d1c8 <line:4:1, line:9:1> line:4:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x562f2aa5d108 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x562f2aa5d4a8 <col:34, line:9:1>
|   |-IfStmt 0x562f2aa5d480 <line:5:3, line:7:3>
|   | |-UnaryOperator 0x562f2aa5d2c8 <line:5:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x562f2aa5d2b0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x562f2aa5d290 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x562f2aa5d270 <col:9> 'int' lvalue ParmVar 0x562f2aa5d108 'cond' 'int'
|   | `-CompoundStmt 0x562f2aa5d468 <col:16, line:7:3>
|   |   `-LabelStmt 0x562f2aa5d450 <line:6:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x562f2aa5d3e0 <col:12, col:35>
|   |       |-CallExpr 0x562f2aa5d340 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x562f2aa5d328 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x562f2aa5d2e0 <col:13> 'void ()' Function 0x562f2aa5ce48 'reach_error' 'void ()'
|   |       `-CallExpr 0x562f2aa5d3c0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x562f2aa5d3a8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x562f2aa5d360 <col:27> 'void (void) __attribute__((noreturn))' Function 0x562f2aa5cd58 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x562f2aa5d498 <line:8:3>
|-FunctionDecl 0x562f2aa5d520 <line:11:1, col:37> col:14 used __VERIFIER_nondet_uint 'unsigned int ()'
`-FunctionDecl 0x562f2aa5d5e8 <line:13:1, line:23:1> line:13:5 main 'int ()'
  `-CompoundStmt 0x562f2aa5e4d8 <col:12, line:23:1>
    |-DeclStmt 0x562f2aa5d740 <line:14:3, col:20>
    | `-VarDecl 0x562f2aa5d6a0 <col:3, col:19> col:16 used sn 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x562f2aa5d728 <col:19> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x562f2aa5d708 <col:19> 'int' 0
    |-DeclStmt 0x562f2aa5d950 <line:15:3, col:75>
    | |-VarDecl 0x562f2aa5d770 <col:3, col:45> col:16 loop1 'unsigned int' cinit
    | | `-CallExpr 0x562f2aa5d840 <col:22, col:45> 'unsigned int'
    | |   `-ImplicitCastExpr 0x562f2aa5d828 <col:22> 'unsigned int (*)()' <FunctionToPointerDecay>
    | |     `-DeclRefExpr 0x562f2aa5d7d8 <col:22> 'unsigned int ()' Function 0x562f2aa5d520 '__VERIFIER_nondet_uint' 'unsigned int ()'
    | `-VarDecl 0x562f2aa5d878 <col:3, col:74> col:48 n1 'unsigned int' cinit
    |   `-CallExpr 0x562f2aa5d918 <col:51, col:74> 'unsigned int'
    |     `-ImplicitCastExpr 0x562f2aa5d900 <col:51> 'unsigned int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x562f2aa5d8e0 <col:51> 'unsigned int ()' Function 0x562f2aa5d520 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |-DeclStmt 0x562f2aa5da20 <line:16:3, col:19>
    | `-VarDecl 0x562f2aa5d980 <col:3, col:18> col:16 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x562f2aa5da08 <col:18> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x562f2aa5d9e8 <col:18> 'int' 0
    `-WhileStmt 0x562f2aa5e4c0 <line:18:3, line:22:3>
      |-IntegerLiteral 0x562f2aa5da38 <line:18:9> 'int' 1
      `-CompoundStmt 0x562f2aa5e498 <col:11, line:22:3>
        |-BinaryOperator 0x562f2aa5db28 <line:19:5, line:10:13> 'unsigned int' '='
        | |-DeclRefExpr 0x562f2aa5da58 <line:19:5> 'unsigned int' lvalue Var 0x562f2aa5d6a0 'sn' 'unsigned int'
        | `-BinaryOperator 0x562f2aa5db08 <col:10, line:10:13> 'unsigned int' '+'
        |   |-ImplicitCastExpr 0x562f2aa5dad8 <line:19:10> 'unsigned int' <LValueToRValue>
        |   | `-DeclRefExpr 0x562f2aa5da78 <col:10> 'unsigned int' lvalue Var 0x562f2aa5d6a0 'sn' 'unsigned int'
        |   `-ImplicitCastExpr 0x562f2aa5daf0 <line:10:11, col:13> 'unsigned int' <IntegralCast>
        |     `-ParenExpr 0x562f2aa5dab8 <col:11, col:13> 'int'
        |       `-IntegerLiteral 0x562f2aa5da98 <col:12> 'int' 2
        |-UnaryOperator 0x562f2aa5db68 <line:20:5, col:6> 'unsigned int' postfix '++'
        | `-DeclRefExpr 0x562f2aa5db48 <col:5> 'unsigned int' lvalue Var 0x562f2aa5d980 'x' 'unsigned int'
        `-CallExpr 0x562f2aa5e470 <line:21:5, col:41> 'void'
          |-ImplicitCastExpr 0x562f2aa5e458 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
          | `-DeclRefExpr 0x562f2aa5db80 <col:5> 'void (int)' Function 0x562f2aa5d1c8 '__VERIFIER_assert' 'void (int)'
          `-BinaryOperator 0x562f2aa5e408 <col:23, col:40> 'int' '||'
            |-BinaryOperator 0x562f2aa5e358 <col:23, line:10:13> 'int' '=='
            | |-ImplicitCastExpr 0x562f2aa5e340 <line:21:23> 'unsigned int' <LValueToRValue>
            | | `-DeclRefExpr 0x562f2aa5dba0 <col:23> 'unsigned int' lvalue Var 0x562f2aa5d6a0 'sn' 'unsigned int'
            | `-BinaryOperator 0x562f2aa5e320 <col:27, line:10:13> 'unsigned int' '*'
            |   |-ImplicitCastExpr 0x562f2aa5e2f0 <line:21:27> 'unsigned int' <LValueToRValue>
            |   | `-DeclRefExpr 0x562f2aa5e290 <col:27> 'unsigned int' lvalue Var 0x562f2aa5d980 'x' 'unsigned int'
            |   `-ImplicitCastExpr 0x562f2aa5e308 <line:10:11, col:13> 'unsigned int' <IntegralCast>
            |     `-ParenExpr 0x562f2aa5e2d0 <col:11, col:13> 'int'
            |       `-IntegerLiteral 0x562f2aa5e2b0 <col:12> 'int' 2
            `-BinaryOperator 0x562f2aa5e3e8 <line:21:34, col:40> 'int' '=='
              |-ImplicitCastExpr 0x562f2aa5e3b8 <col:34> 'unsigned int' <LValueToRValue>
              | `-DeclRefExpr 0x562f2aa5e378 <col:34> 'unsigned int' lvalue Var 0x562f2aa5d6a0 'sn' 'unsigned int'
              `-ImplicitCastExpr 0x562f2aa5e3d0 <col:40> 'unsigned int' <IntegralCast>
                `-IntegerLiteral 0x562f2aa5e398 <col:40> 'int' 0
1 warning generated.
