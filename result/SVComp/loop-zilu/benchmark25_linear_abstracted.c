./Benchmark/PLDI/SVComp/loop-zilu/benchmark25_linear_abstracted.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark25_linear_abstracted.c:1:25: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error(void) {assert(0);}
                        ^
TranslationUnitDecl 0x56400df46028 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x56400df468c0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x56400df465c0 '__int128'
|-TypedefDecl 0x56400df46930 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x56400df465e0 'unsigned __int128'
|-TypedefDecl 0x56400df46c38 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x56400df46a10 'struct __NSConstantString_tag'
|   `-Record 0x56400df46988 '__NSConstantString_tag'
|-TypedefDecl 0x56400df46cd0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x56400df46c90 'char *'
|   `-BuiltinType 0x56400df460c0 'char'
|-TypedefDecl 0x56400df46fc8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x56400df46f70 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x56400df46db0 'struct __va_list_tag'
|     `-Record 0x56400df46d28 '__va_list_tag'
|-FunctionDecl 0x56400dfa6018 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-zilu/benchmark25_linear_abstracted.c:1:1, col:35> col:6 used reach_error 'void (void)'
| `-CompoundStmt 0x56400dfa62a8 <col:24, col:35>
|   `-CallExpr 0x56400dfa6280 <col:25, col:33> 'int'
|     |-ImplicitCastExpr 0x56400dfa6268 <col:25> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x56400dfa6200 <col:25> 'int ()' Function 0x56400dfa6150 'assert' 'int ()'
|     `-IntegerLiteral 0x56400dfa6220 <col:32> 'int' 0
|-FunctionDecl 0x56400dfa6388 <line:2:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56400dfa6428 prev 0x56400dfa6388 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56400dfa6590 <line:4:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x56400dfa66f8 <line:5:1, col:41> col:14 __VERIFIER_nondet_bool '_Bool (void)' extern
|-FunctionDecl 0x56400dfa6878 <line:7:1, line:11:1> line:7:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x56400dfa67b0 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x56400dfa6a20 <col:34, line:11:1>
|   `-IfStmt 0x56400dfa6a08 <line:8:3, line:10:3>
|     |-UnaryOperator 0x56400dfa6958 <line:8:7, col:8> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x56400dfa6940 <col:8> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x56400dfa6920 <col:8> 'int' lvalue ParmVar 0x56400dfa67b0 'cond' 'int'
|     `-CompoundStmt 0x56400dfa69f0 <col:14, line:10:3>
|       `-CallExpr 0x56400dfa69d0 <line:9:5, col:17> 'void'
|         `-ImplicitCastExpr 0x56400dfa69b8 <col:5> 'void (*)(void)' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x56400dfa6970 <col:5> 'void (void)' Function 0x56400dfa6018 'reach_error' 'void (void)'
`-FunctionDecl 0x56400dfa6a60 <line:21:1, line:36:1> line:21:5 main 'int ()'
  `-CompoundStmt 0x56400dfa7b08 <col:12, line:36:1>
    |-DeclStmt 0x56400dfa6c00 <line:22:3, col:34>
    | `-VarDecl 0x56400dfa6b18 <col:3, col:33> col:7 used x 'int' cinit
    |   `-CallExpr 0x56400dfa6be0 <col:11, col:33> 'int'
    |     `-ImplicitCastExpr 0x56400dfa6bc8 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x56400dfa6b80 <col:11> 'int (void)' Function 0x56400dfa6590 '__VERIFIER_nondet_int' 'int (void)'
    |-IfStmt 0x56400dfa6cf8 <line:23:3, col:22>
    | |-UnaryOperator 0x56400dfa6cb0 <col:7, col:12> 'int' prefix '!' cannot overflow
    | | `-ParenExpr 0x56400dfa6c90 <col:8, col:12> 'int'
    | |   `-BinaryOperator 0x56400dfa6c70 <col:9, col:11> 'int' '<'
    | |     |-ImplicitCastExpr 0x56400dfa6c58 <col:9> 'int' <LValueToRValue>
    | |     | `-DeclRefExpr 0x56400dfa6c18 <col:9> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    | |     `-IntegerLiteral 0x56400dfa6c38 <col:11> 'int' 0
    | `-ReturnStmt 0x56400dfa6ce8 <col:15, col:22>
    |   `-IntegerLiteral 0x56400dfa6cc8 <col:22> 'int' 0
    |-IfStmt 0x56400dfa79c0 <line:25:3, line:32:3>
    | |-BinaryOperator 0x56400dfa6d88 <line:25:7, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x56400dfa6d70 <col:7> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x56400dfa6d10 <col:7> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    | | `-ParenExpr 0x56400dfa6d50 <col:11, col:14> 'int'
    | |   `-IntegerLiteral 0x56400dfa6d30 <col:12> 'int' 10
    | `-CompoundStmt 0x56400dfa7990 <col:17, line:32:3>
    |   |-BinaryOperator 0x56400dfa6e20 <line:26:3, col:29> 'int' '='
    |   | |-DeclRefExpr 0x56400dfa6da8 <col:3> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    |   | `-CallExpr 0x56400dfa6e00 <col:7, col:29> 'int'
    |   |   `-ImplicitCastExpr 0x56400dfa6de8 <col:7> 'int (*)(void)' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x56400dfa6dc8 <col:7> 'int (void)' Function 0x56400dfa6590 '__VERIFIER_nondet_int' 'int (void)'
    |   |-IfStmt 0x56400dfa7710 <line:27:3, col:26>
    |   | |-UnaryOperator 0x56400dfa6ef8 <col:7, col:17> 'int' prefix '!' cannot overflow
    |   | | `-ParenExpr 0x56400dfa6ed8 <col:8, col:17> 'int'
    |   | |   `-BinaryOperator 0x56400dfa6eb8 <col:9, col:16> 'int' '<'
    |   | |     |-ImplicitCastExpr 0x56400dfa6ea0 <col:9> 'int' <LValueToRValue>
    |   | |     | `-DeclRefExpr 0x56400dfa6e40 <col:9> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    |   | |     `-ParenExpr 0x56400dfa6e80 <col:13, col:16> 'int'
    |   | |       `-IntegerLiteral 0x56400dfa6e60 <col:14> 'int' 10
    |   | `-CallExpr 0x56400dfa76f0 <col:20, col:26> 'void'
    |   |   `-ImplicitCastExpr 0x56400dfa76d8 <col:20> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |   |     `-DeclRefExpr 0x56400dfa6f10 <col:20> 'void (void) __attribute__((noreturn))' Function 0x56400dfa6428 'abort' 'void (void) __attribute__((noreturn))'
    |   |-IfStmt 0x56400dfa7870 <line:28:3, line:30:5>
    |   | |-BinaryOperator 0x56400dfa7780 <line:28:7, col:9> 'int' '<'
    |   | | |-ImplicitCastExpr 0x56400dfa7768 <col:7> 'int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x56400dfa7728 <col:7> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    |   | | `-IntegerLiteral 0x56400dfa7748 <col:9> 'int' 10
    |   | `-CompoundStmt 0x56400dfa7858 <col:13, line:30:5>
    |   |   `-BinaryOperator 0x56400dfa7838 <line:29:7, col:11> 'int' '='
    |   |     |-DeclRefExpr 0x56400dfa77a0 <col:7> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    |   |     `-BinaryOperator 0x56400dfa7818 <col:9, col:11> 'int' '+'
    |   |       |-ImplicitCastExpr 0x56400dfa7800 <col:9> 'int' <LValueToRValue>
    |   |       | `-DeclRefExpr 0x56400dfa77c0 <col:9> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    |   |       `-IntegerLiteral 0x56400dfa77e0 <col:11> 'int' 1
    |   `-IfStmt 0x56400dfa7978 <line:31:3, col:23>
    |     |-BinaryOperator 0x56400dfa7900 <col:7, col:14> 'int' '<'
    |     | |-ImplicitCastExpr 0x56400dfa78e8 <col:7> 'int' <LValueToRValue>
    |     | | `-DeclRefExpr 0x56400dfa7888 <col:7> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    |     | `-ParenExpr 0x56400dfa78c8 <col:11, col:14> 'int'
    |     |   `-IntegerLiteral 0x56400dfa78a8 <col:12> 'int' 10
    |     `-CallExpr 0x56400dfa7958 <col:17, col:23> 'void'
    |       `-ImplicitCastExpr 0x56400dfa7940 <col:17> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
    |         `-DeclRefExpr 0x56400dfa7920 <col:17> 'void (void) __attribute__((noreturn))' Function 0x56400dfa6428 'abort' 'void (void) __attribute__((noreturn))'
    |-CallExpr 0x56400dfa7ab0 <line:34:3, col:26> 'void'
    | |-ImplicitCastExpr 0x56400dfa7a98 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x56400dfa79d8 <col:3> 'void (int)' Function 0x56400dfa6878 '__VERIFIER_assert' 'void (int)'
    | `-BinaryOperator 0x56400dfa7a50 <col:21, col:24> 'int' '=='
    |   |-ImplicitCastExpr 0x56400dfa7a38 <col:21> 'int' <LValueToRValue>
    |   | `-DeclRefExpr 0x56400dfa79f8 <col:21> 'int' lvalue Var 0x56400dfa6b18 'x' 'int'
    |   `-IntegerLiteral 0x56400dfa7a18 <col:24> 'int' 10
    `-ReturnStmt 0x56400dfa7af8 <line:35:3, col:10>
      `-IntegerLiteral 0x56400dfa7ad8 <col:10> 'int' 0
1 warning generated.
