./Benchmark/PLDI/SVComp/loops/verisec_NetBSD-libc_loop.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/verisec_NetBSD-libc_loop.c:2:22: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error() { assert(0); }
                     ^
TranslationUnitDecl 0x55dfe4a2bf48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55dfe4a2c7e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55dfe4a2c4e0 '__int128'
|-TypedefDecl 0x55dfe4a2c850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55dfe4a2c500 'unsigned __int128'
|-TypedefDecl 0x55dfe4a2cb58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55dfe4a2c930 'struct __NSConstantString_tag'
|   `-Record 0x55dfe4a2c8a8 '__NSConstantString_tag'
|-TypedefDecl 0x55dfe4a2cbf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55dfe4a2cbb0 'char *'
|   `-BuiltinType 0x55dfe4a2bfe0 'char'
|-TypedefDecl 0x55dfe4a2cee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55dfe4a2ce90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55dfe4a2ccd0 'struct __va_list_tag'
|     `-Record 0x55dfe4a2cc48 '__va_list_tag'
|-FunctionDecl 0x55dfe4a8bf08 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/verisec_NetBSD-libc_loop.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55dfe4a8bfa8 prev 0x55dfe4a8bf08 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55dfe4a8c098 <line:2:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55dfe4a8c328 <col:20, col:33>
|   `-CallExpr 0x55dfe4a8c300 <col:22, col:30> 'int'
|     |-ImplicitCastExpr 0x55dfe4a8c2e8 <col:22> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55dfe4a8c280 <col:22> 'int ()' Function 0x55dfe4a8c1d0 'assert' 'int ()'
|     `-IntegerLiteral 0x55dfe4a8c2a0 <col:29> 'int' 0
|-FunctionDecl 0x55dfe4a8c418 <line:4:1, line:9:1> line:4:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x55dfe4a8c358 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x55dfe4a8c6f8 <col:34, line:9:1>
|   |-IfStmt 0x55dfe4a8c6d0 <line:5:3, line:7:3>
|   | |-UnaryOperator 0x55dfe4a8c518 <line:5:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x55dfe4a8c500 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x55dfe4a8c4e0 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x55dfe4a8c4c0 <col:9> 'int' lvalue ParmVar 0x55dfe4a8c358 'cond' 'int'
|   | `-CompoundStmt 0x55dfe4a8c6b8 <col:16, line:7:3>
|   |   `-LabelStmt 0x55dfe4a8c6a0 <line:6:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x55dfe4a8c630 <col:12, col:35>
|   |       |-CallExpr 0x55dfe4a8c590 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x55dfe4a8c578 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x55dfe4a8c530 <col:13> 'void ()' Function 0x55dfe4a8c098 'reach_error' 'void ()'
|   |       `-CallExpr 0x55dfe4a8c610 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x55dfe4a8c5f8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x55dfe4a8c5b0 <col:27> 'void (void) __attribute__((noreturn))' Function 0x55dfe4a8bfa8 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x55dfe4a8c6e8 <line:8:3>
|-TypedefDecl 0x55dfe4a8c730 <line:10:1, col:13> col:13 referenced Char 'int'
| `-BuiltinType 0x55dfe4a2c040 'int'
|-VarDecl 0x55dfe4a8c818 <line:13:1, col:7> col:7 used tmp 'Char *'
|-FunctionDecl 0x55dfe4a8ca20 <line:15:1, line:26:1> line:15:5 used glob2 'int (Char *, Char *)'
| |-ParmVarDecl 0x55dfe4a8c890 <col:12, col:18> col:18 used pathbuf 'Char *'
| |-ParmVarDecl 0x55dfe4a8c908 <col:27, col:33> col:33 used pathlim 'Char *'
| `-CompoundStmt 0x55dfe4a8d488 <line:16:1, line:26:1>
|   |-DeclStmt 0x55dfe4a8cb48 <line:17:3, col:10>
|   | `-VarDecl 0x55dfe4a8cae0 <col:3, col:9> col:9 used p 'Char *'
|   |-ForStmt 0x55dfe4a8d420 <line:19:3, line:23:3>
|   | |-BinaryOperator 0x55dfe4a8cbb8 <line:19:8, col:12> 'Char *' '='
|   | | |-DeclRefExpr 0x55dfe4a8cb60 <col:8> 'Char *' lvalue Var 0x55dfe4a8cae0 'p' 'Char *'
|   | | `-ImplicitCastExpr 0x55dfe4a8cba0 <col:12> 'Char *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55dfe4a8cb80 <col:12> 'Char *' lvalue ParmVar 0x55dfe4a8c890 'pathbuf' 'Char *'
|   | |-<<<NULL>>>
|   | |-BinaryOperator 0x55dfe4a8cc48 <col:21, col:26> 'int' '<='
|   | | |-ImplicitCastExpr 0x55dfe4a8cc18 <col:21> 'Char *' <LValueToRValue>
|   | | | `-DeclRefExpr 0x55dfe4a8cbd8 <col:21> 'Char *' lvalue Var 0x55dfe4a8cae0 'p' 'Char *'
|   | | `-ImplicitCastExpr 0x55dfe4a8cc30 <col:26> 'Char *' <LValueToRValue>
|   | |   `-DeclRefExpr 0x55dfe4a8cbf8 <col:26> 'Char *' lvalue ParmVar 0x55dfe4a8c908 'pathlim' 'Char *'
|   | |-UnaryOperator 0x55dfe4a8cc88 <col:35, col:36> 'Char *' postfix '++'
|   | | `-DeclRefExpr 0x55dfe4a8cc68 <col:35> 'Char *' lvalue Var 0x55dfe4a8cae0 'p' 'Char *'
|   | `-CompoundStmt 0x55dfe4a8d400 <col:40, line:23:3>
|   |   |-CallExpr 0x55dfe4a8cd90 <line:21:5, col:29> 'void'
|   |   | |-ImplicitCastExpr 0x55dfe4a8cd78 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
|   |   | | `-DeclRefExpr 0x55dfe4a8cca0 <col:5> 'void (int)' Function 0x55dfe4a8c418 '__VERIFIER_assert' 'void (int)'
|   |   | `-BinaryOperator 0x55dfe4a8cd30 <col:23, col:26> 'int' '<='
|   |   |   |-ImplicitCastExpr 0x55dfe4a8cd00 <col:23> 'Char *' <LValueToRValue>
|   |   |   | `-DeclRefExpr 0x55dfe4a8ccc0 <col:23> 'Char *' lvalue Var 0x55dfe4a8cae0 'p' 'Char *'
|   |   |   `-ImplicitCastExpr 0x55dfe4a8cd18 <col:26> 'Char *' <LValueToRValue>
|   |   |     `-DeclRefExpr 0x55dfe4a8cce0 <col:26> 'Char *' lvalue Var 0x55dfe4a8c818 'tmp' 'Char *'
|   |   `-BinaryOperator 0x55dfe4a8d3e0 <line:22:5, col:10> 'Char':'int' '='
|   |     |-UnaryOperator 0x55dfe4a8cdf0 <col:5, col:6> 'Char':'int' lvalue prefix '*' cannot overflow
|   |     | `-ImplicitCastExpr 0x55dfe4a8cdd8 <col:6> 'Char *' <LValueToRValue>
|   |     |   `-DeclRefExpr 0x55dfe4a8cdb8 <col:6> 'Char *' lvalue Var 0x55dfe4a8cae0 'p' 'Char *'
|   |     `-IntegerLiteral 0x55dfe4a8d3c0 <col:10> 'int' 1
|   `-ReturnStmt 0x55dfe4a8d478 <line:25:3, col:10>
|     `-IntegerLiteral 0x55dfe4a8d458 <col:10> 'int' 0
`-FunctionDecl 0x55dfe4a8d4d8 <line:28:1, line:39:1> line:28:5 main 'int ()'
  `-CompoundStmt 0x55dfe4a8dbe0 <line:29:1, line:39:1>
    |-DeclStmt 0x55dfe4a8d6f0 <line:30:3, col:29>
    | `-VarDecl 0x55dfe4a8d688 <col:3, col:28> col:8 used pathbuf 'Char [2]'
    |-DeclStmt 0x55dfe4a8d878 <line:32:3, col:46>
    | `-VarDecl 0x55dfe4a8d718 <col:3, col:45> col:9 used bound 'Char *' cinit
    |   `-BinaryOperator 0x55dfe4a8d858 <col:17, col:45> 'Char *' '-'
    |     |-BinaryOperator 0x55dfe4a8d818 <col:17, col:41> 'Char *' '+'
    |     | |-ImplicitCastExpr 0x55dfe4a8d800 <col:17> 'Char *' <ArrayToPointerDecay>
    |     | | `-DeclRefExpr 0x55dfe4a8d780 <col:17> 'Char [2]' lvalue Var 0x55dfe4a8d688 'pathbuf' 'Char [2]'
    |     | `-UnaryExprOrTypeTraitExpr 0x55dfe4a8d7e0 <col:27, col:41> 'unsigned long' sizeof
    |     |   `-ParenExpr 0x55dfe4a8d7c0 <col:33, col:41> 'Char [2]' lvalue
    |     |     `-DeclRefExpr 0x55dfe4a8d7a0 <col:34> 'Char [2]' lvalue Var 0x55dfe4a8d688 'pathbuf' 'Char [2]' non_odr_use_unevaluated
    |     `-IntegerLiteral 0x55dfe4a8d838 <col:45> 'int' 1
    |-BinaryOperator 0x55dfe4a8da58 <line:34:3, col:54> 'Char *' '='
    | |-DeclRefExpr 0x55dfe4a8d890 <col:3> 'Char *' lvalue Var 0x55dfe4a8c818 'tmp' 'Char *'
    | `-BinaryOperator 0x55dfe4a8da38 <col:9, col:54> 'Char *' '-'
    |   |-BinaryOperator 0x55dfe4a8d9f8 <col:9, col:50> 'Char *' '+'
    |   | |-ImplicitCastExpr 0x55dfe4a8d9e0 <col:9> 'Char *' <ArrayToPointerDecay>
    |   | | `-DeclRefExpr 0x55dfe4a8d8b0 <col:9> 'Char [2]' lvalue Var 0x55dfe4a8d688 'pathbuf' 'Char [2]'
    |   | `-BinaryOperator 0x55dfe4a8d9c0 <col:19, col:50> 'unsigned long' '/'
    |   |   |-UnaryExprOrTypeTraitExpr 0x55dfe4a8d910 <col:19, col:33> 'unsigned long' sizeof
    |   |   | `-ParenExpr 0x55dfe4a8d8f0 <col:25, col:33> 'Char [2]' lvalue
    |   |   |   `-DeclRefExpr 0x55dfe4a8d8d0 <col:26> 'Char [2]' lvalue Var 0x55dfe4a8d688 'pathbuf' 'Char [2]' non_odr_use_unevaluated
    |   |   `-UnaryExprOrTypeTraitExpr 0x55dfe4a8d9a0 <col:35, col:50> 'unsigned long' sizeof
    |   |     `-ParenExpr 0x55dfe4a8d980 <col:41, col:50> 'Char':'int' lvalue
    |   |       `-UnaryOperator 0x55dfe4a8d968 <col:42, col:43> 'Char':'int' lvalue prefix '*' cannot overflow
    |   |         `-ImplicitCastExpr 0x55dfe4a8d950 <col:43> 'Char *' <ArrayToPointerDecay>
    |   |           `-DeclRefExpr 0x55dfe4a8d930 <col:43> 'Char [2]' lvalue Var 0x55dfe4a8d688 'pathbuf' 'Char [2]' non_odr_use_unevaluated
    |   `-IntegerLiteral 0x55dfe4a8da18 <col:54> 'int' 1
    |-CallExpr 0x55dfe4a8db50 <line:36:3, col:24> 'int'
    | |-ImplicitCastExpr 0x55dfe4a8db38 <col:3> 'int (*)(Char *, Char *)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55dfe4a8da78 <col:3> 'int (Char *, Char *)' Function 0x55dfe4a8ca20 'glob2' 'int (Char *, Char *)'
    | |-ImplicitCastExpr 0x55dfe4a8db80 <col:10> 'Char *' <ArrayToPointerDecay>
    | | `-DeclRefExpr 0x55dfe4a8da98 <col:10> 'Char [2]' lvalue Var 0x55dfe4a8d688 'pathbuf' 'Char [2]'
    | `-ImplicitCastExpr 0x55dfe4a8db98 <col:19> 'Char *' <LValueToRValue>
    |   `-DeclRefExpr 0x55dfe4a8dab8 <col:19> 'Char *' lvalue Var 0x55dfe4a8d718 'bound' 'Char *'
    `-ReturnStmt 0x55dfe4a8dbd0 <line:38:3, col:10>
      `-IntegerLiteral 0x55dfe4a8dbb0 <col:10> 'int' 0
1 warning generated.
