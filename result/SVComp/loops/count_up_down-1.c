./Benchmark/PLDI/SVComp/loops/count_up_down-1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/count_up_down-1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x56534da23e18 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x56534da246b0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x56534da243b0 '__int128'
|-TypedefDecl 0x56534da24720 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x56534da243d0 'unsigned __int128'
|-TypedefDecl 0x56534da24a28 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x56534da24800 'struct __NSConstantString_tag'
|   `-Record 0x56534da24778 '__NSConstantString_tag'
|-TypedefDecl 0x56534da24ac0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x56534da24a80 'char *'
|   `-BuiltinType 0x56534da23eb0 'char'
|-TypedefDecl 0x56534da24db8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x56534da24d60 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x56534da24ba0 'struct __va_list_tag'
|     `-Record 0x56534da24b18 '__va_list_tag'
|-FunctionDecl 0x56534da83dc8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/count_up_down-1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56534da83e68 prev 0x56534da83dc8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x56534da841e8 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x56534da83f20 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x56534da83fa0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x56534da84020 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x56534da840a0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x56534da842a8 <col:99>
|-FunctionDecl 0x56534da84398 <line:3:1, col:81> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x56534da846d8 <col:20, col:81>
|   `-CallExpr 0x56534da845f0 <col:22, col:78> 'void'
|     |-ImplicitCastExpr 0x56534da845d8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x56534da84438 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x56534da841e8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x56534da84648 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56534da84630 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56534da84498 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x56534da84678 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x56534da84660 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x56534da844f8 <col:41> 'char [18]' lvalue "count_up_down-1.c"
|     |-ImplicitCastExpr 0x56534da84690 <col:62> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x56534da84528 <col:62> 'int' 3
|     `-ImplicitCastExpr 0x56534da846c0 <col:65> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x56534da846a8 <col:65> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x56534da84588 <col:65> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x56534da847c8 <line:5:1, line:10:1> line:5:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x56534da84708 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x56534da84aa8 <col:34, line:10:1>
|   |-IfStmt 0x56534da84a80 <line:6:3, line:8:3>
|   | |-UnaryOperator 0x56534da848c8 <line:6:7, col:13> 'int' prefix '!' cannot overflow
|   | | `-ImplicitCastExpr 0x56534da848b0 <col:8, col:13> 'int' <LValueToRValue>
|   | |   `-ParenExpr 0x56534da84890 <col:8, col:13> 'int' lvalue
|   | |     `-DeclRefExpr 0x56534da84870 <col:9> 'int' lvalue ParmVar 0x56534da84708 'cond' 'int'
|   | `-CompoundStmt 0x56534da84a68 <col:16, line:8:3>
|   |   `-LabelStmt 0x56534da84a50 <line:7:5, col:35> 'ERROR'
|   |     `-CompoundStmt 0x56534da849e0 <col:12, col:35>
|   |       |-CallExpr 0x56534da84940 <col:13, col:25> 'void'
|   |       | `-ImplicitCastExpr 0x56534da84928 <col:13> 'void (*)()' <FunctionToPointerDecay>
|   |       |   `-DeclRefExpr 0x56534da848e0 <col:13> 'void ()' Function 0x56534da84398 'reach_error' 'void ()'
|   |       `-CallExpr 0x56534da849c0 <col:27, col:33> 'void'
|   |         `-ImplicitCastExpr 0x56534da849a8 <col:27> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|   |           `-DeclRefExpr 0x56534da84960 <col:27> 'void (void) __attribute__((noreturn))' Function 0x56534da83e68 'abort' 'void (void) __attribute__((noreturn))'
|   `-ReturnStmt 0x56534da84a98 <line:9:3>
|-FunctionDecl 0x56534da84b20 <line:11:1, col:37> col:14 used __VERIFIER_nondet_uint 'unsigned int ()'
`-FunctionDecl 0x56534da84c10 <line:13:1, line:23:1> line:13:5 main 'int ()'
  `-CompoundStmt 0x56534da86bc8 <line:14:1, line:23:1>
    |-DeclStmt 0x56534da867c0 <line:15:3, col:44>
    | `-VarDecl 0x56534da866d0 <col:3, col:43> col:16 used n 'unsigned int' cinit
    |   `-CallExpr 0x56534da867a0 <col:20, col:43> 'unsigned int'
    |     `-ImplicitCastExpr 0x56534da86788 <col:20> 'unsigned int (*)()' <FunctionToPointerDecay>
    |       `-DeclRefExpr 0x56534da86738 <col:20> 'unsigned int ()' Function 0x56534da84b20 '__VERIFIER_nondet_uint' 'unsigned int ()'
    |-DeclStmt 0x56534da86960 <line:16:3, col:24>
    | |-VarDecl 0x56534da867f0 <col:3, col:18> col:16 used x 'unsigned int' cinit
    | | `-ImplicitCastExpr 0x56534da86878 <col:18> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x56534da86858 <col:18> 'unsigned int' lvalue Var 0x56534da866d0 'n' 'unsigned int'
    | `-VarDecl 0x56534da868a8 <col:3, col:23> col:21 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x56534da86930 <col:23> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x56534da86910 <col:23> 'int' 0
    |-WhileStmt 0x56534da86a98 <line:17:3, line:21:3>
    | |-BinaryOperator 0x56534da869e8 <line:17:9, col:11> 'int' '>'
    | | |-ImplicitCastExpr 0x56534da869b8 <col:9> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x56534da86978 <col:9> 'unsigned int' lvalue Var 0x56534da867f0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x56534da869d0 <col:11> 'unsigned int' <IntegralCast>
    | |   `-IntegerLiteral 0x56534da86998 <col:11> 'int' 0
    | `-CompoundStmt 0x56534da86a78 <line:18:3, line:21:3>
    |   |-UnaryOperator 0x56534da86a28 <line:19:5, col:6> 'unsigned int' postfix '--'
    |   | `-DeclRefExpr 0x56534da86a08 <col:5> 'unsigned int' lvalue Var 0x56534da867f0 'x' 'unsigned int'
    |   `-UnaryOperator 0x56534da86a60 <line:20:5, col:6> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x56534da86a40 <col:5> 'unsigned int' lvalue Var 0x56534da868a8 'y' 'unsigned int'
    `-CallExpr 0x56534da86ba0 <line:22:3, col:25> 'void'
      |-ImplicitCastExpr 0x56534da86b88 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x56534da86ab0 <col:3> 'void (int)' Function 0x56534da847c8 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x56534da86b40 <col:21, col:24> 'int' '=='
        |-ImplicitCastExpr 0x56534da86b10 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x56534da86ad0 <col:21> 'unsigned int' lvalue Var 0x56534da868a8 'y' 'unsigned int'
        `-ImplicitCastExpr 0x56534da86b28 <col:24> 'unsigned int' <LValueToRValue>
          `-DeclRefExpr 0x56534da86af0 <col:24> 'unsigned int' lvalue Var 0x56534da866d0 'n' 'unsigned int'
1 warning generated.
