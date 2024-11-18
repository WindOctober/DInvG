./Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.p+cfa-reducer.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.p+cfa-reducer.c:3:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x563286eb5f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x563286eb67e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x563286eb64e0 '__int128'
|-TypedefDecl 0x563286eb6850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x563286eb6500 'unsigned __int128'
|-TypedefDecl 0x563286eb6b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x563286eb6930 'struct __NSConstantString_tag'
|   `-Record 0x563286eb68a8 '__NSConstantString_tag'
|-TypedefDecl 0x563286eb6bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x563286eb6bb0 'char *'
|   `-BuiltinType 0x563286eb5fe0 'char'
|-TypedefDecl 0x563286eb6ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x563286eb6e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x563286eb6cd0 'struct __va_list_tag'
|     `-Record 0x563286eb6c48 '__va_list_tag'
|-VarDecl 0x563286f16048 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.p+cfa-reducer.c:1:1, col:5> col:5 used __return_main 'int'
|-FunctionDecl 0x563286f161e8 <line:2:6> col:6 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x563286f16288 prev 0x563286f161e8 <col:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x563286f16608 <line:3:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x563286f16340 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x563286f163c0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x563286f16440 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x563286f164c0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x563286f166c8 <col:99>
|-FunctionDecl 0x563286f16768 <line:4:1, col:91> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x563286f16aa8 <col:20, col:91>
|   `-CallExpr 0x563286f169c0 <col:22, col:88> 'void'
|     |-ImplicitCastExpr 0x563286f169a8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x563286f16808 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x563286f16608 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x563286f16a18 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x563286f16a00 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x563286f16868 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x563286f16a48 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x563286f16a30 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x563286f168c8 <col:41> 'char [28]' lvalue "gsv2008.c.i.p+cfa-reducer.c"
|     |-ImplicitCastExpr 0x563286f16a60 <col:72> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x563286f16900 <col:72> 'int' 4
|     `-ImplicitCastExpr 0x563286f16a90 <col:75> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x563286f16a78 <col:75> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x563286f16958 <col:75> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x563286f16b58 prev 0x563286f16288 <line:5:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x563286f16cd8 <line:6:1, line:8:1> line:6:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x563286f16c10 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x563286f16e80 <col:36, line:8:1>
|   `-IfStmt 0x563286f16e68 <line:7:3, col:22>
|     |-UnaryOperator 0x563286f16db8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x563286f16da0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x563286f16d80 <col:7> 'int' lvalue ParmVar 0x563286f16c10 'cond' 'int'
|     `-CompoundStmt 0x563286f16e50 <col:13, col:22>
|       `-CallExpr 0x563286f16e30 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x563286f16e18 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x563286f16dd0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x563286f16b58 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x563286f16f40 <line:9:1, col:32> col:6 __VERIFIER_assert 'void (int)'
| `-ParmVarDecl 0x563286f16eb0 <col:24, col:28> col:28 cond 'int'
|-FunctionDecl 0x563286f188a8 <line:10:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x563286f18970 <line:11:1, col:10> col:5 main 'int ()'
|-VarDecl 0x563286f18a28 <line:12:1, col:5> col:5 used __return_144 'int'
`-FunctionDecl 0x563286f18ab8 prev 0x563286f18970 <line:13:2, line:60:2> line:13:6 main 'int ()'
  `-CompoundStmt 0x563286f1a710 <line:14:2, line:60:2>
    |-DeclStmt 0x563286f18bd8 <line:15:2, col:13>
    | `-VarDecl 0x563286f18b70 <col:2, col:6> col:6 used main__x 'int'
    |-DeclStmt 0x563286f18c70 <line:16:2, col:13>
    | `-VarDecl 0x563286f18c08 <col:2, col:6> col:6 used main__y 'int'
    |-BinaryOperator 0x563286f18ce0 <line:17:2, col:13> 'int' '='
    | |-DeclRefExpr 0x563286f18c88 <col:2> 'int' lvalue Var 0x563286f18b70 'main__x' 'int'
    | `-UnaryOperator 0x563286f18cc8 <col:12, col:13> 'int' prefix '-'
    |   `-IntegerLiteral 0x563286f18ca8 <col:13> 'int' 50
    |-BinaryOperator 0x563286f18da0 <line:18:2, col:34> 'int' '='
    | |-DeclRefExpr 0x563286f18d00 <col:2> 'int' lvalue Var 0x563286f18c08 'main__y' 'int'
    | `-CallExpr 0x563286f18d80 <col:12, col:34> 'int'
    |   `-ImplicitCastExpr 0x563286f18d68 <col:12> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x563286f18d20 <col:12> 'int ()' Function 0x563286f188a8 '__VERIFIER_nondet_int' 'int ()'
    `-IfStmt 0x563286f1a6e8 <line:19:2, line:59:2> has_else
      |-UnaryOperator 0x563286f18e70 <line:19:6, col:23> 'int' prefix '!' cannot overflow
      | `-ParenExpr 0x563286f18e50 <col:7, col:23> 'int'
      |   `-BinaryOperator 0x563286f18e30 <col:8, col:16> 'int' '<'
      |     |-UnaryOperator 0x563286f18de0 <col:8, col:9> 'int' prefix '-'
      |     | `-IntegerLiteral 0x563286f18dc0 <col:9> 'int' 1000
      |     `-ImplicitCastExpr 0x563286f18e18 <col:16> 'int' <LValueToRValue>
      |       `-DeclRefExpr 0x563286f18df8 <col:16> 'int' lvalue Var 0x563286f18c08 'main__y' 'int'
      |-CompoundStmt 0x563286f18ed0 <line:20:2, line:22:2>
      | `-ReturnStmt 0x563286f18ec0 <line:21:2, col:9>
      |   `-ImplicitCastExpr 0x563286f18ea8 <col:9> 'int' <LValueToRValue>
      |     `-DeclRefExpr 0x563286f18e88 <col:9> 'int' lvalue Var 0x563286f16048 '__return_main' 'int'
      `-CompoundStmt 0x563286f1a6d0 <line:24:2, line:59:2>
        `-IfStmt 0x563286f1a6a8 <line:25:2, line:58:2> has_else
          |-UnaryOperator 0x563286f18f80 <line:25:6, col:25> 'int' prefix '!' cannot overflow
          | `-ParenExpr 0x563286f18f60 <col:7, col:25> 'int'
          |   `-BinaryOperator 0x563286f18f40 <col:8, col:18> 'int' '<'
          |     |-ImplicitCastExpr 0x563286f18f28 <col:8> 'int' <LValueToRValue>
          |     | `-DeclRefExpr 0x563286f18ee8 <col:8> 'int' lvalue Var 0x563286f18c08 'main__y' 'int'
          |     `-IntegerLiteral 0x563286f18f08 <col:18> 'int' 1000000
          |-CompoundStmt 0x563286f18fe0 <line:26:2, line:28:2>
          | `-ReturnStmt 0x563286f18fd0 <line:27:2, col:9>
          |   `-ImplicitCastExpr 0x563286f18fb8 <col:9> 'int' <LValueToRValue>
          |     `-DeclRefExpr 0x563286f18f98 <col:9> 'int' lvalue Var 0x563286f16048 '__return_main' 'int'
          `-CompoundStmt 0x563286f1a688 <line:30:2, line:58:2>
            |-LabelStmt 0x563286f19050 <line:31:2, col:12> 'label_129'
            | `-NullStmt 0x563286f18ff8 <col:12>
            `-IfStmt 0x563286f1a660 <line:32:2, line:57:2> has_else
              |-BinaryOperator 0x563286f190c0 <line:32:6, col:16> 'int' '<'
              | |-ImplicitCastExpr 0x563286f190a8 <col:6> 'int' <LValueToRValue>
              | | `-DeclRefExpr 0x563286f19068 <col:6> 'int' lvalue Var 0x563286f18b70 'main__x' 'int'
              | `-IntegerLiteral 0x563286f19088 <col:16> 'int' 0
              |-CompoundStmt 0x563286f19350 <line:33:2, line:38:2>
              | |-BinaryOperator 0x563286f19190 <line:34:2, col:22> 'int' '='
              | | |-DeclRefExpr 0x563286f190e0 <col:2> 'int' lvalue Var 0x563286f18b70 'main__x' 'int'
              | | `-BinaryOperator 0x563286f19170 <col:12, col:22> 'int' '+'
              | |   |-ImplicitCastExpr 0x563286f19140 <col:12> 'int' <LValueToRValue>
              | |   | `-DeclRefExpr 0x563286f19100 <col:12> 'int' lvalue Var 0x563286f18b70 'main__x' 'int'
              | |   `-ImplicitCastExpr 0x563286f19158 <col:22> 'int' <LValueToRValue>
              | |     `-DeclRefExpr 0x563286f19120 <col:22> 'int' lvalue Var 0x563286f18c08 'main__y' 'int'
              | |-DeclStmt 0x563286f19268 <line:35:2, col:40>
              | | `-VarDecl 0x563286f191c8 <col:2, col:33> col:6 main____CPAchecker_TMP_0 'int' cinit
              | |   `-ImplicitCastExpr 0x563286f19250 <col:33> 'int' <LValueToRValue>
              | |     `-DeclRefExpr 0x563286f19230 <col:33> 'int' lvalue Var 0x563286f18c08 'main__y' 'int'
              | |-BinaryOperator 0x563286f19318 <line:36:2, col:22> 'int' '='
              | | |-DeclRefExpr 0x563286f19280 <col:2> 'int' lvalue Var 0x563286f18c08 'main__y' 'int'
              | | `-BinaryOperator 0x563286f192f8 <col:12, col:22> 'int' '+'
              | |   |-ImplicitCastExpr 0x563286f192e0 <col:12> 'int' <LValueToRValue>
              | |   | `-DeclRefExpr 0x563286f192a0 <col:12> 'int' lvalue Var 0x563286f18c08 'main__y' 'int'
              | |   `-IntegerLiteral 0x563286f192c0 <col:22> 'int' 1
              | `-GotoStmt 0x563286f19338 <line:37:2, col:7> 'label_129' 0x563286f19000
              `-CompoundStmt 0x563286f1a648 <line:40:2, line:57:2>
                `-CompoundStmt 0x563286f1a610 <line:41:2, line:56:2>
                  |-DeclStmt 0x563286f19400 <line:42:2, col:13>
                  | `-VarDecl 0x563286f19398 <col:2, col:6> col:6 used __tmp_1 'int'
                  |-BinaryOperator 0x563286f194b0 <line:43:2, col:22> 'int' '='
                  | |-DeclRefExpr 0x563286f19418 <col:2> 'int' lvalue Var 0x563286f19398 '__tmp_1' 'int'
                  | `-BinaryOperator 0x563286f19490 <col:12, col:22> 'int' '>'
                  |   |-ImplicitCastExpr 0x563286f19478 <col:12> 'int' <LValueToRValue>
                  |   | `-DeclRefExpr 0x563286f19438 <col:12> 'int' lvalue Var 0x563286f18c08 'main__y' 'int'
                  |   `-IntegerLiteral 0x563286f19458 <col:22> 'int' 0
                  |-DeclStmt 0x563286f19550 <line:44:2, col:29>
                  | `-VarDecl 0x563286f194e8 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
                  |-BinaryOperator 0x563286f195c0 <line:45:2, col:28> 'int' '='
                  | |-DeclRefExpr 0x563286f19568 <col:2> 'int' lvalue Var 0x563286f194e8 '__VERIFIER_assert__cond' 'int'
                  | `-ImplicitCastExpr 0x563286f195a8 <col:28> 'int' <LValueToRValue>
                  |   `-DeclRefExpr 0x563286f19588 <col:28> 'int' lvalue Var 0x563286f19398 '__tmp_1' 'int'
                  `-IfStmt 0x563286f19828 <line:46:2, line:55:2> has_else
                    |-BinaryOperator 0x563286f19638 <line:46:6, col:33> 'int' '=='
                    | |-ImplicitCastExpr 0x563286f19620 <col:6> 'int' <LValueToRValue>
                    | | `-DeclRefExpr 0x563286f195e0 <col:6> 'int' lvalue Var 0x563286f194e8 '__VERIFIER_assert__cond' 'int'
                    | `-IntegerLiteral 0x563286f19600 <col:33> 'int' 0
                    |-CompoundStmt 0x563286f19740 <line:47:2, line:50:2>
                    | |-CompoundStmt 0x563286f196e0 <line:48:2, col:17>
                    | | `-CallExpr 0x563286f196c0 <col:3, col:15> 'void'
                    | |   `-ImplicitCastExpr 0x563286f196a8 <col:3> 'void (*)()' <FunctionToPointerDecay>
                    | |     `-DeclRefExpr 0x563286f19658 <col:3> 'void ()' Function 0x563286f16768 'reach_error' 'void ()'
                    | `-ReturnStmt 0x563286f19730 <line:49:2, col:9>
                    |   `-ImplicitCastExpr 0x563286f19718 <col:9> 'int' <LValueToRValue>
                    |     `-DeclRefExpr 0x563286f196f8 <col:9> 'int' lvalue Var 0x563286f16048 '__return_main' 'int'
                    `-CompoundStmt 0x563286f19808 <line:52:2, line:55:2>
                      |-BinaryOperator 0x563286f197a0 <line:53:3, col:18> 'int' '='
                      | |-DeclRefExpr 0x563286f19760 <col:3> 'int' lvalue Var 0x563286f18a28 '__return_144' 'int'
                      | `-IntegerLiteral 0x563286f19780 <col:18> 'int' 0
                      `-ReturnStmt 0x563286f197f8 <line:54:2, col:9>
                        `-ImplicitCastExpr 0x563286f197e0 <col:9> 'int' <LValueToRValue>
                          `-DeclRefExpr 0x563286f197c0 <col:9> 'int' lvalue Var 0x563286f18a28 '__return_144' 'int'
1 warning generated.
