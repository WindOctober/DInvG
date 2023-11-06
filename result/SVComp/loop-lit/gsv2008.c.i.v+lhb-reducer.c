./Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.v+lhb-reducer.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.v+lhb-reducer.c:3:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55eedf6f3f48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55eedf6f47e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55eedf6f44e0 '__int128'
|-TypedefDecl 0x55eedf6f4850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55eedf6f4500 'unsigned __int128'
|-TypedefDecl 0x55eedf6f4b58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55eedf6f4930 'struct __NSConstantString_tag'
|   `-Record 0x55eedf6f48a8 '__NSConstantString_tag'
|-TypedefDecl 0x55eedf6f4bf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55eedf6f4bb0 'char *'
|   `-BuiltinType 0x55eedf6f3fe0 'char'
|-TypedefDecl 0x55eedf6f4ee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55eedf6f4e90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55eedf6f4cd0 'struct __va_list_tag'
|     `-Record 0x55eedf6f4c48 '__va_list_tag'
|-VarDecl 0x55eedf754168 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.v+lhb-reducer.c:1:1, col:5> col:5 used __return_main 'int'
|-FunctionDecl 0x55eedf754308 <line:2:6> col:6 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55eedf7543a8 prev 0x55eedf754308 <col:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55eedf754728 <line:3:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55eedf754460 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55eedf7544e0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55eedf754560 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55eedf7545e0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55eedf7547e8 <col:99>
|-FunctionDecl 0x55eedf754888 <line:4:1, col:91> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55eedf754bc8 <col:20, col:91>
|   `-CallExpr 0x55eedf754ae0 <col:22, col:88> 'void'
|     |-ImplicitCastExpr 0x55eedf754ac8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55eedf754928 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55eedf754728 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55eedf754b38 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55eedf754b20 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55eedf754988 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55eedf754b68 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55eedf754b50 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55eedf7549e8 <col:41> 'char [28]' lvalue "gsv2008.c.i.v+lhb-reducer.c"
|     |-ImplicitCastExpr 0x55eedf754b80 <col:72> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55eedf754a20 <col:72> 'int' 4
|     `-ImplicitCastExpr 0x55eedf754bb0 <col:75> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55eedf754b98 <col:75> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55eedf754a78 <col:75> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55eedf754c78 prev 0x55eedf7543a8 <line:5:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55eedf754df8 <line:6:1, line:8:1> line:6:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55eedf754d30 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55eedf754fa0 <col:36, line:8:1>
|   `-IfStmt 0x55eedf754f88 <line:7:3, col:22>
|     |-UnaryOperator 0x55eedf754ed8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55eedf754ec0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55eedf754ea0 <col:7> 'int' lvalue ParmVar 0x55eedf754d30 'cond' 'int'
|     `-CompoundStmt 0x55eedf754f70 <col:13, col:22>
|       `-CallExpr 0x55eedf754f50 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55eedf754f38 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55eedf754ef0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55eedf754c78 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55eedf755060 <line:9:1, col:32> col:6 __VERIFIER_assert 'void (int)'
| `-ParmVarDecl 0x55eedf754fd0 <col:24, col:28> col:28 cond 'int'
|-FunctionDecl 0x55eedf7569c8 <line:10:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x55eedf756a90 <line:11:1, col:10> col:5 main 'int ()'
|-VarDecl 0x55eedf756b48 <line:12:1, col:5> col:5 used __tmp_55_0 'int'
|-VarDecl 0x55eedf756bc8 <line:13:1, col:5> col:5 used __return_65 'int'
`-FunctionDecl 0x55eedf756c58 prev 0x55eedf756a90 <line:14:2, line:74:2> line:14:6 main 'int ()'
  `-CompoundStmt 0x55eedf75cc08 <line:15:2, line:74:2>
    |-DeclStmt 0x55eedf756d78 <line:16:2, col:13>
    | `-VarDecl 0x55eedf756d10 <col:2, col:6> col:6 used main__x 'int'
    |-DeclStmt 0x55eedf756e10 <line:17:2, col:13>
    | `-VarDecl 0x55eedf756da8 <col:2, col:6> col:6 used main__y 'int'
    |-BinaryOperator 0x55eedf756e80 <line:18:2, col:13> 'int' '='
    | |-DeclRefExpr 0x55eedf756e28 <col:2> 'int' lvalue Var 0x55eedf756d10 'main__x' 'int'
    | `-UnaryOperator 0x55eedf756e68 <col:12, col:13> 'int' prefix '-'
    |   `-IntegerLiteral 0x55eedf756e48 <col:13> 'int' 50
    |-BinaryOperator 0x55eedf756f40 <line:19:2, col:34> 'int' '='
    | |-DeclRefExpr 0x55eedf756ea0 <col:2> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
    | `-CallExpr 0x55eedf756f20 <col:12, col:34> 'int'
    |   `-ImplicitCastExpr 0x55eedf756f08 <col:12> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55eedf756ec0 <col:12> 'int ()' Function 0x55eedf7569c8 '__VERIFIER_nondet_int' 'int ()'
    `-IfStmt 0x55eedf75cbe0 <line:20:2, line:73:2> has_else
      |-UnaryOperator 0x55eedf757010 <line:20:6, col:23> 'int' prefix '!' cannot overflow
      | `-ParenExpr 0x55eedf756ff0 <col:7, col:23> 'int'
      |   `-BinaryOperator 0x55eedf756fd0 <col:8, col:16> 'int' '<'
      |     |-UnaryOperator 0x55eedf756f80 <col:8, col:9> 'int' prefix '-'
      |     | `-IntegerLiteral 0x55eedf756f60 <col:9> 'int' 1000
      |     `-ImplicitCastExpr 0x55eedf756fb8 <col:16> 'int' <LValueToRValue>
      |       `-DeclRefExpr 0x55eedf756f98 <col:16> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
      |-CompoundStmt 0x55eedf757070 <line:21:2, line:23:2>
      | `-ReturnStmt 0x55eedf757060 <line:22:2, col:9>
      |   `-ImplicitCastExpr 0x55eedf757048 <col:9> 'int' <LValueToRValue>
      |     `-DeclRefExpr 0x55eedf757028 <col:9> 'int' lvalue Var 0x55eedf754168 '__return_main' 'int'
      `-CompoundStmt 0x55eedf75cbc8 <line:25:2, line:73:2>
        `-IfStmt 0x55eedf75cba0 <line:26:2, line:72:2> has_else
          |-UnaryOperator 0x55eedf757120 <line:26:6, col:25> 'int' prefix '!' cannot overflow
          | `-ParenExpr 0x55eedf757100 <col:7, col:25> 'int'
          |   `-BinaryOperator 0x55eedf7570e0 <col:8, col:18> 'int' '<'
          |     |-ImplicitCastExpr 0x55eedf7570c8 <col:8> 'int' <LValueToRValue>
          |     | `-DeclRefExpr 0x55eedf757088 <col:8> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
          |     `-IntegerLiteral 0x55eedf7570a8 <col:18> 'int' 1000000
          |-CompoundStmt 0x55eedf757180 <line:27:2, line:29:2>
          | `-ReturnStmt 0x55eedf757170 <line:28:2, col:9>
          |   `-ImplicitCastExpr 0x55eedf757158 <col:9> 'int' <LValueToRValue>
          |     `-DeclRefExpr 0x55eedf757138 <col:9> 'int' lvalue Var 0x55eedf754168 '__return_main' 'int'
          `-CompoundStmt 0x55eedf75cb88 <line:31:2, line:72:2>
            `-IfStmt 0x55eedf75cb60 <line:32:2, line:71:2> has_else
              |-BinaryOperator 0x55eedf7571f0 <line:32:6, col:16> 'int' '<'
              | |-ImplicitCastExpr 0x55eedf7571d8 <col:6> 'int' <LValueToRValue>
              | | `-DeclRefExpr 0x55eedf757198 <col:6> 'int' lvalue Var 0x55eedf756d10 'main__x' 'int'
              | `-IntegerLiteral 0x55eedf7571b8 <col:16> 'int' 0
              |-CompoundStmt 0x55eedf75cab8 <line:33:2, line:67:2>
              | |-BinaryOperator 0x55eedf7572c0 <line:34:2, col:22> 'int' '='
              | | |-DeclRefExpr 0x55eedf757210 <col:2> 'int' lvalue Var 0x55eedf756d10 'main__x' 'int'
              | | `-BinaryOperator 0x55eedf7572a0 <col:12, col:22> 'int' '+'
              | |   |-ImplicitCastExpr 0x55eedf757270 <col:12> 'int' <LValueToRValue>
              | |   | `-DeclRefExpr 0x55eedf757230 <col:12> 'int' lvalue Var 0x55eedf756d10 'main__x' 'int'
              | |   `-ImplicitCastExpr 0x55eedf757288 <col:22> 'int' <LValueToRValue>
              | |     `-DeclRefExpr 0x55eedf757250 <col:22> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              | |-DeclStmt 0x55eedf757398 <line:35:2, col:40>
              | | `-VarDecl 0x55eedf7572f8 <col:2, col:33> col:6 used main____CPAchecker_TMP_0 'int' cinit
              | |   `-ImplicitCastExpr 0x55eedf757380 <col:33> 'int' <LValueToRValue>
              | |     `-DeclRefExpr 0x55eedf757360 <col:33> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              | |-BinaryOperator 0x55eedf757448 <line:36:2, col:22> 'int' '='
              | | |-DeclRefExpr 0x55eedf7573b0 <col:2> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              | | `-BinaryOperator 0x55eedf757428 <col:12, col:22> 'int' '+'
              | |   |-ImplicitCastExpr 0x55eedf757410 <col:12> 'int' <LValueToRValue>
              | |   | `-DeclRefExpr 0x55eedf7573d0 <col:12> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              | |   `-IntegerLiteral 0x55eedf7573f0 <col:22> 'int' 1
              | |-BinaryOperator 0x55eedf7574c0 <line:37:2, col:15> 'int' '='
              | | |-DeclRefExpr 0x55eedf757468 <col:2> 'int' lvalue Var 0x55eedf756b48 '__tmp_55_0' 'int'
              | | `-ImplicitCastExpr 0x55eedf7574a8 <col:15> 'int' <LValueToRValue>
              | |   `-DeclRefExpr 0x55eedf757488 <col:15> 'int' lvalue Var 0x55eedf7572f8 'main____CPAchecker_TMP_0' 'int'
              | |-LabelStmt 0x55eedf757538 <line:38:2, col:11> 'label_55'
              | | `-NullStmt 0x55eedf7574e0 <col:11>
              | |-BinaryOperator 0x55eedf7575a8 <line:39:2, col:29> 'int' '='
              | | |-DeclRefExpr 0x55eedf757550 <col:2> 'int' lvalue Var 0x55eedf7572f8 'main____CPAchecker_TMP_0' 'int'
              | | `-ImplicitCastExpr 0x55eedf757590 <col:29> 'int' <LValueToRValue>
              | |   `-DeclRefExpr 0x55eedf757570 <col:29> 'int' lvalue Var 0x55eedf756b48 '__tmp_55_0' 'int'
              | `-IfStmt 0x55eedf75ca90 <line:40:2, line:66:2> has_else
              |   |-BinaryOperator 0x55eedf757620 <line:40:6, col:16> 'int' '<'
              |   | |-ImplicitCastExpr 0x55eedf757608 <col:6> 'int' <LValueToRValue>
              |   | | `-DeclRefExpr 0x55eedf7575c8 <col:6> 'int' lvalue Var 0x55eedf756d10 'main__x' 'int'
              |   | `-IntegerLiteral 0x55eedf7575e8 <col:16> 'int' 0
              |   |-CompoundStmt 0x55eedf757928 <line:41:2, line:47:2>
              |   | |-BinaryOperator 0x55eedf7576f0 <line:42:2, col:22> 'int' '='
              |   | | |-DeclRefExpr 0x55eedf757640 <col:2> 'int' lvalue Var 0x55eedf756d10 'main__x' 'int'
              |   | | `-BinaryOperator 0x55eedf7576d0 <col:12, col:22> 'int' '+'
              |   | |   |-ImplicitCastExpr 0x55eedf7576a0 <col:12> 'int' <LValueToRValue>
              |   | |   | `-DeclRefExpr 0x55eedf757660 <col:12> 'int' lvalue Var 0x55eedf756d10 'main__x' 'int'
              |   | |   `-ImplicitCastExpr 0x55eedf7576b8 <col:22> 'int' <LValueToRValue>
              |   | |     `-DeclRefExpr 0x55eedf757680 <col:22> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              |   | |-DeclStmt 0x55eedf7577c8 <line:43:2, col:40>
              |   | | `-VarDecl 0x55eedf757728 <col:2, col:33> col:6 used main____CPAchecker_TMP_0 'int' cinit
              |   | |   `-ImplicitCastExpr 0x55eedf7577b0 <col:33> 'int' <LValueToRValue>
              |   | |     `-DeclRefExpr 0x55eedf757790 <col:33> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              |   | |-BinaryOperator 0x55eedf757878 <line:44:2, col:22> 'int' '='
              |   | | |-DeclRefExpr 0x55eedf7577e0 <col:2> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              |   | | `-BinaryOperator 0x55eedf757858 <col:12, col:22> 'int' '+'
              |   | |   |-ImplicitCastExpr 0x55eedf757840 <col:12> 'int' <LValueToRValue>
              |   | |   | `-DeclRefExpr 0x55eedf757800 <col:12> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              |   | |   `-IntegerLiteral 0x55eedf757820 <col:22> 'int' 1
              |   | |-BinaryOperator 0x55eedf7578f0 <line:45:2, col:15> 'int' '='
              |   | | |-DeclRefExpr 0x55eedf757898 <col:2> 'int' lvalue Var 0x55eedf756b48 '__tmp_55_0' 'int'
              |   | | `-ImplicitCastExpr 0x55eedf7578d8 <col:15> 'int' <LValueToRValue>
              |   | |   `-DeclRefExpr 0x55eedf7578b8 <col:15> 'int' lvalue Var 0x55eedf757728 'main____CPAchecker_TMP_0' 'int'
              |   | `-GotoStmt 0x55eedf757910 <line:46:2, col:7> 'label_55' 0x55eedf7574e8
              |   `-CompoundStmt 0x55eedf75ca78 <line:49:2, line:66:2>
              |     `-CompoundStmt 0x55eedf75ca40 <line:50:2, line:65:2>
              |       |-DeclStmt 0x55eedf75c5f8 <line:51:2, col:13>
              |       | `-VarDecl 0x55eedf75c590 <col:2, col:6> col:6 used __tmp_1 'int'
              |       |-BinaryOperator 0x55eedf75c6a8 <line:52:2, col:22> 'int' '='
              |       | |-DeclRefExpr 0x55eedf75c610 <col:2> 'int' lvalue Var 0x55eedf75c590 '__tmp_1' 'int'
              |       | `-BinaryOperator 0x55eedf75c688 <col:12, col:22> 'int' '>'
              |       |   |-ImplicitCastExpr 0x55eedf75c670 <col:12> 'int' <LValueToRValue>
              |       |   | `-DeclRefExpr 0x55eedf75c630 <col:12> 'int' lvalue Var 0x55eedf756da8 'main__y' 'int'
              |       |   `-IntegerLiteral 0x55eedf75c650 <col:22> 'int' 0
              |       |-DeclStmt 0x55eedf75c748 <line:53:2, col:29>
              |       | `-VarDecl 0x55eedf75c6e0 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
              |       |-BinaryOperator 0x55eedf75c7b8 <line:54:2, col:28> 'int' '='
              |       | |-DeclRefExpr 0x55eedf75c760 <col:2> 'int' lvalue Var 0x55eedf75c6e0 '__VERIFIER_assert__cond' 'int'
              |       | `-ImplicitCastExpr 0x55eedf75c7a0 <col:28> 'int' <LValueToRValue>
              |       |   `-DeclRefExpr 0x55eedf75c780 <col:28> 'int' lvalue Var 0x55eedf75c590 '__tmp_1' 'int'
              |       `-IfStmt 0x55eedf75ca18 <line:55:2, line:64:2> has_else
              |         |-BinaryOperator 0x55eedf75c830 <line:55:6, col:33> 'int' '=='
              |         | |-ImplicitCastExpr 0x55eedf75c818 <col:6> 'int' <LValueToRValue>
              |         | | `-DeclRefExpr 0x55eedf75c7d8 <col:6> 'int' lvalue Var 0x55eedf75c6e0 '__VERIFIER_assert__cond' 'int'
              |         | `-IntegerLiteral 0x55eedf75c7f8 <col:33> 'int' 0
              |         |-CompoundStmt 0x55eedf75c930 <line:56:2, line:59:2>
              |         | |-CompoundStmt 0x55eedf75c8d0 <line:57:2, col:17>
              |         | | `-CallExpr 0x55eedf75c8b0 <col:3, col:15> 'void'
              |         | |   `-ImplicitCastExpr 0x55eedf75c898 <col:3> 'void (*)()' <FunctionToPointerDecay>
              |         | |     `-DeclRefExpr 0x55eedf75c850 <col:3> 'void ()' Function 0x55eedf754888 'reach_error' 'void ()'
              |         | `-ReturnStmt 0x55eedf75c920 <line:58:2, col:9>
              |         |   `-ImplicitCastExpr 0x55eedf75c908 <col:9> 'int' <LValueToRValue>
              |         |     `-DeclRefExpr 0x55eedf75c8e8 <col:9> 'int' lvalue Var 0x55eedf754168 '__return_main' 'int'
              |         `-CompoundStmt 0x55eedf75c9f8 <line:61:2, line:64:2>
              |           |-BinaryOperator 0x55eedf75c990 <line:62:3, col:17> 'int' '='
              |           | |-DeclRefExpr 0x55eedf75c950 <col:3> 'int' lvalue Var 0x55eedf756bc8 '__return_65' 'int'
              |           | `-IntegerLiteral 0x55eedf75c970 <col:17> 'int' 0
              |           `-ReturnStmt 0x55eedf75c9e8 <line:63:2, col:9>
              |             `-ImplicitCastExpr 0x55eedf75c9d0 <col:9> 'int' <LValueToRValue>
              |               `-DeclRefExpr 0x55eedf75c9b0 <col:9> 'int' lvalue Var 0x55eedf756bc8 '__return_65' 'int'
              `-CompoundStmt 0x55eedf75cb48 <line:69:2, line:71:2>
                `-ReturnStmt 0x55eedf75cb38 <line:70:2, col:9>
                  `-ImplicitCastExpr 0x55eedf75cb20 <col:9> 'int' <LValueToRValue>
                    `-DeclRefExpr 0x55eedf75cb00 <col:9> 'int' lvalue Var 0x55eedf754168 '__return_main' 'int'
1 warning generated.
