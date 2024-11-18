./Benchmark/PLDI/SVComp/loop-lit/jm2006.c.i.v+cfa-reducer.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/jm2006.c.i.v+cfa-reducer.c:3:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x55d55abdbf48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x55d55abdc7e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x55d55abdc4e0 '__int128'
|-TypedefDecl 0x55d55abdc850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x55d55abdc500 'unsigned __int128'
|-TypedefDecl 0x55d55abdcb58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x55d55abdc930 'struct __NSConstantString_tag'
|   `-Record 0x55d55abdc8a8 '__NSConstantString_tag'
|-TypedefDecl 0x55d55abdcbf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x55d55abdcbb0 'char *'
|   `-BuiltinType 0x55d55abdbfe0 'char'
|-TypedefDecl 0x55d55abdcee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x55d55abdce90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x55d55abdccd0 'struct __va_list_tag'
|     `-Record 0x55d55abdcc48 '__va_list_tag'
|-VarDecl 0x55d55ac3c0e8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/jm2006.c.i.v+cfa-reducer.c:1:1, col:5> col:5 used __return_main 'int'
|-FunctionDecl 0x55d55ac3c288 <line:2:6> col:6 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x55d55ac3c328 prev 0x55d55ac3c288 <col:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55d55ac3c6a8 <line:3:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x55d55ac3c3e0 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x55d55ac3c460 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x55d55ac3c4e0 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x55d55ac3c560 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x55d55ac3c768 <col:99>
|-FunctionDecl 0x55d55ac3c808 <line:4:1, col:90> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x55d55ac3cb48 <col:20, col:90>
|   `-CallExpr 0x55d55ac3ca60 <col:22, col:87> 'void'
|     |-ImplicitCastExpr 0x55d55ac3ca48 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x55d55ac3c8a8 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x55d55ac3c6a8 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x55d55ac3cab8 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d55ac3caa0 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d55ac3c908 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x55d55ac3cae8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x55d55ac3cad0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x55d55ac3c968 <col:41> 'char [27]' lvalue "jm2006.c.i.v+cfa-reducer.c"
|     |-ImplicitCastExpr 0x55d55ac3cb00 <col:71> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x55d55ac3c9a0 <col:71> 'int' 4
|     `-ImplicitCastExpr 0x55d55ac3cb30 <col:74> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x55d55ac3cb18 <col:74> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x55d55ac3c9f8 <col:74> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x55d55ac3cbf8 prev 0x55d55ac3c328 <line:5:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55d55ac3cd78 <line:6:1, line:8:1> line:6:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x55d55ac3ccb0 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x55d55ac3cf20 <col:36, line:8:1>
|   `-IfStmt 0x55d55ac3cf08 <line:7:3, col:22>
|     |-UnaryOperator 0x55d55ac3ce58 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x55d55ac3ce40 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x55d55ac3ce20 <col:7> 'int' lvalue ParmVar 0x55d55ac3ccb0 'cond' 'int'
|     `-CompoundStmt 0x55d55ac3cef0 <col:13, col:22>
|       `-CallExpr 0x55d55ac3ced0 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x55d55ac3ceb8 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x55d55ac3ce70 <col:14> 'void (void) __attribute__((noreturn))' Function 0x55d55ac3cbf8 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x55d55ac3cfe0 <line:9:1, col:32> col:6 __VERIFIER_assert 'void (int)'
| `-ParmVarDecl 0x55d55ac3cf50 <col:24, col:28> col:28 cond 'int'
|-FunctionDecl 0x55d55ac3e948 <line:10:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x55d55ac3ea10 <line:11:1, col:10> col:5 main 'int ()'
|-VarDecl 0x55d55ac3eac8 <line:12:1, col:5> col:5 used __return_72 'int'
`-FunctionDecl 0x55d55ac3eb58 prev 0x55d55ac3ea10 <line:13:2, line:70:2> line:13:6 main 'int ()'
  `-CompoundStmt 0x55d55ac40990 <line:14:2, line:70:2>
    |-DeclStmt 0x55d55ac3ec78 <line:15:2, col:13>
    | `-VarDecl 0x55d55ac3ec10 <col:2, col:6> col:6 used main__i 'int'
    |-DeclStmt 0x55d55ac3ed10 <line:16:2, col:13>
    | `-VarDecl 0x55d55ac3eca8 <col:2, col:6> col:6 used main__j 'int'
    |-BinaryOperator 0x55d55ac3edd0 <line:17:2, col:34> 'int' '='
    | |-DeclRefExpr 0x55d55ac3ed28 <col:2> 'int' lvalue Var 0x55d55ac3ec10 'main__i' 'int'
    | `-CallExpr 0x55d55ac3edb0 <col:12, col:34> 'int'
    |   `-ImplicitCastExpr 0x55d55ac3ed98 <col:12> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55d55ac3ed48 <col:12> 'int ()' Function 0x55d55ac3e948 '__VERIFIER_nondet_int' 'int ()'
    |-BinaryOperator 0x55d55ac3ee68 <line:18:2, col:34> 'int' '='
    | |-DeclRefExpr 0x55d55ac3edf0 <col:2> 'int' lvalue Var 0x55d55ac3eca8 'main__j' 'int'
    | `-CallExpr 0x55d55ac3ee48 <col:12, col:34> 'int'
    |   `-ImplicitCastExpr 0x55d55ac3ee30 <col:12> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x55d55ac3ee10 <col:12> 'int ()' Function 0x55d55ac3e948 '__VERIFIER_nondet_int' 'int ()'
    `-IfStmt 0x55d55ac40968 <line:19:2, line:69:2> has_else
      |-UnaryOperator 0x55d55ac3ef20 <line:19:6, col:20> 'int' prefix '!' cannot overflow
      | `-ParenExpr 0x55d55ac3ef00 <col:7, col:20> 'int'
      |   `-BinaryOperator 0x55d55ac3eee0 <col:8, col:19> 'int' '>='
      |     |-ImplicitCastExpr 0x55d55ac3eec8 <col:8> 'int' <LValueToRValue>
      |     | `-DeclRefExpr 0x55d55ac3ee88 <col:8> 'int' lvalue Var 0x55d55ac3ec10 'main__i' 'int'
      |     `-IntegerLiteral 0x55d55ac3eea8 <col:19> 'int' 0
      |-CompoundStmt 0x55d55ac3ef80 <line:20:2, line:22:2>
      | `-ReturnStmt 0x55d55ac3ef70 <line:21:2, col:9>
      |   `-ImplicitCastExpr 0x55d55ac3ef58 <col:9> 'int' <LValueToRValue>
      |     `-DeclRefExpr 0x55d55ac3ef38 <col:9> 'int' lvalue Var 0x55d55ac3c0e8 '__return_main' 'int'
      `-CompoundStmt 0x55d55ac40950 <line:24:2, line:69:2>
        `-IfStmt 0x55d55ac40928 <line:25:2, line:68:2> has_else
          |-UnaryOperator 0x55d55ac3f030 <line:25:6, col:20> 'int' prefix '!' cannot overflow
          | `-ParenExpr 0x55d55ac3f010 <col:7, col:20> 'int'
          |   `-BinaryOperator 0x55d55ac3eff0 <col:8, col:19> 'int' '>='
          |     |-ImplicitCastExpr 0x55d55ac3efd8 <col:8> 'int' <LValueToRValue>
          |     | `-DeclRefExpr 0x55d55ac3ef98 <col:8> 'int' lvalue Var 0x55d55ac3eca8 'main__j' 'int'
          |     `-IntegerLiteral 0x55d55ac3efb8 <col:19> 'int' 0
          |-CompoundStmt 0x55d55ac3f090 <line:26:2, line:28:2>
          | `-ReturnStmt 0x55d55ac3f080 <line:27:2, col:9>
          |   `-ImplicitCastExpr 0x55d55ac3f068 <col:9> 'int' <LValueToRValue>
          |     `-DeclRefExpr 0x55d55ac3f048 <col:9> 'int' lvalue Var 0x55d55ac3c0e8 '__return_main' 'int'
          `-CompoundStmt 0x55d55ac408f8 <line:30:2, line:68:2>
            |-DeclStmt 0x55d55ac3f160 <line:31:2, col:23>
            | `-VarDecl 0x55d55ac3f0c0 <col:2, col:16> col:6 used main__x 'int' cinit
            |   `-ImplicitCastExpr 0x55d55ac3f148 <col:16> 'int' <LValueToRValue>
            |     `-DeclRefExpr 0x55d55ac3f128 <col:16> 'int' lvalue Var 0x55d55ac3ec10 'main__i' 'int'
            |-DeclStmt 0x55d55ac3f230 <line:32:2, col:23>
            | `-VarDecl 0x55d55ac3f190 <col:2, col:16> col:6 used main__y 'int' cinit
            |   `-ImplicitCastExpr 0x55d55ac3f218 <col:16> 'int' <LValueToRValue>
            |     `-DeclRefExpr 0x55d55ac3f1f8 <col:16> 'int' lvalue Var 0x55d55ac3eca8 'main__j' 'int'
            |-LabelStmt 0x55d55ac3f2a0 <line:33:2, col:11> 'label_53'
            | `-NullStmt 0x55d55ac3f248 <col:11>
            `-IfStmt 0x55d55ac408d0 <line:34:2, line:67:2> has_else
              |-BinaryOperator 0x55d55ac3f310 <line:34:6, col:17> 'int' '!='
              | |-ImplicitCastExpr 0x55d55ac3f2f8 <col:6> 'int' <LValueToRValue>
              | | `-DeclRefExpr 0x55d55ac3f2b8 <col:6> 'int' lvalue Var 0x55d55ac3f0c0 'main__x' 'int'
              | `-IntegerLiteral 0x55d55ac3f2d8 <col:17> 'int' 0
              |-CompoundStmt 0x55d55ac3f658 <line:35:2, line:41:2>
              | |-DeclStmt 0x55d55ac3f3e8 <line:36:2, col:40>
              | | `-VarDecl 0x55d55ac3f348 <col:2, col:33> col:6 main____CPAchecker_TMP_0 'int' cinit
              | |   `-ImplicitCastExpr 0x55d55ac3f3d0 <col:33> 'int' <LValueToRValue>
              | |     `-DeclRefExpr 0x55d55ac3f3b0 <col:33> 'int' lvalue Var 0x55d55ac3f0c0 'main__x' 'int'
              | |-BinaryOperator 0x55d55ac3f498 <line:37:2, col:22> 'int' '='
              | | |-DeclRefExpr 0x55d55ac3f400 <col:2> 'int' lvalue Var 0x55d55ac3f0c0 'main__x' 'int'
              | | `-BinaryOperator 0x55d55ac3f478 <col:12, col:22> 'int' '-'
              | |   |-ImplicitCastExpr 0x55d55ac3f460 <col:12> 'int' <LValueToRValue>
              | |   | `-DeclRefExpr 0x55d55ac3f420 <col:12> 'int' lvalue Var 0x55d55ac3f0c0 'main__x' 'int'
              | |   `-IntegerLiteral 0x55d55ac3f440 <col:22> 'int' 1
              | |-DeclStmt 0x55d55ac3f570 <line:38:2, col:40>
              | | `-VarDecl 0x55d55ac3f4d0 <col:2, col:33> col:6 main____CPAchecker_TMP_1 'int' cinit
              | |   `-ImplicitCastExpr 0x55d55ac3f558 <col:33> 'int' <LValueToRValue>
              | |     `-DeclRefExpr 0x55d55ac3f538 <col:33> 'int' lvalue Var 0x55d55ac3f190 'main__y' 'int'
              | |-BinaryOperator 0x55d55ac3f620 <line:39:2, col:22> 'int' '='
              | | |-DeclRefExpr 0x55d55ac3f588 <col:2> 'int' lvalue Var 0x55d55ac3f190 'main__y' 'int'
              | | `-BinaryOperator 0x55d55ac3f600 <col:12, col:22> 'int' '-'
              | |   |-ImplicitCastExpr 0x55d55ac3f5e8 <col:12> 'int' <LValueToRValue>
              | |   | `-DeclRefExpr 0x55d55ac3f5a8 <col:12> 'int' lvalue Var 0x55d55ac3f190 'main__y' 'int'
              | |   `-IntegerLiteral 0x55d55ac3f5c8 <col:22> 'int' 1
              | `-GotoStmt 0x55d55ac3f640 <line:40:2, col:7> 'label_53' 0x55d55ac3f250
              `-CompoundStmt 0x55d55ac408b8 <line:43:2, line:67:2>
                `-IfStmt 0x55d55ac40890 <line:44:2, line:66:2> has_else
                  |-BinaryOperator 0x55d55ac3f700 <line:44:6, col:17> 'int' '=='
                  | |-ImplicitCastExpr 0x55d55ac3f6d0 <col:6> 'int' <LValueToRValue>
                  | | `-DeclRefExpr 0x55d55ac3f690 <col:6> 'int' lvalue Var 0x55d55ac3ec10 'main__i' 'int'
                  | `-ImplicitCastExpr 0x55d55ac3f6e8 <col:17> 'int' <LValueToRValue>
                  |   `-DeclRefExpr 0x55d55ac3f6b0 <col:17> 'int' lvalue Var 0x55d55ac3eca8 'main__j' 'int'
                  |-CompoundStmt 0x55d55ac40818 <line:45:2, line:62:2>
                  | `-CompoundStmt 0x55d55ac407e0 <line:46:2, line:61:2>
                  |   |-DeclStmt 0x55d55ac3f7a0 <line:47:2, col:13>
                  |   | `-VarDecl 0x55d55ac3f738 <col:2, col:6> col:6 used __tmp_1 'int'
                  |   |-BinaryOperator 0x55d55ac3f850 <line:48:2, col:23> 'int' '='
                  |   | |-DeclRefExpr 0x55d55ac3f7b8 <col:2> 'int' lvalue Var 0x55d55ac3f738 '__tmp_1' 'int'
                  |   | `-BinaryOperator 0x55d55ac3f830 <col:12, col:23> 'int' '=='
                  |   |   |-ImplicitCastExpr 0x55d55ac3f818 <col:12> 'int' <LValueToRValue>
                  |   |   | `-DeclRefExpr 0x55d55ac3f7d8 <col:12> 'int' lvalue Var 0x55d55ac3f190 'main__y' 'int'
                  |   |   `-IntegerLiteral 0x55d55ac3f7f8 <col:23> 'int' 0
                  |   |-DeclStmt 0x55d55ac3f8f0 <line:49:2, col:29>
                  |   | `-VarDecl 0x55d55ac3f888 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
                  |   |-BinaryOperator 0x55d55ac40558 <line:50:2, col:28> 'int' '='
                  |   | |-DeclRefExpr 0x55d55ac40500 <col:2> 'int' lvalue Var 0x55d55ac3f888 '__VERIFIER_assert__cond' 'int'
                  |   | `-ImplicitCastExpr 0x55d55ac40540 <col:28> 'int' <LValueToRValue>
                  |   |   `-DeclRefExpr 0x55d55ac40520 <col:28> 'int' lvalue Var 0x55d55ac3f738 '__tmp_1' 'int'
                  |   `-IfStmt 0x55d55ac407b8 <line:51:2, line:60:2> has_else
                  |     |-BinaryOperator 0x55d55ac405d0 <line:51:6, col:33> 'int' '=='
                  |     | |-ImplicitCastExpr 0x55d55ac405b8 <col:6> 'int' <LValueToRValue>
                  |     | | `-DeclRefExpr 0x55d55ac40578 <col:6> 'int' lvalue Var 0x55d55ac3f888 '__VERIFIER_assert__cond' 'int'
                  |     | `-IntegerLiteral 0x55d55ac40598 <col:33> 'int' 0
                  |     |-CompoundStmt 0x55d55ac406d0 <line:52:2, line:55:2>
                  |     | |-CompoundStmt 0x55d55ac40670 <line:53:2, col:17>
                  |     | | `-CallExpr 0x55d55ac40650 <col:3, col:15> 'void'
                  |     | |   `-ImplicitCastExpr 0x55d55ac40638 <col:3> 'void (*)()' <FunctionToPointerDecay>
                  |     | |     `-DeclRefExpr 0x55d55ac405f0 <col:3> 'void ()' Function 0x55d55ac3c808 'reach_error' 'void ()'
                  |     | `-ReturnStmt 0x55d55ac406c0 <line:54:2, col:9>
                  |     |   `-ImplicitCastExpr 0x55d55ac406a8 <col:9> 'int' <LValueToRValue>
                  |     |     `-DeclRefExpr 0x55d55ac40688 <col:9> 'int' lvalue Var 0x55d55ac3c0e8 '__return_main' 'int'
                  |     `-CompoundStmt 0x55d55ac40798 <line:57:2, line:60:2>
                  |       |-BinaryOperator 0x55d55ac40730 <line:58:3, col:17> 'int' '='
                  |       | |-DeclRefExpr 0x55d55ac406f0 <col:3> 'int' lvalue Var 0x55d55ac3eac8 '__return_72' 'int'
                  |       | `-IntegerLiteral 0x55d55ac40710 <col:17> 'int' 0
                  |       `-ReturnStmt 0x55d55ac40788 <line:59:2, col:9>
                  |         `-ImplicitCastExpr 0x55d55ac40770 <col:9> 'int' <LValueToRValue>
                  |           `-DeclRefExpr 0x55d55ac40750 <col:9> 'int' lvalue Var 0x55d55ac3eac8 '__return_72' 'int'
                  `-CompoundStmt 0x55d55ac40878 <line:64:2, line:66:2>
                    `-ReturnStmt 0x55d55ac40868 <line:65:2, col:9>
                      `-ImplicitCastExpr 0x55d55ac40850 <col:9> 'int' <LValueToRValue>
                        `-DeclRefExpr 0x55d55ac40830 <col:9> 'int' lvalue Var 0x55d55ac3c0e8 '__return_main' 'int'
1 warning generated.
