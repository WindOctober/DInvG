./Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.v+cfa-reducer.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.v+cfa-reducer.c:3:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x5584c009cf48 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5584c009d7e0 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5584c009d4e0 '__int128'
|-TypedefDecl 0x5584c009d850 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5584c009d500 'unsigned __int128'
|-TypedefDecl 0x5584c009db58 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5584c009d930 'struct __NSConstantString_tag'
|   `-Record 0x5584c009d8a8 '__NSConstantString_tag'
|-TypedefDecl 0x5584c009dbf0 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5584c009dbb0 'char *'
|   `-BuiltinType 0x5584c009cfe0 'char'
|-TypedefDecl 0x5584c009dee8 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5584c009de90 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5584c009dcd0 'struct __va_list_tag'
|     `-Record 0x5584c009dc48 '__va_list_tag'
|-VarDecl 0x5584c00fd048 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loop-lit/gsv2008.c.i.v+cfa-reducer.c:1:1, col:5> col:5 used __return_main 'int'
|-FunctionDecl 0x5584c00fd1e8 <line:2:6> col:6 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x5584c00fd288 prev 0x5584c00fd1e8 <col:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5584c00fd608 <line:3:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x5584c00fd340 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x5584c00fd3c0 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x5584c00fd440 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x5584c00fd4c0 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x5584c00fd6c8 <col:99>
|-FunctionDecl 0x5584c00fd768 <line:4:1, col:91> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x5584c00fdaa8 <col:20, col:91>
|   `-CallExpr 0x5584c00fd9c0 <col:22, col:88> 'void'
|     |-ImplicitCastExpr 0x5584c00fd9a8 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x5584c00fd808 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x5584c00fd608 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x5584c00fda18 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5584c00fda00 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5584c00fd868 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x5584c00fda48 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x5584c00fda30 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x5584c00fd8c8 <col:41> 'char [28]' lvalue "gsv2008.c.i.v+cfa-reducer.c"
|     |-ImplicitCastExpr 0x5584c00fda60 <col:72> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x5584c00fd900 <col:72> 'int' 4
|     `-ImplicitCastExpr 0x5584c00fda90 <col:75> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x5584c00fda78 <col:75> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x5584c00fd958 <col:75> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x5584c00fdb58 prev 0x5584c00fd288 <line:5:1, col:16> col:6 used abort 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5584c00fdcd8 <line:6:1, line:8:1> line:6:6 assume_abort_if_not 'void (int)'
| |-ParmVarDecl 0x5584c00fdc10 <col:26, col:30> col:30 used cond 'int'
| `-CompoundStmt 0x5584c00fde80 <col:36, line:8:1>
|   `-IfStmt 0x5584c00fde68 <line:7:3, col:22>
|     |-UnaryOperator 0x5584c00fddb8 <col:6, col:7> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x5584c00fdda0 <col:7> 'int' <LValueToRValue>
|     |   `-DeclRefExpr 0x5584c00fdd80 <col:7> 'int' lvalue ParmVar 0x5584c00fdc10 'cond' 'int'
|     `-CompoundStmt 0x5584c00fde50 <col:13, col:22>
|       `-CallExpr 0x5584c00fde30 <col:14, col:20> 'void'
|         `-ImplicitCastExpr 0x5584c00fde18 <col:14> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|           `-DeclRefExpr 0x5584c00fddd0 <col:14> 'void (void) __attribute__((noreturn))' Function 0x5584c00fdb58 'abort' 'void (void) __attribute__((noreturn))'
|-FunctionDecl 0x5584c00fdf40 <line:9:1, col:32> col:6 __VERIFIER_assert 'void (int)'
| `-ParmVarDecl 0x5584c00fdeb0 <col:24, col:28> col:28 cond 'int'
|-FunctionDecl 0x5584c00ff8a8 <line:10:1, col:27> col:5 used __VERIFIER_nondet_int 'int ()'
|-FunctionDecl 0x5584c00ff970 <line:11:1, col:10> col:5 main 'int ()'
|-VarDecl 0x5584c00ffa28 <line:12:1, col:5> col:5 used __return_65 'int'
`-FunctionDecl 0x5584c00ffab8 prev 0x5584c00ff970 <line:13:2, line:60:2> line:13:6 main 'int ()'
  `-CompoundStmt 0x5584c0101710 <line:14:2, line:60:2>
    |-DeclStmt 0x5584c00ffbd8 <line:15:2, col:13>
    | `-VarDecl 0x5584c00ffb70 <col:2, col:6> col:6 used main__x 'int'
    |-DeclStmt 0x5584c00ffc70 <line:16:2, col:13>
    | `-VarDecl 0x5584c00ffc08 <col:2, col:6> col:6 used main__y 'int'
    |-BinaryOperator 0x5584c00ffce0 <line:17:2, col:13> 'int' '='
    | |-DeclRefExpr 0x5584c00ffc88 <col:2> 'int' lvalue Var 0x5584c00ffb70 'main__x' 'int'
    | `-UnaryOperator 0x5584c00ffcc8 <col:12, col:13> 'int' prefix '-'
    |   `-IntegerLiteral 0x5584c00ffca8 <col:13> 'int' 50
    |-BinaryOperator 0x5584c00ffda0 <line:18:2, col:34> 'int' '='
    | |-DeclRefExpr 0x5584c00ffd00 <col:2> 'int' lvalue Var 0x5584c00ffc08 'main__y' 'int'
    | `-CallExpr 0x5584c00ffd80 <col:12, col:34> 'int'
    |   `-ImplicitCastExpr 0x5584c00ffd68 <col:12> 'int (*)()' <FunctionToPointerDecay>
    |     `-DeclRefExpr 0x5584c00ffd20 <col:12> 'int ()' Function 0x5584c00ff8a8 '__VERIFIER_nondet_int' 'int ()'
    `-IfStmt 0x5584c01016e8 <line:19:2, line:59:2> has_else
      |-UnaryOperator 0x5584c00ffe70 <line:19:6, col:23> 'int' prefix '!' cannot overflow
      | `-ParenExpr 0x5584c00ffe50 <col:7, col:23> 'int'
      |   `-BinaryOperator 0x5584c00ffe30 <col:8, col:16> 'int' '<'
      |     |-UnaryOperator 0x5584c00ffde0 <col:8, col:9> 'int' prefix '-'
      |     | `-IntegerLiteral 0x5584c00ffdc0 <col:9> 'int' 1000
      |     `-ImplicitCastExpr 0x5584c00ffe18 <col:16> 'int' <LValueToRValue>
      |       `-DeclRefExpr 0x5584c00ffdf8 <col:16> 'int' lvalue Var 0x5584c00ffc08 'main__y' 'int'
      |-CompoundStmt 0x5584c00ffed0 <line:20:2, line:22:2>
      | `-ReturnStmt 0x5584c00ffec0 <line:21:2, col:9>
      |   `-ImplicitCastExpr 0x5584c00ffea8 <col:9> 'int' <LValueToRValue>
      |     `-DeclRefExpr 0x5584c00ffe88 <col:9> 'int' lvalue Var 0x5584c00fd048 '__return_main' 'int'
      `-CompoundStmt 0x5584c01016d0 <line:24:2, line:59:2>
        `-IfStmt 0x5584c01016a8 <line:25:2, line:58:2> has_else
          |-UnaryOperator 0x5584c00fff80 <line:25:6, col:25> 'int' prefix '!' cannot overflow
          | `-ParenExpr 0x5584c00fff60 <col:7, col:25> 'int'
          |   `-BinaryOperator 0x5584c00fff40 <col:8, col:18> 'int' '<'
          |     |-ImplicitCastExpr 0x5584c00fff28 <col:8> 'int' <LValueToRValue>
          |     | `-DeclRefExpr 0x5584c00ffee8 <col:8> 'int' lvalue Var 0x5584c00ffc08 'main__y' 'int'
          |     `-IntegerLiteral 0x5584c00fff08 <col:18> 'int' 1000000
          |-CompoundStmt 0x5584c00fffe0 <line:26:2, line:28:2>
          | `-ReturnStmt 0x5584c00fffd0 <line:27:2, col:9>
          |   `-ImplicitCastExpr 0x5584c00fffb8 <col:9> 'int' <LValueToRValue>
          |     `-DeclRefExpr 0x5584c00fff98 <col:9> 'int' lvalue Var 0x5584c00fd048 '__return_main' 'int'
          `-CompoundStmt 0x5584c0101688 <line:30:2, line:58:2>
            |-LabelStmt 0x5584c0100050 <line:31:2, col:11> 'label_50'
            | `-NullStmt 0x5584c00ffff8 <col:11>
            `-IfStmt 0x5584c0101660 <line:32:2, line:57:2> has_else
              |-BinaryOperator 0x5584c01000c0 <line:32:6, col:16> 'int' '<'
              | |-ImplicitCastExpr 0x5584c01000a8 <col:6> 'int' <LValueToRValue>
              | | `-DeclRefExpr 0x5584c0100068 <col:6> 'int' lvalue Var 0x5584c00ffb70 'main__x' 'int'
              | `-IntegerLiteral 0x5584c0100088 <col:16> 'int' 0
              |-CompoundStmt 0x5584c0100350 <line:33:2, line:38:2>
              | |-BinaryOperator 0x5584c0100190 <line:34:2, col:22> 'int' '='
              | | |-DeclRefExpr 0x5584c01000e0 <col:2> 'int' lvalue Var 0x5584c00ffb70 'main__x' 'int'
              | | `-BinaryOperator 0x5584c0100170 <col:12, col:22> 'int' '+'
              | |   |-ImplicitCastExpr 0x5584c0100140 <col:12> 'int' <LValueToRValue>
              | |   | `-DeclRefExpr 0x5584c0100100 <col:12> 'int' lvalue Var 0x5584c00ffb70 'main__x' 'int'
              | |   `-ImplicitCastExpr 0x5584c0100158 <col:22> 'int' <LValueToRValue>
              | |     `-DeclRefExpr 0x5584c0100120 <col:22> 'int' lvalue Var 0x5584c00ffc08 'main__y' 'int'
              | |-DeclStmt 0x5584c0100268 <line:35:2, col:40>
              | | `-VarDecl 0x5584c01001c8 <col:2, col:33> col:6 main____CPAchecker_TMP_0 'int' cinit
              | |   `-ImplicitCastExpr 0x5584c0100250 <col:33> 'int' <LValueToRValue>
              | |     `-DeclRefExpr 0x5584c0100230 <col:33> 'int' lvalue Var 0x5584c00ffc08 'main__y' 'int'
              | |-BinaryOperator 0x5584c0100318 <line:36:2, col:22> 'int' '='
              | | |-DeclRefExpr 0x5584c0100280 <col:2> 'int' lvalue Var 0x5584c00ffc08 'main__y' 'int'
              | | `-BinaryOperator 0x5584c01002f8 <col:12, col:22> 'int' '+'
              | |   |-ImplicitCastExpr 0x5584c01002e0 <col:12> 'int' <LValueToRValue>
              | |   | `-DeclRefExpr 0x5584c01002a0 <col:12> 'int' lvalue Var 0x5584c00ffc08 'main__y' 'int'
              | |   `-IntegerLiteral 0x5584c01002c0 <col:22> 'int' 1
              | `-GotoStmt 0x5584c0100338 <line:37:2, col:7> 'label_50' 0x5584c0100000
              `-CompoundStmt 0x5584c0101648 <line:40:2, line:57:2>
                `-CompoundStmt 0x5584c0101610 <line:41:2, line:56:2>
                  |-DeclStmt 0x5584c0100400 <line:42:2, col:13>
                  | `-VarDecl 0x5584c0100398 <col:2, col:6> col:6 used __tmp_1 'int'
                  |-BinaryOperator 0x5584c01004b0 <line:43:2, col:22> 'int' '='
                  | |-DeclRefExpr 0x5584c0100418 <col:2> 'int' lvalue Var 0x5584c0100398 '__tmp_1' 'int'
                  | `-BinaryOperator 0x5584c0100490 <col:12, col:22> 'int' '>'
                  |   |-ImplicitCastExpr 0x5584c0100478 <col:12> 'int' <LValueToRValue>
                  |   | `-DeclRefExpr 0x5584c0100438 <col:12> 'int' lvalue Var 0x5584c00ffc08 'main__y' 'int'
                  |   `-IntegerLiteral 0x5584c0100458 <col:22> 'int' 0
                  |-DeclStmt 0x5584c0100550 <line:44:2, col:29>
                  | `-VarDecl 0x5584c01004e8 <col:2, col:6> col:6 used __VERIFIER_assert__cond 'int'
                  |-BinaryOperator 0x5584c01005c0 <line:45:2, col:28> 'int' '='
                  | |-DeclRefExpr 0x5584c0100568 <col:2> 'int' lvalue Var 0x5584c01004e8 '__VERIFIER_assert__cond' 'int'
                  | `-ImplicitCastExpr 0x5584c01005a8 <col:28> 'int' <LValueToRValue>
                  |   `-DeclRefExpr 0x5584c0100588 <col:28> 'int' lvalue Var 0x5584c0100398 '__tmp_1' 'int'
                  `-IfStmt 0x5584c0100828 <line:46:2, line:55:2> has_else
                    |-BinaryOperator 0x5584c0100638 <line:46:6, col:33> 'int' '=='
                    | |-ImplicitCastExpr 0x5584c0100620 <col:6> 'int' <LValueToRValue>
                    | | `-DeclRefExpr 0x5584c01005e0 <col:6> 'int' lvalue Var 0x5584c01004e8 '__VERIFIER_assert__cond' 'int'
                    | `-IntegerLiteral 0x5584c0100600 <col:33> 'int' 0
                    |-CompoundStmt 0x5584c0100740 <line:47:2, line:50:2>
                    | |-CompoundStmt 0x5584c01006e0 <line:48:2, col:17>
                    | | `-CallExpr 0x5584c01006c0 <col:3, col:15> 'void'
                    | |   `-ImplicitCastExpr 0x5584c01006a8 <col:3> 'void (*)()' <FunctionToPointerDecay>
                    | |     `-DeclRefExpr 0x5584c0100658 <col:3> 'void ()' Function 0x5584c00fd768 'reach_error' 'void ()'
                    | `-ReturnStmt 0x5584c0100730 <line:49:2, col:9>
                    |   `-ImplicitCastExpr 0x5584c0100718 <col:9> 'int' <LValueToRValue>
                    |     `-DeclRefExpr 0x5584c01006f8 <col:9> 'int' lvalue Var 0x5584c00fd048 '__return_main' 'int'
                    `-CompoundStmt 0x5584c0100808 <line:52:2, line:55:2>
                      |-BinaryOperator 0x5584c01007a0 <line:53:3, col:17> 'int' '='
                      | |-DeclRefExpr 0x5584c0100760 <col:3> 'int' lvalue Var 0x5584c00ffa28 '__return_65' 'int'
                      | `-IntegerLiteral 0x5584c0100780 <col:17> 'int' 0
                      `-ReturnStmt 0x5584c01007f8 <line:54:2, col:9>
                        `-ImplicitCastExpr 0x5584c01007e0 <col:9> 'int' <LValueToRValue>
                          `-DeclRefExpr 0x5584c01007c0 <col:9> 'int' lvalue Var 0x5584c00ffa28 '__return_65' 'int'
1 warning generated.
