./Benchmark/PLDI/SVComp/loops-crafted-1/Mono5_1.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono5_1.c:2:113: warning: unknown attribute '__leaf__' ignored [-Wunknown-attributes]
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
                                                                                                                ^
TranslationUnitDecl 0x556732f30e98 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x556732f31730 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x556732f31430 '__int128'
|-TypedefDecl 0x556732f317a0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x556732f31450 'unsigned __int128'
|-TypedefDecl 0x556732f31aa8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x556732f31880 'struct __NSConstantString_tag'
|   `-Record 0x556732f317f8 '__NSConstantString_tag'
|-TypedefDecl 0x556732f31b40 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x556732f31b00 'char *'
|   `-BuiltinType 0x556732f30f30 'char'
|-TypedefDecl 0x556732f31e38 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x556732f31de0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x556732f31c20 'struct __va_list_tag'
|     `-Record 0x556732f31b98 '__va_list_tag'
|-FunctionDecl 0x556732f90e28 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops-crafted-1/Mono5_1.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556732f90ec8 prev 0x556732f90e28 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x556732f91248 <line:2:1, col:153> col:13 used __assert_fail 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' extern
| |-ParmVarDecl 0x556732f90f80 <col:27, col:38> col:39 'const char *'
| |-ParmVarDecl 0x556732f91000 <col:41, col:52> col:53 'const char *'
| |-ParmVarDecl 0x556732f91080 <col:55, col:64> col:67 'unsigned int'
| |-ParmVarDecl 0x556732f91100 <col:69, col:80> col:81 'const char *'
| `-NoThrowAttr 0x556732f91308 <col:99>
|-FunctionDecl 0x556732f913f8 <line:3:1, col:73> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x556732f91728 <col:20, col:73>
|   `-CallExpr 0x556732f91640 <col:22, col:70> 'void'
|     |-ImplicitCastExpr 0x556732f91628 <col:22> 'void (*)(const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x556732f91498 <col:22> 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))' Function 0x556732f91248 '__assert_fail' 'void (const char *, const char *, unsigned int, const char *) __attribute__((noreturn))'
|     |-ImplicitCastExpr 0x556732f91698 <col:36> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x556732f91680 <col:36> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x556732f914f8 <col:36> 'char [2]' lvalue "0"
|     |-ImplicitCastExpr 0x556732f916c8 <col:41> 'const char *' <NoOp>
|     | `-ImplicitCastExpr 0x556732f916b0 <col:41> 'char *' <ArrayToPointerDecay>
|     |   `-StringLiteral 0x556732f91558 <col:41> 'char [10]' lvalue "Mono5_1.c"
|     |-ImplicitCastExpr 0x556732f916e0 <col:54> 'unsigned int' <IntegralCast>
|     | `-IntegerLiteral 0x556732f91580 <col:54> 'int' 3
|     `-ImplicitCastExpr 0x556732f91710 <col:57> 'const char *' <NoOp>
|       `-ImplicitCastExpr 0x556732f916f8 <col:57> 'char *' <ArrayToPointerDecay>
|         `-StringLiteral 0x556732f915d8 <col:57> 'char [12]' lvalue "reach_error"
|-FunctionDecl 0x556732f91818 <line:4:1, col:84> col:6 used __VERIFIER_assert 'void (int)'
| |-ParmVarDecl 0x556732f91758 <col:24, col:28> col:28 used cond 'int'
| `-CompoundStmt 0x556732f91ae8 <col:34, col:84>
|   `-IfStmt 0x556732f91ad0 <col:36, col:82>
|     |-UnaryOperator 0x556732f91918 <col:39, col:45> 'int' prefix '!' cannot overflow
|     | `-ImplicitCastExpr 0x556732f91900 <col:40, col:45> 'int' <LValueToRValue>
|     |   `-ParenExpr 0x556732f918e0 <col:40, col:45> 'int' lvalue
|     |     `-DeclRefExpr 0x556732f918c0 <col:41> 'int' lvalue ParmVar 0x556732f91758 'cond' 'int'
|     `-CompoundStmt 0x556732f91ab8 <col:48, col:82>
|       `-LabelStmt 0x556732f91aa0 <col:50, col:80> 'ERROR'
|         `-CompoundStmt 0x556732f91a30 <col:57, col:80>
|           |-CallExpr 0x556732f91990 <col:58, col:70> 'void'
|           | `-ImplicitCastExpr 0x556732f91978 <col:58> 'void (*)()' <FunctionToPointerDecay>
|           |   `-DeclRefExpr 0x556732f91930 <col:58> 'void ()' Function 0x556732f913f8 'reach_error' 'void ()'
|           `-CallExpr 0x556732f91a10 <col:72, col:78> 'void'
|             `-ImplicitCastExpr 0x556732f919f8 <col:72> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|               `-DeclRefExpr 0x556732f919b0 <col:72> 'void (void) __attribute__((noreturn))' Function 0x556732f90ec8 'abort' 'void (void) __attribute__((noreturn))'
`-FunctionDecl 0x556732f91bd0 <line:5:1, line:15:1> line:5:5 main 'int (void)'
  `-CompoundStmt 0x556732f93c18 <col:16, line:15:1>
    |-DeclStmt 0x556732f93768 <line:6:1, col:19>
    | `-VarDecl 0x556732f91cb0 <col:1, col:18> col:14 used x 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x556732f93750 <col:18> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x556732f93730 <col:18> 'int' 0
    |-DeclStmt 0x556732f93838 <line:7:1, col:26>
    | `-VarDecl 0x556732f93798 <col:1, col:18> col:14 used y 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x556732f93820 <col:18> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x556732f93800 <col:18> 'int' 10000000
    |-DeclStmt 0x556732f93908 <line:8:1, col:23>
    | `-VarDecl 0x556732f93868 <col:1, col:16> col:14 used z 'unsigned int' cinit
    |   `-ImplicitCastExpr 0x556732f938f0 <col:16> 'unsigned int' <IntegralCast>
    |     `-IntegerLiteral 0x556732f938d0 <col:16> 'int' 5000000
    |-WhileStmt 0x556732f93ae8 <line:9:2, line:13:2>
    | |-BinaryOperator 0x556732f93990 <line:9:8, col:10> 'int' '<'
    | | |-ImplicitCastExpr 0x556732f93960 <col:8> 'unsigned int' <LValueToRValue>
    | | | `-DeclRefExpr 0x556732f93920 <col:8> 'unsigned int' lvalue Var 0x556732f91cb0 'x' 'unsigned int'
    | | `-ImplicitCastExpr 0x556732f93978 <col:10> 'unsigned int' <LValueToRValue>
    | |   `-DeclRefExpr 0x556732f93940 <col:10> 'unsigned int' lvalue Var 0x556732f93798 'y' 'unsigned int'
    | `-CompoundStmt 0x556732f93ac8 <col:12, line:13:2>
    |   |-IfStmt 0x556732f93a78 <line:10:3, line:11:5>
    |   | |-BinaryOperator 0x556732f93a20 <line:10:6, col:9> 'int' '>='
    |   | | |-ImplicitCastExpr 0x556732f939f0 <col:6> 'unsigned int' <LValueToRValue>
    |   | | | `-DeclRefExpr 0x556732f939b0 <col:6> 'unsigned int' lvalue Var 0x556732f91cb0 'x' 'unsigned int'
    |   | | `-ImplicitCastExpr 0x556732f93a08 <col:9> 'unsigned int' <IntegralCast>
    |   | |   `-IntegerLiteral 0x556732f939d0 <col:9> 'int' 5000000
    |   | `-UnaryOperator 0x556732f93a60 <line:11:4, col:5> 'unsigned int' postfix '--'
    |   |   `-DeclRefExpr 0x556732f93a40 <col:4> 'unsigned int' lvalue Var 0x556732f93868 'z' 'unsigned int'
    |   `-UnaryOperator 0x556732f93ab0 <line:12:3, col:4> 'unsigned int' postfix '++'
    |     `-DeclRefExpr 0x556732f93a90 <col:3> 'unsigned int' lvalue Var 0x556732f91cb0 'x' 'unsigned int'
    `-CallExpr 0x556732f93bf0 <line:14:3, col:25> 'void'
      |-ImplicitCastExpr 0x556732f93bd8 <col:3> 'void (*)(int)' <FunctionToPointerDecay>
      | `-DeclRefExpr 0x556732f93b00 <col:3> 'void (int)' Function 0x556732f91818 '__VERIFIER_assert' 'void (int)'
      `-BinaryOperator 0x556732f93b90 <col:21, col:24> 'int' '!='
        |-ImplicitCastExpr 0x556732f93b60 <col:21> 'unsigned int' <LValueToRValue>
        | `-DeclRefExpr 0x556732f93b20 <col:21> 'unsigned int' lvalue Var 0x556732f93868 'z' 'unsigned int'
        `-ImplicitCastExpr 0x556732f93b78 <col:24> 'unsigned int' <IntegralCast>
          `-IntegerLiteral 0x556732f93b40 <col:24> 'int' 0
1 warning generated.
