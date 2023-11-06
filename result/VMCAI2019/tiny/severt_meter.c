./Benchmark/PLDI/VMCAI2019/tiny/severt_meter.c
[info] Using default compilation options.
TranslationUnitDecl 0x5615f4106dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x5615f4107660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x5615f4107360 '__int128'
|-TypedefDecl 0x5615f41076d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x5615f4107380 'unsigned __int128'
|-TypedefDecl 0x5615f41079d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x5615f41077b0 'struct __NSConstantString_tag'
|   `-Record 0x5615f4107728 '__NSConstantString_tag'
|-TypedefDecl 0x5615f4107a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x5615f4107a30 'char *'
|   `-BuiltinType 0x5615f4106e60 'char'
|-TypedefDecl 0x5615f4107d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x5615f4107d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x5615f4107b50 'struct __va_list_tag'
|     `-Record 0x5615f4107ac8 '__va_list_tag'
|-FunctionDecl 0x5615f41671f8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/severt_meter.c:1:1, col:35> col:13 used read_reset 'void (int *)' extern
| `-ParmVarDecl 0x5615f4167130 <col:24, col:30> col:30 reset 'int *'
|-FunctionDecl 0x5615f4167390 <line:2:1, col:35> col:13 used read_event 'void (int *)' extern
| `-ParmVarDecl 0x5615f4167300 <col:24, col:30> col:30 event 'int *'
|-FunctionDecl 0x5615f41676c8 <line:47:1, line:57:1> line:47:6 used counter_step 'void (int *, int, int, int)'
| |-ParmVarDecl 0x5615f4167450 <col:19, col:25> col:25 used cnt 'int *'
| |-ParmVarDecl 0x5615f41674d0 <col:30, col:34> col:34 used reset 'int'
| |-ParmVarDecl 0x5615f4167550 <col:41, col:45> col:45 used event 'int'
| |-ParmVarDecl 0x5615f41675d0 <col:52, col:56> col:56 used max 'int'
| `-CompoundStmt 0x5615f4167b20 <line:48:1, line:57:1>
|   `-IfStmt 0x5615f4167af8 <line:49:5, line:56:5> has_else
|     |-ImplicitCastExpr 0x5615f41677a8 <line:49:8> 'int' <LValueToRValue>
|     | `-DeclRefExpr 0x5615f4167788 <col:8> 'int' lvalue ParmVar 0x5615f41674d0 'reset' 'int'
|     |-CompoundStmt 0x5615f4167850 <line:50:5, line:52:5>
|     | `-BinaryOperator 0x5615f4167830 <line:51:9, col:16> 'int' '='
|     |   |-UnaryOperator 0x5615f41677f8 <col:9, col:10> 'int' lvalue prefix '*' cannot overflow
|     |   | `-ImplicitCastExpr 0x5615f41677e0 <col:10> 'int *' <LValueToRValue>
|     |   |   `-DeclRefExpr 0x5615f41677c0 <col:10> 'int *' lvalue ParmVar 0x5615f4167450 'cnt' 'int *'
|     |   `-IntegerLiteral 0x5615f4167810 <col:16> 'int' 0
|     `-IfStmt 0x5615f4167ae0 <line:53:10, line:56:5>
|       |-BinaryOperator 0x5615f4167990 <line:53:13, col:29> 'int' '&&'
|       | |-ImplicitCastExpr 0x5615f4167978 <col:13> 'int' <LValueToRValue>
|       | | `-DeclRefExpr 0x5615f4167868 <col:13> 'int' lvalue ParmVar 0x5615f4167550 'event' 'int'
|       | `-BinaryOperator 0x5615f4167958 <col:22, col:29> 'int' '<'
|       |   |-ImplicitCastExpr 0x5615f4167928 <col:22, col:23> 'int' <LValueToRValue>
|       |   | `-UnaryOperator 0x5615f41678f0 <col:22, col:23> 'int' lvalue prefix '*' cannot overflow
|       |   |   `-ImplicitCastExpr 0x5615f41678d8 <col:23> 'int *' <LValueToRValue>
|       |   |     `-DeclRefExpr 0x5615f41678b8 <col:23> 'int *' lvalue ParmVar 0x5615f4167450 'cnt' 'int *'
|       |   `-ImplicitCastExpr 0x5615f4167940 <col:29> 'int' <LValueToRValue>
|       |     `-DeclRefExpr 0x5615f4167908 <col:29> 'int' lvalue ParmVar 0x5615f41675d0 'max' 'int'
|       `-CompoundStmt 0x5615f4167ac8 <line:54:5, line:56:5>
|         `-BinaryOperator 0x5615f4167aa8 <line:55:9, col:23> 'int' '='
|           |-UnaryOperator 0x5615f41679e8 <col:9, col:10> 'int' lvalue prefix '*' cannot overflow
|           | `-ImplicitCastExpr 0x5615f41679d0 <col:10> 'int *' <LValueToRValue>
|           |   `-DeclRefExpr 0x5615f41679b0 <col:10> 'int *' lvalue ParmVar 0x5615f4167450 'cnt' 'int *'
|           `-BinaryOperator 0x5615f4167a88 <col:16, col:23> 'int' '+'
|             |-ImplicitCastExpr 0x5615f4167a70 <col:16, col:17> 'int' <LValueToRValue>
|             | `-UnaryOperator 0x5615f4167a38 <col:16, col:17> 'int' lvalue prefix '*' cannot overflow
|             |   `-ImplicitCastExpr 0x5615f4167a20 <col:17> 'int *' <LValueToRValue>
|             |     `-DeclRefExpr 0x5615f4167a00 <col:17> 'int *' lvalue ParmVar 0x5615f4167450 'cnt' 'int *'
|             `-IntegerLiteral 0x5615f4167a50 <col:23> 'int' 1
|-FunctionDecl 0x5615f4167be0 <line:59:1, line:62:1> line:59:6 used counter_init 'void (int *)'
| |-ParmVarDecl 0x5615f4167b50 <col:19, col:25> col:25 used cnt 'int *'
| `-CompoundStmt 0x5615f4167d18 <line:60:1, line:62:1>
|   `-BinaryOperator 0x5615f4167cf8 <line:61:5, col:12> 'int' '='
|     |-UnaryOperator 0x5615f4167cc0 <col:5, col:6> 'int' lvalue prefix '*' cannot overflow
|     | `-ImplicitCastExpr 0x5615f4167ca8 <col:6> 'int *' <LValueToRValue>
|     |   `-DeclRefExpr 0x5615f4167c88 <col:6> 'int *' lvalue ParmVar 0x5615f4167b50 'cnt' 'int *'
|     `-IntegerLiteral 0x5615f4167cd8 <col:12> 'int' 0
`-FunctionDecl 0x5615f4167e08 <line:64:1, line:84:1> line:64:6 severt_meter 'void (int)'
  |-ParmVarDecl 0x5615f4167d48 <col:19, col:23> col:23 used max 'int'
  `-CompoundStmt 0x5615f4168bb8 <line:65:1, line:84:1>
    |-DeclStmt 0x5615f4167f30 <line:66:5, col:13>
    | `-VarDecl 0x5615f4167ec8 <col:5, col:9> col:9 used cnt1 'int'
    |-DeclStmt 0x5615f4167fc8 <line:67:5, col:14>
    | `-VarDecl 0x5615f4167f60 <col:5, col:9> col:9 used reset 'int'
    |-DeclStmt 0x5615f4168060 <line:68:5, col:14>
    | `-VarDecl 0x5615f4167ff8 <col:5, col:9> col:9 used event 'int'
    |-IfStmt 0x5615f41687d0 <line:70:5, line:71:9>
    | |-BinaryOperator 0x5615f41680d0 <line:70:8, col:14> 'int' '<'
    | | |-ImplicitCastExpr 0x5615f41680b8 <col:8> 'int' <LValueToRValue>
    | | | `-DeclRefExpr 0x5615f4168078 <col:8> 'int' lvalue ParmVar 0x5615f4167d48 'max' 'int'
    | | `-IntegerLiteral 0x5615f4168098 <col:14> 'int' 0
    | `-ReturnStmt 0x5615f41687c0 <line:71:9>
    |-CallExpr 0x5615f4168880 <line:73:5, col:23> 'void'
    | |-ImplicitCastExpr 0x5615f4168868 <col:5> 'void (*)(int *)' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x5615f41687e8 <col:5> 'void (int *)' Function 0x5615f4167be0 'counter_init' 'void (int *)'
    | `-UnaryOperator 0x5615f4168828 <col:18, col:19> 'int *' prefix '&' cannot overflow
    |   `-DeclRefExpr 0x5615f4168808 <col:19> 'int' lvalue Var 0x5615f4167ec8 'cnt1' 'int'
    `-WhileStmt 0x5615f4168ba0 <line:75:5, line:83:5>
      |-IntegerLiteral 0x5615f41688a8 <line:75:11> 'int' 1
      `-CompoundStmt 0x5615f4168b78 <line:76:5, line:83:5>
        |-CallExpr 0x5615f4168938 <line:79:9, col:26> 'void'
        | |-ImplicitCastExpr 0x5615f4168920 <col:9> 'void (*)(int *)' <FunctionToPointerDecay>
        | | `-DeclRefExpr 0x5615f41688c8 <col:9> 'void (int *)' Function 0x5615f41671f8 'read_reset' 'void (int *)'
        | `-UnaryOperator 0x5615f4168908 <col:20, col:21> 'int *' prefix '&' cannot overflow
        |   `-DeclRefExpr 0x5615f41688e8 <col:21> 'int' lvalue Var 0x5615f4167f60 'reset' 'int'
        |-CallExpr 0x5615f41689d0 <line:80:9, col:26> 'void'
        | |-ImplicitCastExpr 0x5615f41689b8 <col:9> 'void (*)(int *)' <FunctionToPointerDecay>
        | | `-DeclRefExpr 0x5615f4168960 <col:9> 'void (int *)' Function 0x5615f4167390 'read_event' 'void (int *)'
        | `-UnaryOperator 0x5615f41689a0 <col:20, col:21> 'int *' prefix '&' cannot overflow
        |   `-DeclRefExpr 0x5615f4168980 <col:21> 'int' lvalue Var 0x5615f4167ff8 'event' 'int'
        `-CallExpr 0x5615f4168af0 <line:82:9, col:46> 'void'
          |-ImplicitCastExpr 0x5615f4168ad8 <col:9> 'void (*)(int *, int, int, int)' <FunctionToPointerDecay>
          | `-DeclRefExpr 0x5615f41689f8 <col:9> 'void (int *, int, int, int)' Function 0x5615f41676c8 'counter_step' 'void (int *, int, int, int)'
          |-UnaryOperator 0x5615f4168a38 <col:22, col:23> 'int *' prefix '&' cannot overflow
          | `-DeclRefExpr 0x5615f4168a18 <col:23> 'int' lvalue Var 0x5615f4167ec8 'cnt1' 'int'
          |-ImplicitCastExpr 0x5615f4168b30 <col:29> 'int' <LValueToRValue>
          | `-DeclRefExpr 0x5615f4168a50 <col:29> 'int' lvalue Var 0x5615f4167f60 'reset' 'int'
          |-ImplicitCastExpr 0x5615f4168b48 <col:36> 'int' <LValueToRValue>
          | `-DeclRefExpr 0x5615f4168a70 <col:36> 'int' lvalue Var 0x5615f4167ff8 'event' 'int'
          `-ImplicitCastExpr 0x5615f4168b60 <col:43> 'int' <LValueToRValue>
            `-DeclRefExpr 0x5615f4168a90 <col:43> 'int' lvalue ParmVar 0x5615f4167d48 'max' 'int'
