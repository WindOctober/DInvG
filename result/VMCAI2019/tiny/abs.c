./Benchmark/PLDI/VMCAI2019/tiny/abs.c
[info] Using default compilation options.
TranslationUnitDecl 0x563b3c68ed88 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x563b3c68f620 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x563b3c68f320 '__int128'
|-TypedefDecl 0x563b3c68f690 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x563b3c68f340 'unsigned __int128'
|-TypedefDecl 0x563b3c68f998 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x563b3c68f770 'struct __NSConstantString_tag'
|   `-Record 0x563b3c68f6e8 '__NSConstantString_tag'
|-TypedefDecl 0x563b3c68fa30 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x563b3c68f9f0 'char *'
|   `-BuiltinType 0x563b3c68ee20 'char'
|-TypedefDecl 0x563b3c68fd28 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x563b3c68fcd0 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x563b3c68fb10 'struct __va_list_tag'
|     `-Record 0x563b3c68fa88 '__va_list_tag'
|-FunctionDecl 0x563b3c6eea60 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/VMCAI2019/tiny/abs.c:13:1, line:23:1> line:13:5 used my_abs 'int (int)'
| |-ParmVarDecl 0x563b3c6ee998 <col:12, col:16> col:16 used x 'int'
| `-CompoundStmt 0x563b3c6eedd8 <line:14:1, line:23:1>
|   |-DeclStmt 0x563b3c6eebd0 <line:15:5, col:10>
|   | `-VarDecl 0x563b3c6eeb68 <col:5, col:9> col:9 used r 'int'
|   |-IfStmt 0x563b3c6eed68 <line:17:5, line:20:13> has_else
|   | |-BinaryOperator 0x563b3c6eec40 <line:17:8, col:12> 'int' '<'
|   | | |-ImplicitCastExpr 0x563b3c6eec28 <col:8> 'int' <LValueToRValue>
|   | | | `-DeclRefExpr 0x563b3c6eebe8 <col:8> 'int' lvalue ParmVar 0x563b3c6ee998 'x' 'int'
|   | | `-IntegerLiteral 0x563b3c6eec08 <col:12> 'int' 0
|   | |-BinaryOperator 0x563b3c6eecd0 <line:18:9, col:14> 'int' '='
|   | | |-DeclRefExpr 0x563b3c6eec60 <col:9> 'int' lvalue Var 0x563b3c6eeb68 'r' 'int'
|   | | `-UnaryOperator 0x563b3c6eecb8 <col:13, col:14> 'int' prefix '-'
|   | |   `-ImplicitCastExpr 0x563b3c6eeca0 <col:14> 'int' <LValueToRValue>
|   | |     `-DeclRefExpr 0x563b3c6eec80 <col:14> 'int' lvalue ParmVar 0x563b3c6ee998 'x' 'int'
|   | `-BinaryOperator 0x563b3c6eed48 <line:20:9, col:13> 'int' '='
|   |   |-DeclRefExpr 0x563b3c6eecf0 <col:9> 'int' lvalue Var 0x563b3c6eeb68 'r' 'int'
|   |   `-ImplicitCastExpr 0x563b3c6eed30 <col:13> 'int' <LValueToRValue>
|   |     `-DeclRefExpr 0x563b3c6eed10 <col:13> 'int' lvalue ParmVar 0x563b3c6ee998 'x' 'int'
|   `-ReturnStmt 0x563b3c6eedc8 <line:22:5, col:12>
|     `-ImplicitCastExpr 0x563b3c6eedb0 <col:12> 'int' <LValueToRValue>
|       `-DeclRefExpr 0x563b3c6eed90 <col:12> 'int' lvalue Var 0x563b3c6eeb68 'r' 'int'
`-FunctionDecl 0x563b3c6eee48 <line:25:1, line:31:1> line:25:6 test 'void ()'
  `-CompoundStmt 0x563b3c6ef140 <line:26:1, line:31:1>
    |-DeclStmt 0x563b3c6eef68 <line:27:5, col:10>
    | `-VarDecl 0x563b3c6eef00 <col:5, col:9> col:9 used r 'int'
    |-DeclStmt 0x563b3c6ef020 <line:28:5, col:15>
    | `-VarDecl 0x563b3c6eef98 <col:5, col:13> col:9 used k 'int' cinit
    |   `-IntegerLiteral 0x563b3c6ef000 <col:13> 'int' 42
    `-BinaryOperator 0x563b3c6ef120 <line:30:5, col:17> 'int' '='
      |-DeclRefExpr 0x563b3c6ef038 <col:5> 'int' lvalue Var 0x563b3c6eef00 'r' 'int'
      `-CallExpr 0x563b3c6ef0e0 <col:9, col:17> 'int'
        |-ImplicitCastExpr 0x563b3c6ef0c8 <col:9> 'int (*)(int)' <FunctionToPointerDecay>
        | `-DeclRefExpr 0x563b3c6ef058 <col:9> 'int (int)' Function 0x563b3c6eea60 'my_abs' 'int (int)'
        `-ImplicitCastExpr 0x563b3c6ef108 <col:16> 'int' <LValueToRValue>
          `-DeclRefExpr 0x563b3c6ef078 <col:16> 'int' lvalue Var 0x563b3c6eef98 'k' 'int'
