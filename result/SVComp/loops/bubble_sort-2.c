./Benchmark/PLDI/SVComp/loops/bubble_sort-2.c
[info] Using default compilation options.
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:2:22: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
void reach_error() { assert(0); }
                     ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:17:44: warning: incompatible redeclaration of library function 'malloc' [-Wincompatible-library-redeclaration]
extern  __attribute__((__nothrow__)) void *malloc(size_t __size )  __attribute__((__malloc__)) ;
                                           ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:17:44: note: 'malloc' is a builtin with type 'void *(unsigned long)'
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:25:34: warning: implicit declaration of function 'assert' is invalid in C99 [-Wimplicit-function-declaration]
  ERROR: {reach_error();abort();}assert(0);
                                 ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:195:21: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp10 = *((struct list_head * const  *)__cil_tmp9);
                    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:212:19: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
  __cil_tmp15 = *((struct list_head * const  *)__cil_tmp14);
                  ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:255:21: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp23 = *((struct list_head * const  *)__cil_tmp22);
                    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:273:17: warning: cast to 'struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
  __cil_tmp29 = (struct list_head *)__cil_tmp28;
                ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:299:19: warning: cast to 'const struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp36 = (struct list_head  const  *)__cil_tmp35;
                  ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:303:21: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp40 = *((struct list_head * const  *)__cil_tmp39);
                    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:324:19: warning: cast to 'const struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp45 = (struct list_head  const  *)__cil_tmp44;
                  ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:329:21: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp50 = *((struct list_head * const  *)__cil_tmp49);
                    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:350:19: warning: cast to 'const struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp55 = (struct list_head  const  *)__cil_tmp54;
                  ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:354:21: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp59 = *((struct list_head * const  *)__cil_tmp58);
                    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:375:19: warning: cast to 'const struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp64 = (struct list_head  const  *)__cil_tmp63;
                  ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:380:21: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp69 = *((struct list_head * const  *)__cil_tmp68);
                    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:421:19: warning: cast to 'const struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp78 = (struct list_head  const  *)__cil_tmp77;
                  ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:465:21: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp90 = *((struct list_head * const  *)__cil_tmp89);
                    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:468:21: warning: cast to 'struct list_head **' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp93 = *((struct list_head **)__cil_tmp92);
                    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:491:22: warning: cast to 'struct list_head *const *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp100 = *((struct list_head * const  *)__cil_tmp99);
                     ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:517:20: warning: cast to 'const struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp109 = (struct list_head  const  *)__cil_tmp108;
                   ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:538:20: warning: cast to 'struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp116 = (struct list_head *)__cil_tmp115;
                   ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:569:5: warning: cast to 'struct list_head **' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
  *((struct list_head **)__cil_tmp5) = new;
    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:573:5: warning: cast to 'struct list_head **' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
  *((struct list_head **)__cil_tmp7) = prev;
    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:585:5: warning: cast to 'struct list_head **' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
  *((struct list_head **)__cil_tmp4) = prev;
    ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:611:18: warning: cast to 'struct list_head **' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
  __cil_tmp5 = *((struct list_head **)__cil_tmp4);
                 ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:652:16: warning: cast to 'struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
  __cil_tmp7 = (struct list_head *)__cil_tmp6;
               ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:662:7: warning: cast to 'struct list_head **' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    *((struct list_head **)__cil_tmp9) = (struct list_head *)__cil_tmp11;
      ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:662:42: warning: cast to 'struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    *((struct list_head **)__cil_tmp9) = (struct list_head *)__cil_tmp11;
                                         ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:667:7: warning: cast to 'struct list_head **' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    *((struct list_head **)__cil_tmp13) = (struct list_head *)__cil_tmp15;
      ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:667:43: warning: cast to 'struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    *((struct list_head **)__cil_tmp13) = (struct list_head *)__cil_tmp15;
                                          ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:736:18: warning: cast to 'struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
    __cil_tmp9 = (struct list_head *)__cil_tmp8;
                 ^
/home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:764:16: warning: cast to 'struct list_head *' from smaller integer type 'unsigned int' [-Wint-to-pointer-cast]
  __cil_tmp6 = (struct list_head *)__cil_tmp5;
               ^
TranslationUnitDecl 0x560375a37dc8 <<invalid sloc>> <invalid sloc>
|-TypedefDecl 0x560375a38660 <<invalid sloc>> <invalid sloc> implicit __int128_t '__int128'
| `-BuiltinType 0x560375a38360 '__int128'
|-TypedefDecl 0x560375a386d0 <<invalid sloc>> <invalid sloc> implicit __uint128_t 'unsigned __int128'
| `-BuiltinType 0x560375a38380 'unsigned __int128'
|-TypedefDecl 0x560375a389d8 <<invalid sloc>> <invalid sloc> implicit __NSConstantString 'struct __NSConstantString_tag'
| `-RecordType 0x560375a387b0 'struct __NSConstantString_tag'
|   `-Record 0x560375a38728 '__NSConstantString_tag'
|-TypedefDecl 0x560375a38a70 <<invalid sloc>> <invalid sloc> implicit __builtin_ms_va_list 'char *'
| `-PointerType 0x560375a38a30 'char *'
|   `-BuiltinType 0x560375a37e60 'char'
|-TypedefDecl 0x560375a38d68 <<invalid sloc>> <invalid sloc> implicit __builtin_va_list 'struct __va_list_tag [1]'
| `-ConstantArrayType 0x560375a38d10 'struct __va_list_tag [1]' 1 
|   `-RecordType 0x560375a38b50 'struct __va_list_tag'
|     `-Record 0x560375a38ac8 '__va_list_tag'
|-FunctionDecl 0x560375a97ab8 </home/windoctober/Desktop/Clang-based-Invariant-Generator/Benchmark/PLDI/SVComp/loops/bubble_sort-2.c:1:13> col:13 implicit used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x560375a97b58 prev 0x560375a97ab8 <col:1, col:23> col:13 used abort 'void (void) __attribute__((noreturn))' extern
|-FunctionDecl 0x560375a97c48 <line:2:1, col:33> col:6 used reach_error 'void ()'
| `-CompoundStmt 0x560375a97ed8 <col:20, col:33>
|   `-CallExpr 0x560375a97eb0 <col:22, col:30> 'int'
|     |-ImplicitCastExpr 0x560375a97e98 <col:22> 'int (*)()' <FunctionToPointerDecay>
|     | `-DeclRefExpr 0x560375a97e30 <col:22> 'int ()' Function 0x560375a97d80 'assert' 'int ()'
|     `-IntegerLiteral 0x560375a97e50 <col:29> 'int' 0
|-TypedefDecl 0x560375a97f08 <line:7:1, col:22> col:22 referenced size_t 'unsigned int'
| `-BuiltinType 0x560375a37f60 'unsigned int'
|-RecordDecl 0x560375a97f60 <line:8:1, line:11:1> line:8:8 struct list_head definition
| |-FieldDecl 0x560375a980b0 <line:9:4, col:22> col:22 next 'struct list_head *'
| `-FieldDecl 0x560375a98128 <line:10:4, col:22> col:22 prev 'struct list_head *'
|-RecordDecl 0x560375a98178 <line:12:1, line:16:1> line:12:8 struct node definition
| |-FieldDecl 0x560375a98238 <line:13:4, col:8> col:8 value 'int'
| |-FieldDecl 0x560375a982a8 <line:14:4, col:21> col:21 linkage 'struct list_head':'struct list_head'
| `-FieldDecl 0x560375a98318 <line:15:4, col:21> col:21 nested 'struct list_head':'struct list_head'
|-FunctionDecl 0x560375a984d0 <line:17:44> col:44 implicit used malloc 'void *(unsigned long)' extern
| `-ParmVarDecl 0x560375a98570 <<invalid sloc>> <invalid sloc> 'unsigned long'
|-FunctionDecl 0x560375a985e0 prev 0x560375a984d0 <col:1, col:94> col:44 used malloc 'void *(size_t)' extern
| |-ParmVarDecl 0x560375a983a0 <col:51, col:58> col:58 __size 'size_t':'unsigned int'
| |-NoThrowAttr 0x560375a98688 <col:24>
| `-RestrictAttr 0x560375a986e0 <col:83> malloc
|-FunctionDecl 0x560375a9bbf8 <line:18:1, col:60> col:43 used free 'void (void *)' extern
| |-ParmVarDecl 0x560375a9bb38 <col:48, col:54> col:54 __ptr 'void *'
| `-NoThrowAttr 0x560375a9bca0 <col:24>
|-FunctionDecl 0x560375a9bd90 prev 0x560375a97b58 <line:19:1, col:67> col:57 used abort 'void (void) __attribute__((noreturn))' extern
| `-NoThrowAttr 0x560375a9be30 <col:24>
|-FunctionDecl 0x560375a9bf50 <line:20:1, col:38> col:12 used __VERIFIER_nondet_int 'int (void)' extern
|-FunctionDecl 0x560375a9c088 <line:21:1, line:28:1> line:21:13 used fail 'void (void)' static
| `-CompoundStmt 0x560375a9c378 <line:22:1, line:28:1>
|   `-CompoundStmt 0x560375a9c350 <line:24:3, line:27:1>
|     |-LabelStmt 0x560375a9c2a0 <line:25:3, col:33> 'ERROR'
|     | `-CompoundStmt 0x560375a9c230 <col:10, col:33>
|     |   |-CallExpr 0x560375a9c190 <col:11, col:23> 'void'
|     |   | `-ImplicitCastExpr 0x560375a9c178 <col:11> 'void (*)()' <FunctionToPointerDecay>
|     |   |   `-DeclRefExpr 0x560375a9c128 <col:11> 'void ()' Function 0x560375a97c48 'reach_error' 'void ()'
|     |   `-CallExpr 0x560375a9c210 <col:25, col:31> 'void'
|     |     `-ImplicitCastExpr 0x560375a9c1f8 <col:25> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|     |       `-DeclRefExpr 0x560375a9c1b0 <col:25> 'void (void) __attribute__((noreturn))' Function 0x560375a9bd90 'abort' 'void (void) __attribute__((noreturn))'
|     |-CallExpr 0x560375a9c310 <col:34, col:42> 'int'
|     | |-ImplicitCastExpr 0x560375a9c2f8 <col:34> 'int (*)()' <FunctionToPointerDecay>
|     | | `-DeclRefExpr 0x560375a9c2b8 <col:34> 'int ()' Function 0x560375a97d80 'assert' 'int ()'
|     | `-IntegerLiteral 0x560375a9c2d8 <col:41> 'int' 0
|     `-GotoStmt 0x560375a9c338 <line:26:3, col:8> 'ERROR' 0x560375a9c250
|-VarDecl 0x560375a9c3b0 <line:29:1, col:53> col:18 used gl_list 'struct list_head':'struct list_head' cinit
| `-InitListExpr 0x560375a9c4e8 <col:32, col:53> 'struct list_head':'struct list_head'
|   |-UnaryOperator 0x560375a9c438 <col:33, col:35> 'struct list_head *' prefix '&' cannot overflow
|   | `-DeclRefExpr 0x560375a9c418 <col:35> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
|   `-UnaryOperator 0x560375a9c470 <col:44, col:46> 'struct list_head *' prefix '&' cannot overflow
|     `-DeclRefExpr 0x560375a9c450 <col:46> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
|-FunctionDecl 0x560375a9c6b8 <line:30:1, line:559:1> line:30:13 used inspect 'void (const struct list_head *)' static
| |-ParmVarDecl 0x560375a9c5c0 <col:21, col:47> col:47 used head 'const struct list_head *'
| `-CompoundStmt 0x560375ab3b80 <line:31:1, line:559:1>
|   |-DeclStmt 0x560375a9c878 <line:31:3, col:29>
|   | `-VarDecl 0x560375a9c810 <col:3, col:24> col:24 used node 'const struct node *'
|   |-DeclStmt 0x560375a9c910 <line:32:3, col:27>
|   | `-VarDecl 0x560375a9c8a8 <col:3, col:16> col:16 used __cil_tmp3 'unsigned int'
|   |-DeclStmt 0x560375a9c9b8 <line:33:3, col:32>
|   | `-VarDecl 0x560375a9c950 <col:3, col:21> col:21 used __cil_tmp4 'struct list_head *'
|   |-DeclStmt 0x560375aa1aa8 <line:34:3, col:27>
|   | `-VarDecl 0x560375aa1a40 <col:3, col:16> col:16 used __cil_tmp5 'unsigned int'
|   |-DeclStmt 0x560375aa1b40 <line:35:3, col:18>
|   | `-VarDecl 0x560375aa1ad8 <col:3, col:7> col:7 used __cil_tmp6 'int'
|   |-DeclStmt 0x560375aa1bd8 <line:36:3, col:27>
|   | `-VarDecl 0x560375aa1b70 <col:3, col:16> col:16 used __cil_tmp7 'unsigned int'
|   |-DeclStmt 0x560375aa1c70 <line:37:3, col:27>
|   | `-VarDecl 0x560375aa1c08 <col:3, col:16> col:16 used __cil_tmp8 'unsigned int'
|   |-DeclStmt 0x560375aa1d08 <line:38:3, col:27>
|   | `-VarDecl 0x560375aa1ca0 <col:3, col:16> col:16 used __cil_tmp9 'unsigned int'
|   |-DeclStmt 0x560375aa1db0 <line:39:3, col:33>
|   | `-VarDecl 0x560375aa1d48 <col:3, col:21> col:21 used __cil_tmp10 'struct list_head *'
|   |-DeclStmt 0x560375aa1e48 <line:40:3, col:28>
|   | `-VarDecl 0x560375aa1de0 <col:3, col:16> col:16 used __cil_tmp11 'unsigned int'
|   |-DeclStmt 0x560375aa1ee0 <line:41:3, col:19>
|   | `-VarDecl 0x560375aa1e78 <col:3, col:7> col:7 used __cil_tmp12 'int'
|   |-DeclStmt 0x560375aa1f78 <line:42:3, col:28>
|   | `-VarDecl 0x560375aa1f10 <col:3, col:16> col:16 used __cil_tmp13 'unsigned int'
|   |-DeclStmt 0x560375aa2010 <line:43:3, col:28>
|   | `-VarDecl 0x560375aa1fa8 <col:3, col:16> col:16 used __cil_tmp14 'unsigned int'
|   |-DeclStmt 0x560375aa20b8 <line:44:3, col:33>
|   | `-VarDecl 0x560375aa2050 <col:3, col:21> col:21 used __cil_tmp15 'struct list_head *'
|   |-DeclStmt 0x560375aa2150 <line:45:3, col:28>
|   | `-VarDecl 0x560375aa20e8 <col:3, col:16> col:16 used __cil_tmp16 'unsigned int'
|   |-DeclStmt 0x560375aa21f8 <line:46:3, col:33>
|   | `-VarDecl 0x560375aa2190 <col:3, col:21> col:21 used __cil_tmp17 'struct list_head *'
|   |-DeclStmt 0x560375aa2290 <line:47:3, col:28>
|   | `-VarDecl 0x560375aa2228 <col:3, col:16> col:16 used __cil_tmp18 'unsigned int'
|   |-DeclStmt 0x560375aa2328 <line:48:3, col:19>
|   | `-VarDecl 0x560375aa22c0 <col:3, col:7> col:7 used __cil_tmp19 'int'
|   |-DeclStmt 0x560375aa23c0 <line:49:3, col:28>
|   | `-VarDecl 0x560375aa2358 <col:3, col:16> col:16 used __cil_tmp20 'unsigned int'
|   |-DeclStmt 0x560375aa2458 <line:50:3, col:28>
|   | `-VarDecl 0x560375aa23f0 <col:3, col:16> col:16 used __cil_tmp21 'unsigned int'
|   |-DeclStmt 0x560375aa24f0 <line:51:3, col:28>
|   | `-VarDecl 0x560375aa2488 <col:3, col:16> col:16 used __cil_tmp22 'unsigned int'
|   |-DeclStmt 0x560375aa2598 <line:52:3, col:33>
|   | `-VarDecl 0x560375aa2530 <col:3, col:21> col:21 used __cil_tmp23 'struct list_head *'
|   |-DeclStmt 0x560375aa2630 <line:53:3, col:28>
|   | `-VarDecl 0x560375aa25c8 <col:3, col:16> col:16 used __cil_tmp24 'unsigned int'
|   |-DeclStmt 0x560375aa26c8 <line:54:3, col:19>
|   | `-VarDecl 0x560375aa2660 <col:3, col:7> col:7 used __cil_tmp25 'int'
|   |-DeclStmt 0x560375aa27c8 <line:55:3, col:28>
|   | `-VarDecl 0x560375aa2760 <col:3, col:16> col:16 used __cil_tmp26 'struct node *'
|   |-DeclStmt 0x560375aa2860 <line:56:3, col:28>
|   | `-VarDecl 0x560375aa27f8 <col:3, col:16> col:16 used __cil_tmp27 'unsigned int'
|   |-DeclStmt 0x560375aa28f8 <line:57:3, col:28>
|   | `-VarDecl 0x560375aa2890 <col:3, col:16> col:16 used __cil_tmp28 'unsigned int'
|   |-DeclStmt 0x560375aa29a0 <line:58:3, col:33>
|   | `-VarDecl 0x560375aa2938 <col:3, col:21> col:21 used __cil_tmp29 'struct list_head *'
|   |-DeclStmt 0x560375aa2a50 <line:59:3, col:29>
|   | `-VarDecl 0x560375aa29d0 <col:3, col:17> col:17 used __cil_tmp30 'unsigned long'
|   |-DeclStmt 0x560375aa2ae8 <line:60:3, col:21>
|   | `-VarDecl 0x560375aa2a80 <col:3, col:9> col:9 used __cil_tmp31 'char *'
|   |-DeclStmt 0x560375aa2b80 <line:61:3, col:21>
|   | `-VarDecl 0x560375aa2b18 <col:3, col:9> col:9 used __cil_tmp32 'char *'
|   |-DeclStmt 0x560375aa2c28 <line:62:3, col:28>
|   | `-VarDecl 0x560375aa2bc0 <col:3, col:16> col:16 used __cil_tmp33 'struct node *'
|   |-DeclStmt 0x560375aa2cc0 <line:63:3, col:28>
|   | `-VarDecl 0x560375aa2c58 <col:3, col:16> col:16 used __cil_tmp34 'unsigned int'
|   |-DeclStmt 0x560375aa2d58 <line:64:3, col:28>
|   | `-VarDecl 0x560375aa2cf0 <col:3, col:16> col:16 used __cil_tmp35 'unsigned int'
|   |-DeclStmt 0x560375aa2e00 <line:65:3, col:41>
|   | `-VarDecl 0x560375aa2d98 <col:3, col:29> col:29 used __cil_tmp36 'const struct list_head *'
|   |-DeclStmt 0x560375aa2e98 <line:66:3, col:28>
|   | `-VarDecl 0x560375aa2e30 <col:3, col:16> col:16 used __cil_tmp37 'unsigned int'
|   |-DeclStmt 0x560375aa2f30 <line:67:3, col:28>
|   | `-VarDecl 0x560375aa2ec8 <col:3, col:16> col:16 used __cil_tmp38 'unsigned int'
|   |-DeclStmt 0x560375aa2fc8 <line:68:3, col:28>
|   | `-VarDecl 0x560375aa2f60 <col:3, col:16> col:16 used __cil_tmp39 'unsigned int'
|   |-DeclStmt 0x560375aa3070 <line:69:3, col:33>
|   | `-VarDecl 0x560375aa3008 <col:3, col:21> col:21 used __cil_tmp40 'struct list_head *'
|   |-DeclStmt 0x560375aa3108 <line:70:3, col:28>
|   | `-VarDecl 0x560375aa30a0 <col:3, col:16> col:16 used __cil_tmp41 'unsigned int'
|   |-DeclStmt 0x560375aa31a0 <line:71:3, col:19>
|   | `-VarDecl 0x560375aa3138 <col:3, col:7> col:7 used __cil_tmp42 'int'
|   |-DeclStmt 0x560375aa3238 <line:72:3, col:28>
|   | `-VarDecl 0x560375aa31d0 <col:3, col:16> col:16 used __cil_tmp43 'unsigned int'
|   |-DeclStmt 0x560375aa32d0 <line:73:3, col:28>
|   | `-VarDecl 0x560375aa3268 <col:3, col:16> col:16 used __cil_tmp44 'unsigned int'
|   |-DeclStmt 0x560375aa3378 <line:74:3, col:41>
|   | `-VarDecl 0x560375aa3310 <col:3, col:29> col:29 used __cil_tmp45 'const struct list_head *'
|   |-DeclStmt 0x560375aa3410 <line:75:3, col:28>
|   | `-VarDecl 0x560375aa33a8 <col:3, col:16> col:16 used __cil_tmp46 'unsigned int'
|   |-DeclStmt 0x560375aa34a8 <line:76:3, col:28>
|   | `-VarDecl 0x560375aa3440 <col:3, col:16> col:16 used __cil_tmp47 'unsigned int'
|   |-DeclStmt 0x560375aa3540 <line:77:3, col:28>
|   | `-VarDecl 0x560375aa34d8 <col:3, col:16> col:16 used __cil_tmp48 'unsigned int'
|   |-DeclStmt 0x560375aa35d8 <line:78:3, col:28>
|   | `-VarDecl 0x560375aa3570 <col:3, col:16> col:16 used __cil_tmp49 'unsigned int'
|   |-DeclStmt 0x560375aa3680 <line:79:3, col:33>
|   | `-VarDecl 0x560375aa3618 <col:3, col:21> col:21 used __cil_tmp50 'struct list_head *'
|   |-DeclStmt 0x560375aa3718 <line:80:3, col:28>
|   | `-VarDecl 0x560375aa36b0 <col:3, col:16> col:16 used __cil_tmp51 'unsigned int'
|   |-DeclStmt 0x560375aa37b0 <line:81:3, col:19>
|   | `-VarDecl 0x560375aa3748 <col:3, col:7> col:7 used __cil_tmp52 'int'
|   |-DeclStmt 0x560375aa3848 <line:82:3, col:28>
|   | `-VarDecl 0x560375aa37e0 <col:3, col:16> col:16 used __cil_tmp53 'unsigned int'
|   |-DeclStmt 0x560375aa38e0 <line:83:3, col:28>
|   | `-VarDecl 0x560375aa3878 <col:3, col:16> col:16 used __cil_tmp54 'unsigned int'
|   |-DeclStmt 0x560375aa3988 <line:84:3, col:41>
|   | `-VarDecl 0x560375aa3920 <col:3, col:29> col:29 used __cil_tmp55 'const struct list_head *'
|   |-DeclStmt 0x560375aa3a20 <line:85:3, col:28>
|   | `-VarDecl 0x560375aa39b8 <col:3, col:16> col:16 used __cil_tmp56 'unsigned int'
|   |-DeclStmt 0x560375aa3ac8 <line:86:3, col:28>
|   | `-VarDecl 0x560375aa3a60 <col:3, col:16> col:16 used __cil_tmp57 'unsigned int'
|   |-DeclStmt 0x560375aa3b60 <line:87:3, col:28>
|   | `-VarDecl 0x560375aa3af8 <col:3, col:16> col:16 used __cil_tmp58 'unsigned int'
|   |-DeclStmt 0x560375aa3c08 <line:88:3, col:33>
|   | `-VarDecl 0x560375aa3ba0 <col:3, col:21> col:21 used __cil_tmp59 'struct list_head *'
|   |-DeclStmt 0x560375aa3ca0 <line:89:3, col:28>
|   | `-VarDecl 0x560375aa3c38 <col:3, col:16> col:16 used __cil_tmp60 'unsigned int'
|   |-DeclStmt 0x560375aa3d38 <line:90:3, col:19>
|   | `-VarDecl 0x560375aa3cd0 <col:3, col:7> col:7 used __cil_tmp61 'int'
|   |-DeclStmt 0x560375aa3dd0 <line:91:3, col:28>
|   | `-VarDecl 0x560375aa3d68 <col:3, col:16> col:16 used __cil_tmp62 'unsigned int'
|   |-DeclStmt 0x560375aa3e68 <line:92:3, col:28>
|   | `-VarDecl 0x560375aa3e00 <col:3, col:16> col:16 used __cil_tmp63 'unsigned int'
|   |-DeclStmt 0x560375aa3f10 <line:93:3, col:41>
|   | `-VarDecl 0x560375aa3ea8 <col:3, col:29> col:29 used __cil_tmp64 'const struct list_head *'
|   |-DeclStmt 0x560375aa3fa8 <line:94:3, col:28>
|   | `-VarDecl 0x560375aa3f40 <col:3, col:16> col:16 used __cil_tmp65 'unsigned int'
|   |-DeclStmt 0x560375aa4040 <line:95:3, col:28>
|   | `-VarDecl 0x560375aa3fd8 <col:3, col:16> col:16 used __cil_tmp66 'unsigned int'
|   |-DeclStmt 0x560375aa40d8 <line:96:3, col:28>
|   | `-VarDecl 0x560375aa4070 <col:3, col:16> col:16 used __cil_tmp67 'unsigned int'
|   |-DeclStmt 0x560375aa4170 <line:97:3, col:28>
|   | `-VarDecl 0x560375aa4108 <col:3, col:16> col:16 used __cil_tmp68 'unsigned int'
|   |-DeclStmt 0x560375aa4218 <line:98:3, col:33>
|   | `-VarDecl 0x560375aa41b0 <col:3, col:21> col:21 used __cil_tmp69 'struct list_head *'
|   |-DeclStmt 0x560375aa42b0 <line:99:3, col:28>
|   | `-VarDecl 0x560375aa4248 <col:3, col:16> col:16 used __cil_tmp70 'unsigned int'
|   |-DeclStmt 0x560375aa4348 <line:100:3, col:19>
|   | `-VarDecl 0x560375aa42e0 <col:3, col:7> col:7 used __cil_tmp71 'int'
|   |-DeclStmt 0x560375aa43f0 <line:101:3, col:36>
|   | `-VarDecl 0x560375aa4388 <col:3, col:24> col:24 used __cil_tmp72 'const struct node *'
|   |-DeclStmt 0x560375aa4488 <line:102:3, col:28>
|   | `-VarDecl 0x560375aa4420 <col:3, col:16> col:16 used __cil_tmp73 'unsigned int'
|   |-DeclStmt 0x560375aa4520 <line:103:3, col:28>
|   | `-VarDecl 0x560375aa44b8 <col:3, col:16> col:16 used __cil_tmp74 'unsigned int'
|   |-DeclStmt 0x560375aa45b8 <line:104:3, col:19>
|   | `-VarDecl 0x560375aa4550 <col:3, col:7> col:7 used __cil_tmp75 'int'
|   |-DeclStmt 0x560375aa4650 <line:105:3, col:28>
|   | `-VarDecl 0x560375aa45e8 <col:3, col:16> col:16 used __cil_tmp76 'unsigned int'
|   |-DeclStmt 0x560375aa46e8 <line:106:3, col:28>
|   | `-VarDecl 0x560375aa4680 <col:3, col:16> col:16 used __cil_tmp77 'unsigned int'
|   |-DeclStmt 0x560375aa4790 <line:107:3, col:41>
|   | `-VarDecl 0x560375aa4728 <col:3, col:29> col:29 used __cil_tmp78 'const struct list_head *'
|   |-DeclStmt 0x560375aa4838 <line:108:3, col:36>
|   | `-VarDecl 0x560375aa47d0 <col:3, col:24> col:24 used __cil_tmp79 'const struct node *'
|   |-DeclStmt 0x560375aa48d0 <line:109:3, col:28>
|   | `-VarDecl 0x560375aa4868 <col:3, col:16> col:16 used __cil_tmp80 'unsigned int'
|   |-DeclStmt 0x560375aa4968 <line:110:3, col:28>
|   | `-VarDecl 0x560375aa4900 <col:3, col:16> col:16 used __cil_tmp81 'unsigned int'
|   |-DeclStmt 0x560375aa4a00 <line:111:3, col:19>
|   | `-VarDecl 0x560375aa4998 <col:3, col:7> col:7 used __cil_tmp82 'int'
|   |-DeclStmt 0x560375aa5ae8 <line:112:3, col:28>
|   | `-VarDecl 0x560375aa5a80 <col:3, col:16> col:16 used __cil_tmp83 'const int *'
|   |-DeclStmt 0x560375aa5b90 <line:113:3, col:36>
|   | `-VarDecl 0x560375aa5b28 <col:3, col:24> col:24 used __cil_tmp84 'const struct node *'
|   |-DeclStmt 0x560375aa5c28 <line:114:3, col:28>
|   | `-VarDecl 0x560375aa5bc0 <col:3, col:16> col:16 used __cil_tmp85 'unsigned int'
|   |-DeclStmt 0x560375aa5cc0 <line:115:3, col:28>
|   | `-VarDecl 0x560375aa5c58 <col:3, col:16> col:16 used __cil_tmp86 'unsigned int'
|   |-DeclStmt 0x560375aa5d58 <line:116:3, col:19>
|   | `-VarDecl 0x560375aa5cf0 <col:3, col:7> col:7 used __cil_tmp87 'int'
|   |-DeclStmt 0x560375aa5df0 <line:117:3, col:28>
|   | `-VarDecl 0x560375aa5d88 <col:3, col:16> col:16 used __cil_tmp88 'unsigned int'
|   |-DeclStmt 0x560375aa5e88 <line:118:3, col:28>
|   | `-VarDecl 0x560375aa5e20 <col:3, col:16> col:16 used __cil_tmp89 'unsigned int'
|   |-DeclStmt 0x560375aa5f30 <line:119:3, col:33>
|   | `-VarDecl 0x560375aa5ec8 <col:3, col:21> col:21 used __cil_tmp90 'struct list_head *'
|   |-DeclStmt 0x560375aa5fc8 <line:120:3, col:28>
|   | `-VarDecl 0x560375aa5f60 <col:3, col:16> col:16 used __cil_tmp91 'unsigned int'
|   |-DeclStmt 0x560375aa6060 <line:121:3, col:28>
|   | `-VarDecl 0x560375aa5ff8 <col:3, col:16> col:16 used __cil_tmp92 'unsigned int'
|   |-DeclStmt 0x560375aa6108 <line:122:3, col:33>
|   | `-VarDecl 0x560375aa60a0 <col:3, col:21> col:21 used __cil_tmp93 'struct list_head *'
|   |-DeclStmt 0x560375aa61a0 <line:123:3, col:28>
|   | `-VarDecl 0x560375aa6138 <col:3, col:16> col:16 used __cil_tmp94 'unsigned int'
|   |-DeclStmt 0x560375aa6238 <line:124:3, col:28>
|   | `-VarDecl 0x560375aa61d0 <col:3, col:16> col:16 used __cil_tmp95 'unsigned int'
|   |-DeclStmt 0x560375aa62d0 <line:125:3, col:19>
|   | `-VarDecl 0x560375aa6268 <col:3, col:7> col:7 used __cil_tmp96 'int'
|   |-DeclStmt 0x560375aa6368 <line:126:3, col:28>
|   | `-VarDecl 0x560375aa6300 <col:3, col:16> col:16 used __cil_tmp97 'unsigned int'
|   |-DeclStmt 0x560375aa6400 <line:127:3, col:28>
|   | `-VarDecl 0x560375aa6398 <col:3, col:16> col:16 used __cil_tmp98 'unsigned int'
|   |-DeclStmt 0x560375aa6498 <line:128:3, col:28>
|   | `-VarDecl 0x560375aa6430 <col:3, col:16> col:16 used __cil_tmp99 'unsigned int'
|   |-DeclStmt 0x560375aa6540 <line:129:3, col:34>
|   | `-VarDecl 0x560375aa64d8 <col:3, col:21> col:21 used __cil_tmp100 'struct list_head *'
|   |-DeclStmt 0x560375aa65e8 <line:130:3, col:34>
|   | `-VarDecl 0x560375aa6580 <col:3, col:21> col:21 used __cil_tmp101 'struct list_head *'
|   |-DeclStmt 0x560375aa6680 <line:131:3, col:29>
|   | `-VarDecl 0x560375aa6618 <col:3, col:16> col:16 used __cil_tmp102 'unsigned int'
|   |-DeclStmt 0x560375aa6718 <line:132:3, col:29>
|   | `-VarDecl 0x560375aa66b0 <col:3, col:16> col:16 used __cil_tmp103 'unsigned int'
|   |-DeclStmt 0x560375aa67b0 <line:133:3, col:20>
|   | `-VarDecl 0x560375aa6748 <col:3, col:7> col:7 used __cil_tmp104 'int'
|   |-DeclStmt 0x560375aa6858 <line:134:3, col:34>
|   | `-VarDecl 0x560375aa67f0 <col:3, col:21> col:21 used __cil_tmp105 'struct list_head *'
|   |-DeclStmt 0x560375aa68f0 <line:135:3, col:29>
|   | `-VarDecl 0x560375aa6888 <col:3, col:16> col:16 used __cil_tmp106 'unsigned int'
|   |-DeclStmt 0x560375aa6988 <line:136:3, col:29>
|   | `-VarDecl 0x560375aa6920 <col:3, col:16> col:16 used __cil_tmp107 'unsigned int'
|   |-DeclStmt 0x560375aa6a20 <line:137:3, col:29>
|   | `-VarDecl 0x560375aa69b8 <col:3, col:16> col:16 used __cil_tmp108 'unsigned int'
|   |-DeclStmt 0x560375aa7308 <line:138:3, col:42>
|   | `-VarDecl 0x560375aa72a0 <col:3, col:29> col:29 used __cil_tmp109 'const struct list_head *'
|   |-DeclStmt 0x560375aa73a0 <line:139:3, col:29>
|   | `-VarDecl 0x560375aa7338 <col:3, col:16> col:16 used __cil_tmp110 'unsigned int'
|   |-DeclStmt 0x560375aa7448 <line:140:3, col:34>
|   | `-VarDecl 0x560375aa73e0 <col:3, col:21> col:21 used __cil_tmp111 'struct list_head *'
|   |-DeclStmt 0x560375aa74e0 <line:141:3, col:29>
|   | `-VarDecl 0x560375aa7478 <col:3, col:16> col:16 used __cil_tmp112 'unsigned int'
|   |-DeclStmt 0x560375aa7588 <line:142:3, col:29>
|   | `-VarDecl 0x560375aa7520 <col:3, col:16> col:16 used __cil_tmp113 'struct node *'
|   |-DeclStmt 0x560375aa7620 <line:143:3, col:29>
|   | `-VarDecl 0x560375aa75b8 <col:3, col:16> col:16 used __cil_tmp114 'unsigned int'
|   |-DeclStmt 0x560375aa76b8 <line:144:3, col:29>
|   | `-VarDecl 0x560375aa7650 <col:3, col:16> col:16 used __cil_tmp115 'unsigned int'
|   |-DeclStmt 0x560375aa7760 <line:145:3, col:34>
|   | `-VarDecl 0x560375aa76f8 <col:3, col:21> col:21 used __cil_tmp116 'struct list_head *'
|   |-DeclStmt 0x560375aa77f8 <line:146:3, col:30>
|   | `-VarDecl 0x560375aa7790 <col:3, col:17> col:17 used __cil_tmp117 'unsigned long'
|   |-DeclStmt 0x560375aa7890 <line:147:3, col:22>
|   | `-VarDecl 0x560375aa7828 <col:3, col:9> col:9 used __cil_tmp118 'char *'
|   |-DeclStmt 0x560375aa7928 <line:148:3, col:22>
|   | `-VarDecl 0x560375aa78c0 <col:3, col:9> col:9 used __cil_tmp119 'char *'
|   |-DeclStmt 0x560375aa79d0 <line:149:3, col:29>
|   | `-VarDecl 0x560375aa7968 <col:3, col:16> col:16 used __cil_tmp120 'struct node *'
|   |-DeclStmt 0x560375aa7a68 <line:150:3, col:29>
|   | `-VarDecl 0x560375aa7a00 <col:3, col:16> col:16 used __cil_tmp121 'unsigned int'
|   |-DeclStmt 0x560375aa7b00 <line:151:3, col:20>
|   | `-VarDecl 0x560375aa7a98 <col:3, col:7> col:7 used __cil_tmp122 'int'
|   `-CompoundStmt 0x560375ab3a60 <line:153:3, line:558:1>
|     |-CompoundStmt 0x560375aa7db0 <line:154:3, line:167:3>
|     | |-WhileStmt 0x560375aa7d78 <line:155:3, line:165:3>
|     | | |-IntegerLiteral 0x560375aa7b18 <line:155:10> 'int' 1
|     | | `-CompoundStmt 0x560375aa7d50 <col:13, line:165:3>
|     | |   |-LabelStmt 0x560375aa7b90 <line:156:5, col:39> 'while_0_continue'
|     | |   | `-NullStmt 0x560375aa7b38 <col:39>
|     | |   |-IfStmt 0x560375aa7cc0 <line:157:5, line:163:5> has_else
|     | |   | |-UnaryOperator 0x560375aa7be0 <line:157:9, col:11> 'int' prefix '!' cannot overflow
|     | |   | | `-ImplicitCastExpr 0x560375aa7bc8 <col:11> 'const struct list_head *' <LValueToRValue>
|     | |   | |   `-DeclRefExpr 0x560375aa7ba8 <col:11> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-CompoundStmt 0x560375aa7c98 <col:17, line:161:5>
|     | |   | | `-CompoundStmt 0x560375aa7c80 <line:158:7, line:160:7>
|     | |   | |   `-CallExpr 0x560375aa7c60 <line:159:7, col:12> 'void'
|     | |   | |     `-ImplicitCastExpr 0x560375aa7c48 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   | |       `-DeclRefExpr 0x560375aa7bf8 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   | `-CompoundStmt 0x560375aa7cb0 <line:161:12, line:163:5>
|     | |   `-GotoStmt 0x560375aa7d38 <line:164:5, col:10> 'while_0_break' 0x560375aa7ce8
|     | `-LabelStmt 0x560375aa7d98 <line:166:3, col:34> 'while_0_break'
|     |   `-NullStmt 0x560375aa7d90 <col:34>
|     |-CompoundStmt 0x560375aa9660 <line:168:3, line:187:3>
|     | |-WhileStmt 0x560375aa9628 <line:169:3, line:185:3>
|     | | |-IntegerLiteral 0x560375aa7dd0 <line:169:10> 'int' 1
|     | | `-CompoundStmt 0x560375aa9600 <col:13, line:185:3>
|     | |   |-LabelStmt 0x560375aa7e48 <line:170:5, col:39> 'while_1_continue'
|     | |   | `-NullStmt 0x560375aa7df0 <col:39>
|     | |   |-CompoundStmt 0x560375aa9560 <line:171:5, line:183:5>
|     | |   | |-BinaryOperator 0x560375aa7ef8 <line:172:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aa7e60 <col:5> 'unsigned int' lvalue Var 0x560375a9c8a8 '__cil_tmp3' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aa7ed0 <col:18, col:33> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aa7eb8 <col:33> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aa7e80 <col:33> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aa80d0 <line:173:5, col:53> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aa7f18 <col:5> 'struct list_head *' lvalue Var 0x560375a9c950 '__cil_tmp4' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375aa80b8 <col:18, col:53> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375aa80a0 <col:18, col:53> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375aa8080 <col:19, col:53> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375aa8058 <col:20, col:49> 'struct list_head *const *' <BitCast>
|     | |   | |         `-ImplicitCastExpr 0x560375aa8040 <col:49> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375aa7f98 <col:49> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aa8188 <line:174:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aa80f0 <col:5> 'unsigned int' lvalue Var 0x560375aa1a40 '__cil_tmp5' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aa8160 <col:18, col:33> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aa8148 <col:33> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aa8110 <col:33> 'struct list_head *' lvalue Var 0x560375a9c950 '__cil_tmp4' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375aa8258 <line:175:5, col:32> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aa81a8 <col:5> 'int' lvalue Var 0x560375aa1ad8 '__cil_tmp6' 'int'
|     | |   | | `-BinaryOperator 0x560375aa8238 <col:18, col:32> 'int' '!='
|     | |   | |   |-ImplicitCastExpr 0x560375aa8208 <col:18> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aa81c8 <col:18> 'unsigned int' lvalue Var 0x560375aa1a40 '__cil_tmp5' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aa8220 <col:32> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aa81e8 <col:32> 'unsigned int' lvalue Var 0x560375a9c8a8 '__cil_tmp3' 'unsigned int'
|     | |   | `-IfStmt 0x560375aa9538 <line:176:5, line:182:5> has_else
|     | |   |   |-UnaryOperator 0x560375aa9488 <line:176:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aa9470 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aa8278 <col:11> 'int' lvalue Var 0x560375aa1ad8 '__cil_tmp6' 'int'
|     | |   |   |-CompoundStmt 0x560375aa9510 <col:23, line:180:5>
|     | |   |   | `-CompoundStmt 0x560375aa94f8 <line:177:7, line:179:7>
|     | |   |   |   `-CallExpr 0x560375aa94d8 <line:178:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aa94c0 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aa94a0 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aa9528 <line:180:12, line:182:5>
|     | |   `-GotoStmt 0x560375aa95e8 <line:184:5, col:10> 'while_1_break' 0x560375aa9598
|     | `-LabelStmt 0x560375aa9648 <line:186:3, col:34> 'while_1_break'
|     |   `-NullStmt 0x560375aa9640 <col:34>
|     |-CompoundStmt 0x560375aa9e10 <line:188:3, line:209:3>
|     | |-WhileStmt 0x560375aa9dd8 <line:189:3, line:207:3>
|     | | |-IntegerLiteral 0x560375aa9680 <line:189:10> 'int' 1
|     | | `-CompoundStmt 0x560375aa9db0 <col:13, line:207:3>
|     | |   |-LabelStmt 0x560375aa96f8 <line:190:5, col:39> 'while_2_continue'
|     | |   | `-NullStmt 0x560375aa96a0 <col:39>
|     | |   |-CompoundStmt 0x560375aa9d00 <line:191:5, line:205:5>
|     | |   | |-BinaryOperator 0x560375aa97a8 <line:192:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aa9710 <col:5> 'unsigned int' lvalue Var 0x560375aa1b70 '__cil_tmp7' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aa9780 <col:18, col:33> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aa9768 <col:33> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aa9730 <col:33> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aa9860 <line:193:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aa97c8 <col:5> 'unsigned int' lvalue Var 0x560375aa1c08 '__cil_tmp8' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aa9838 <col:18, col:33> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aa9820 <col:33> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aa97e8 <col:33> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aa9930 <line:194:5, col:31> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aa9880 <col:5> 'unsigned int' lvalue Var 0x560375aa1ca0 '__cil_tmp9' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aa9910 <col:18, col:31> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aa98e0 <col:18> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aa98a0 <col:18> 'unsigned int' lvalue Var 0x560375aa1c08 '__cil_tmp8' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aa98f8 <col:31> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aa98c0 <col:31> 'int' 4
|     | |   | |-BinaryOperator 0x560375aa9a48 <line:195:5, col:60> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aa9950 <col:5> 'struct list_head *' lvalue Var 0x560375aa1d48 '__cil_tmp10' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375aa9a30 <col:19, col:60> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375aa9a18 <col:19, col:60> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375aa99f8 <col:20, col:60> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375aa99d0 <col:21, col:50> 'struct list_head *const *' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375aa99b8 <col:50> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375aa9970 <col:50> 'unsigned int' lvalue Var 0x560375aa1ca0 '__cil_tmp9' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aa9b00 <line:196:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aa9a68 <col:5> 'unsigned int' lvalue Var 0x560375aa1de0 '__cil_tmp11' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aa9ad8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aa9ac0 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aa9a88 <col:34> 'struct list_head *' lvalue Var 0x560375aa1d48 '__cil_tmp10' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375aa9bd0 <line:197:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aa9b20 <col:5> 'int' lvalue Var 0x560375aa1e78 '__cil_tmp12' 'int'
|     | |   | | `-BinaryOperator 0x560375aa9bb0 <col:19, col:34> 'int' '!='
|     | |   | |   |-ImplicitCastExpr 0x560375aa9b80 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aa9b40 <col:19> 'unsigned int' lvalue Var 0x560375aa1de0 '__cil_tmp11' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aa9b98 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aa9b60 <col:34> 'unsigned int' lvalue Var 0x560375aa1b70 '__cil_tmp7' 'unsigned int'
|     | |   | `-IfStmt 0x560375aa9cd8 <line:198:5, line:204:5> has_else
|     | |   |   |-UnaryOperator 0x560375aa9c28 <line:198:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aa9c10 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aa9bf0 <col:11> 'int' lvalue Var 0x560375aa1e78 '__cil_tmp12' 'int'
|     | |   |   |-CompoundStmt 0x560375aa9cb0 <col:24, line:202:5>
|     | |   |   | `-CompoundStmt 0x560375aa9c98 <line:199:7, line:201:7>
|     | |   |   |   `-CallExpr 0x560375aa9c78 <line:200:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aa9c60 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aa9c40 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aa9cc8 <line:202:12, line:204:5>
|     | |   `-GotoStmt 0x560375aa9d98 <line:206:5, col:10> 'while_2_break' 0x560375aa9d48
|     | `-LabelStmt 0x560375aa9df8 <line:208:3, col:34> 'while_2_break'
|     |   `-NullStmt 0x560375aa9df0 <col:34>
|     |-BinaryOperator 0x560375aa9ec8 <line:210:3, col:32> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375aa9e30 <col:3> 'unsigned int' lvalue Var 0x560375aa1f10 '__cil_tmp13' 'unsigned int'
|     | `-CStyleCastExpr 0x560375aa9ea0 <col:17, col:32> 'unsigned int' <PointerToIntegral>
|     |   `-ImplicitCastExpr 0x560375aa9e88 <col:32> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375aa9e50 <col:32> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     |-BinaryOperator 0x560375aa9f98 <line:211:3, col:31> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375aa9ee8 <col:3> 'unsigned int' lvalue Var 0x560375aa1fa8 '__cil_tmp14' 'unsigned int'
|     | `-BinaryOperator 0x560375aa9f78 <col:17, col:31> 'unsigned int' '+'
|     |   |-ImplicitCastExpr 0x560375aa9f48 <col:17> 'unsigned int' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375aa9f08 <col:17> 'unsigned int' lvalue Var 0x560375aa1f10 '__cil_tmp13' 'unsigned int'
|     |   `-ImplicitCastExpr 0x560375aa9f60 <col:31> 'unsigned int' <IntegralCast>
|     |     `-IntegerLiteral 0x560375aa9f28 <col:31> 'int' 4
|     |-BinaryOperator 0x560375aaa0b0 <line:212:3, col:59> 'struct list_head *' '='
|     | |-DeclRefExpr 0x560375aa9fb8 <col:3> 'struct list_head *' lvalue Var 0x560375aa2050 '__cil_tmp15' 'struct list_head *'
|     | `-ImplicitCastExpr 0x560375aaa098 <col:17, col:59> 'struct list_head *' <LValueToRValue>
|     |   `-UnaryOperator 0x560375aaa080 <col:17, col:59> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     |     `-ParenExpr 0x560375aaa060 <col:18, col:59> 'struct list_head *const *'
|     |       `-CStyleCastExpr 0x560375aaa038 <col:19, col:48> 'struct list_head *const *' <IntegralToPointer>
|     |         `-ImplicitCastExpr 0x560375aaa020 <col:48> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     |           `-DeclRefExpr 0x560375aa9fd8 <col:48> 'unsigned int' lvalue Var 0x560375aa1fa8 '__cil_tmp14' 'unsigned int'
|     |-BinaryOperator 0x560375aaa178 <line:213:3, col:38> 'const struct list_head *' '='
|     | |-DeclRefExpr 0x560375aaa0d0 <col:3> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | `-CStyleCastExpr 0x560375aaa150 <col:10, col:38> 'const struct list_head *' <NoOp>
|     |   `-ImplicitCastExpr 0x560375aaa138 <col:38> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375aaa0f0 <col:38> 'struct list_head *' lvalue Var 0x560375aa2050 '__cil_tmp15' 'struct list_head *'
|     |-CompoundStmt 0x560375aaa400 <line:214:3, line:227:3>
|     | |-WhileStmt 0x560375aaa3c8 <line:215:3, line:225:3>
|     | | |-IntegerLiteral 0x560375aaa198 <line:215:10> 'int' 1
|     | | `-CompoundStmt 0x560375aaa3a0 <col:13, line:225:3>
|     | |   |-LabelStmt 0x560375aaa210 <line:216:5, col:39> 'while_3_continue'
|     | |   | `-NullStmt 0x560375aaa1b8 <col:39>
|     | |   |-IfStmt 0x560375aaa310 <line:217:5, line:223:5> has_else
|     | |   | |-UnaryOperator 0x560375aaa260 <line:217:9, col:11> 'int' prefix '!' cannot overflow
|     | |   | | `-ImplicitCastExpr 0x560375aaa248 <col:11> 'const struct list_head *' <LValueToRValue>
|     | |   | |   `-DeclRefExpr 0x560375aaa228 <col:11> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-CompoundStmt 0x560375aaa2e8 <col:17, line:221:5>
|     | |   | | `-CompoundStmt 0x560375aaa2d0 <line:218:7, line:220:7>
|     | |   | |   `-CallExpr 0x560375aaa2b0 <line:219:7, col:12> 'void'
|     | |   | |     `-ImplicitCastExpr 0x560375aaa298 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   | |       `-DeclRefExpr 0x560375aaa278 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   | `-CompoundStmt 0x560375aaa300 <line:221:12, line:223:5>
|     | |   `-GotoStmt 0x560375aaa388 <line:224:5, col:10> 'while_3_break' 0x560375aaa338
|     | `-LabelStmt 0x560375aaa3e8 <line:226:3, col:34> 'while_3_break'
|     |   `-NullStmt 0x560375aaa3e0 <col:34>
|     |-CompoundStmt 0x560375aaacf0 <line:228:3, line:247:3>
|     | |-WhileStmt 0x560375aaacb8 <line:229:3, line:245:3>
|     | | |-IntegerLiteral 0x560375aaa420 <line:229:10> 'int' 1
|     | | `-CompoundStmt 0x560375aaac90 <col:13, line:245:3>
|     | |   |-LabelStmt 0x560375aaa770 <line:230:5, col:39> 'while_4_continue'
|     | |   | `-NullStmt 0x560375aaa440 <col:39>
|     | |   |-CompoundStmt 0x560375aaabf0 <line:231:5, line:243:5>
|     | |   | |-BinaryOperator 0x560375aaa820 <line:232:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaa788 <col:5> 'unsigned int' lvalue Var 0x560375aa20e8 '__cil_tmp16' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaa7f8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaa7e0 <col:34> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaa7a8 <col:34> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aaa938 <line:233:5, col:54> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aaa840 <col:5> 'struct list_head *' lvalue Var 0x560375aa2190 '__cil_tmp17' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375aaa920 <col:19, col:54> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375aaa908 <col:19, col:54> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375aaa8e8 <col:20, col:54> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375aaa8c0 <col:21, col:50> 'struct list_head *const *' <BitCast>
|     | |   | |         `-ImplicitCastExpr 0x560375aaa8a8 <col:50> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375aaa860 <col:50> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aaa9f0 <line:234:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaa958 <col:5> 'unsigned int' lvalue Var 0x560375aa2228 '__cil_tmp18' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaa9c8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaa9b0 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaa978 <col:34> 'struct list_head *' lvalue Var 0x560375aa2190 '__cil_tmp17' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375aaaac0 <line:235:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aaaa10 <col:5> 'int' lvalue Var 0x560375aa22c0 '__cil_tmp19' 'int'
|     | |   | | `-BinaryOperator 0x560375aaaaa0 <col:19, col:34> 'int' '!='
|     | |   | |   |-ImplicitCastExpr 0x560375aaaa70 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aaaa30 <col:19> 'unsigned int' lvalue Var 0x560375aa2228 '__cil_tmp18' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aaaa88 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aaaa50 <col:34> 'unsigned int' lvalue Var 0x560375aa20e8 '__cil_tmp16' 'unsigned int'
|     | |   | `-IfStmt 0x560375aaabc8 <line:236:5, line:242:5> has_else
|     | |   |   |-UnaryOperator 0x560375aaab18 <line:236:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aaab00 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aaaae0 <col:11> 'int' lvalue Var 0x560375aa22c0 '__cil_tmp19' 'int'
|     | |   |   |-CompoundStmt 0x560375aaaba0 <col:24, line:240:5>
|     | |   |   | `-CompoundStmt 0x560375aaab88 <line:237:7, line:239:7>
|     | |   |   |   `-CallExpr 0x560375aaab68 <line:238:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aaab50 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aaab30 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aaabb8 <line:240:12, line:242:5>
|     | |   `-GotoStmt 0x560375aaac78 <line:244:5, col:10> 'while_4_break' 0x560375aaac28
|     | `-LabelStmt 0x560375aaacd8 <line:246:3, col:34> 'while_4_break'
|     |   `-NullStmt 0x560375aaacd0 <col:34>
|     |-CompoundStmt 0x560375aab4a0 <line:248:3, line:269:3>
|     | |-WhileStmt 0x560375aab468 <line:249:3, line:267:3>
|     | | |-IntegerLiteral 0x560375aaad10 <line:249:10> 'int' 1
|     | | `-CompoundStmt 0x560375aab440 <col:13, line:267:3>
|     | |   |-LabelStmt 0x560375aaad88 <line:250:5, col:39> 'while_5_continue'
|     | |   | `-NullStmt 0x560375aaad30 <col:39>
|     | |   |-CompoundStmt 0x560375aab390 <line:251:5, line:265:5>
|     | |   | |-BinaryOperator 0x560375aaae38 <line:252:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaada0 <col:5> 'unsigned int' lvalue Var 0x560375aa2358 '__cil_tmp20' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaae10 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaadf8 <col:34> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaadc0 <col:34> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aaaef0 <line:253:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaae58 <col:5> 'unsigned int' lvalue Var 0x560375aa23f0 '__cil_tmp21' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaaec8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaaeb0 <col:34> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaae78 <col:34> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aaafc0 <line:254:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaaf10 <col:5> 'unsigned int' lvalue Var 0x560375aa2488 '__cil_tmp22' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aaafa0 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aaaf70 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aaaf30 <col:19> 'unsigned int' lvalue Var 0x560375aa23f0 '__cil_tmp21' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aaaf88 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aaaf50 <col:33> 'int' 4
|     | |   | |-BinaryOperator 0x560375aab0d8 <line:255:5, col:61> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aaafe0 <col:5> 'struct list_head *' lvalue Var 0x560375aa2530 '__cil_tmp23' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375aab0c0 <col:19, col:61> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375aab0a8 <col:19, col:61> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375aab088 <col:20, col:61> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375aab060 <col:21, col:50> 'struct list_head *const *' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375aab048 <col:50> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375aab000 <col:50> 'unsigned int' lvalue Var 0x560375aa2488 '__cil_tmp22' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aab190 <line:256:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aab0f8 <col:5> 'unsigned int' lvalue Var 0x560375aa25c8 '__cil_tmp24' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aab168 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aab150 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aab118 <col:34> 'struct list_head *' lvalue Var 0x560375aa2530 '__cil_tmp23' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375aab260 <line:257:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aab1b0 <col:5> 'int' lvalue Var 0x560375aa2660 '__cil_tmp25' 'int'
|     | |   | | `-BinaryOperator 0x560375aab240 <col:19, col:34> 'int' '!='
|     | |   | |   |-ImplicitCastExpr 0x560375aab210 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aab1d0 <col:19> 'unsigned int' lvalue Var 0x560375aa25c8 '__cil_tmp24' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aab228 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aab1f0 <col:34> 'unsigned int' lvalue Var 0x560375aa2358 '__cil_tmp20' 'unsigned int'
|     | |   | `-IfStmt 0x560375aab368 <line:258:5, line:264:5> has_else
|     | |   |   |-UnaryOperator 0x560375aab2b8 <line:258:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aab2a0 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aab280 <col:11> 'int' lvalue Var 0x560375aa2660 '__cil_tmp25' 'int'
|     | |   |   |-CompoundStmt 0x560375aab340 <col:24, line:262:5>
|     | |   |   | `-CompoundStmt 0x560375aab328 <line:259:7, line:261:7>
|     | |   |   |   `-CallExpr 0x560375aab308 <line:260:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aab2f0 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aab2d0 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aab358 <line:262:12, line:264:5>
|     | |   `-GotoStmt 0x560375aab428 <line:266:5, col:10> 'while_5_break' 0x560375aab3d8
|     | `-LabelStmt 0x560375aab488 <line:268:3, col:34> 'while_5_break'
|     |   `-NullStmt 0x560375aab480 <col:34>
|     |-BinaryOperator 0x560375aab550 <line:270:3, col:32> 'struct node *' '='
|     | |-DeclRefExpr 0x560375aab4c0 <col:3> 'struct node *' lvalue Var 0x560375aa2760 '__cil_tmp26' 'struct node *'
|     | `-CStyleCastExpr 0x560375aab528 <col:17, col:32> 'struct node *' <NullToPointer>
|     |   `-IntegerLiteral 0x560375aab4e0 <col:32> 'int' 0
|     |-BinaryOperator 0x560375aab608 <line:271:3, col:32> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375aab570 <col:3> 'unsigned int' lvalue Var 0x560375aa27f8 '__cil_tmp27' 'unsigned int'
|     | `-CStyleCastExpr 0x560375aab5e0 <col:17, col:32> 'unsigned int' <PointerToIntegral>
|     |   `-ImplicitCastExpr 0x560375aab5c8 <col:32> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375aab590 <col:32> 'struct node *' lvalue Var 0x560375aa2760 '__cil_tmp26' 'struct node *'
|     |-BinaryOperator 0x560375aab6d8 <line:272:3, col:31> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375aab628 <col:3> 'unsigned int' lvalue Var 0x560375aa2890 '__cil_tmp28' 'unsigned int'
|     | `-BinaryOperator 0x560375aab6b8 <col:17, col:31> 'unsigned int' '+'
|     |   |-ImplicitCastExpr 0x560375aab688 <col:17> 'unsigned int' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375aab648 <col:17> 'unsigned int' lvalue Var 0x560375aa27f8 '__cil_tmp27' 'unsigned int'
|     |   `-ImplicitCastExpr 0x560375aab6a0 <col:31> 'unsigned int' <IntegralCast>
|     |     `-IntegerLiteral 0x560375aab668 <col:31> 'int' 4
|     |-BinaryOperator 0x560375aab858 <line:273:3, col:37> 'struct list_head *' '='
|     | |-DeclRefExpr 0x560375aab6f8 <col:3> 'struct list_head *' lvalue Var 0x560375aa2938 '__cil_tmp29' 'struct list_head *'
|     | `-CStyleCastExpr 0x560375aab830 <col:17, col:37> 'struct list_head *' <IntegralToPointer>
|     |   `-ImplicitCastExpr 0x560375aab818 <col:37> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375aab7d0 <col:37> 'unsigned int' lvalue Var 0x560375aa2890 '__cil_tmp28' 'unsigned int'
|     |-BinaryOperator 0x560375aab910 <line:274:3, col:33> 'unsigned long' '='
|     | |-DeclRefExpr 0x560375aab878 <col:3> 'unsigned long' lvalue Var 0x560375aa29d0 '__cil_tmp30' 'unsigned long'
|     | `-CStyleCastExpr 0x560375aab8e8 <col:17, col:33> 'unsigned long' <PointerToIntegral>
|     |   `-ImplicitCastExpr 0x560375aab8d0 <col:33> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375aab898 <col:33> 'struct list_head *' lvalue Var 0x560375aa2938 '__cil_tmp29' 'struct list_head *'
|     |-BinaryOperator 0x560375aab9c8 <line:275:3, col:25> 'char *' '='
|     | |-DeclRefExpr 0x560375aab930 <col:3> 'char *' lvalue Var 0x560375aa2a80 '__cil_tmp31' 'char *'
|     | `-CStyleCastExpr 0x560375aab9a0 <col:17, col:25> 'char *' <BitCast>
|     |   `-ImplicitCastExpr 0x560375aab988 <col:25> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375aab950 <col:25> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     |-BinaryOperator 0x560375aaba98 <line:276:3, col:31> 'char *' '='
|     | |-DeclRefExpr 0x560375aab9e8 <col:3> 'char *' lvalue Var 0x560375aa2b18 '__cil_tmp32' 'char *'
|     | `-BinaryOperator 0x560375aaba78 <col:17, col:31> 'char *' '-'
|     |   |-ImplicitCastExpr 0x560375aaba48 <col:17> 'char *' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375aaba08 <col:17> 'char *' lvalue Var 0x560375aa2a80 '__cil_tmp31' 'char *'
|     |   `-ImplicitCastExpr 0x560375aaba60 <col:31> 'unsigned long' <LValueToRValue>
|     |     `-DeclRefExpr 0x560375aaba28 <col:31> 'unsigned long' lvalue Var 0x560375aa29d0 '__cil_tmp30' 'unsigned long'
|     |-BinaryOperator 0x560375aabb60 <line:277:3, col:32> 'struct node *' '='
|     | |-DeclRefExpr 0x560375aabab8 <col:3> 'struct node *' lvalue Var 0x560375aa2bc0 '__cil_tmp33' 'struct node *'
|     | `-CStyleCastExpr 0x560375aabb38 <col:17, col:32> 'struct node *' <BitCast>
|     |   `-ImplicitCastExpr 0x560375aabb20 <col:32> 'char *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375aabad8 <col:32> 'char *' lvalue Var 0x560375aa2b18 '__cil_tmp32' 'char *'
|     |-BinaryOperator 0x560375aabc28 <line:278:3, col:33> 'const struct node *' '='
|     | |-DeclRefExpr 0x560375aabb80 <col:3> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | `-CStyleCastExpr 0x560375aabc00 <col:10, col:33> 'const struct node *' <NoOp>
|     |   `-ImplicitCastExpr 0x560375aabbe8 <col:33> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375aabba0 <col:33> 'struct node *' lvalue Var 0x560375aa2bc0 '__cil_tmp33' 'struct node *'
|     |-CompoundStmt 0x560375aabeb0 <line:279:3, line:292:3>
|     | |-WhileStmt 0x560375aabe78 <line:280:3, line:290:3>
|     | | |-IntegerLiteral 0x560375aabc48 <line:280:10> 'int' 1
|     | | `-CompoundStmt 0x560375aabe50 <col:13, line:290:3>
|     | |   |-LabelStmt 0x560375aabcc0 <line:281:5, col:39> 'while_6_continue'
|     | |   | `-NullStmt 0x560375aabc68 <col:39>
|     | |   |-IfStmt 0x560375aabdc0 <line:282:5, line:288:5> has_else
|     | |   | |-UnaryOperator 0x560375aabd10 <line:282:9, col:11> 'int' prefix '!' cannot overflow
|     | |   | | `-ImplicitCastExpr 0x560375aabcf8 <col:11> 'const struct node *' <LValueToRValue>
|     | |   | |   `-DeclRefExpr 0x560375aabcd8 <col:11> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-CompoundStmt 0x560375aabd98 <col:17, line:286:5>
|     | |   | | `-CompoundStmt 0x560375aabd80 <line:283:7, line:285:7>
|     | |   | |   `-CallExpr 0x560375aabd60 <line:284:7, col:12> 'void'
|     | |   | |     `-ImplicitCastExpr 0x560375aabd48 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   | |       `-DeclRefExpr 0x560375aabd28 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   | `-CompoundStmt 0x560375aabdb0 <line:286:12, line:288:5>
|     | |   `-GotoStmt 0x560375aabe38 <line:289:5, col:10> 'while_6_break' 0x560375aabde8
|     | `-LabelStmt 0x560375aabe98 <line:291:3, col:34> 'while_6_break'
|     |   `-NullStmt 0x560375aabe90 <col:34>
|     |-CompoundStmt 0x560375aac908 <line:293:3, line:317:3>
|     | |-WhileStmt 0x560375aac8d0 <line:294:3, line:315:3>
|     | | |-IntegerLiteral 0x560375aabed0 <line:294:10> 'int' 1
|     | | `-CompoundStmt 0x560375aac8a8 <col:13, line:315:3>
|     | |   |-LabelStmt 0x560375aabf48 <line:295:5, col:39> 'while_7_continue'
|     | |   | `-NullStmt 0x560375aabef0 <col:39>
|     | |   |-CompoundStmt 0x560375aac7e0 <line:296:5, line:313:5>
|     | |   | |-BinaryOperator 0x560375aabff8 <line:297:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aabf60 <col:5> 'unsigned int' lvalue Var 0x560375aa2c58 '__cil_tmp34' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aabfd0 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aabfb8 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aabf80 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aac0c8 <line:298:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aac018 <col:5> 'unsigned int' lvalue Var 0x560375aa2cf0 '__cil_tmp35' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aac0a8 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aac078 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aac038 <col:19> 'unsigned int' lvalue Var 0x560375aa2c58 '__cil_tmp34' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aac090 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aac058 <col:33> 'int' 12
|     | |   | |-BinaryOperator 0x560375aac190 <line:299:5, col:47> 'const struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aac0e8 <col:5> 'const struct list_head *' lvalue Var 0x560375aa2d98 '__cil_tmp36' 'const struct list_head *'
|     | |   | | `-CStyleCastExpr 0x560375aac168 <col:19, col:47> 'const struct list_head *' <IntegralToPointer>
|     | |   | |   `-ImplicitCastExpr 0x560375aac150 <col:47> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aac108 <col:47> 'unsigned int' lvalue Var 0x560375aa2cf0 '__cil_tmp35' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aac248 <line:300:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aac1b0 <col:5> 'unsigned int' lvalue Var 0x560375aa2e30 '__cil_tmp37' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aac220 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aac208 <col:34> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aac1d0 <col:34> 'const struct list_head *' lvalue Var 0x560375aa2d98 '__cil_tmp36' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aac300 <line:301:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aac268 <col:5> 'unsigned int' lvalue Var 0x560375aa2ec8 '__cil_tmp38' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aac2d8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aac2c0 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aac288 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aac3d0 <line:302:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aac320 <col:5> 'unsigned int' lvalue Var 0x560375aa2f60 '__cil_tmp39' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aac3b0 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aac380 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aac340 <col:19> 'unsigned int' lvalue Var 0x560375aa2ec8 '__cil_tmp38' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aac398 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aac360 <col:33> 'int' 12
|     | |   | |-BinaryOperator 0x560375aac4e8 <line:303:5, col:61> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aac3f0 <col:5> 'struct list_head *' lvalue Var 0x560375aa3008 '__cil_tmp40' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375aac4d0 <col:19, col:61> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375aac4b8 <col:19, col:61> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375aac498 <col:20, col:61> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375aac470 <col:21, col:50> 'struct list_head *const *' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375aac458 <col:50> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375aac410 <col:50> 'unsigned int' lvalue Var 0x560375aa2f60 '__cil_tmp39' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aac5a0 <line:304:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aac508 <col:5> 'unsigned int' lvalue Var 0x560375aa30a0 '__cil_tmp41' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aac578 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aac560 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aac528 <col:34> 'struct list_head *' lvalue Var 0x560375aa3008 '__cil_tmp40' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375aac670 <line:305:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aac5c0 <col:5> 'int' lvalue Var 0x560375aa3138 '__cil_tmp42' 'int'
|     | |   | | `-BinaryOperator 0x560375aac650 <col:19, col:34> 'int' '=='
|     | |   | |   |-ImplicitCastExpr 0x560375aac620 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aac5e0 <col:19> 'unsigned int' lvalue Var 0x560375aa30a0 '__cil_tmp41' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aac638 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aac600 <col:34> 'unsigned int' lvalue Var 0x560375aa2e30 '__cil_tmp37' 'unsigned int'
|     | |   | `-IfStmt 0x560375aac778 <line:306:5, line:312:5> has_else
|     | |   |   |-UnaryOperator 0x560375aac6c8 <line:306:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aac6b0 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aac690 <col:11> 'int' lvalue Var 0x560375aa3138 '__cil_tmp42' 'int'
|     | |   |   |-CompoundStmt 0x560375aac750 <col:24, line:310:5>
|     | |   |   | `-CompoundStmt 0x560375aac738 <line:307:7, line:309:7>
|     | |   |   |   `-CallExpr 0x560375aac718 <line:308:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aac700 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aac6e0 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aac768 <line:310:12, line:312:5>
|     | |   `-GotoStmt 0x560375aac890 <line:314:5, col:10> 'while_7_break' 0x560375aac840
|     | `-LabelStmt 0x560375aac8f0 <line:316:3, col:34> 'while_7_break'
|     |   `-NullStmt 0x560375aac8e8 <col:34>
|     |-CompoundStmt 0x560375aad3e0 <line:318:3, line:343:3>
|     | |-WhileStmt 0x560375aad3a8 <line:319:3, line:341:3>
|     | | |-IntegerLiteral 0x560375aac928 <line:319:10> 'int' 1
|     | | `-CompoundStmt 0x560375aad380 <col:13, line:341:3>
|     | |   |-LabelStmt 0x560375aac9a0 <line:320:5, col:39> 'while_8_continue'
|     | |   | `-NullStmt 0x560375aac948 <col:39>
|     | |   |-CompoundStmt 0x560375aad2b0 <line:321:5, line:339:5>
|     | |   | |-BinaryOperator 0x560375aaca50 <line:322:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aac9b8 <col:5> 'unsigned int' lvalue Var 0x560375aa31d0 '__cil_tmp43' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaca28 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaca10 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aac9d8 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aacb20 <line:323:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaca70 <col:5> 'unsigned int' lvalue Var 0x560375aa3268 '__cil_tmp44' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aacb00 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aacad0 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aaca90 <col:19> 'unsigned int' lvalue Var 0x560375aa31d0 '__cil_tmp43' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aacae8 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aacab0 <col:33> 'int' 12
|     | |   | |-BinaryOperator 0x560375aacbe8 <line:324:5, col:47> 'const struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aacb40 <col:5> 'const struct list_head *' lvalue Var 0x560375aa3310 '__cil_tmp45' 'const struct list_head *'
|     | |   | | `-CStyleCastExpr 0x560375aacbc0 <col:19, col:47> 'const struct list_head *' <IntegralToPointer>
|     | |   | |   `-ImplicitCastExpr 0x560375aacba8 <col:47> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aacb60 <col:47> 'unsigned int' lvalue Var 0x560375aa3268 '__cil_tmp44' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aacca0 <line:325:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aacc08 <col:5> 'unsigned int' lvalue Var 0x560375aa33a8 '__cil_tmp46' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aacc78 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aacc60 <col:34> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aacc28 <col:34> 'const struct list_head *' lvalue Var 0x560375aa3310 '__cil_tmp45' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aacd58 <line:326:5, col:24> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaccc0 <col:5> 'unsigned int' lvalue Var 0x560375aa3440 '__cil_tmp47' 'unsigned int'
|     | |   | | `-ImplicitCastExpr 0x560375aacd40 <col:19, col:24> 'unsigned int' <IntegralCast>
|     | |   | |   `-BinaryOperator 0x560375aacd20 <col:19, col:24> 'int' '+'
|     | |   | |     |-IntegerLiteral 0x560375aacce0 <col:19> 'int' 12
|     | |   | |     `-IntegerLiteral 0x560375aacd00 <col:24> 'int' 4
|     | |   | |-BinaryOperator 0x560375aace10 <line:327:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aacd78 <col:5> 'unsigned int' lvalue Var 0x560375aa34d8 '__cil_tmp48' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aacde8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aacdd0 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aacd98 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aacee0 <line:328:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aace30 <col:5> 'unsigned int' lvalue Var 0x560375aa3570 '__cil_tmp49' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aacec0 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aace90 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aace50 <col:19> 'unsigned int' lvalue Var 0x560375aa34d8 '__cil_tmp48' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aacea8 <col:33> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aace70 <col:33> 'unsigned int' lvalue Var 0x560375aa3440 '__cil_tmp47' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aacff8 <line:329:5, col:61> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aacf00 <col:5> 'struct list_head *' lvalue Var 0x560375aa3618 '__cil_tmp50' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375aacfe0 <col:19, col:61> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375aacfc8 <col:19, col:61> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375aacfa8 <col:20, col:61> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375aacf80 <col:21, col:50> 'struct list_head *const *' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375aacf68 <col:50> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375aacf20 <col:50> 'unsigned int' lvalue Var 0x560375aa3570 '__cil_tmp49' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aad0b0 <line:330:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aad018 <col:5> 'unsigned int' lvalue Var 0x560375aa36b0 '__cil_tmp51' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aad088 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aad070 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aad038 <col:34> 'struct list_head *' lvalue Var 0x560375aa3618 '__cil_tmp50' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375aad180 <line:331:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aad0d0 <col:5> 'int' lvalue Var 0x560375aa3748 '__cil_tmp52' 'int'
|     | |   | | `-BinaryOperator 0x560375aad160 <col:19, col:34> 'int' '=='
|     | |   | |   |-ImplicitCastExpr 0x560375aad130 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aad0f0 <col:19> 'unsigned int' lvalue Var 0x560375aa36b0 '__cil_tmp51' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aad148 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aad110 <col:34> 'unsigned int' lvalue Var 0x560375aa33a8 '__cil_tmp46' 'unsigned int'
|     | |   | `-IfStmt 0x560375aad288 <line:332:5, line:338:5> has_else
|     | |   |   |-UnaryOperator 0x560375aad1d8 <line:332:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aad1c0 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aad1a0 <col:11> 'int' lvalue Var 0x560375aa3748 '__cil_tmp52' 'int'
|     | |   |   |-CompoundStmt 0x560375aad260 <col:24, line:336:5>
|     | |   |   | `-CompoundStmt 0x560375aad248 <line:333:7, line:335:7>
|     | |   |   |   `-CallExpr 0x560375aad228 <line:334:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aad210 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aad1f0 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aad278 <line:336:12, line:338:5>
|     | |   `-GotoStmt 0x560375aad368 <line:340:5, col:10> 'while_8_break' 0x560375aad318
|     | `-LabelStmt 0x560375aad3c8 <line:342:3, col:34> 'while_8_break'
|     |   `-NullStmt 0x560375aad3c0 <col:34>
|     |-CompoundStmt 0x560375aade10 <line:344:3, line:368:3>
|     | |-WhileStmt 0x560375aaddd8 <line:345:3, line:366:3>
|     | | |-IntegerLiteral 0x560375aad400 <line:345:10> 'int' 1
|     | | `-CompoundStmt 0x560375aaddb0 <col:13, line:366:3>
|     | |   |-LabelStmt 0x560375aad478 <line:346:5, col:39> 'while_9_continue'
|     | |   | `-NullStmt 0x560375aad420 <col:39>
|     | |   |-CompoundStmt 0x560375aadce8 <line:347:5, line:364:5>
|     | |   | |-BinaryOperator 0x560375aad528 <line:348:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aad490 <col:5> 'unsigned int' lvalue Var 0x560375aa37e0 '__cil_tmp53' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aad500 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aad4e8 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aad4b0 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aad5f8 <line:349:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aad548 <col:5> 'unsigned int' lvalue Var 0x560375aa3878 '__cil_tmp54' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aad5d8 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aad5a8 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aad568 <col:19> 'unsigned int' lvalue Var 0x560375aa37e0 '__cil_tmp53' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aad5c0 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aad588 <col:33> 'int' 4
|     | |   | |-BinaryOperator 0x560375aad6c0 <line:350:5, col:47> 'const struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aad618 <col:5> 'const struct list_head *' lvalue Var 0x560375aa3920 '__cil_tmp55' 'const struct list_head *'
|     | |   | | `-CStyleCastExpr 0x560375aad698 <col:19, col:47> 'const struct list_head *' <IntegralToPointer>
|     | |   | |   `-ImplicitCastExpr 0x560375aad680 <col:47> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aad638 <col:47> 'unsigned int' lvalue Var 0x560375aa3878 '__cil_tmp54' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aad778 <line:351:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aad6e0 <col:5> 'unsigned int' lvalue Var 0x560375aa39b8 '__cil_tmp56' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aad750 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aad738 <col:34> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aad700 <col:34> 'const struct list_head *' lvalue Var 0x560375aa3920 '__cil_tmp55' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aad848 <line:352:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aad798 <col:5> 'unsigned int' lvalue Var 0x560375aa3a60 '__cil_tmp57' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aad820 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aad808 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aad7b8 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aad918 <line:353:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aad868 <col:5> 'unsigned int' lvalue Var 0x560375aa3af8 '__cil_tmp58' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aad8f8 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aad8c8 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aad888 <col:19> 'unsigned int' lvalue Var 0x560375aa3a60 '__cil_tmp57' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aad8e0 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aad8a8 <col:33> 'int' 12
|     | |   | |-BinaryOperator 0x560375aada30 <line:354:5, col:61> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aad938 <col:5> 'struct list_head *' lvalue Var 0x560375aa3ba0 '__cil_tmp59' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375aada18 <col:19, col:61> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375aada00 <col:19, col:61> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375aad9e0 <col:20, col:61> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375aad9b8 <col:21, col:50> 'struct list_head *const *' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375aad9a0 <col:50> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375aad958 <col:50> 'unsigned int' lvalue Var 0x560375aa3af8 '__cil_tmp58' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aadae8 <line:355:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aada50 <col:5> 'unsigned int' lvalue Var 0x560375aa3c38 '__cil_tmp60' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aadac0 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aadaa8 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aada70 <col:34> 'struct list_head *' lvalue Var 0x560375aa3ba0 '__cil_tmp59' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375aadbb8 <line:356:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aadb08 <col:5> 'int' lvalue Var 0x560375aa3cd0 '__cil_tmp61' 'int'
|     | |   | | `-BinaryOperator 0x560375aadb98 <col:19, col:34> 'int' '!='
|     | |   | |   |-ImplicitCastExpr 0x560375aadb68 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aadb28 <col:19> 'unsigned int' lvalue Var 0x560375aa3c38 '__cil_tmp60' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aadb80 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aadb48 <col:34> 'unsigned int' lvalue Var 0x560375aa39b8 '__cil_tmp56' 'unsigned int'
|     | |   | `-IfStmt 0x560375aadcc0 <line:357:5, line:363:5> has_else
|     | |   |   |-UnaryOperator 0x560375aadc10 <line:357:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aadbf8 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aadbd8 <col:11> 'int' lvalue Var 0x560375aa3cd0 '__cil_tmp61' 'int'
|     | |   |   |-CompoundStmt 0x560375aadc98 <col:24, line:361:5>
|     | |   |   | `-CompoundStmt 0x560375aadc80 <line:358:7, line:360:7>
|     | |   |   |   `-CallExpr 0x560375aadc60 <line:359:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aadc48 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aadc28 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aadcb0 <line:361:12, line:363:5>
|     | |   `-GotoStmt 0x560375aadd98 <line:365:5, col:10> 'while_9_break' 0x560375aadd48
|     | `-LabelStmt 0x560375aaddf8 <line:367:3, col:34> 'while_9_break'
|     |   `-NullStmt 0x560375aaddf0 <col:34>
|     |-CompoundStmt 0x560375aae930 <line:369:3, line:394:3>
|     | |-WhileStmt 0x560375aae8f8 <line:370:3, line:392:3>
|     | | |-IntegerLiteral 0x560375aade30 <line:370:10> 'int' 1
|     | | `-CompoundStmt 0x560375aae8d0 <col:13, line:392:3>
|     | |   |-LabelStmt 0x560375aadea8 <line:371:5, col:40> 'while_10_continue'
|     | |   | `-NullStmt 0x560375aade50 <col:40>
|     | |   |-CompoundStmt 0x560375aae800 <line:372:5, line:390:5>
|     | |   | |-BinaryOperator 0x560375aadf58 <line:373:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aadec0 <col:5> 'unsigned int' lvalue Var 0x560375aa3d68 '__cil_tmp62' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aadf30 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aadf18 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aadee0 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aae028 <line:374:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aadf78 <col:5> 'unsigned int' lvalue Var 0x560375aa3e00 '__cil_tmp63' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aae008 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aadfd8 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aadf98 <col:19> 'unsigned int' lvalue Var 0x560375aa3d68 '__cil_tmp62' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aadff0 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aadfb8 <col:33> 'int' 4
|     | |   | |-BinaryOperator 0x560375aae0f0 <line:375:5, col:47> 'const struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aae048 <col:5> 'const struct list_head *' lvalue Var 0x560375aa3ea8 '__cil_tmp64' 'const struct list_head *'
|     | |   | | `-CStyleCastExpr 0x560375aae0c8 <col:19, col:47> 'const struct list_head *' <IntegralToPointer>
|     | |   | |   `-ImplicitCastExpr 0x560375aae0b0 <col:47> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aae068 <col:47> 'unsigned int' lvalue Var 0x560375aa3e00 '__cil_tmp63' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aae1a8 <line:376:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aae110 <col:5> 'unsigned int' lvalue Var 0x560375aa3f40 '__cil_tmp65' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aae180 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aae168 <col:34> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aae130 <col:34> 'const struct list_head *' lvalue Var 0x560375aa3ea8 '__cil_tmp64' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aae260 <line:377:5, col:24> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aae1c8 <col:5> 'unsigned int' lvalue Var 0x560375aa3fd8 '__cil_tmp66' 'unsigned int'
|     | |   | | `-ImplicitCastExpr 0x560375aae248 <col:19, col:24> 'unsigned int' <IntegralCast>
|     | |   | |   `-BinaryOperator 0x560375aae228 <col:19, col:24> 'int' '+'
|     | |   | |     |-IntegerLiteral 0x560375aae1e8 <col:19> 'int' 12
|     | |   | |     `-IntegerLiteral 0x560375aae208 <col:24> 'int' 4
|     | |   | |-BinaryOperator 0x560375aae318 <line:378:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aae280 <col:5> 'unsigned int' lvalue Var 0x560375aa4070 '__cil_tmp67' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aae2f0 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aae2d8 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aae2a0 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aae3e8 <line:379:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aae338 <col:5> 'unsigned int' lvalue Var 0x560375aa4108 '__cil_tmp68' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aae3c8 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aae398 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aae358 <col:19> 'unsigned int' lvalue Var 0x560375aa4070 '__cil_tmp67' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aae3b0 <col:33> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aae378 <col:33> 'unsigned int' lvalue Var 0x560375aa3fd8 '__cil_tmp66' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aae500 <line:380:5, col:61> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aae408 <col:5> 'struct list_head *' lvalue Var 0x560375aa41b0 '__cil_tmp69' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375aae4e8 <col:19, col:61> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375aae4d0 <col:19, col:61> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375aae4b0 <col:20, col:61> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375aae488 <col:21, col:50> 'struct list_head *const *' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375aae470 <col:50> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375aae428 <col:50> 'unsigned int' lvalue Var 0x560375aa4108 '__cil_tmp68' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aae5b8 <line:381:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aae520 <col:5> 'unsigned int' lvalue Var 0x560375aa4248 '__cil_tmp70' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aae590 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aae578 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aae540 <col:34> 'struct list_head *' lvalue Var 0x560375aa41b0 '__cil_tmp69' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375aae688 <line:382:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aae5d8 <col:5> 'int' lvalue Var 0x560375aa42e0 '__cil_tmp71' 'int'
|     | |   | | `-BinaryOperator 0x560375aae668 <col:19, col:34> 'int' '!='
|     | |   | |   |-ImplicitCastExpr 0x560375aae638 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aae5f8 <col:19> 'unsigned int' lvalue Var 0x560375aa4248 '__cil_tmp70' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aae650 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aae618 <col:34> 'unsigned int' lvalue Var 0x560375aa3f40 '__cil_tmp65' 'unsigned int'
|     | |   | `-IfStmt 0x560375aae790 <line:383:5, line:389:5> has_else
|     | |   |   |-UnaryOperator 0x560375aae6e0 <line:383:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aae6c8 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aae6a8 <col:11> 'int' lvalue Var 0x560375aa42e0 '__cil_tmp71' 'int'
|     | |   |   |-CompoundStmt 0x560375aae768 <col:24, line:387:5>
|     | |   |   | `-CompoundStmt 0x560375aae750 <line:384:7, line:386:7>
|     | |   |   |   `-CallExpr 0x560375aae730 <line:385:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aae718 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aae6f8 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aae780 <line:387:12, line:389:5>
|     | |   `-GotoStmt 0x560375aae8b8 <line:391:5, col:10> 'while_10_break' 0x560375aae868
|     | `-LabelStmt 0x560375aae918 <line:393:3, col:35> 'while_10_break'
|     |   `-NullStmt 0x560375aae910 <col:35>
|     |-CompoundStmt 0x560375aaeef8 <line:395:3, line:414:3>
|     | |-WhileStmt 0x560375aaeec0 <line:396:3, line:412:3>
|     | | |-IntegerLiteral 0x560375aae950 <line:396:10> 'int' 1
|     | | `-CompoundStmt 0x560375aaee98 <col:13, line:412:3>
|     | |   |-LabelStmt 0x560375aae9c8 <line:397:5, col:40> 'while_11_continue'
|     | |   | `-NullStmt 0x560375aae970 <col:40>
|     | |   |-CompoundStmt 0x560375aaedf8 <line:398:5, line:410:5>
|     | |   | |-BinaryOperator 0x560375aaea88 <line:399:5, col:42> 'const struct node *' '='
|     | |   | | |-DeclRefExpr 0x560375aae9e0 <col:5> 'const struct node *' lvalue Var 0x560375aa4388 '__cil_tmp72' 'const struct node *'
|     | |   | | `-CStyleCastExpr 0x560375aaea60 <col:19, col:42> 'const struct node *' <BitCast>
|     | |   | |   `-ImplicitCastExpr 0x560375aaea48 <col:42> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaea00 <col:42> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aaeb40 <line:400:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaeaa8 <col:5> 'unsigned int' lvalue Var 0x560375aa4420 '__cil_tmp73' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaeb18 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaeb00 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaeac8 <col:34> 'const struct node *' lvalue Var 0x560375aa4388 '__cil_tmp72' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aaebf8 <line:401:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaeb60 <col:5> 'unsigned int' lvalue Var 0x560375aa44b8 '__cil_tmp74' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaebd0 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaebb8 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaeb80 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aaecc8 <line:402:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aaec18 <col:5> 'int' lvalue Var 0x560375aa4550 '__cil_tmp75' 'int'
|     | |   | | `-BinaryOperator 0x560375aaeca8 <col:19, col:34> 'int' '!='
|     | |   | |   |-ImplicitCastExpr 0x560375aaec78 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aaec38 <col:19> 'unsigned int' lvalue Var 0x560375aa44b8 '__cil_tmp74' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aaec90 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aaec58 <col:34> 'unsigned int' lvalue Var 0x560375aa4420 '__cil_tmp73' 'unsigned int'
|     | |   | `-IfStmt 0x560375aaedd0 <line:403:5, line:409:5> has_else
|     | |   |   |-UnaryOperator 0x560375aaed20 <line:403:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aaed08 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aaece8 <col:11> 'int' lvalue Var 0x560375aa4550 '__cil_tmp75' 'int'
|     | |   |   |-CompoundStmt 0x560375aaeda8 <col:24, line:407:5>
|     | |   |   | `-CompoundStmt 0x560375aaed90 <line:404:7, line:406:7>
|     | |   |   |   `-CallExpr 0x560375aaed70 <line:405:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aaed58 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aaed38 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aaedc0 <line:407:12, line:409:5>
|     | |   `-GotoStmt 0x560375aaee80 <line:411:5, col:10> 'while_11_break' 0x560375aaee30
|     | `-LabelStmt 0x560375aaeee0 <line:413:3, col:35> 'while_11_break'
|     |   `-NullStmt 0x560375aaeed8 <col:35>
|     |-CompoundStmt 0x560375aaf728 <line:415:3, line:437:3>
|     | |-WhileStmt 0x560375aaf6f0 <line:416:3, line:435:3>
|     | | |-IntegerLiteral 0x560375aaef18 <line:416:10> 'int' 1
|     | | `-CompoundStmt 0x560375aaf6c8 <col:13, line:435:3>
|     | |   |-LabelStmt 0x560375aaef90 <line:417:5, col:40> 'while_12_continue'
|     | |   | `-NullStmt 0x560375aaef38 <col:40>
|     | |   |-CompoundStmt 0x560375aaf610 <line:418:5, line:433:5>
|     | |   | |-BinaryOperator 0x560375aaf040 <line:419:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaefa8 <col:5> 'unsigned int' lvalue Var 0x560375aa45e8 '__cil_tmp76' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaf018 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaf000 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaefc8 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aaf110 <line:420:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaf060 <col:5> 'unsigned int' lvalue Var 0x560375aa4680 '__cil_tmp77' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375aaf0f0 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375aaf0c0 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aaf080 <col:19> 'unsigned int' lvalue Var 0x560375aa45e8 '__cil_tmp76' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aaf0d8 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375aaf0a0 <col:33> 'int' 4
|     | |   | |-BinaryOperator 0x560375aaf1d8 <line:421:5, col:47> 'const struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375aaf130 <col:5> 'const struct list_head *' lvalue Var 0x560375aa4728 '__cil_tmp78' 'const struct list_head *'
|     | |   | | `-CStyleCastExpr 0x560375aaf1b0 <col:19, col:47> 'const struct list_head *' <IntegralToPointer>
|     | |   | |   `-ImplicitCastExpr 0x560375aaf198 <col:47> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaf150 <col:47> 'unsigned int' lvalue Var 0x560375aa4680 '__cil_tmp77' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375aaf2a0 <line:422:5, col:42> 'const struct node *' '='
|     | |   | | |-DeclRefExpr 0x560375aaf1f8 <col:5> 'const struct node *' lvalue Var 0x560375aa47d0 '__cil_tmp79' 'const struct node *'
|     | |   | | `-CStyleCastExpr 0x560375aaf278 <col:19, col:42> 'const struct node *' <BitCast>
|     | |   | |   `-ImplicitCastExpr 0x560375aaf260 <col:42> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaf218 <col:42> 'const struct list_head *' lvalue Var 0x560375aa4728 '__cil_tmp78' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375aaf358 <line:423:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaf2c0 <col:5> 'unsigned int' lvalue Var 0x560375aa4868 '__cil_tmp80' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaf330 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaf318 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaf2e0 <col:34> 'const struct node *' lvalue Var 0x560375aa47d0 '__cil_tmp79' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aaf410 <line:424:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375aaf378 <col:5> 'unsigned int' lvalue Var 0x560375aa4900 '__cil_tmp81' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375aaf3e8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375aaf3d0 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375aaf398 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375aaf4e0 <line:425:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375aaf430 <col:5> 'int' lvalue Var 0x560375aa4998 '__cil_tmp82' 'int'
|     | |   | | `-BinaryOperator 0x560375aaf4c0 <col:19, col:34> 'int' '!='
|     | |   | |   |-ImplicitCastExpr 0x560375aaf490 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375aaf450 <col:19> 'unsigned int' lvalue Var 0x560375aa4900 '__cil_tmp81' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375aaf4a8 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375aaf470 <col:34> 'unsigned int' lvalue Var 0x560375aa4868 '__cil_tmp80' 'unsigned int'
|     | |   | `-IfStmt 0x560375aaf5e8 <line:426:5, line:432:5> has_else
|     | |   |   |-UnaryOperator 0x560375aaf538 <line:426:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375aaf520 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375aaf500 <col:11> 'int' lvalue Var 0x560375aa4998 '__cil_tmp82' 'int'
|     | |   |   |-CompoundStmt 0x560375aaf5c0 <col:24, line:430:5>
|     | |   |   | `-CompoundStmt 0x560375aaf5a8 <line:427:7, line:429:7>
|     | |   |   |   `-CallExpr 0x560375aaf588 <line:428:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375aaf570 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375aaf550 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375aaf5d8 <line:430:12, line:432:5>
|     | |   `-GotoStmt 0x560375aaf6b0 <line:434:5, col:10> 'while_12_break' 0x560375aaf660
|     | `-LabelStmt 0x560375aaf710 <line:436:3, col:35> 'while_12_break'
|     |   `-NullStmt 0x560375aaf708 <col:35>
|     |-CompoundStmt 0x560375ab0dd8 <line:438:3, line:458:3>
|     | |-WhileStmt 0x560375ab0da0 <line:439:3, line:456:3>
|     | | |-IntegerLiteral 0x560375aaf748 <line:439:10> 'int' 1
|     | | `-CompoundStmt 0x560375ab0d78 <col:13, line:456:3>
|     | |   |-LabelStmt 0x560375aaf7c0 <line:440:5, col:40> 'while_13_continue'
|     | |   | `-NullStmt 0x560375aaf768 <col:40>
|     | |   |-CompoundStmt 0x560375ab0cd0 <line:441:5, line:454:5>
|     | |   | |-BinaryOperator 0x560375ab0898 <line:442:5, col:34> 'const int *' '='
|     | |   | | |-DeclRefExpr 0x560375aaf7d8 <col:5> 'const int *' lvalue Var 0x560375aa5a80 '__cil_tmp83' 'const int *'
|     | |   | | `-CStyleCastExpr 0x560375ab0870 <col:19, col:34> 'const int *' <BitCast>
|     | |   | |   `-ImplicitCastExpr 0x560375ab0858 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab0820 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375ab0960 <line:443:5, col:42> 'const struct node *' '='
|     | |   | | |-DeclRefExpr 0x560375ab08b8 <col:5> 'const struct node *' lvalue Var 0x560375aa5b28 '__cil_tmp84' 'const struct node *'
|     | |   | | `-CStyleCastExpr 0x560375ab0938 <col:19, col:42> 'const struct node *' <BitCast>
|     | |   | |   `-ImplicitCastExpr 0x560375ab0920 <col:42> 'const int *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab08d8 <col:42> 'const int *' lvalue Var 0x560375aa5a80 '__cil_tmp83' 'const int *'
|     | |   | |-BinaryOperator 0x560375ab0a18 <line:444:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab0980 <col:5> 'unsigned int' lvalue Var 0x560375aa5bc0 '__cil_tmp85' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab09f0 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab09d8 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab09a0 <col:34> 'const struct node *' lvalue Var 0x560375aa5b28 '__cil_tmp84' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375ab0ad0 <line:445:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab0a38 <col:5> 'unsigned int' lvalue Var 0x560375aa5c58 '__cil_tmp86' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab0aa8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab0a90 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab0a58 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375ab0ba0 <line:446:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375ab0af0 <col:5> 'int' lvalue Var 0x560375aa5cf0 '__cil_tmp87' 'int'
|     | |   | | `-BinaryOperator 0x560375ab0b80 <col:19, col:34> 'int' '=='
|     | |   | |   |-ImplicitCastExpr 0x560375ab0b50 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab0b10 <col:19> 'unsigned int' lvalue Var 0x560375aa5c58 '__cil_tmp86' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab0b68 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375ab0b30 <col:34> 'unsigned int' lvalue Var 0x560375aa5bc0 '__cil_tmp85' 'unsigned int'
|     | |   | `-IfStmt 0x560375ab0ca8 <line:447:5, line:453:5> has_else
|     | |   |   |-UnaryOperator 0x560375ab0bf8 <line:447:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375ab0be0 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375ab0bc0 <col:11> 'int' lvalue Var 0x560375aa5cf0 '__cil_tmp87' 'int'
|     | |   |   |-CompoundStmt 0x560375ab0c80 <col:24, line:451:5>
|     | |   |   | `-CompoundStmt 0x560375ab0c68 <line:448:7, line:450:7>
|     | |   |   |   `-CallExpr 0x560375ab0c48 <line:449:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375ab0c30 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375ab0c10 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375ab0c98 <line:451:12, line:453:5>
|     | |   `-GotoStmt 0x560375ab0d60 <line:455:5, col:10> 'while_13_break' 0x560375ab0d10
|     | `-LabelStmt 0x560375ab0dc0 <line:457:3, col:35> 'while_13_break'
|     |   `-NullStmt 0x560375ab0db8 <col:35>
|     |-CompoundStmt 0x560375ab1850 <line:459:3, line:483:3>
|     | |-WhileStmt 0x560375ab1808 <line:460:3, line:481:3>
|     | | |-IntegerLiteral 0x560375ab0df8 <line:460:10> 'int' 1
|     | | `-CompoundStmt 0x560375ab17e0 <col:13, line:481:3>
|     | |   |-LabelStmt 0x560375ab0e70 <line:461:5, col:40> 'while_14_continue'
|     | |   | `-NullStmt 0x560375ab0e18 <col:40>
|     | |   |-CompoundStmt 0x560375ab1718 <line:462:5, line:479:5>
|     | |   | |-BinaryOperator 0x560375ab0f20 <line:463:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab0e88 <col:5> 'unsigned int' lvalue Var 0x560375aa5d88 '__cil_tmp88' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab0ef8 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab0ee0 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab0ea8 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375ab0ff0 <line:464:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab0f40 <col:5> 'unsigned int' lvalue Var 0x560375aa5e20 '__cil_tmp89' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375ab0fd0 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375ab0fa0 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab0f60 <col:19> 'unsigned int' lvalue Var 0x560375aa5d88 '__cil_tmp88' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab0fb8 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375ab0f80 <col:33> 'int' 4
|     | |   | |-BinaryOperator 0x560375ab1108 <line:465:5, col:61> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375ab1010 <col:5> 'struct list_head *' lvalue Var 0x560375aa5ec8 '__cil_tmp90' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375ab10f0 <col:19, col:61> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375ab10d8 <col:19, col:61> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375ab10b8 <col:20, col:61> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375ab1090 <col:21, col:50> 'struct list_head *const *' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375ab1078 <col:50> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375ab1030 <col:50> 'unsigned int' lvalue Var 0x560375aa5e20 '__cil_tmp89' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375ab11c0 <line:466:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab1128 <col:5> 'unsigned int' lvalue Var 0x560375aa5f60 '__cil_tmp91' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab1198 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab1180 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab1148 <col:34> 'struct list_head *' lvalue Var 0x560375aa5ec8 '__cil_tmp90' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab1290 <line:467:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab11e0 <col:5> 'unsigned int' lvalue Var 0x560375aa5ff8 '__cil_tmp92' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375ab1270 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375ab1240 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab1200 <col:19> 'unsigned int' lvalue Var 0x560375aa5f60 '__cil_tmp91' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab1258 <col:33> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375ab1220 <col:33> 'int' 4
|     | |   | |-BinaryOperator 0x560375ab13a8 <line:468:5, col:53> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375ab12b0 <col:5> 'struct list_head *' lvalue Var 0x560375aa60a0 '__cil_tmp93' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375ab1390 <col:19, col:53> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375ab1378 <col:19, col:53> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375ab1358 <col:20, col:53> 'struct list_head **'
|     | |   | |       `-CStyleCastExpr 0x560375ab1330 <col:21, col:42> 'struct list_head **' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375ab1318 <col:42> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375ab12d0 <col:42> 'unsigned int' lvalue Var 0x560375aa5ff8 '__cil_tmp92' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375ab1460 <line:469:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab13c8 <col:5> 'unsigned int' lvalue Var 0x560375aa6138 '__cil_tmp94' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab1438 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab1420 <col:34> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab13e8 <col:34> 'struct list_head *' lvalue Var 0x560375aa60a0 '__cil_tmp93' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab1518 <line:470:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab1480 <col:5> 'unsigned int' lvalue Var 0x560375aa61d0 '__cil_tmp95' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab14f0 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab14d8 <col:34> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab14a0 <col:34> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab15e8 <line:471:5, col:34> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375ab1538 <col:5> 'int' lvalue Var 0x560375aa6268 '__cil_tmp96' 'int'
|     | |   | | `-BinaryOperator 0x560375ab15c8 <col:19, col:34> 'int' '=='
|     | |   | |   |-ImplicitCastExpr 0x560375ab1598 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab1558 <col:19> 'unsigned int' lvalue Var 0x560375aa61d0 '__cil_tmp95' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab15b0 <col:34> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375ab1578 <col:34> 'unsigned int' lvalue Var 0x560375aa6138 '__cil_tmp94' 'unsigned int'
|     | |   | `-IfStmt 0x560375ab16f0 <line:472:5, line:478:5> has_else
|     | |   |   |-UnaryOperator 0x560375ab1640 <line:472:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375ab1628 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375ab1608 <col:11> 'int' lvalue Var 0x560375aa6268 '__cil_tmp96' 'int'
|     | |   |   |-CompoundStmt 0x560375ab16c8 <col:24, line:476:5>
|     | |   |   | `-CompoundStmt 0x560375ab16b0 <line:473:7, line:475:7>
|     | |   |   |   `-CallExpr 0x560375ab1690 <line:474:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375ab1678 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375ab1658 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375ab16e0 <line:476:12, line:478:5>
|     | |   `-GotoStmt 0x560375ab17c8 <line:480:5, col:10> 'while_14_break' 0x560375ab1778
|     | `-LabelStmt 0x560375ab1838 <line:482:3, col:35> 'while_14_break'
|     |   `-NullStmt 0x560375ab1830 <col:35>
|     |-CompoundStmt 0x560375ab21e0 <line:484:3, line:507:3>
|     | |-WhileStmt 0x560375ab21a8 <line:485:3, line:505:3>
|     | | |-IntegerLiteral 0x560375ab1870 <line:485:10> 'int' 1
|     | | `-CompoundStmt 0x560375ab2180 <col:13, line:505:3>
|     | |   |-LabelStmt 0x560375ab18e8 <line:486:5, col:40> 'while_15_continue'
|     | |   | `-NullStmt 0x560375ab1890 <col:40>
|     | |   |-CompoundStmt 0x560375ab20c0 <line:487:5, line:503:5>
|     | |   | |-BinaryOperator 0x560375ab1998 <line:488:5, col:23> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab1900 <col:5> 'unsigned int' lvalue Var 0x560375aa6300 '__cil_tmp97' 'unsigned int'
|     | |   | | `-ImplicitCastExpr 0x560375ab1980 <col:19, col:23> 'unsigned int' <IntegralCast>
|     | |   | |   `-BinaryOperator 0x560375ab1960 <col:19, col:23> 'int' '+'
|     | |   | |     |-IntegerLiteral 0x560375ab1920 <col:19> 'int' 4
|     | |   | |     `-IntegerLiteral 0x560375ab1940 <col:23> 'int' 4
|     | |   | |-BinaryOperator 0x560375ab1a50 <line:489:5, col:34> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab19b8 <col:5> 'unsigned int' lvalue Var 0x560375aa6398 '__cil_tmp98' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab1a28 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab1a10 <col:34> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab19d8 <col:34> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375ab1b20 <line:490:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab1a70 <col:5> 'unsigned int' lvalue Var 0x560375aa6430 '__cil_tmp99' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375ab1b00 <col:19, col:33> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375ab1ad0 <col:19> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab1a90 <col:19> 'unsigned int' lvalue Var 0x560375aa6398 '__cil_tmp98' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab1ae8 <col:33> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375ab1ab0 <col:33> 'unsigned int' lvalue Var 0x560375aa6300 '__cil_tmp97' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375ab1c38 <line:491:5, col:62> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375ab1b40 <col:5> 'struct list_head *' lvalue Var 0x560375aa64d8 '__cil_tmp100' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375ab1c20 <col:20, col:62> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375ab1c08 <col:20, col:62> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375ab1be8 <col:21, col:62> 'struct list_head *const *'
|     | |   | |       `-CStyleCastExpr 0x560375ab1bc0 <col:22, col:51> 'struct list_head *const *' <IntegralToPointer>
|     | |   | |         `-ImplicitCastExpr 0x560375ab1ba8 <col:51> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375ab1b60 <col:51> 'unsigned int' lvalue Var 0x560375aa6430 '__cil_tmp99' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375ab1d50 <line:492:5, col:55> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375ab1c58 <col:5> 'struct list_head *' lvalue Var 0x560375aa6580 '__cil_tmp101' 'struct list_head *'
|     | |   | | `-ImplicitCastExpr 0x560375ab1d38 <col:20, col:55> 'struct list_head *' <LValueToRValue>
|     | |   | |   `-UnaryOperator 0x560375ab1d20 <col:20, col:55> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |   | |     `-ParenExpr 0x560375ab1d00 <col:21, col:55> 'struct list_head **'
|     | |   | |       `-CStyleCastExpr 0x560375ab1cd8 <col:22, col:43> 'struct list_head **' <BitCast>
|     | |   | |         `-ImplicitCastExpr 0x560375ab1cc0 <col:43> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |           `-DeclRefExpr 0x560375ab1c78 <col:43> 'struct list_head *' lvalue Var 0x560375aa64d8 '__cil_tmp100' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab1e08 <line:493:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab1d70 <col:5> 'unsigned int' lvalue Var 0x560375aa6618 '__cil_tmp102' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab1de0 <col:20, col:35> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab1dc8 <col:35> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab1d90 <col:35> 'struct list_head *' lvalue Var 0x560375aa6580 '__cil_tmp101' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab1ec0 <line:494:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab1e28 <col:5> 'unsigned int' lvalue Var 0x560375aa66b0 '__cil_tmp103' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab1e98 <col:20, col:35> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab1e80 <col:35> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab1e48 <col:35> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab1f90 <line:495:5, col:36> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375ab1ee0 <col:5> 'int' lvalue Var 0x560375aa6748 '__cil_tmp104' 'int'
|     | |   | | `-BinaryOperator 0x560375ab1f70 <col:20, col:36> 'int' '=='
|     | |   | |   |-ImplicitCastExpr 0x560375ab1f40 <col:20> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab1f00 <col:20> 'unsigned int' lvalue Var 0x560375aa66b0 '__cil_tmp103' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab1f58 <col:36> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375ab1f20 <col:36> 'unsigned int' lvalue Var 0x560375aa6618 '__cil_tmp102' 'unsigned int'
|     | |   | `-IfStmt 0x560375ab2098 <line:496:5, line:502:5> has_else
|     | |   |   |-UnaryOperator 0x560375ab1fe8 <line:496:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375ab1fd0 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375ab1fb0 <col:11> 'int' lvalue Var 0x560375aa6748 '__cil_tmp104' 'int'
|     | |   |   |-CompoundStmt 0x560375ab2070 <col:25, line:500:5>
|     | |   |   | `-CompoundStmt 0x560375ab2058 <line:497:7, line:499:7>
|     | |   |   |   `-CallExpr 0x560375ab2038 <line:498:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375ab2020 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375ab2000 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375ab2088 <line:500:12, line:502:5>
|     | |   `-GotoStmt 0x560375ab2168 <line:504:5, col:10> 'while_15_break' 0x560375ab2118
|     | `-LabelStmt 0x560375ab21c8 <line:506:3, col:35> 'while_15_break'
|     |   `-NullStmt 0x560375ab21c0 <col:35>
|     |-BinaryOperator 0x560375ab22f8 <line:508:3, col:53> 'struct list_head *' '='
|     | |-DeclRefExpr 0x560375ab2200 <col:3> 'struct list_head *' lvalue Var 0x560375aa67f0 '__cil_tmp105' 'struct list_head *'
|     | `-ImplicitCastExpr 0x560375ab22e0 <col:18, col:53> 'struct list_head *' <LValueToRValue>
|     |   `-UnaryOperator 0x560375ab22c8 <col:18, col:53> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     |     `-ParenExpr 0x560375ab22a8 <col:19, col:53> 'struct list_head *const *'
|     |       `-CStyleCastExpr 0x560375ab2280 <col:20, col:49> 'struct list_head *const *' <BitCast>
|     |         `-ImplicitCastExpr 0x560375ab2268 <col:49> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |           `-DeclRefExpr 0x560375ab2220 <col:49> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     |-BinaryOperator 0x560375ab23c0 <line:509:3, col:38> 'const struct list_head *' '='
|     | |-DeclRefExpr 0x560375ab2318 <col:3> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | `-CStyleCastExpr 0x560375ab2398 <col:10, col:38> 'const struct list_head *' <NoOp>
|     |   `-ImplicitCastExpr 0x560375ab2380 <col:38> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375ab2338 <col:38> 'struct list_head *' lvalue Var 0x560375aa67f0 '__cil_tmp105' 'struct list_head *'
|     |-CompoundStmt 0x560375ab2c10 <line:510:3, line:529:3>
|     | |-WhileStmt 0x560375ab2bd8 <line:511:3, line:527:3>
|     | | |-IntegerLiteral 0x560375ab23e0 <line:511:10> 'int' 1
|     | | `-CompoundStmt 0x560375ab2ba8 <col:13, line:527:3>
|     | |   |-LabelStmt 0x560375ab2458 <line:512:5, col:40> 'while_16_continue'
|     | |   | `-NullStmt 0x560375ab2400 <col:40>
|     | |   |-CompoundStmt 0x560375ab2988 <line:513:5, line:524:5>
|     | |   | |-BinaryOperator 0x560375ab2508 <line:514:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab2470 <col:5> 'unsigned int' lvalue Var 0x560375aa6888 '__cil_tmp106' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab24e0 <col:20, col:35> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab24c8 <col:35> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab2490 <col:35> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab25c0 <line:515:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab2528 <col:5> 'unsigned int' lvalue Var 0x560375aa6920 '__cil_tmp107' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab2598 <col:20, col:35> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab2580 <col:35> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab2548 <col:35> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375ab2690 <line:516:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab25e0 <col:5> 'unsigned int' lvalue Var 0x560375aa69b8 '__cil_tmp108' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375ab2670 <col:20, col:35> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375ab2640 <col:20> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab2600 <col:20> 'unsigned int' lvalue Var 0x560375aa6920 '__cil_tmp107' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab2658 <col:35> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375ab2620 <col:35> 'int' 4
|     | |   | |-BinaryOperator 0x560375ab2758 <line:517:5, col:48> 'const struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375ab26b0 <col:5> 'const struct list_head *' lvalue Var 0x560375aa72a0 '__cil_tmp109' 'const struct list_head *'
|     | |   | | `-CStyleCastExpr 0x560375ab2730 <col:20, col:48> 'const struct list_head *' <IntegralToPointer>
|     | |   | |   `-ImplicitCastExpr 0x560375ab2718 <col:48> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab26d0 <col:48> 'unsigned int' lvalue Var 0x560375aa69b8 '__cil_tmp108' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375ab2810 <line:518:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab2778 <col:5> 'unsigned int' lvalue Var 0x560375aa7338 '__cil_tmp110' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab27e8 <col:20, col:35> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab27d0 <col:35> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab2798 <col:35> 'const struct list_head *' lvalue Var 0x560375aa72a0 '__cil_tmp109' 'const struct list_head *'
|     | |   | `-IfStmt 0x560375ab2960 <line:519:5, line:523:5> has_else
|     | |   |   |-BinaryOperator 0x560375ab28b0 <line:519:9, col:25> 'int' '!='
|     | |   |   | |-ImplicitCastExpr 0x560375ab2880 <col:9> 'unsigned int' <LValueToRValue>
|     | |   |   | | `-DeclRefExpr 0x560375ab2840 <col:9> 'unsigned int' lvalue Var 0x560375aa7338 '__cil_tmp110' 'unsigned int'
|     | |   |   | `-ImplicitCastExpr 0x560375ab2898 <col:25> 'unsigned int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375ab2860 <col:25> 'unsigned int' lvalue Var 0x560375aa6888 '__cil_tmp106' 'unsigned int'
|     | |   |   |-CompoundStmt 0x560375ab28d0 <col:39, line:521:5>
|     | |   |   `-CompoundStmt 0x560375ab2948 <col:12, line:523:5>
|     | |   |     `-GotoStmt 0x560375ab2930 <line:522:7, col:12> 'while_16_break' 0x560375ab28e0
|     | |   |-BinaryOperator 0x560375ab2ac0 <line:525:5, col:55> 'struct list_head *' '='
|     | |   | |-DeclRefExpr 0x560375ab29c8 <col:5> 'struct list_head *' lvalue Var 0x560375aa73e0 '__cil_tmp111' 'struct list_head *'
|     | |   | `-ImplicitCastExpr 0x560375ab2aa8 <col:20, col:55> 'struct list_head *' <LValueToRValue>
|     | |   |   `-UnaryOperator 0x560375ab2a90 <col:20, col:55> 'struct list_head *const' lvalue prefix '*' cannot overflow
|     | |   |     `-ParenExpr 0x560375ab2a70 <col:21, col:55> 'struct list_head *const *'
|     | |   |       `-CStyleCastExpr 0x560375ab2a48 <col:22, col:51> 'struct list_head *const *' <BitCast>
|     | |   |         `-ImplicitCastExpr 0x560375ab2a30 <col:51> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   |           `-DeclRefExpr 0x560375ab29e8 <col:51> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   `-BinaryOperator 0x560375ab2b88 <line:526:5, col:40> 'const struct list_head *' '='
|     | |     |-DeclRefExpr 0x560375ab2ae0 <col:5> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |     `-CStyleCastExpr 0x560375ab2b60 <col:12, col:40> 'const struct list_head *' <NoOp>
|     | |       `-ImplicitCastExpr 0x560375ab2b48 <col:40> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |         `-DeclRefExpr 0x560375ab2b00 <col:40> 'struct list_head *' lvalue Var 0x560375aa73e0 '__cil_tmp111' 'struct list_head *'
|     | `-LabelStmt 0x560375ab2bf8 <line:528:3, col:35> 'while_16_break'
|     |   `-NullStmt 0x560375ab2bf0 <col:35>
|     |-CompoundStmt 0x560375ab3750 <line:530:3, line:556:3>
|     | |-WhileStmt 0x560375ab3718 <line:531:3, line:554:3>
|     | | |-IntegerLiteral 0x560375ab2c30 <line:531:10> 'int' 1
|     | | `-CompoundStmt 0x560375ab36f0 <col:13, line:554:3>
|     | |   |-LabelStmt 0x560375ab2ca8 <line:532:5, col:40> 'while_17_continue'
|     | |   | `-NullStmt 0x560375ab2c50 <col:40>
|     | |   |-CompoundStmt 0x560375ab3618 <line:533:5, line:552:5>
|     | |   | |-BinaryOperator 0x560375ab2d58 <line:534:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab2cc0 <col:5> 'unsigned int' lvalue Var 0x560375aa7478 '__cil_tmp112' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab2d30 <col:20, col:35> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab2d18 <col:35> 'const struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab2ce0 <col:35> 'const struct node *' lvalue Var 0x560375a9c810 'node' 'const struct node *'
|     | |   | |-BinaryOperator 0x560375ab2e08 <line:535:5, col:35> 'struct node *' '='
|     | |   | | |-DeclRefExpr 0x560375ab2d78 <col:5> 'struct node *' lvalue Var 0x560375aa7520 '__cil_tmp113' 'struct node *'
|     | |   | | `-CStyleCastExpr 0x560375ab2de0 <col:20, col:35> 'struct node *' <NullToPointer>
|     | |   | |   `-IntegerLiteral 0x560375ab2d98 <col:35> 'int' 0
|     | |   | |-BinaryOperator 0x560375ab2ec0 <line:536:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab2e28 <col:5> 'unsigned int' lvalue Var 0x560375aa75b8 '__cil_tmp114' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab2e98 <col:20, col:35> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab2e80 <col:35> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab2e48 <col:35> 'struct node *' lvalue Var 0x560375aa7520 '__cil_tmp113' 'struct node *'
|     | |   | |-BinaryOperator 0x560375ab2f90 <line:537:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab2ee0 <col:5> 'unsigned int' lvalue Var 0x560375aa7650 '__cil_tmp115' 'unsigned int'
|     | |   | | `-BinaryOperator 0x560375ab2f70 <col:20, col:35> 'unsigned int' '+'
|     | |   | |   |-ImplicitCastExpr 0x560375ab2f40 <col:20> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab2f00 <col:20> 'unsigned int' lvalue Var 0x560375aa75b8 '__cil_tmp114' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab2f58 <col:35> 'unsigned int' <IntegralCast>
|     | |   | |     `-IntegerLiteral 0x560375ab2f20 <col:35> 'int' 4
|     | |   | |-BinaryOperator 0x560375ab3058 <line:538:5, col:40> 'struct list_head *' '='
|     | |   | | |-DeclRefExpr 0x560375ab2fb0 <col:5> 'struct list_head *' lvalue Var 0x560375aa76f8 '__cil_tmp116' 'struct list_head *'
|     | |   | | `-CStyleCastExpr 0x560375ab3030 <col:20, col:40> 'struct list_head *' <IntegralToPointer>
|     | |   | |   `-ImplicitCastExpr 0x560375ab3018 <col:40> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab2fd0 <col:40> 'unsigned int' lvalue Var 0x560375aa7650 '__cil_tmp115' 'unsigned int'
|     | |   | |-BinaryOperator 0x560375ab3110 <line:539:5, col:36> 'unsigned long' '='
|     | |   | | |-DeclRefExpr 0x560375ab3078 <col:5> 'unsigned long' lvalue Var 0x560375aa7790 '__cil_tmp117' 'unsigned long'
|     | |   | | `-CStyleCastExpr 0x560375ab30e8 <col:20, col:36> 'unsigned long' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab30d0 <col:36> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab3098 <col:36> 'struct list_head *' lvalue Var 0x560375aa76f8 '__cil_tmp116' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab31c8 <line:540:5, col:28> 'char *' '='
|     | |   | | |-DeclRefExpr 0x560375ab3130 <col:5> 'char *' lvalue Var 0x560375aa7828 '__cil_tmp118' 'char *'
|     | |   | | `-CStyleCastExpr 0x560375ab31a0 <col:20, col:28> 'char *' <BitCast>
|     | |   | |   `-ImplicitCastExpr 0x560375ab3188 <col:28> 'const struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab3150 <col:28> 'const struct list_head *' lvalue ParmVar 0x560375a9c5c0 'head' 'const struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab3298 <line:541:5, col:35> 'char *' '='
|     | |   | | |-DeclRefExpr 0x560375ab31e8 <col:5> 'char *' lvalue Var 0x560375aa78c0 '__cil_tmp119' 'char *'
|     | |   | | `-BinaryOperator 0x560375ab3278 <col:20, col:35> 'char *' '-'
|     | |   | |   |-ImplicitCastExpr 0x560375ab3248 <col:20> 'char *' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab3208 <col:20> 'char *' lvalue Var 0x560375aa7828 '__cil_tmp118' 'char *'
|     | |   | |   `-ImplicitCastExpr 0x560375ab3260 <col:35> 'unsigned long' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375ab3228 <col:35> 'unsigned long' lvalue Var 0x560375aa7790 '__cil_tmp117' 'unsigned long'
|     | |   | |-BinaryOperator 0x560375ab3360 <line:542:5, col:35> 'struct node *' '='
|     | |   | | |-DeclRefExpr 0x560375ab32b8 <col:5> 'struct node *' lvalue Var 0x560375aa7968 '__cil_tmp120' 'struct node *'
|     | |   | | `-CStyleCastExpr 0x560375ab3338 <col:20, col:35> 'struct node *' <BitCast>
|     | |   | |   `-ImplicitCastExpr 0x560375ab3320 <col:35> 'char *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab32d8 <col:35> 'char *' lvalue Var 0x560375aa78c0 '__cil_tmp119' 'char *'
|     | |   | |-BinaryOperator 0x560375ab3418 <line:543:5, col:35> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab3380 <col:5> 'unsigned int' lvalue Var 0x560375aa7a00 '__cil_tmp121' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab33f0 <col:20, col:35> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab33d8 <col:35> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab33a0 <col:35> 'struct node *' lvalue Var 0x560375aa7968 '__cil_tmp120' 'struct node *'
|     | |   | |-BinaryOperator 0x560375ab34e8 <line:544:5, col:36> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375ab3438 <col:5> 'int' lvalue Var 0x560375aa7a98 '__cil_tmp122' 'int'
|     | |   | | `-BinaryOperator 0x560375ab34c8 <col:20, col:36> 'int' '=='
|     | |   | |   |-ImplicitCastExpr 0x560375ab3498 <col:20> 'unsigned int' <LValueToRValue>
|     | |   | |   | `-DeclRefExpr 0x560375ab3458 <col:20> 'unsigned int' lvalue Var 0x560375aa7a00 '__cil_tmp121' 'unsigned int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab34b0 <col:36> 'unsigned int' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375ab3478 <col:36> 'unsigned int' lvalue Var 0x560375aa7478 '__cil_tmp112' 'unsigned int'
|     | |   | `-IfStmt 0x560375ab35f0 <line:545:5, line:551:5> has_else
|     | |   |   |-UnaryOperator 0x560375ab3540 <line:545:9, col:11> 'int' prefix '!' cannot overflow
|     | |   |   | `-ImplicitCastExpr 0x560375ab3528 <col:11> 'int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375ab3508 <col:11> 'int' lvalue Var 0x560375aa7a98 '__cil_tmp122' 'int'
|     | |   |   |-CompoundStmt 0x560375ab35c8 <col:25, line:549:5>
|     | |   |   | `-CompoundStmt 0x560375ab35b0 <line:546:7, line:548:7>
|     | |   |   |   `-CallExpr 0x560375ab3590 <line:547:7, col:12> 'void'
|     | |   |   |     `-ImplicitCastExpr 0x560375ab3578 <col:7> 'void (*)(void)' <FunctionToPointerDecay>
|     | |   |   |       `-DeclRefExpr 0x560375ab3558 <col:7> 'void (void)' Function 0x560375a9c088 'fail' 'void (void)'
|     | |   |   `-CompoundStmt 0x560375ab35e0 <line:549:12, line:551:5>
|     | |   `-GotoStmt 0x560375ab36d8 <line:553:5, col:10> 'while_17_break' 0x560375ab3688
|     | `-LabelStmt 0x560375ab3738 <line:555:3, col:35> 'while_17_break'
|     |   `-NullStmt 0x560375ab3730 <col:35>
|     `-ReturnStmt 0x560375ab3770 <line:557:3>
|-FunctionDecl 0x560375ab41c8 <line:560:1, line:577:1> line:560:22 used __list_add 'void (struct list_head *, struct list_head *, struct list_head *)' static inline
| |-ParmVarDecl 0x560375ab3f88 <col:33, col:51> col:51 used new 'struct list_head *'
| |-ParmVarDecl 0x560375ab4018 <col:57, col:75> col:75 used prev 'struct list_head *'
| |-ParmVarDecl 0x560375ab40a8 <col:82, col:100> col:100 used next 'struct list_head *'
| `-CompoundStmt 0x560375ab4ce8 <line:561:1, line:577:1>
|   |-DeclStmt 0x560375ab4300 <line:561:3, col:27>
|   | `-VarDecl 0x560375ab4298 <col:3, col:16> col:16 used __cil_tmp4 'unsigned int'
|   |-DeclStmt 0x560375ab4398 <line:562:3, col:27>
|   | `-VarDecl 0x560375ab4330 <col:3, col:16> col:16 used __cil_tmp5 'unsigned int'
|   |-DeclStmt 0x560375ab4430 <line:563:3, col:27>
|   | `-VarDecl 0x560375ab43c8 <col:3, col:16> col:16 used __cil_tmp6 'unsigned int'
|   |-DeclStmt 0x560375ab44c8 <line:564:3, col:27>
|   | `-VarDecl 0x560375ab4460 <col:3, col:16> col:16 used __cil_tmp7 'unsigned int'
|   `-CompoundStmt 0x560375ab4c90 <line:566:3, line:576:1>
|     |-BinaryOperator 0x560375ab4578 <line:567:3, col:31> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375ab44e0 <col:3> 'unsigned int' lvalue Var 0x560375ab4298 '__cil_tmp4' 'unsigned int'
|     | `-CStyleCastExpr 0x560375ab4550 <col:16, col:31> 'unsigned int' <PointerToIntegral>
|     |   `-ImplicitCastExpr 0x560375ab4538 <col:31> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375ab4500 <col:31> 'struct list_head *' lvalue ParmVar 0x560375ab40a8 'next' 'struct list_head *'
|     |-BinaryOperator 0x560375ab4648 <line:568:3, col:29> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375ab4598 <col:3> 'unsigned int' lvalue Var 0x560375ab4330 '__cil_tmp5' 'unsigned int'
|     | `-BinaryOperator 0x560375ab4628 <col:16, col:29> 'unsigned int' '+'
|     |   |-ImplicitCastExpr 0x560375ab45f8 <col:16> 'unsigned int' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375ab45b8 <col:16> 'unsigned int' lvalue Var 0x560375ab4298 '__cil_tmp4' 'unsigned int'
|     |   `-ImplicitCastExpr 0x560375ab4610 <col:29> 'unsigned int' <IntegralCast>
|     |     `-IntegerLiteral 0x560375ab45d8 <col:29> 'int' 4
|     |-BinaryOperator 0x560375ab4760 <line:569:3, col:40> 'struct list_head *' '='
|     | |-UnaryOperator 0x560375ab4710 <col:3, col:36> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | | `-ParenExpr 0x560375ab46f0 <col:4, col:36> 'struct list_head **'
|     | |   `-CStyleCastExpr 0x560375ab46c8 <col:5, col:26> 'struct list_head **' <IntegralToPointer>
|     | |     `-ImplicitCastExpr 0x560375ab46b0 <col:26> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |       `-DeclRefExpr 0x560375ab4668 <col:26> 'unsigned int' lvalue Var 0x560375ab4330 '__cil_tmp5' 'unsigned int'
|     | `-ImplicitCastExpr 0x560375ab4748 <col:40> 'struct list_head *' <LValueToRValue>
|     |   `-DeclRefExpr 0x560375ab4728 <col:40> 'struct list_head *' lvalue ParmVar 0x560375ab3f88 'new' 'struct list_head *'
|     |-BinaryOperator 0x560375ab4878 <line:570:3, col:33> 'struct list_head *' '='
|     | |-UnaryOperator 0x560375ab4828 <col:3, col:29> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | | `-ParenExpr 0x560375ab4808 <col:4, col:29> 'struct list_head **'
|     | |   `-CStyleCastExpr 0x560375ab47e0 <col:5, col:26> 'struct list_head **' <BitCast>
|     | |     `-ImplicitCastExpr 0x560375ab47c8 <col:26> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |       `-DeclRefExpr 0x560375ab4780 <col:26> 'struct list_head *' lvalue ParmVar 0x560375ab3f88 'new' 'struct list_head *'
|     | `-ImplicitCastExpr 0x560375ab4860 <col:33> 'struct list_head *' <LValueToRValue>
|     |   `-DeclRefExpr 0x560375ab4840 <col:33> 'struct list_head *' lvalue ParmVar 0x560375ab40a8 'next' 'struct list_head *'
|     |-BinaryOperator 0x560375ab4930 <line:571:3, col:31> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375ab4898 <col:3> 'unsigned int' lvalue Var 0x560375ab43c8 '__cil_tmp6' 'unsigned int'
|     | `-CStyleCastExpr 0x560375ab4908 <col:16, col:31> 'unsigned int' <PointerToIntegral>
|     |   `-ImplicitCastExpr 0x560375ab48f0 <col:31> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375ab48b8 <col:31> 'struct list_head *' lvalue ParmVar 0x560375ab3f88 'new' 'struct list_head *'
|     |-BinaryOperator 0x560375ab4a00 <line:572:3, col:29> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375ab4950 <col:3> 'unsigned int' lvalue Var 0x560375ab4460 '__cil_tmp7' 'unsigned int'
|     | `-BinaryOperator 0x560375ab49e0 <col:16, col:29> 'unsigned int' '+'
|     |   |-ImplicitCastExpr 0x560375ab49b0 <col:16> 'unsigned int' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375ab4970 <col:16> 'unsigned int' lvalue Var 0x560375ab43c8 '__cil_tmp6' 'unsigned int'
|     |   `-ImplicitCastExpr 0x560375ab49c8 <col:29> 'unsigned int' <IntegralCast>
|     |     `-IntegerLiteral 0x560375ab4990 <col:29> 'int' 4
|     |-BinaryOperator 0x560375ab4b48 <line:573:3, col:40> 'struct list_head *' '='
|     | |-UnaryOperator 0x560375ab4af8 <col:3, col:36> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | | `-ParenExpr 0x560375ab4ad8 <col:4, col:36> 'struct list_head **'
|     | |   `-CStyleCastExpr 0x560375ab4ab0 <col:5, col:26> 'struct list_head **' <IntegralToPointer>
|     | |     `-ImplicitCastExpr 0x560375ab4a98 <col:26> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |       `-DeclRefExpr 0x560375ab4a20 <col:26> 'unsigned int' lvalue Var 0x560375ab4460 '__cil_tmp7' 'unsigned int'
|     | `-ImplicitCastExpr 0x560375ab4b30 <col:40> 'struct list_head *' <LValueToRValue>
|     |   `-DeclRefExpr 0x560375ab4b10 <col:40> 'struct list_head *' lvalue ParmVar 0x560375ab4018 'prev' 'struct list_head *'
|     |-BinaryOperator 0x560375ab4c60 <line:574:3, col:34> 'struct list_head *' '='
|     | |-UnaryOperator 0x560375ab4c10 <col:3, col:30> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | | `-ParenExpr 0x560375ab4bf0 <col:4, col:30> 'struct list_head **'
|     | |   `-CStyleCastExpr 0x560375ab4bc8 <col:5, col:26> 'struct list_head **' <BitCast>
|     | |     `-ImplicitCastExpr 0x560375ab4bb0 <col:26> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |       `-DeclRefExpr 0x560375ab4b68 <col:26> 'struct list_head *' lvalue ParmVar 0x560375ab4018 'prev' 'struct list_head *'
|     | `-ImplicitCastExpr 0x560375ab4c48 <col:34> 'struct list_head *' <LValueToRValue>
|     |   `-DeclRefExpr 0x560375ab4c28 <col:34> 'struct list_head *' lvalue ParmVar 0x560375ab3f88 'new' 'struct list_head *'
|     `-ReturnStmt 0x560375ab4c80 <line:575:3>
|-FunctionDecl 0x560375ab4ee8 <line:578:1, line:589:1> line:578:22 used __list_del 'void (struct list_head *, struct list_head *)' static inline
| |-ParmVarDecl 0x560375ab4d48 <col:33, col:51> col:51 used prev 'struct list_head *'
| |-ParmVarDecl 0x560375ab4dd8 <col:58, col:76> col:76 used next 'struct list_head *'
| `-CompoundStmt 0x560375ab54c8 <line:579:1, line:589:1>
|   |-DeclStmt 0x560375ab5018 <line:579:3, col:27>
|   | `-VarDecl 0x560375ab4fb0 <col:3, col:16> col:16 used __cil_tmp3 'unsigned int'
|   |-DeclStmt 0x560375ab50b0 <line:580:3, col:27>
|   | `-VarDecl 0x560375ab5048 <col:3, col:16> col:16 used __cil_tmp4 'unsigned int'
|   `-CompoundStmt 0x560375ab5490 <line:582:3, line:588:1>
|     |-BinaryOperator 0x560375ab5160 <line:583:3, col:31> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375ab50c8 <col:3> 'unsigned int' lvalue Var 0x560375ab4fb0 '__cil_tmp3' 'unsigned int'
|     | `-CStyleCastExpr 0x560375ab5138 <col:16, col:31> 'unsigned int' <PointerToIntegral>
|     |   `-ImplicitCastExpr 0x560375ab5120 <col:31> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375ab50e8 <col:31> 'struct list_head *' lvalue ParmVar 0x560375ab4dd8 'next' 'struct list_head *'
|     |-BinaryOperator 0x560375ab5230 <line:584:3, col:29> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375ab5180 <col:3> 'unsigned int' lvalue Var 0x560375ab5048 '__cil_tmp4' 'unsigned int'
|     | `-BinaryOperator 0x560375ab5210 <col:16, col:29> 'unsigned int' '+'
|     |   |-ImplicitCastExpr 0x560375ab51e0 <col:16> 'unsigned int' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375ab51a0 <col:16> 'unsigned int' lvalue Var 0x560375ab4fb0 '__cil_tmp3' 'unsigned int'
|     |   `-ImplicitCastExpr 0x560375ab51f8 <col:29> 'unsigned int' <IntegralCast>
|     |     `-IntegerLiteral 0x560375ab51c0 <col:29> 'int' 4
|     |-BinaryOperator 0x560375ab5348 <line:585:3, col:40> 'struct list_head *' '='
|     | |-UnaryOperator 0x560375ab52f8 <col:3, col:36> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | | `-ParenExpr 0x560375ab52d8 <col:4, col:36> 'struct list_head **'
|     | |   `-CStyleCastExpr 0x560375ab52b0 <col:5, col:26> 'struct list_head **' <IntegralToPointer>
|     | |     `-ImplicitCastExpr 0x560375ab5298 <col:26> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |       `-DeclRefExpr 0x560375ab5250 <col:26> 'unsigned int' lvalue Var 0x560375ab5048 '__cil_tmp4' 'unsigned int'
|     | `-ImplicitCastExpr 0x560375ab5330 <col:40> 'struct list_head *' <LValueToRValue>
|     |   `-DeclRefExpr 0x560375ab5310 <col:40> 'struct list_head *' lvalue ParmVar 0x560375ab4d48 'prev' 'struct list_head *'
|     |-BinaryOperator 0x560375ab5460 <line:586:3, col:34> 'struct list_head *' '='
|     | |-UnaryOperator 0x560375ab5410 <col:3, col:30> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | | `-ParenExpr 0x560375ab53f0 <col:4, col:30> 'struct list_head **'
|     | |   `-CStyleCastExpr 0x560375ab53c8 <col:5, col:26> 'struct list_head **' <BitCast>
|     | |     `-ImplicitCastExpr 0x560375ab53b0 <col:26> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |       `-DeclRefExpr 0x560375ab5368 <col:26> 'struct list_head *' lvalue ParmVar 0x560375ab4d48 'prev' 'struct list_head *'
|     | `-ImplicitCastExpr 0x560375ab5448 <col:34> 'struct list_head *' <LValueToRValue>
|     |   `-DeclRefExpr 0x560375ab5428 <col:34> 'struct list_head *' lvalue ParmVar 0x560375ab4dd8 'next' 'struct list_head *'
|     `-ReturnStmt 0x560375ab5480 <line:587:3>
|-FunctionDecl 0x560375ab5640 <line:590:1, line:600:1> line:590:22 used list_add 'void (struct list_head *, struct list_head *)' static inline
| |-ParmVarDecl 0x560375ab5518 <col:31, col:49> col:49 used new 'struct list_head *'
| |-ParmVarDecl 0x560375ab55a8 <col:55, col:73> col:73 used head 'struct list_head *'
| `-CompoundStmt 0x560375ab5a80 <line:591:1, line:600:1>
|   |-DeclStmt 0x560375ab5780 <line:591:3, col:32>
|   | `-VarDecl 0x560375ab5718 <col:3, col:21> col:21 used __cil_tmp3 'struct list_head *'
|   `-CompoundStmt 0x560375ab5a50 <line:593:3, line:599:1>
|     |-CompoundStmt 0x560375ab5a20 <line:594:3, line:597:3>
|     | |-BinaryOperator 0x560375ab5890 <line:595:3, col:43> 'struct list_head *' '='
|     | | |-DeclRefExpr 0x560375ab5798 <col:3> 'struct list_head *' lvalue Var 0x560375ab5718 '__cil_tmp3' 'struct list_head *'
|     | | `-ImplicitCastExpr 0x560375ab5878 <col:16, col:43> 'struct list_head *' <LValueToRValue>
|     | |   `-UnaryOperator 0x560375ab5860 <col:16, col:43> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |     `-ParenExpr 0x560375ab5840 <col:17, col:43> 'struct list_head **'
|     | |       `-CStyleCastExpr 0x560375ab5818 <col:18, col:39> 'struct list_head **' <BitCast>
|     | |         `-ImplicitCastExpr 0x560375ab5800 <col:39> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |           `-DeclRefExpr 0x560375ab57b8 <col:39> 'struct list_head *' lvalue ParmVar 0x560375ab55a8 'head' 'struct list_head *'
|     | `-CallExpr 0x560375ab59a0 <line:596:3, col:35> 'void'
|     |   |-ImplicitCastExpr 0x560375ab5988 <col:3> 'void (*)(struct list_head *, struct list_head *, struct list_head *)' <FunctionToPointerDecay>
|     |   | `-DeclRefExpr 0x560375ab58b0 <col:3> 'void (struct list_head *, struct list_head *, struct list_head *)' Function 0x560375ab41c8 '__list_add' 'void (struct list_head *, struct list_head *, struct list_head *)'
|     |   |-ImplicitCastExpr 0x560375ab59d8 <col:14> 'struct list_head *' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375ab58d0 <col:14> 'struct list_head *' lvalue ParmVar 0x560375ab5518 'new' 'struct list_head *'
|     |   |-ImplicitCastExpr 0x560375ab59f0 <col:19> 'struct list_head *' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375ab58f0 <col:19> 'struct list_head *' lvalue ParmVar 0x560375ab55a8 'head' 'struct list_head *'
|     |   `-ImplicitCastExpr 0x560375ab5a08 <col:25> 'struct list_head *' <LValueToRValue>
|     |     `-DeclRefExpr 0x560375ab5910 <col:25> 'struct list_head *' lvalue Var 0x560375ab5718 '__cil_tmp3' 'struct list_head *'
|     `-ReturnStmt 0x560375ab5a40 <line:598:3>
|-FunctionDecl 0x560375ab5bf0 <line:601:1, line:618:1> line:601:22 used list_move 'void (struct list_head *, struct list_head *)' static inline
| |-ParmVarDecl 0x560375ab5ac8 <col:32, col:50> col:50 used list 'struct list_head *'
| |-ParmVarDecl 0x560375ab5b58 <col:57, col:75> col:75 used head 'struct list_head *'
| `-CompoundStmt 0x560375ab6558 <line:602:1, line:618:1>
|   |-DeclStmt 0x560375ab5d20 <line:602:3, col:27>
|   | `-VarDecl 0x560375ab5cb8 <col:3, col:16> col:16 used __cil_tmp3 'unsigned int'
|   |-DeclStmt 0x560375ab5db8 <line:603:3, col:27>
|   | `-VarDecl 0x560375ab5d50 <col:3, col:16> col:16 used __cil_tmp4 'unsigned int'
|   |-DeclStmt 0x560375ab5e60 <line:604:3, col:32>
|   | `-VarDecl 0x560375ab5df8 <col:3, col:21> col:21 used __cil_tmp5 'struct list_head *'
|   |-DeclStmt 0x560375ab5f08 <line:605:3, col:32>
|   | `-VarDecl 0x560375ab5ea0 <col:3, col:21> col:21 used __cil_tmp6 'struct list_head *'
|   `-CompoundStmt 0x560375ab6538 <line:607:3, line:617:1>
|     |-CompoundStmt 0x560375ab64e8 <line:608:3, line:615:3>
|     | |-BinaryOperator 0x560375ab5fb8 <line:609:3, col:31> 'unsigned int' '='
|     | | |-DeclRefExpr 0x560375ab5f20 <col:3> 'unsigned int' lvalue Var 0x560375ab5cb8 '__cil_tmp3' 'unsigned int'
|     | | `-CStyleCastExpr 0x560375ab5f90 <col:16, col:31> 'unsigned int' <PointerToIntegral>
|     | |   `-ImplicitCastExpr 0x560375ab5f78 <col:31> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |     `-DeclRefExpr 0x560375ab5f40 <col:31> 'struct list_head *' lvalue ParmVar 0x560375ab5ac8 'list' 'struct list_head *'
|     | |-BinaryOperator 0x560375ab6088 <line:610:3, col:29> 'unsigned int' '='
|     | | |-DeclRefExpr 0x560375ab5fd8 <col:3> 'unsigned int' lvalue Var 0x560375ab5d50 '__cil_tmp4' 'unsigned int'
|     | | `-BinaryOperator 0x560375ab6068 <col:16, col:29> 'unsigned int' '+'
|     | |   |-ImplicitCastExpr 0x560375ab6038 <col:16> 'unsigned int' <LValueToRValue>
|     | |   | `-DeclRefExpr 0x560375ab5ff8 <col:16> 'unsigned int' lvalue Var 0x560375ab5cb8 '__cil_tmp3' 'unsigned int'
|     | |   `-ImplicitCastExpr 0x560375ab6050 <col:29> 'unsigned int' <IntegralCast>
|     | |     `-IntegerLiteral 0x560375ab6018 <col:29> 'int' 4
|     | |-BinaryOperator 0x560375ab61a0 <line:611:3, col:49> 'struct list_head *' '='
|     | | |-DeclRefExpr 0x560375ab60a8 <col:3> 'struct list_head *' lvalue Var 0x560375ab5df8 '__cil_tmp5' 'struct list_head *'
|     | | `-ImplicitCastExpr 0x560375ab6188 <col:16, col:49> 'struct list_head *' <LValueToRValue>
|     | |   `-UnaryOperator 0x560375ab6170 <col:16, col:49> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |     `-ParenExpr 0x560375ab6150 <col:17, col:49> 'struct list_head **'
|     | |       `-CStyleCastExpr 0x560375ab6128 <col:18, col:39> 'struct list_head **' <IntegralToPointer>
|     | |         `-ImplicitCastExpr 0x560375ab6110 <col:39> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |           `-DeclRefExpr 0x560375ab60c8 <col:39> 'unsigned int' lvalue Var 0x560375ab5d50 '__cil_tmp4' 'unsigned int'
|     | |-BinaryOperator 0x560375ab62b8 <line:612:3, col:43> 'struct list_head *' '='
|     | | |-DeclRefExpr 0x560375ab61c0 <col:3> 'struct list_head *' lvalue Var 0x560375ab5ea0 '__cil_tmp6' 'struct list_head *'
|     | | `-ImplicitCastExpr 0x560375ab62a0 <col:16, col:43> 'struct list_head *' <LValueToRValue>
|     | |   `-UnaryOperator 0x560375ab6288 <col:16, col:43> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |     `-ParenExpr 0x560375ab6268 <col:17, col:43> 'struct list_head **'
|     | |       `-CStyleCastExpr 0x560375ab6240 <col:18, col:39> 'struct list_head **' <BitCast>
|     | |         `-ImplicitCastExpr 0x560375ab6228 <col:39> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |           `-DeclRefExpr 0x560375ab61e0 <col:39> 'struct list_head *' lvalue ParmVar 0x560375ab5ac8 'list' 'struct list_head *'
|     | |-CallExpr 0x560375ab63b0 <line:613:3, col:36> 'void'
|     | | |-ImplicitCastExpr 0x560375ab6398 <col:3> 'void (*)(struct list_head *, struct list_head *)' <FunctionToPointerDecay>
|     | | | `-DeclRefExpr 0x560375ab62d8 <col:3> 'void (struct list_head *, struct list_head *)' Function 0x560375ab4ee8 '__list_del' 'void (struct list_head *, struct list_head *)'
|     | | |-ImplicitCastExpr 0x560375ab63e0 <col:14> 'struct list_head *' <LValueToRValue>
|     | | | `-DeclRefExpr 0x560375ab62f8 <col:14> 'struct list_head *' lvalue Var 0x560375ab5df8 '__cil_tmp5' 'struct list_head *'
|     | | `-ImplicitCastExpr 0x560375ab63f8 <col:26> 'struct list_head *' <LValueToRValue>
|     | |   `-DeclRefExpr 0x560375ab6318 <col:26> 'struct list_head *' lvalue Var 0x560375ab5ea0 '__cil_tmp6' 'struct list_head *'
|     | `-CallExpr 0x560375ab6488 <line:614:3, col:22> 'void'
|     |   |-ImplicitCastExpr 0x560375ab6470 <col:3> 'void (*)(struct list_head *, struct list_head *)' <FunctionToPointerDecay>
|     |   | `-DeclRefExpr 0x560375ab6410 <col:3> 'void (struct list_head *, struct list_head *)' Function 0x560375ab5640 'list_add' 'void (struct list_head *, struct list_head *)'
|     |   |-ImplicitCastExpr 0x560375ab64b8 <col:12> 'struct list_head *' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375ab6430 <col:12> 'struct list_head *' lvalue ParmVar 0x560375ab5ac8 'list' 'struct list_head *'
|     |   `-ImplicitCastExpr 0x560375ab64d0 <col:18> 'struct list_head *' <LValueToRValue>
|     |     `-DeclRefExpr 0x560375ab6450 <col:18> 'struct list_head *' lvalue ParmVar 0x560375ab5b58 'head' 'struct list_head *'
|     `-ReturnStmt 0x560375ab6528 <line:616:3>
|-FunctionDecl 0x560375ab6668 <line:619:1, line:674:1> line:619:13 used gl_insert 'void (int)' static
| |-ParmVarDecl 0x560375ab65a8 <col:23, col:27> col:27 used value 'int'
| `-CompoundStmt 0x560375ab8340 <line:620:1, line:674:1>
|   |-DeclStmt 0x560375ab67a0 <line:620:3, col:21>
|   | `-VarDecl 0x560375ab6738 <col:3, col:16> col:16 used node 'struct node *'
|   |-DeclStmt 0x560375ab6838 <line:621:3, col:13>
|   | `-VarDecl 0x560375ab67d0 <col:3, col:9> col:9 used tmp 'void *'
|   |-DeclStmt 0x560375ab68d0 <line:622:3, col:27>
|   | `-VarDecl 0x560375ab6868 <col:3, col:16> col:16 used __cil_tmp4 'unsigned int'
|   |-DeclStmt 0x560375ab6968 <line:623:3, col:27>
|   | `-VarDecl 0x560375ab6900 <col:3, col:16> col:16 used __cil_tmp5 'unsigned int'
|   |-DeclStmt 0x560375ab6a00 <line:624:3, col:27>
|   | `-VarDecl 0x560375ab6998 <col:3, col:16> col:16 used __cil_tmp6 'unsigned int'
|   |-DeclStmt 0x560375ab6af8 <line:625:3, col:32>
|   | `-VarDecl 0x560375ab6a90 <col:3, col:21> col:21 used __cil_tmp7 'struct list_head *'
|   |-DeclStmt 0x560375ab6b90 <line:626:3, col:27>
|   | `-VarDecl 0x560375ab6b28 <col:3, col:16> col:16 used __cil_tmp8 'unsigned int'
|   |-DeclStmt 0x560375ab6c28 <line:627:3, col:27>
|   | `-VarDecl 0x560375ab6bc0 <col:3, col:16> col:16 used __cil_tmp9 'unsigned int'
|   |-DeclStmt 0x560375ab6cc0 <line:628:3, col:28>
|   | `-VarDecl 0x560375ab6c58 <col:3, col:16> col:16 used __cil_tmp10 'unsigned int'
|   |-DeclStmt 0x560375ab6d58 <line:629:3, col:28>
|   | `-VarDecl 0x560375ab6cf0 <col:3, col:16> col:16 used __cil_tmp11 'unsigned int'
|   |-DeclStmt 0x560375ab6df0 <line:630:3, col:28>
|   | `-VarDecl 0x560375ab6d88 <col:3, col:16> col:16 used __cil_tmp12 'unsigned int'
|   |-DeclStmt 0x560375ab6e88 <line:631:3, col:28>
|   | `-VarDecl 0x560375ab6e20 <col:3, col:16> col:16 used __cil_tmp13 'unsigned int'
|   |-DeclStmt 0x560375ab6f20 <line:632:3, col:28>
|   | `-VarDecl 0x560375ab6eb8 <col:3, col:16> col:16 used __cil_tmp14 'unsigned int'
|   |-DeclStmt 0x560375ab6fb8 <line:633:3, col:28>
|   | `-VarDecl 0x560375ab6f50 <col:3, col:16> col:16 used __cil_tmp15 'unsigned int'
|   `-CompoundStmt 0x560375ab8308 <line:635:3, line:673:1>
|     |-CompoundStmt 0x560375ab7268 <line:636:3, line:640:3>
|     | |-BinaryOperator 0x560375ab7050 <line:637:3, col:31> 'unsigned int' '='
|     | | |-DeclRefExpr 0x560375ab6fd0 <col:3> 'unsigned int' lvalue Var 0x560375ab6868 '__cil_tmp4' 'unsigned int'
|     | | `-CStyleCastExpr 0x560375ab7028 <col:16, col:31> 'unsigned int' <IntegralCast>
|     | |   `-IntegerLiteral 0x560375ab6ff0 <col:31> 'unsigned long' 20
|     | |-BinaryOperator 0x560375ab7180 <line:638:3, col:26> 'void *' '='
|     | | |-DeclRefExpr 0x560375ab7070 <col:3> 'void *' lvalue Var 0x560375ab67d0 'tmp' 'void *'
|     | | `-CallExpr 0x560375ab7140 <col:9, col:26> 'void *'
|     | |   |-ImplicitCastExpr 0x560375ab7128 <col:9> 'void *(*)(size_t)' <FunctionToPointerDecay>
|     | |   | `-DeclRefExpr 0x560375ab7090 <col:9> 'void *(size_t)' Function 0x560375a985e0 'malloc' 'void *(size_t)'
|     | |   `-ImplicitCastExpr 0x560375ab7168 <col:16> 'unsigned int' <LValueToRValue>
|     | |     `-DeclRefExpr 0x560375ab70b0 <col:16> 'unsigned int' lvalue Var 0x560375ab6868 '__cil_tmp4' 'unsigned int'
|     | `-BinaryOperator 0x560375ab7248 <line:639:3, col:25> 'struct node *' '='
|     |   |-DeclRefExpr 0x560375ab71a0 <col:3> 'struct node *' lvalue Var 0x560375ab6738 'node' 'struct node *'
|     |   `-CStyleCastExpr 0x560375ab7220 <col:10, col:25> 'struct node *' <BitCast>
|     |     `-ImplicitCastExpr 0x560375ab7208 <col:25> 'void *' <LValueToRValue> part_of_explicit_cast
|     |       `-DeclRefExpr 0x560375ab71c0 <col:25> 'void *' lvalue Var 0x560375ab67d0 'tmp' 'void *'
|     |-IfStmt 0x560375ab7378 <line:641:3, line:647:3> has_else
|     | |-UnaryOperator 0x560375ab72c8 <line:641:7, col:9> 'int' prefix '!' cannot overflow
|     | | `-ImplicitCastExpr 0x560375ab72b0 <col:9> 'struct node *' <LValueToRValue>
|     | |   `-DeclRefExpr 0x560375ab7290 <col:9> 'struct node *' lvalue Var 0x560375ab6738 'node' 'struct node *'
|     | |-CompoundStmt 0x560375ab7350 <col:15, line:645:3>
|     | | `-CompoundStmt 0x560375ab7338 <line:642:5, line:644:5>
|     | |   `-CallExpr 0x560375ab7318 <line:643:5, col:11> 'void'
|     | |     `-ImplicitCastExpr 0x560375ab7300 <col:5> 'void (*)(void) __attribute__((noreturn))' <FunctionToPointerDecay>
|     | |       `-DeclRefExpr 0x560375ab72e0 <col:5> 'void (void) __attribute__((noreturn))' Function 0x560375a9bd90 'abort' 'void (void) __attribute__((noreturn))'
|     | `-CompoundStmt 0x560375ab7368 <line:645:10, line:647:3>
|     |-CompoundStmt 0x560375ab77f8 <line:648:3, line:654:3>
|     | |-BinaryOperator 0x560375ab74b0 <line:649:3, col:20> 'int' '='
|     | | |-UnaryOperator 0x560375ab7460 <col:3, col:16> 'int' lvalue prefix '*' cannot overflow
|     | | | `-ParenExpr 0x560375ab7440 <col:4, col:16> 'int *'
|     | | |   `-CStyleCastExpr 0x560375ab7418 <col:5, col:12> 'int *' <BitCast>
|     | | |     `-ImplicitCastExpr 0x560375ab7400 <col:12> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | | |       `-DeclRefExpr 0x560375ab73a0 <col:12> 'struct node *' lvalue Var 0x560375ab6738 'node' 'struct node *'
|     | | `-ImplicitCastExpr 0x560375ab7498 <col:20> 'int' <LValueToRValue>
|     | |   `-DeclRefExpr 0x560375ab7478 <col:20> 'int' lvalue ParmVar 0x560375ab65a8 'value' 'int'
|     | |-BinaryOperator 0x560375ab7568 <line:650:3, col:31> 'unsigned int' '='
|     | | |-DeclRefExpr 0x560375ab74d0 <col:3> 'unsigned int' lvalue Var 0x560375ab6900 '__cil_tmp5' 'unsigned int'
|     | | `-CStyleCastExpr 0x560375ab7540 <col:16, col:31> 'unsigned int' <PointerToIntegral>
|     | |   `-ImplicitCastExpr 0x560375ab7528 <col:31> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |     `-DeclRefExpr 0x560375ab74f0 <col:31> 'struct node *' lvalue Var 0x560375ab6738 'node' 'struct node *'
|     | |-BinaryOperator 0x560375ab7638 <line:651:3, col:29> 'unsigned int' '='
|     | | |-DeclRefExpr 0x560375ab7588 <col:3> 'unsigned int' lvalue Var 0x560375ab6998 '__cil_tmp6' 'unsigned int'
|     | | `-BinaryOperator 0x560375ab7618 <col:16, col:29> 'unsigned int' '+'
|     | |   |-ImplicitCastExpr 0x560375ab75e8 <col:16> 'unsigned int' <LValueToRValue>
|     | |   | `-DeclRefExpr 0x560375ab75a8 <col:16> 'unsigned int' lvalue Var 0x560375ab6900 '__cil_tmp5' 'unsigned int'
|     | |   `-ImplicitCastExpr 0x560375ab7600 <col:29> 'unsigned int' <IntegralCast>
|     | |     `-IntegerLiteral 0x560375ab75c8 <col:29> 'int' 4
|     | |-BinaryOperator 0x560375ab7700 <line:652:3, col:36> 'struct list_head *' '='
|     | | |-DeclRefExpr 0x560375ab7658 <col:3> 'struct list_head *' lvalue Var 0x560375ab6a90 '__cil_tmp7' 'struct list_head *'
|     | | `-CStyleCastExpr 0x560375ab76d8 <col:16, col:36> 'struct list_head *' <IntegralToPointer>
|     | |   `-ImplicitCastExpr 0x560375ab76c0 <col:36> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |     `-DeclRefExpr 0x560375ab7678 <col:36> 'unsigned int' lvalue Var 0x560375ab6998 '__cil_tmp6' 'unsigned int'
|     | `-CallExpr 0x560375ab77b0 <line:653:3, col:33> 'void'
|     |   |-ImplicitCastExpr 0x560375ab7798 <col:3> 'void (*)(struct list_head *, struct list_head *)' <FunctionToPointerDecay>
|     |   | `-DeclRefExpr 0x560375ab7720 <col:3> 'void (struct list_head *, struct list_head *)' Function 0x560375ab5640 'list_add' 'void (struct list_head *, struct list_head *)'
|     |   |-ImplicitCastExpr 0x560375ab77e0 <col:12> 'struct list_head *' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375ab7740 <col:12> 'struct list_head *' lvalue Var 0x560375ab6a90 '__cil_tmp7' 'struct list_head *'
|     |   `-UnaryOperator 0x560375ab7780 <col:24, col:26> 'struct list_head *' prefix '&' cannot overflow
|     |     `-DeclRefExpr 0x560375ab7760 <col:26> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
|     |-CompoundStmt 0x560375ab82d8 <line:655:3, line:671:3>
|     | |-WhileStmt 0x560375ab82a0 <line:656:3, line:669:3>
|     | | |-IntegerLiteral 0x560375ab7830 <line:656:10> 'int' 1
|     | | `-CompoundStmt 0x560375ab8230 <col:13, line:669:3>
|     | |   |-LabelStmt 0x560375ab78a8 <line:657:5, col:40> 'while_18_continue'
|     | |   | `-NullStmt 0x560375ab7850 <col:40>
|     | |   |-BinaryOperator 0x560375ab7958 <line:658:5, col:33> 'unsigned int' '='
|     | |   | |-DeclRefExpr 0x560375ab78c0 <col:5> 'unsigned int' lvalue Var 0x560375ab6b28 '__cil_tmp8' 'unsigned int'
|     | |   | `-CStyleCastExpr 0x560375ab7930 <col:18, col:33> 'unsigned int' <PointerToIntegral>
|     | |   |   `-ImplicitCastExpr 0x560375ab7918 <col:33> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   |     `-DeclRefExpr 0x560375ab78e0 <col:33> 'struct node *' lvalue Var 0x560375ab6738 'node' 'struct node *'
|     | |   |-BinaryOperator 0x560375ab7a28 <line:659:5, col:31> 'unsigned int' '='
|     | |   | |-DeclRefExpr 0x560375ab7978 <col:5> 'unsigned int' lvalue Var 0x560375ab6bc0 '__cil_tmp9' 'unsigned int'
|     | |   | `-BinaryOperator 0x560375ab7a08 <col:18, col:31> 'unsigned int' '+'
|     | |   |   |-ImplicitCastExpr 0x560375ab79d8 <col:18> 'unsigned int' <LValueToRValue>
|     | |   |   | `-DeclRefExpr 0x560375ab7998 <col:18> 'unsigned int' lvalue Var 0x560375ab6b28 '__cil_tmp8' 'unsigned int'
|     | |   |   `-ImplicitCastExpr 0x560375ab79f0 <col:31> 'unsigned int' <IntegralCast>
|     | |   |     `-IntegerLiteral 0x560375ab79b8 <col:31> 'int' 12
|     | |   |-BinaryOperator 0x560375ab7af8 <line:660:5, col:34> 'unsigned int' '='
|     | |   | |-DeclRefExpr 0x560375ab7a48 <col:5> 'unsigned int' lvalue Var 0x560375ab6c58 '__cil_tmp10' 'unsigned int'
|     | |   | `-CStyleCastExpr 0x560375ab7ad0 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   |   `-ImplicitCastExpr 0x560375ab7ab8 <col:34> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   |     `-DeclRefExpr 0x560375ab7a68 <col:34> 'struct node *' lvalue Var 0x560375ab6738 'node' 'struct node *'
|     | |   |-BinaryOperator 0x560375ab7bc8 <line:661:5, col:33> 'unsigned int' '='
|     | |   | |-DeclRefExpr 0x560375ab7b18 <col:5> 'unsigned int' lvalue Var 0x560375ab6cf0 '__cil_tmp11' 'unsigned int'
|     | |   | `-BinaryOperator 0x560375ab7ba8 <col:19, col:33> 'unsigned int' '+'
|     | |   |   |-ImplicitCastExpr 0x560375ab7b78 <col:19> 'unsigned int' <LValueToRValue>
|     | |   |   | `-DeclRefExpr 0x560375ab7b38 <col:19> 'unsigned int' lvalue Var 0x560375ab6c58 '__cil_tmp10' 'unsigned int'
|     | |   |   `-ImplicitCastExpr 0x560375ab7b90 <col:33> 'unsigned int' <IntegralCast>
|     | |   |     `-IntegerLiteral 0x560375ab7b58 <col:33> 'int' 12
|     | |   |-BinaryOperator 0x560375ab7d30 <line:662:5, col:62> 'struct list_head *' '='
|     | |   | |-UnaryOperator 0x560375ab7c90 <col:5, col:38> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |   | | `-ParenExpr 0x560375ab7c70 <col:6, col:38> 'struct list_head **'
|     | |   | |   `-CStyleCastExpr 0x560375ab7c48 <col:7, col:28> 'struct list_head **' <IntegralToPointer>
|     | |   | |     `-ImplicitCastExpr 0x560375ab7c30 <col:28> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |       `-DeclRefExpr 0x560375ab7be8 <col:28> 'unsigned int' lvalue Var 0x560375ab6bc0 '__cil_tmp9' 'unsigned int'
|     | |   | `-CStyleCastExpr 0x560375ab7d08 <col:42, col:62> 'struct list_head *' <IntegralToPointer>
|     | |   |   `-ImplicitCastExpr 0x560375ab7cf0 <col:62> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   |     `-DeclRefExpr 0x560375ab7ca8 <col:62> 'unsigned int' lvalue Var 0x560375ab6cf0 '__cil_tmp11' 'unsigned int'
|     | |   |-BinaryOperator 0x560375ab7de8 <line:663:5, col:34> 'unsigned int' '='
|     | |   | |-DeclRefExpr 0x560375ab7d50 <col:5> 'unsigned int' lvalue Var 0x560375ab6d88 '__cil_tmp12' 'unsigned int'
|     | |   | `-CStyleCastExpr 0x560375ab7dc0 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   |   `-ImplicitCastExpr 0x560375ab7da8 <col:34> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   |     `-DeclRefExpr 0x560375ab7d70 <col:34> 'struct node *' lvalue Var 0x560375ab6738 'node' 'struct node *'
|     | |   |-BinaryOperator 0x560375ab7eb8 <line:664:5, col:33> 'unsigned int' '='
|     | |   | |-DeclRefExpr 0x560375ab7e08 <col:5> 'unsigned int' lvalue Var 0x560375ab6e20 '__cil_tmp13' 'unsigned int'
|     | |   | `-BinaryOperator 0x560375ab7e98 <col:19, col:33> 'unsigned int' '+'
|     | |   |   |-ImplicitCastExpr 0x560375ab7e68 <col:19> 'unsigned int' <LValueToRValue>
|     | |   |   | `-DeclRefExpr 0x560375ab7e28 <col:19> 'unsigned int' lvalue Var 0x560375ab6d88 '__cil_tmp12' 'unsigned int'
|     | |   |   `-ImplicitCastExpr 0x560375ab7e80 <col:33> 'unsigned int' <IntegralCast>
|     | |   |     `-IntegerLiteral 0x560375ab7e48 <col:33> 'int' 12
|     | |   |-BinaryOperator 0x560375ab7f70 <line:665:5, col:34> 'unsigned int' '='
|     | |   | |-DeclRefExpr 0x560375ab7ed8 <col:5> 'unsigned int' lvalue Var 0x560375ab6eb8 '__cil_tmp14' 'unsigned int'
|     | |   | `-CStyleCastExpr 0x560375ab7f48 <col:19, col:34> 'unsigned int' <PointerToIntegral>
|     | |   |   `-ImplicitCastExpr 0x560375ab7f30 <col:34> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |   |     `-DeclRefExpr 0x560375ab7ef8 <col:34> 'struct node *' lvalue Var 0x560375ab6738 'node' 'struct node *'
|     | |   |-BinaryOperator 0x560375ab8040 <line:666:5, col:33> 'unsigned int' '='
|     | |   | |-DeclRefExpr 0x560375ab7f90 <col:5> 'unsigned int' lvalue Var 0x560375ab6f50 '__cil_tmp15' 'unsigned int'
|     | |   | `-BinaryOperator 0x560375ab8020 <col:19, col:33> 'unsigned int' '+'
|     | |   |   |-ImplicitCastExpr 0x560375ab7ff0 <col:19> 'unsigned int' <LValueToRValue>
|     | |   |   | `-DeclRefExpr 0x560375ab7fb0 <col:19> 'unsigned int' lvalue Var 0x560375ab6eb8 '__cil_tmp14' 'unsigned int'
|     | |   |   `-ImplicitCastExpr 0x560375ab8008 <col:33> 'unsigned int' <IntegralCast>
|     | |   |     `-IntegerLiteral 0x560375ab7fd0 <col:33> 'int' 12
|     | |   |-BinaryOperator 0x560375ab81a8 <line:667:5, col:63> 'struct list_head *' '='
|     | |   | |-UnaryOperator 0x560375ab8108 <col:5, col:39> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |   | | `-ParenExpr 0x560375ab80e8 <col:6, col:39> 'struct list_head **'
|     | |   | |   `-CStyleCastExpr 0x560375ab80c0 <col:7, col:28> 'struct list_head **' <IntegralToPointer>
|     | |   | |     `-ImplicitCastExpr 0x560375ab80a8 <col:28> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   | |       `-DeclRefExpr 0x560375ab8060 <col:28> 'unsigned int' lvalue Var 0x560375ab6e20 '__cil_tmp13' 'unsigned int'
|     | |   | `-CStyleCastExpr 0x560375ab8180 <col:43, col:63> 'struct list_head *' <IntegralToPointer>
|     | |   |   `-ImplicitCastExpr 0x560375ab8168 <col:63> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |   |     `-DeclRefExpr 0x560375ab8120 <col:63> 'unsigned int' lvalue Var 0x560375ab6f50 '__cil_tmp15' 'unsigned int'
|     | |   `-GotoStmt 0x560375ab8218 <line:668:5, col:10> 'while_18_break' 0x560375ab81c8
|     | `-LabelStmt 0x560375ab82c0 <line:670:3, col:35> 'while_18_break'
|     |   `-NullStmt 0x560375ab82b8 <col:35>
|     `-ReturnStmt 0x560375ab82f8 <line:672:3>
|-FunctionDecl 0x560375ab8460 <line:675:1, line:698:1> line:675:13 used gl_read 'void (void)' static
| `-CompoundStmt 0x560375ab8ab0 <line:676:1, line:698:1>
|   |-DeclStmt 0x560375ab8580 <line:676:3, col:11>
|   | `-VarDecl 0x560375ab8518 <col:3, col:7> col:7 used tmp 'int'
|   |-DeclStmt 0x560375ab8618 <line:677:3, col:15>
|   | `-VarDecl 0x560375ab85b0 <col:3, col:7> col:7 used tmp___0 'int'
|   `-CompoundStmt 0x560375ab8a80 <line:679:3, line:697:1>
|     |-CompoundStmt 0x560375ab8a50 <line:680:3, line:695:3>
|     | |-WhileStmt 0x560375ab8a18 <line:681:3, line:693:3>
|     | | |-IntegerLiteral 0x560375ab8630 <line:681:10> 'int' 1
|     | | `-CompoundStmt 0x560375ab89f0 <col:13, line:693:3>
|     | |   |-LabelStmt 0x560375ab86a8 <line:682:5, col:40> 'while_19_continue'
|     | |   | `-NullStmt 0x560375ab8650 <col:40>
|     | |   |-CompoundStmt 0x560375ab88d8 <line:683:5, line:687:5>
|     | |   | |-BinaryOperator 0x560375ab8760 <line:684:5, col:33> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375ab86c0 <col:5> 'int' lvalue Var 0x560375ab8518 'tmp' 'int'
|     | |   | | `-CallExpr 0x560375ab8740 <col:11, col:33> 'int'
|     | |   | |   `-ImplicitCastExpr 0x560375ab8728 <col:11> 'int (*)(void)' <FunctionToPointerDecay>
|     | |   | |     `-DeclRefExpr 0x560375ab86e0 <col:11> 'int (void)' Function 0x560375a9bf50 '__VERIFIER_nondet_int' 'int (void)'
|     | |   | |-CallExpr 0x560375ab8800 <line:685:5, col:18> 'void'
|     | |   | | |-ImplicitCastExpr 0x560375ab87e8 <col:5> 'void (*)(int)' <FunctionToPointerDecay>
|     | |   | | | `-DeclRefExpr 0x560375ab8780 <col:5> 'void (int)' Function 0x560375ab6668 'gl_insert' 'void (int)'
|     | |   | | `-ImplicitCastExpr 0x560375ab8828 <col:15> 'int' <LValueToRValue>
|     | |   | |   `-DeclRefExpr 0x560375ab87a0 <col:15> 'int' lvalue Var 0x560375ab8518 'tmp' 'int'
|     | |   | `-BinaryOperator 0x560375ab88b8 <line:686:5, col:37> 'int' '='
|     | |   |   |-DeclRefExpr 0x560375ab8840 <col:5> 'int' lvalue Var 0x560375ab85b0 'tmp___0' 'int'
|     | |   |   `-CallExpr 0x560375ab8898 <col:15, col:37> 'int'
|     | |   |     `-ImplicitCastExpr 0x560375ab8880 <col:15> 'int (*)(void)' <FunctionToPointerDecay>
|     | |   |       `-DeclRefExpr 0x560375ab8860 <col:15> 'int (void)' Function 0x560375a9bf50 '__VERIFIER_nondet_int' 'int (void)'
|     | |   `-IfStmt 0x560375ab89c8 <line:688:5, line:692:5> has_else
|     | |     |-ImplicitCastExpr 0x560375ab8920 <line:688:9> 'int' <LValueToRValue>
|     | |     | `-DeclRefExpr 0x560375ab8900 <col:9> 'int' lvalue Var 0x560375ab85b0 'tmp___0' 'int'
|     | |     |-CompoundStmt 0x560375ab8938 <col:18, line:690:5>
|     | |     `-CompoundStmt 0x560375ab89b0 <col:12, line:692:5>
|     | |       `-GotoStmt 0x560375ab8998 <line:691:7, col:12> 'while_19_break' 0x560375ab8948
|     | `-LabelStmt 0x560375ab8a38 <line:694:3, col:35> 'while_19_break'
|     |   `-NullStmt 0x560375ab8a30 <col:35>
|     `-ReturnStmt 0x560375ab8a70 <line:696:3>
|-FunctionDecl 0x560375ab8b70 <line:699:1, line:749:1> line:699:13 used gl_destroy 'void (void)' static
| `-CompoundStmt 0x560375aba510 <line:700:1, line:749:1>
|   |-DeclStmt 0x560375ab8ca0 <line:700:3, col:26>
|   | `-VarDecl 0x560375ab8c38 <col:3, col:21> col:21 used next 'struct list_head *'
|   |-DeclStmt 0x560375ab8d48 <line:701:3, col:32>
|   | `-VarDecl 0x560375ab8ce0 <col:3, col:21> col:21 used __cil_tmp2 'struct list_head *'
|   |-DeclStmt 0x560375ab8de0 <line:702:3, col:27>
|   | `-VarDecl 0x560375ab8d78 <col:3, col:16> col:16 used __cil_tmp3 'unsigned int'
|   |-DeclStmt 0x560375ab8e78 <line:703:3, col:27>
|   | `-VarDecl 0x560375ab8e10 <col:3, col:16> col:16 used __cil_tmp4 'unsigned int'
|   |-DeclStmt 0x560375ab8f20 <line:704:3, col:32>
|   | `-VarDecl 0x560375ab8eb8 <col:3, col:21> col:21 used __cil_tmp5 'struct list_head *'
|   |-DeclStmt 0x560375ab8fc8 <line:705:3, col:27>
|   | `-VarDecl 0x560375ab8f60 <col:3, col:16> col:16 used __cil_tmp6 'struct node *'
|   |-DeclStmt 0x560375ab9060 <line:706:3, col:27>
|   | `-VarDecl 0x560375ab8ff8 <col:3, col:16> col:16 used __cil_tmp7 'unsigned int'
|   |-DeclStmt 0x560375ab90f8 <line:707:3, col:27>
|   | `-VarDecl 0x560375ab9090 <col:3, col:16> col:16 used __cil_tmp8 'unsigned int'
|   |-DeclStmt 0x560375ab91a0 <line:708:3, col:32>
|   | `-VarDecl 0x560375ab9138 <col:3, col:21> col:21 used __cil_tmp9 'struct list_head *'
|   |-DeclStmt 0x560375ab9238 <line:709:3, col:29>
|   | `-VarDecl 0x560375ab91d0 <col:3, col:17> col:17 used __cil_tmp10 'unsigned long'
|   |-DeclStmt 0x560375ab92d0 <line:710:3, col:21>
|   | `-VarDecl 0x560375ab9268 <col:3, col:9> col:9 used __cil_tmp11 'char *'
|   |-DeclStmt 0x560375ab9368 <line:711:3, col:21>
|   | `-VarDecl 0x560375ab9300 <col:3, col:9> col:9 used __cil_tmp12 'char *'
|   |-DeclStmt 0x560375ab9410 <line:712:3, col:28>
|   | `-VarDecl 0x560375ab93a8 <col:3, col:16> col:16 used __cil_tmp13 'struct node *'
|   |-DeclStmt 0x560375ab94a8 <line:713:3, col:21>
|   | `-VarDecl 0x560375ab9440 <col:3, col:9> col:9 used __cil_tmp14 'void *'
|   `-CompoundStmt 0x560375aba4f0 <line:715:3, line:748:1>
|     |-CompoundStmt 0x560375aba4c0 <line:716:3, line:746:3>
|     | |-WhileStmt 0x560375aba488 <line:717:3, line:744:3>
|     | | |-IntegerLiteral 0x560375ab94c0 <line:717:10> 'int' 1
|     | | `-CompoundStmt 0x560375aba450 <col:13, line:744:3>
|     | |   |-LabelStmt 0x560375ab9538 <line:718:5, col:40> 'while_20_continue'
|     | |   | `-NullStmt 0x560375ab94e0 <col:40>
|     | |   |-BinaryOperator 0x560375ab95a8 <line:719:5, col:20> 'struct list_head *' '='
|     | |   | |-DeclRefExpr 0x560375ab9550 <col:5> 'struct list_head *' lvalue Var 0x560375ab8ce0 '__cil_tmp2' 'struct list_head *'
|     | |   | `-UnaryOperator 0x560375ab9590 <col:18, col:20> 'struct list_head *' prefix '&' cannot overflow
|     | |   |   `-DeclRefExpr 0x560375ab9570 <col:20> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
|     | |   |-BinaryOperator 0x560375ab96c0 <line:720:5, col:45> 'struct list_head *' '='
|     | |   | |-DeclRefExpr 0x560375ab95c8 <col:5> 'struct list_head *' lvalue Var 0x560375ab8c38 'next' 'struct list_head *'
|     | |   | `-ImplicitCastExpr 0x560375ab96a8 <col:12, col:45> 'struct list_head *' <LValueToRValue>
|     | |   |   `-UnaryOperator 0x560375ab9690 <col:12, col:45> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |   |     `-ParenExpr 0x560375ab9670 <col:13, col:45> 'struct list_head **'
|     | |   |       `-CStyleCastExpr 0x560375ab9648 <col:14, col:35> 'struct list_head **' <BitCast>
|     | |   |         `-ImplicitCastExpr 0x560375ab9630 <col:35> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   |           `-DeclRefExpr 0x560375ab95e8 <col:35> 'struct list_head *' lvalue Var 0x560375ab8ce0 '__cil_tmp2' 'struct list_head *'
|     | |   |-CompoundStmt 0x560375ab99d8 <line:721:5, line:729:5>
|     | |   | |-BinaryOperator 0x560375ab9778 <line:722:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab96e0 <col:5> 'unsigned int' lvalue Var 0x560375ab8d78 '__cil_tmp3' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab9750 <col:18, col:33> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375ab9738 <col:33> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375ab9700 <col:33> 'struct list_head *' lvalue Var 0x560375ab8c38 'next' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375ab9870 <line:723:5, col:43> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375ab9798 <col:5> 'unsigned int' lvalue Var 0x560375ab8e10 '__cil_tmp4' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375ab9848 <col:18, col:43> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ParenExpr 0x560375ab9828 <col:33, col:43> 'struct list_head *'
|     | |   | |     `-UnaryOperator 0x560375ab97d8 <col:34, col:36> 'struct list_head *' prefix '&' cannot overflow
|     | |   | |       `-DeclRefExpr 0x560375ab97b8 <col:36> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
|     | |   | `-IfStmt 0x560375ab99b0 <line:724:5, line:728:5> has_else
|     | |   |   |-BinaryOperator 0x560375ab9900 <line:724:9, col:23> 'int' '!='
|     | |   |   | |-ImplicitCastExpr 0x560375ab98d0 <col:9> 'unsigned int' <LValueToRValue>
|     | |   |   | | `-DeclRefExpr 0x560375ab9890 <col:9> 'unsigned int' lvalue Var 0x560375ab8e10 '__cil_tmp4' 'unsigned int'
|     | |   |   | `-ImplicitCastExpr 0x560375ab98e8 <col:23> 'unsigned int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375ab98b0 <col:23> 'unsigned int' lvalue Var 0x560375ab8d78 '__cil_tmp3' 'unsigned int'
|     | |   |   |-CompoundStmt 0x560375ab9920 <col:35, line:726:5>
|     | |   |   `-CompoundStmt 0x560375ab9998 <col:12, line:728:5>
|     | |   |     `-GotoStmt 0x560375ab9980 <line:727:7, col:12> 'while_20_break' 0x560375ab9930
|     | |   `-CompoundStmt 0x560375aba3e0 <line:730:5, line:743:5>
|     | |     |-BinaryOperator 0x560375ab9a58 <line:731:5, col:20> 'struct list_head *' '='
|     | |     | |-DeclRefExpr 0x560375ab9a00 <col:5> 'struct list_head *' lvalue Var 0x560375ab8eb8 '__cil_tmp5' 'struct list_head *'
|     | |     | `-UnaryOperator 0x560375ab9a40 <col:18, col:20> 'struct list_head *' prefix '&' cannot overflow
|     | |     |   `-DeclRefExpr 0x560375ab9a20 <col:20> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
|     | |     |-BinaryOperator 0x560375ab9c38 <line:732:5, col:69> 'struct list_head *' '='
|     | |     | |-UnaryOperator 0x560375ab9b48 <col:5, col:38> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |     | | `-ParenExpr 0x560375ab9b28 <col:6, col:38> 'struct list_head **'
|     | |     | |   `-CStyleCastExpr 0x560375ab9b00 <col:7, col:28> 'struct list_head **' <BitCast>
|     | |     | |     `-ImplicitCastExpr 0x560375ab9ae8 <col:28> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |     | |       `-DeclRefExpr 0x560375ab9a78 <col:28> 'struct list_head *' lvalue Var 0x560375ab8eb8 '__cil_tmp5' 'struct list_head *'
|     | |     | `-ImplicitCastExpr 0x560375ab9c20 <col:42, col:69> 'struct list_head *' <LValueToRValue>
|     | |     |   `-UnaryOperator 0x560375ab9c08 <col:42, col:69> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |     |     `-ParenExpr 0x560375ab9be8 <col:43, col:69> 'struct list_head **'
|     | |     |       `-CStyleCastExpr 0x560375ab9bc0 <col:44, col:65> 'struct list_head **' <BitCast>
|     | |     |         `-ImplicitCastExpr 0x560375ab9ba8 <col:65> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |     |           `-DeclRefExpr 0x560375ab9b60 <col:65> 'struct list_head *' lvalue Var 0x560375ab8c38 'next' 'struct list_head *'
|     | |     |-BinaryOperator 0x560375ab9ce8 <line:733:5, col:33> 'struct node *' '='
|     | |     | |-DeclRefExpr 0x560375ab9c58 <col:5> 'struct node *' lvalue Var 0x560375ab8f60 '__cil_tmp6' 'struct node *'
|     | |     | `-CStyleCastExpr 0x560375ab9cc0 <col:18, col:33> 'struct node *' <NullToPointer>
|     | |     |   `-IntegerLiteral 0x560375ab9c78 <col:33> 'int' 0
|     | |     |-BinaryOperator 0x560375ab9da0 <line:734:5, col:33> 'unsigned int' '='
|     | |     | |-DeclRefExpr 0x560375ab9d08 <col:5> 'unsigned int' lvalue Var 0x560375ab8ff8 '__cil_tmp7' 'unsigned int'
|     | |     | `-CStyleCastExpr 0x560375ab9d78 <col:18, col:33> 'unsigned int' <PointerToIntegral>
|     | |     |   `-ImplicitCastExpr 0x560375ab9d60 <col:33> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |     |     `-DeclRefExpr 0x560375ab9d28 <col:33> 'struct node *' lvalue Var 0x560375ab8f60 '__cil_tmp6' 'struct node *'
|     | |     |-BinaryOperator 0x560375ab9e70 <line:735:5, col:31> 'unsigned int' '='
|     | |     | |-DeclRefExpr 0x560375ab9dc0 <col:5> 'unsigned int' lvalue Var 0x560375ab9090 '__cil_tmp8' 'unsigned int'
|     | |     | `-BinaryOperator 0x560375ab9e50 <col:18, col:31> 'unsigned int' '+'
|     | |     |   |-ImplicitCastExpr 0x560375ab9e20 <col:18> 'unsigned int' <LValueToRValue>
|     | |     |   | `-DeclRefExpr 0x560375ab9de0 <col:18> 'unsigned int' lvalue Var 0x560375ab8ff8 '__cil_tmp7' 'unsigned int'
|     | |     |   `-ImplicitCastExpr 0x560375ab9e38 <col:31> 'unsigned int' <IntegralCast>
|     | |     |     `-IntegerLiteral 0x560375ab9e00 <col:31> 'int' 4
|     | |     |-BinaryOperator 0x560375ab9f38 <line:736:5, col:38> 'struct list_head *' '='
|     | |     | |-DeclRefExpr 0x560375ab9e90 <col:5> 'struct list_head *' lvalue Var 0x560375ab9138 '__cil_tmp9' 'struct list_head *'
|     | |     | `-CStyleCastExpr 0x560375ab9f10 <col:18, col:38> 'struct list_head *' <IntegralToPointer>
|     | |     |   `-ImplicitCastExpr 0x560375ab9ef8 <col:38> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     | |     |     `-DeclRefExpr 0x560375ab9eb0 <col:38> 'unsigned int' lvalue Var 0x560375ab9090 '__cil_tmp8' 'unsigned int'
|     | |     |-BinaryOperator 0x560375ab9ff0 <line:737:5, col:35> 'unsigned long' '='
|     | |     | |-DeclRefExpr 0x560375ab9f58 <col:5> 'unsigned long' lvalue Var 0x560375ab91d0 '__cil_tmp10' 'unsigned long'
|     | |     | `-CStyleCastExpr 0x560375ab9fc8 <col:19, col:35> 'unsigned long' <PointerToIntegral>
|     | |     |   `-ImplicitCastExpr 0x560375ab9fb0 <col:35> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |     |     `-DeclRefExpr 0x560375ab9f78 <col:35> 'struct list_head *' lvalue Var 0x560375ab9138 '__cil_tmp9' 'struct list_head *'
|     | |     |-BinaryOperator 0x560375aba0a8 <line:738:5, col:27> 'char *' '='
|     | |     | |-DeclRefExpr 0x560375aba010 <col:5> 'char *' lvalue Var 0x560375ab9268 '__cil_tmp11' 'char *'
|     | |     | `-CStyleCastExpr 0x560375aba080 <col:19, col:27> 'char *' <BitCast>
|     | |     |   `-ImplicitCastExpr 0x560375aba068 <col:27> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |     |     `-DeclRefExpr 0x560375aba030 <col:27> 'struct list_head *' lvalue Var 0x560375ab8c38 'next' 'struct list_head *'
|     | |     |-BinaryOperator 0x560375aba178 <line:739:5, col:33> 'char *' '='
|     | |     | |-DeclRefExpr 0x560375aba0c8 <col:5> 'char *' lvalue Var 0x560375ab9300 '__cil_tmp12' 'char *'
|     | |     | `-BinaryOperator 0x560375aba158 <col:19, col:33> 'char *' '-'
|     | |     |   |-ImplicitCastExpr 0x560375aba128 <col:19> 'char *' <LValueToRValue>
|     | |     |   | `-DeclRefExpr 0x560375aba0e8 <col:19> 'char *' lvalue Var 0x560375ab9268 '__cil_tmp11' 'char *'
|     | |     |   `-ImplicitCastExpr 0x560375aba140 <col:33> 'unsigned long' <LValueToRValue>
|     | |     |     `-DeclRefExpr 0x560375aba108 <col:33> 'unsigned long' lvalue Var 0x560375ab91d0 '__cil_tmp10' 'unsigned long'
|     | |     |-BinaryOperator 0x560375aba240 <line:740:5, col:34> 'struct node *' '='
|     | |     | |-DeclRefExpr 0x560375aba198 <col:5> 'struct node *' lvalue Var 0x560375ab93a8 '__cil_tmp13' 'struct node *'
|     | |     | `-CStyleCastExpr 0x560375aba218 <col:19, col:34> 'struct node *' <BitCast>
|     | |     |   `-ImplicitCastExpr 0x560375aba200 <col:34> 'char *' <LValueToRValue> part_of_explicit_cast
|     | |     |     `-DeclRefExpr 0x560375aba1b8 <col:34> 'char *' lvalue Var 0x560375ab9300 '__cil_tmp12' 'char *'
|     | |     |-BinaryOperator 0x560375aba2f8 <line:741:5, col:27> 'void *' '='
|     | |     | |-DeclRefExpr 0x560375aba260 <col:5> 'void *' lvalue Var 0x560375ab9440 '__cil_tmp14' 'void *'
|     | |     | `-CStyleCastExpr 0x560375aba2d0 <col:19, col:27> 'void *' <BitCast>
|     | |     |   `-ImplicitCastExpr 0x560375aba2b8 <col:27> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     | |     |     `-DeclRefExpr 0x560375aba280 <col:27> 'struct node *' lvalue Var 0x560375ab93a8 '__cil_tmp13' 'struct node *'
|     | |     `-CallExpr 0x560375aba3a0 <line:742:5, col:21> 'void'
|     | |       |-ImplicitCastExpr 0x560375aba388 <col:5> 'void (*)(void *)' <FunctionToPointerDecay>
|     | |       | `-DeclRefExpr 0x560375aba318 <col:5> 'void (void *)' Function 0x560375a9bbf8 'free' 'void (void *)'
|     | |       `-ImplicitCastExpr 0x560375aba3c8 <col:10> 'void *' <LValueToRValue>
|     | |         `-DeclRefExpr 0x560375aba338 <col:10> 'void *' lvalue Var 0x560375ab9440 '__cil_tmp14' 'void *'
|     | `-LabelStmt 0x560375aba4a8 <line:745:3, col:35> 'while_20_break'
|     |   `-NullStmt 0x560375aba4a0 <col:35>
|     `-ReturnStmt 0x560375aba4e0 <line:747:3>
|-FunctionDecl 0x560375aba6c0 <line:750:1, line:771:1> line:750:12 used val_from_node 'int (struct list_head *)' static
| |-ParmVarDecl 0x560375aba5c0 <col:26, col:44> col:44 used head 'struct list_head *'
| `-CompoundStmt 0x560375abb3d8 <line:751:1, line:771:1>
|   |-DeclStmt 0x560375aba7f8 <line:751:3, col:22>
|   | `-VarDecl 0x560375aba790 <col:3, col:16> col:16 used entry 'struct node *'
|   |-DeclStmt 0x560375aba8a0 <line:752:3, col:27>
|   | `-VarDecl 0x560375aba838 <col:3, col:16> col:16 used __cil_tmp3 'struct node *'
|   |-DeclStmt 0x560375aba938 <line:753:3, col:27>
|   | `-VarDecl 0x560375aba8d0 <col:3, col:16> col:16 used __cil_tmp4 'unsigned int'
|   |-DeclStmt 0x560375aba9d0 <line:754:3, col:27>
|   | `-VarDecl 0x560375aba968 <col:3, col:16> col:16 used __cil_tmp5 'unsigned int'
|   |-DeclStmt 0x560375abaa78 <line:755:3, col:32>
|   | `-VarDecl 0x560375abaa10 <col:3, col:21> col:21 used __cil_tmp6 'struct list_head *'
|   |-DeclStmt 0x560375abab38 <line:756:3, col:28>
|   | `-VarDecl 0x560375abaad0 <col:3, col:17> col:17 used __cil_tmp7 'unsigned long'
|   |-DeclStmt 0x560375ababd0 <line:757:3, col:20>
|   | `-VarDecl 0x560375abab68 <col:3, col:9> col:9 used __cil_tmp8 'char *'
|   |-DeclStmt 0x560375abac68 <line:758:3, col:20>
|   | `-VarDecl 0x560375abac00 <col:3, col:9> col:9 used __cil_tmp9 'char *'
|   `-CompoundStmt 0x560375abb380 <line:760:3, line:770:1>
|     |-BinaryOperator 0x560375abad10 <line:761:3, col:31> 'struct node *' '='
|     | |-DeclRefExpr 0x560375abac80 <col:3> 'struct node *' lvalue Var 0x560375aba838 '__cil_tmp3' 'struct node *'
|     | `-CStyleCastExpr 0x560375abace8 <col:16, col:31> 'struct node *' <NullToPointer>
|     |   `-IntegerLiteral 0x560375abaca0 <col:31> 'int' 0
|     |-BinaryOperator 0x560375abadc8 <line:762:3, col:31> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375abad30 <col:3> 'unsigned int' lvalue Var 0x560375aba8d0 '__cil_tmp4' 'unsigned int'
|     | `-CStyleCastExpr 0x560375abada0 <col:16, col:31> 'unsigned int' <PointerToIntegral>
|     |   `-ImplicitCastExpr 0x560375abad88 <col:31> 'struct node *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375abad50 <col:31> 'struct node *' lvalue Var 0x560375aba838 '__cil_tmp3' 'struct node *'
|     |-BinaryOperator 0x560375abae98 <line:763:3, col:29> 'unsigned int' '='
|     | |-DeclRefExpr 0x560375abade8 <col:3> 'unsigned int' lvalue Var 0x560375aba968 '__cil_tmp5' 'unsigned int'
|     | `-BinaryOperator 0x560375abae78 <col:16, col:29> 'unsigned int' '+'
|     |   |-ImplicitCastExpr 0x560375abae48 <col:16> 'unsigned int' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375abae08 <col:16> 'unsigned int' lvalue Var 0x560375aba8d0 '__cil_tmp4' 'unsigned int'
|     |   `-ImplicitCastExpr 0x560375abae60 <col:29> 'unsigned int' <IntegralCast>
|     |     `-IntegerLiteral 0x560375abae28 <col:29> 'int' 4
|     |-BinaryOperator 0x560375abaf60 <line:764:3, col:36> 'struct list_head *' '='
|     | |-DeclRefExpr 0x560375abaeb8 <col:3> 'struct list_head *' lvalue Var 0x560375abaa10 '__cil_tmp6' 'struct list_head *'
|     | `-CStyleCastExpr 0x560375abaf38 <col:16, col:36> 'struct list_head *' <IntegralToPointer>
|     |   `-ImplicitCastExpr 0x560375abaf20 <col:36> 'unsigned int' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375abaed8 <col:36> 'unsigned int' lvalue Var 0x560375aba968 '__cil_tmp5' 'unsigned int'
|     |-BinaryOperator 0x560375abb018 <line:765:3, col:32> 'unsigned long' '='
|     | |-DeclRefExpr 0x560375abaf80 <col:3> 'unsigned long' lvalue Var 0x560375abaad0 '__cil_tmp7' 'unsigned long'
|     | `-CStyleCastExpr 0x560375abaff0 <col:16, col:32> 'unsigned long' <PointerToIntegral>
|     |   `-ImplicitCastExpr 0x560375abafd8 <col:32> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375abafa0 <col:32> 'struct list_head *' lvalue Var 0x560375abaa10 '__cil_tmp6' 'struct list_head *'
|     |-BinaryOperator 0x560375abb0d0 <line:766:3, col:24> 'char *' '='
|     | |-DeclRefExpr 0x560375abb038 <col:3> 'char *' lvalue Var 0x560375abab68 '__cil_tmp8' 'char *'
|     | `-CStyleCastExpr 0x560375abb0a8 <col:16, col:24> 'char *' <BitCast>
|     |   `-ImplicitCastExpr 0x560375abb090 <col:24> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375abb058 <col:24> 'struct list_head *' lvalue ParmVar 0x560375aba5c0 'head' 'struct list_head *'
|     |-BinaryOperator 0x560375abb1a0 <line:767:3, col:29> 'char *' '='
|     | |-DeclRefExpr 0x560375abb0f0 <col:3> 'char *' lvalue Var 0x560375abac00 '__cil_tmp9' 'char *'
|     | `-BinaryOperator 0x560375abb180 <col:16, col:29> 'char *' '-'
|     |   |-ImplicitCastExpr 0x560375abb150 <col:16> 'char *' <LValueToRValue>
|     |   | `-DeclRefExpr 0x560375abb110 <col:16> 'char *' lvalue Var 0x560375abab68 '__cil_tmp8' 'char *'
|     |   `-ImplicitCastExpr 0x560375abb168 <col:29> 'unsigned long' <LValueToRValue>
|     |     `-DeclRefExpr 0x560375abb130 <col:29> 'unsigned long' lvalue Var 0x560375abaad0 '__cil_tmp7' 'unsigned long'
|     |-BinaryOperator 0x560375abb268 <line:768:3, col:26> 'struct node *' '='
|     | |-DeclRefExpr 0x560375abb1c0 <col:3> 'struct node *' lvalue Var 0x560375aba790 'entry' 'struct node *'
|     | `-CStyleCastExpr 0x560375abb240 <col:11, col:26> 'struct node *' <BitCast>
|     |   `-ImplicitCastExpr 0x560375abb228 <col:26> 'char *' <LValueToRValue> part_of_explicit_cast
|     |     `-DeclRefExpr 0x560375abb1e0 <col:26> 'char *' lvalue Var 0x560375abac00 '__cil_tmp9' 'char *'
|     `-ReturnStmt 0x560375abb370 <line:769:3, col:26>
|       `-ImplicitCastExpr 0x560375abb358 <col:10, col:26> 'int' <LValueToRValue>
|         `-ParenExpr 0x560375abb338 <col:10, col:26> 'int' lvalue
|           `-UnaryOperator 0x560375abb320 <col:11, col:25> 'int' lvalue prefix '*' cannot overflow
|             `-ParenExpr 0x560375abb300 <col:12, col:25> 'int *'
|               `-CStyleCastExpr 0x560375abb2d8 <col:13, col:20> 'int *' <BitCast>
|                 `-ImplicitCastExpr 0x560375abb2c0 <col:20> 'struct node *' <LValueToRValue> part_of_explicit_cast
|                   `-DeclRefExpr 0x560375abb288 <col:20> 'struct node *' lvalue Var 0x560375aba790 'entry' 'struct node *'
|-FunctionDecl 0x560375abb4f8 <line:772:1, line:822:1> line:772:14 used gl_sort_pass '_Bool (void)' static
| `-CompoundStmt 0x560375abda68 <line:773:1, line:822:1>
|   |-DeclStmt 0x560375abb610 <line:773:3, col:20>
|   | `-VarDecl 0x560375abb5a8 <col:3, col:9> col:9 used any_change '_Bool'
|   |-DeclStmt 0x560375abb6b8 <line:774:3, col:26>
|   | `-VarDecl 0x560375abb650 <col:3, col:21> col:21 used pos0 'struct list_head *'
|   |-DeclStmt 0x560375abb760 <line:775:3, col:26>
|   | `-VarDecl 0x560375abb6f8 <col:3, col:21> col:21 used pos1 'struct list_head *'
|   |-DeclStmt 0x560375abb7f8 <line:776:3, col:12>
|   | `-VarDecl 0x560375abb790 <col:3, col:7> col:7 used val0 'int'
|   |-DeclStmt 0x560375abb890 <line:777:3, col:11>
|   | `-VarDecl 0x560375abb828 <col:3, col:7> col:7 used tmp 'int'
|   |-DeclStmt 0x560375abb928 <line:778:3, col:12>
|   | `-VarDecl 0x560375abb8c0 <col:3, col:7> col:7 used val1 'int'
|   |-DeclStmt 0x560375abb9c0 <line:779:3, col:15>
|   | `-VarDecl 0x560375abb958 <col:3, col:7> col:7 used tmp___0 'int'
|   |-DeclStmt 0x560375abba68 <line:780:3, col:32>
|   | `-VarDecl 0x560375abba00 <col:3, col:21> col:21 used __cil_tmp8 'struct list_head *'
|   |-DeclStmt 0x560375abcb58 <line:781:3, col:27>
|   | `-VarDecl 0x560375abcaf0 <col:3, col:16> col:16 used __cil_tmp9 'unsigned int'
|   |-DeclStmt 0x560375abcbf0 <line:782:3, col:28>
|   | `-VarDecl 0x560375abcb88 <col:3, col:16> col:16 used __cil_tmp10 'unsigned int'
|   `-CompoundStmt 0x560375abda30 <line:784:3, line:821:1>
|     |-BinaryOperator 0x560375abcc80 <line:785:3, col:23> '_Bool' '='
|     | |-DeclRefExpr 0x560375abcc08 <col:3> '_Bool' lvalue Var 0x560375abb5a8 'any_change' '_Bool'
|     | `-CStyleCastExpr 0x560375abcc58 <col:16, col:23> '_Bool' <IntegralToBoolean>
|     |   `-IntegerLiteral 0x560375abcc28 <col:23> 'int' 0
|     |-BinaryOperator 0x560375abccf8 <line:786:3, col:18> 'struct list_head *' '='
|     | |-DeclRefExpr 0x560375abcca0 <col:3> 'struct list_head *' lvalue Var 0x560375abba00 '__cil_tmp8' 'struct list_head *'
|     | `-UnaryOperator 0x560375abcce0 <col:16, col:18> 'struct list_head *' prefix '&' cannot overflow
|     |   `-DeclRefExpr 0x560375abccc0 <col:18> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
|     |-BinaryOperator 0x560375abce10 <line:787:3, col:43> 'struct list_head *' '='
|     | |-DeclRefExpr 0x560375abcd18 <col:3> 'struct list_head *' lvalue Var 0x560375abb650 'pos0' 'struct list_head *'
|     | `-ImplicitCastExpr 0x560375abcdf8 <col:10, col:43> 'struct list_head *' <LValueToRValue>
|     |   `-UnaryOperator 0x560375abcde0 <col:10, col:43> 'struct list_head *' lvalue prefix '*' cannot overflow
|     |     `-ParenExpr 0x560375abcdc0 <col:11, col:43> 'struct list_head **'
|     |       `-CStyleCastExpr 0x560375abcd98 <col:12, col:33> 'struct list_head **' <BitCast>
|     |         `-ImplicitCastExpr 0x560375abcd80 <col:33> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     |           `-DeclRefExpr 0x560375abcd38 <col:33> 'struct list_head *' lvalue Var 0x560375abba00 '__cil_tmp8' 'struct list_head *'
|     |-CompoundStmt 0x560375abd9a8 <line:788:3, line:819:3>
|     | |-WhileStmt 0x560375abd970 <line:789:3, line:817:3>
|     | | |-IntegerLiteral 0x560375abce30 <line:789:10> 'int' 1
|     | | `-CompoundStmt 0x560375abd930 <col:13, line:817:3>
|     | |   |-LabelStmt 0x560375abcea8 <line:790:5, col:40> 'while_21_continue'
|     | |   | `-NullStmt 0x560375abce50 <col:40>
|     | |   |-BinaryOperator 0x560375abcfb8 <line:791:5, col:39> 'struct list_head *' '='
|     | |   | |-DeclRefExpr 0x560375abcec0 <col:5> 'struct list_head *' lvalue Var 0x560375abb6f8 'pos1' 'struct list_head *'
|     | |   | `-ImplicitCastExpr 0x560375abcfa0 <col:12, col:39> 'struct list_head *' <LValueToRValue>
|     | |   |   `-UnaryOperator 0x560375abcf88 <col:12, col:39> 'struct list_head *' lvalue prefix '*' cannot overflow
|     | |   |     `-ParenExpr 0x560375abcf68 <col:13, col:39> 'struct list_head **'
|     | |   |       `-CStyleCastExpr 0x560375abcf40 <col:14, col:35> 'struct list_head **' <BitCast>
|     | |   |         `-ImplicitCastExpr 0x560375abcf28 <col:35> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   |           `-DeclRefExpr 0x560375abcee0 <col:35> 'struct list_head *' lvalue Var 0x560375abb650 'pos0' 'struct list_head *'
|     | |   |-CompoundStmt 0x560375abd2d0 <line:792:5, line:800:5>
|     | |   | |-BinaryOperator 0x560375abd070 <line:793:5, col:33> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375abcfd8 <col:5> 'unsigned int' lvalue Var 0x560375abcaf0 '__cil_tmp9' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375abd048 <col:18, col:33> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ImplicitCastExpr 0x560375abd030 <col:33> 'struct list_head *' <LValueToRValue> part_of_explicit_cast
|     | |   | |     `-DeclRefExpr 0x560375abcff8 <col:33> 'struct list_head *' lvalue Var 0x560375abb6f8 'pos1' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375abd168 <line:794:5, col:44> 'unsigned int' '='
|     | |   | | |-DeclRefExpr 0x560375abd090 <col:5> 'unsigned int' lvalue Var 0x560375abcb88 '__cil_tmp10' 'unsigned int'
|     | |   | | `-CStyleCastExpr 0x560375abd140 <col:19, col:44> 'unsigned int' <PointerToIntegral>
|     | |   | |   `-ParenExpr 0x560375abd120 <col:34, col:44> 'struct list_head *'
|     | |   | |     `-UnaryOperator 0x560375abd0d0 <col:35, col:37> 'struct list_head *' prefix '&' cannot overflow
|     | |   | |       `-DeclRefExpr 0x560375abd0b0 <col:37> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
|     | |   | `-IfStmt 0x560375abd2a8 <line:795:5, line:799:5> has_else
|     | |   |   |-BinaryOperator 0x560375abd1f8 <line:795:9, col:24> 'int' '!='
|     | |   |   | |-ImplicitCastExpr 0x560375abd1c8 <col:9> 'unsigned int' <LValueToRValue>
|     | |   |   | | `-DeclRefExpr 0x560375abd188 <col:9> 'unsigned int' lvalue Var 0x560375abcb88 '__cil_tmp10' 'unsigned int'
|     | |   |   | `-ImplicitCastExpr 0x560375abd1e0 <col:24> 'unsigned int' <LValueToRValue>
|     | |   |   |   `-DeclRefExpr 0x560375abd1a8 <col:24> 'unsigned int' lvalue Var 0x560375abcaf0 '__cil_tmp9' 'unsigned int'
|     | |   |   |-CompoundStmt 0x560375abd218 <col:36, line:797:5>
|     | |   |   `-CompoundStmt 0x560375abd290 <col:12, line:799:5>
|     | |   |     `-GotoStmt 0x560375abd278 <line:798:7, col:12> 'while_21_break' 0x560375abd228
|     | |   |-CompoundStmt 0x560375abd5f8 <line:801:5, line:806:5>
|     | |   | |-BinaryOperator 0x560375abd410 <line:802:5, col:29> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375abd2f8 <col:5> 'int' lvalue Var 0x560375abb828 'tmp' 'int'
|     | |   | | `-CallExpr 0x560375abd3d0 <col:11, col:29> 'int'
|     | |   | |   |-ImplicitCastExpr 0x560375abd3b8 <col:11> 'int (*)(struct list_head *)' <FunctionToPointerDecay>
|     | |   | |   | `-DeclRefExpr 0x560375abd318 <col:11> 'int (struct list_head *)' Function 0x560375aba6c0 'val_from_node' 'int (struct list_head *)'
|     | |   | |   `-ImplicitCastExpr 0x560375abd3f8 <col:25> 'struct list_head *' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375abd338 <col:25> 'struct list_head *' lvalue Var 0x560375abb650 'pos0' 'struct list_head *'
|     | |   | |-BinaryOperator 0x560375abd488 <line:803:5, col:12> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375abd430 <col:5> 'int' lvalue Var 0x560375abb790 'val0' 'int'
|     | |   | | `-ImplicitCastExpr 0x560375abd470 <col:12> 'int' <LValueToRValue>
|     | |   | |   `-DeclRefExpr 0x560375abd450 <col:12> 'int' lvalue Var 0x560375abb828 'tmp' 'int'
|     | |   | |-BinaryOperator 0x560375abd560 <line:804:5, col:33> 'int' '='
|     | |   | | |-DeclRefExpr 0x560375abd4a8 <col:5> 'int' lvalue Var 0x560375abb958 'tmp___0' 'int'
|     | |   | | `-CallExpr 0x560375abd520 <col:15, col:33> 'int'
|     | |   | |   |-ImplicitCastExpr 0x560375abd508 <col:15> 'int (*)(struct list_head *)' <FunctionToPointerDecay>
|     | |   | |   | `-DeclRefExpr 0x560375abd4c8 <col:15> 'int (struct list_head *)' Function 0x560375aba6c0 'val_from_node' 'int (struct list_head *)'
|     | |   | |   `-ImplicitCastExpr 0x560375abd548 <col:29> 'struct list_head *' <LValueToRValue>
|     | |   | |     `-DeclRefExpr 0x560375abd4e8 <col:29> 'struct list_head *' lvalue Var 0x560375abb6f8 'pos1' 'struct list_head *'
|     | |   | `-BinaryOperator 0x560375abd5d8 <line:805:5, col:12> 'int' '='
|     | |   |   |-DeclRefExpr 0x560375abd580 <col:5> 'int' lvalue Var 0x560375abb8c0 'val1' 'int'
|     | |   |   `-ImplicitCastExpr 0x560375abd5c0 <col:12> 'int' <LValueToRValue>
|     | |   |     `-DeclRefExpr 0x560375abd5a0 <col:12> 'int' lvalue Var 0x560375abb958 'tmp___0' 'int'
|     | |   |-IfStmt 0x560375abd778 <line:807:5, line:812:5> has_else
|     | |   | |-BinaryOperator 0x560375abd698 <line:807:9, col:17> 'int' '<='
|     | |   | | |-ImplicitCastExpr 0x560375abd668 <col:9> 'int' <LValueToRValue>
|     | |   | | | `-DeclRefExpr 0x560375abd628 <col:9> 'int' lvalue Var 0x560375abb790 'val0' 'int'
|     | |   | | `-ImplicitCastExpr 0x560375abd680 <col:17> 'int' <LValueToRValue>
|     | |   | |   `-DeclRefExpr 0x560375abd648 <col:17> 'int' lvalue Var 0x560375abb8c0 'val1' 'int'
|     | |   | |-CompoundStmt 0x560375abd748 <col:23, line:810:5>
|     | |   | | |-BinaryOperator 0x560375abd710 <line:808:7, col:14> 'struct list_head *' '='
|     | |   | | | |-DeclRefExpr 0x560375abd6b8 <col:7> 'struct list_head *' lvalue Var 0x560375abb650 'pos0' 'struct list_head *'
|     | |   | | | `-ImplicitCastExpr 0x560375abd6f8 <col:14> 'struct list_head *' <LValueToRValue>
|     | |   | | |   `-DeclRefExpr 0x560375abd6d8 <col:14> 'struct list_head *' lvalue Var 0x560375abb6f8 'pos1' 'struct list_head *'
|     | |   | | `-GotoStmt 0x560375abd730 <line:809:7, col:12> 'while_21_continue' 0x560375abce58
|     | |   | `-CompoundStmt 0x560375abd768 <line:810:12, line:812:5>
|     | |   `-CompoundStmt 0x560375abd910 <line:813:5, line:816:5>
|     | |     |-BinaryOperator 0x560375abd818 <line:814:5, col:25> '_Bool' '='
|     | |     | |-DeclRefExpr 0x560375abd7a0 <col:5> '_Bool' lvalue Var 0x560375abb5a8 'any_change' '_Bool'
|     | |     | `-CStyleCastExpr 0x560375abd7f0 <col:18, col:25> '_Bool' <IntegralToBoolean>
|     | |     |   `-IntegerLiteral 0x560375abd7c0 <col:25> 'int' 1
|     | |     `-CallExpr 0x560375abd8b0 <line:815:5, col:25> 'void'
|     | |       |-ImplicitCastExpr 0x560375abd898 <col:5> 'void (*)(struct list_head *, struct list_head *)' <FunctionToPointerDecay>
|     | |       | `-DeclRefExpr 0x560375abd838 <col:5> 'void (struct list_head *, struct list_head *)' Function 0x560375ab5bf0 'list_move' 'void (struct list_head *, struct list_head *)'
|     | |       |-ImplicitCastExpr 0x560375abd8e0 <col:15> 'struct list_head *' <LValueToRValue>
|     | |       | `-DeclRefExpr 0x560375abd858 <col:15> 'struct list_head *' lvalue Var 0x560375abb650 'pos0' 'struct list_head *'
|     | |       `-ImplicitCastExpr 0x560375abd8f8 <col:21> 'struct list_head *' <LValueToRValue>
|     | |         `-DeclRefExpr 0x560375abd878 <col:21> 'struct list_head *' lvalue Var 0x560375abb6f8 'pos1' 'struct list_head *'
|     | `-LabelStmt 0x560375abd990 <line:818:3, col:35> 'while_21_break'
|     |   `-NullStmt 0x560375abd988 <col:35>
|     `-ReturnStmt 0x560375abda20 <line:820:3, col:21>
|       `-ImplicitCastExpr 0x560375abda08 <col:10, col:21> '_Bool' <LValueToRValue>
|         `-ParenExpr 0x560375abd9e8 <col:10, col:21> '_Bool' lvalue
|           `-DeclRefExpr 0x560375abd9c8 <col:11> '_Bool' lvalue Var 0x560375abb5a8 'any_change' '_Bool'
|-FunctionDecl 0x560375abdb88 <line:823:1, line:843:1> line:823:13 used gl_sort 'void (void)' static
| `-CompoundStmt 0x560375abdfc8 <line:824:1, line:843:1>
|   |-DeclStmt 0x560375abdca0 <line:824:3, col:13>
|   | `-VarDecl 0x560375abdc38 <col:3, col:9> col:9 used tmp '_Bool'
|   `-CompoundStmt 0x560375abdfa8 <line:826:3, line:842:1>
|     |-CompoundStmt 0x560375abdf78 <line:827:3, line:840:3>
|     | |-WhileStmt 0x560375abdf40 <line:828:3, line:838:3>
|     | | |-IntegerLiteral 0x560375abdcb8 <line:828:10> 'int' 1
|     | | `-CompoundStmt 0x560375abdf18 <col:13, line:838:3>
|     | |   |-LabelStmt 0x560375abdd30 <line:829:5, col:40> 'while_22_continue'
|     | |   | `-NullStmt 0x560375abdcd8 <col:40>
|     | |   |-CompoundStmt 0x560375abde10 <line:830:5, line:832:5>
|     | |   | `-BinaryOperator 0x560375abddf0 <line:831:5, col:24> '_Bool' '='
|     | |   |   |-DeclRefExpr 0x560375abdd48 <col:5> '_Bool' lvalue Var 0x560375abdc38 'tmp' '_Bool'
|     | |   |   `-CallExpr 0x560375abddd0 <col:11, col:24> '_Bool'
|     | |   |     `-ImplicitCastExpr 0x560375abddb8 <col:11> '_Bool (*)(void)' <FunctionToPointerDecay>
|     | |   |       `-DeclRefExpr 0x560375abdd68 <col:11> '_Bool (void)' Function 0x560375abb4f8 'gl_sort_pass' '_Bool (void)'
|     | |   `-IfStmt 0x560375abdef0 <line:833:5, line:837:5> has_else
|     | |     |-ImplicitCastExpr 0x560375abde48 <line:833:9> '_Bool' <LValueToRValue>
|     | |     | `-DeclRefExpr 0x560375abde28 <col:9> '_Bool' lvalue Var 0x560375abdc38 'tmp' '_Bool'
|     | |     |-CompoundStmt 0x560375abde60 <col:14, line:835:5>
|     | |     `-CompoundStmt 0x560375abded8 <col:12, line:837:5>
|     | |       `-GotoStmt 0x560375abdec0 <line:836:7, col:12> 'while_22_break' 0x560375abde70
|     | `-LabelStmt 0x560375abdf60 <line:839:3, col:35> 'while_22_break'
|     |   `-NullStmt 0x560375abdf58 <col:35>
|     `-ReturnStmt 0x560375abdf98 <line:841:3>
`-FunctionDecl 0x560375abe088 <line:844:1, line:860:1> line:844:5 main 'int (void)'
  `-CompoundStmt 0x560375abe808 <line:845:1, line:860:1>
    |-DeclStmt 0x560375abe1e8 <line:845:3, col:40>
    | `-VarDecl 0x560375abe180 <col:3, col:29> col:29 used __cil_tmp1 'const struct list_head *'
    |-DeclStmt 0x560375abe290 <line:846:3, col:40>
    | `-VarDecl 0x560375abe228 <col:3, col:29> col:29 used __cil_tmp2 'const struct list_head *'
    `-CompoundStmt 0x560375abe7e8 <line:848:3, line:859:1>
      |-CompoundStmt 0x560375abe750 <line:849:3, line:857:3>
      | |-CallExpr 0x560375abe2e0 <line:850:3, col:11> 'void'
      | | `-ImplicitCastExpr 0x560375abe2c8 <col:3> 'void (*)(void)' <FunctionToPointerDecay>
      | |   `-DeclRefExpr 0x560375abe2a8 <col:3> 'void (void)' Function 0x560375ab8460 'gl_read' 'void (void)'
      | |-BinaryOperator 0x560375abe3e8 <line:851:3, col:54> 'const struct list_head *' '='
      | | |-DeclRefExpr 0x560375abe300 <col:3> 'const struct list_head *' lvalue Var 0x560375abe180 '__cil_tmp1' 'const struct list_head *'
      | | `-CStyleCastExpr 0x560375abe3c0 <col:16, col:54> 'const struct list_head *' <NoOp>
      | |   `-ParenExpr 0x560375abe3a0 <col:44, col:54> 'struct list_head *'
      | |     `-UnaryOperator 0x560375abe340 <col:45, col:47> 'struct list_head *' prefix '&' cannot overflow
      | |       `-DeclRefExpr 0x560375abe320 <col:47> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
      | |-CallExpr 0x560375abe4c0 <line:852:3, col:21> 'void'
      | | |-ImplicitCastExpr 0x560375abe4a8 <col:3> 'void (*)(const struct list_head *)' <FunctionToPointerDecay>
      | | | `-DeclRefExpr 0x560375abe408 <col:3> 'void (const struct list_head *)' Function 0x560375a9c6b8 'inspect' 'void (const struct list_head *)'
      | | `-ImplicitCastExpr 0x560375abe4e8 <col:11> 'const struct list_head *' <LValueToRValue>
      | |   `-DeclRefExpr 0x560375abe428 <col:11> 'const struct list_head *' lvalue Var 0x560375abe180 '__cil_tmp1' 'const struct list_head *'
      | |-CallExpr 0x560375abe538 <line:853:3, col:11> 'void'
      | | `-ImplicitCastExpr 0x560375abe520 <col:3> 'void (*)(void)' <FunctionToPointerDecay>
      | |   `-DeclRefExpr 0x560375abe500 <col:3> 'void (void)' Function 0x560375abdb88 'gl_sort' 'void (void)'
      | |-BinaryOperator 0x560375abe640 <line:854:3, col:54> 'const struct list_head *' '='
      | | |-DeclRefExpr 0x560375abe558 <col:3> 'const struct list_head *' lvalue Var 0x560375abe228 '__cil_tmp2' 'const struct list_head *'
      | | `-CStyleCastExpr 0x560375abe618 <col:16, col:54> 'const struct list_head *' <NoOp>
      | |   `-ParenExpr 0x560375abe5f8 <col:44, col:54> 'struct list_head *'
      | |     `-UnaryOperator 0x560375abe598 <col:45, col:47> 'struct list_head *' prefix '&' cannot overflow
      | |       `-DeclRefExpr 0x560375abe578 <col:47> 'struct list_head':'struct list_head' lvalue Var 0x560375a9c3b0 'gl_list' 'struct list_head':'struct list_head'
      | |-CallExpr 0x560375abe6b8 <line:855:3, col:21> 'void'
      | | |-ImplicitCastExpr 0x560375abe6a0 <col:3> 'void (*)(const struct list_head *)' <FunctionToPointerDecay>
      | | | `-DeclRefExpr 0x560375abe660 <col:3> 'void (const struct list_head *)' Function 0x560375a9c6b8 'inspect' 'void (const struct list_head *)'
      | | `-ImplicitCastExpr 0x560375abe6e0 <col:11> 'const struct list_head *' <LValueToRValue>
      | |   `-DeclRefExpr 0x560375abe680 <col:11> 'const struct list_head *' lvalue Var 0x560375abe228 '__cil_tmp2' 'const struct list_head *'
      | `-CallExpr 0x560375abe730 <line:856:3, col:14> 'void'
      |   `-ImplicitCastExpr 0x560375abe718 <col:3> 'void (*)(void)' <FunctionToPointerDecay>
      |     `-DeclRefExpr 0x560375abe6f8 <col:3> 'void (void)' Function 0x560375ab8b70 'gl_destroy' 'void (void)'
      `-ReturnStmt 0x560375abe7d8 <line:858:3, col:12>
        `-ParenExpr 0x560375abe7b8 <col:10, col:12> 'int'
          `-IntegerLiteral 0x560375abe798 <col:11> 'int' 0
32 warnings generated.
