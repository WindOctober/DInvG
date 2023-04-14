/* A Bison parser, made by GNU Bison 3.5.1.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2020 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Undocumented macros, especially those whose name start with YY_,
   are private implementation details.  Do not rely on them.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.5.1"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* First part of user prologue.  */
#line 1 "ltrtest.y"

#include <iostream>
#include <vector>
#include "var-info.h"
#include "Location.h"
#include "PolyUtils.h"
#include "TransitionRelation.h"
#include "InvariantMap.h"
#include "DualInvariantMap.h"
#include "System.h"
#include "Timer.h"
#include "ppl.hh"
#include "Elimination.h"
#include "Tree.h"
#include "Propagation.h"
#include "Macro.h"

 
   using namespace std;
   using namespace Parma_Polyhedra_Library;
   using namespace Parma_Polyhedra_Library::IO_Operators;

   bool gendrop;
   int debug;
   int debug_2;
   int debug_3;
   int num_context;
   bool print_tree;
   bool zero;
   bool one;
   bool falsepath;
   bool trsat;
   bool noexitpath;
   bool djinv;
   bool arrinv;
   int prop_steps;
   int weave_time;
   int total_time;
   bool ch79,bhrz03,dual;
   string projection;
   string tree_prior;
   string some_per_group;
   bool clear_lower_gli = false;
   int clear_lower_gli_depth = -1;
   bool backhere_flag = false;
   int related_location_number;
   int related_transition_number;
   
   C_Polyhedron * trivial, *dualp;
   
#ifndef MAX_ID_SIZE
#define MAX_ID_SIZE 100
#endif
   
#define DEBUG 1001
#define DEBUG_2 1002
#define DEBUG_3 1003
#define NO_PRINT_TREE 1010
#define ONECONTEXT 0
#define GENDROP 1
#define MANYCONTEXT 2
#define BULLSHIT 3
#define NEW_MANYCONTEXT 401
#define NEW_2_MANYCONTEXT 402
#define NEW_3_MANYCONTEXT 403
#define NEWDFS 404
#define NEWDFS_SEQUENCES 405
#define NEWDFS_SEQ_PROPAGATION 406
#define NO_PROJECTION 410
#define KOHLER_ELIMINATE_C 411
#define FARKAS_ELIMINATE_C 412
#define FOUMOT_ELIMINATE_C 413
#define NO_PRIOR 420
#define TARGET_PRIOR1 421
#define TARGET_PRIOR2 422
#define TARGET_PRIOR3 423
#define ONE_PER_GROUP 431
#define TWO_PER_GROUP 432
#define THREE_PER_GROUP 433
#define FOUR_PER_GROUP 434
#define ZERO_ONLY 501
#define ONE_ONLY 502
#define ZERO_ONE 503
#define YES_FALSEPATH 511
#define NO_FALSEPATH 512
#define YES_TRSAT 513
#define NO_TRSAT 514
#define YES_EXITPATH 521
#define NO_EXITPATH 522
#define YES_DJINV 601
#define NO_DJINV 602
#define YES_ARRINV 611
#define NO_ARRINV 612
#define NO_INSTANTIATION 8
#define NO_CH79 9
#define NO_BHRZ03 10
#define NO_DUAL 11
#define YES_CH79 12
#define YES_BHRZ03 13
#define YES_DUAL 14
#define INV_CHECK 15
#define NO_INV_CHECK 16

   
   
  vector<int> **location_matrix;
  int global_binary_i=0;
  long int global_contains_time=0;
  vector<int> target_prior;

  char err_str[100];
  extern int linenum;
  int dimension;
  var_info * f, *fd, *fm;
  vector<Location *> * loclist;
  vector<TransitionRelation *> * trlist;
  Context *glc;// The global context
  vector<Context *>* children;
  vector<System *> * global_sub_system_list;
  System * global_system;
  Timer total_timer;
  Timer weave_timer;
  Timer dfs_traverse_timer;
  Timer single_dfs_traverse_timer;
  Timer collect_timer;
  Timer prune_nodes_timer;
  Timer backtrack_timer;
  Timer single_dfs_sequences_generation_timer;
  Timer single_dfs_sequences_traverse_timer;
  Timer single_merge_sub_sequences_timer;
  long int dfs_traverse_time;
  int collect_time = 0;
  int prune_nodes_time = 0;
  int backtrack_time = 0;
  vector<int> vector_single_collect_time;
  vector<int> vector_single_dfs_traverse_time;
  vector<int> vector_single_dfs_sequences_generation_time;
  vector<int> vector_single_dfs_sequences_traverse_time;
  int single_collect_time;
  int * tt;
  C_Polyhedron * invd;

  bool inv_check;
   
   
  extern int yyparse();
  extern int yylex();
  void yyerror(char const * x);
  void yyerror(string  const & x);
  void collect_generators(vector<Context *> * children , Generator_System & g);
  int parse_cmd_line(char * x);
  int single_weave_count;
  vector<int> vector_single_weave_count;
  int weave_count;
  int single_bang_count;
  vector<int> vector_single_bang_count;
  int single_pre_prune_bang_count;
  int single_post_prune_bang_count;
  vector<int> vector_single_pre_prune_bang_count;
  vector<int> vector_single_post_prune_bang_count;
  int bang_count;
  int backtrack_count;
  int backtrack_success;
  bool backtrack_flag;
  int prune_count;
  int clump_prune_count;
  int context_count;
  int merge_count;
  int bang_count_in_merge;
  Counter counter;
  bool search_location(char * w, Location ** m);
  bool search_transition_relation(char * w, TransitionRelation ** m);
  int find_variable( char* what);
  void add_preloc_invariants_to_transitions();
  void print_status();
  void print_bake_off(InvariantMap const & what);
   
  void check_invariant_ok();
   

#line 223 "ltrtest.tab.c"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Use api.header.include to #include this header
   instead of duplicating it here.  */
#ifndef YY_YY_LTRTEST_TAB_H_INCLUDED
# define YY_YY_LTRTEST_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    INT = 258,
    IDENT = 259,
    PRIME = 260,
    END = 261,
    VARIABLED = 262,
    LOCATION = 263,
    TRANSITION = 264,
    EQ = 265,
    LEQ = 266,
    GEQ = 267,
    LE = 268,
    GE = 269,
    PRES = 270,
    PROPS = 271,
    INVARIANT = 272,
    UMINUS = 273
  };
#endif
/* Tokens.  */
#define INT 258
#define IDENT 259
#define PRIME 260
#define END 261
#define VARIABLED 262
#define LOCATION 263
#define TRANSITION 264
#define EQ 265
#define LEQ 266
#define GEQ 267
#define LE 268
#define GE 269
#define PRES 270
#define PROPS 271
#define INVARIANT 272
#define UMINUS 273

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 154 "ltrtest.y"

   char * string;
   var_info * v;
   int dummy;
   int integer;
   char identifier[MAX_ID_SIZE];
   var_info * vi;
   Location *ll;
   TransitionRelation * tt;
   Linear_Expression * li;
   Constraint * cc;
   C_Polyhedron * pp;
   vector<int> * vv;

#line 326 "ltrtest.tab.c"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_LTRTEST_TAB_H_INCLUDED  */



#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))

/* Stored state numbers (used for stacks). */
typedef yytype_int8 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && ! defined __ICC && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                            \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  5
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   110

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  28
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  23
/* YYNRULES -- Number of rules.  */
#define YYNRULES  55
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  99

#define YYUNDEFTOK  2
#define YYMAXUTOK   273


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      24,    25,    20,    18,    27,    19,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    26,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    22,     2,    23,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    21
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   196,   196,   200,   200,   207,   210,   213,   217,   222,
     225,   228,   231,   234,   235,   238,   241,   247,   252,   259,
     262,   268,   279,   291,   297,   304,   309,   314,   320,   329,
     332,   342,   345,   351,   356,   362,   368,   374,   377,   384,
     398,   403,   408,   414,   419,   424,   430,   434,   438,   441,
     445,   450,   453,   459,   464,   470
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "INT", "IDENT", "PRIME", "END",
  "VARIABLED", "LOCATION", "TRANSITION", "EQ", "LEQ", "GEQ", "LE", "GE",
  "PRES", "PROPS", "INVARIANT", "'+'", "'-'", "'*'", "UMINUS", "'['",
  "']'", "'('", "')'", "':'", "','", "$accept", "program", "header", "$@1",
  "optional_commands", "dimvector", "system_descriptor",
  "location_descriptor", "transition_descriptor", "invariant_descriptor",
  "location_identifier", "transition_identifier", "linear_assertion",
  "linear_inequality", "linear_term", "linear_expression",
  "primed_linear_assertion", "preservative", "variable_list",
  "primed_linear_inequality", "primed_term", "primed_linear_expression",
  "identifier", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_int16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,    43,    45,
      42,   273,    91,    93,    40,    41,    58,    44
};
# endif

#define YYPACT_NINF (-79)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-22)

#define yytable_value_is_error(Yyn) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int8 yypact[] =
{
      30,   -79,    54,    23,    40,   -79,    53,    61,    60,    77,
      60,    60,    60,    95,    61,    61,    61,   -79,     4,   -79,
      62,    19,   -79,    76,   -79,     2,   -79,   -79,   -79,   -79,
     -79,   -79,   -79,    83,    46,   -79,    19,   -79,     1,   -79,
      60,    19,   -79,    60,   -79,   -79,    19,    19,    19,    46,
      46,    78,   -79,   -79,    48,    48,    48,   -79,   -79,    21,
      84,    60,    85,    39,    79,   -79,    21,    21,   -79,    71,
      82,    93,   -79,    60,   -79,   -79,    21,   -79,   -79,    12,
      12,    12,    39,    39,    60,   -79,    87,     3,   -79,    81,
      81,    81,   -79,   -79,   -79,   -79,    60,   -79,   -79
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       0,     3,     0,     6,     0,     1,     0,     0,     0,     0,
       0,     0,     0,     0,    11,    12,    14,    55,     0,     8,
       0,    15,    21,     0,    22,     0,     2,     9,    10,    13,
       4,     7,     5,    29,     0,    16,    24,    31,     0,    28,
       0,     0,    19,     0,    34,    23,     0,     0,     0,     0,
       0,     0,    20,    30,    27,    25,    26,    32,    33,     0,
      48,     0,     0,     0,     0,    18,    37,    36,    51,     0,
      46,     0,    47,     0,    54,    46,     0,    38,    35,     0,
       0,     0,     0,     0,     0,    49,     0,    42,    17,    44,
      43,    45,    52,    53,    50,    39,     0,    40,    41
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] =
{
     -79,   -79,   -79,   -79,   -79,   -79,    70,   -79,   -79,   -79,
     -11,   -79,    16,   -79,    11,    45,   -20,   -79,   -78,   -79,
     -49,    15,    -8
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] =
{
      -1,     2,     3,     4,     7,    18,    13,    14,    15,    16,
      21,    23,    35,    36,    37,    38,    65,    66,    86,    67,
      68,    69,    39
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int8 yytable[] =
{
      19,    25,    22,    24,    22,    33,    17,    17,    17,    97,
      31,    46,    47,    48,    74,    60,    17,    61,    98,    49,
      50,    34,    33,    17,    60,    17,    61,    30,    41,    51,
      96,    63,    22,    92,    93,    53,    62,     1,    34,     6,
      63,    42,    60,    17,    61,    44,    77,    78,    64,    33,
      17,    70,    45,    72,     5,    75,    88,    52,    75,    75,
      57,    58,     8,    85,    17,    87,    49,    50,    75,    10,
      11,    75,    75,    75,    75,    75,    94,     9,    12,    87,
      20,    79,    80,    81,    27,    28,    29,    32,    87,    82,
      83,    54,    55,    56,    89,    90,    91,    17,    84,    82,
      83,    26,    40,    43,    71,    59,    76,    73,     0,   -21,
      95
};

static const yytype_int8 yycheck[] =
{
       8,    12,    10,    11,    12,     3,     4,     4,     4,    87,
      18,    10,    11,    12,    63,     3,     4,     5,    96,    18,
      19,    19,     3,     4,     3,     4,     5,    23,    26,    40,
      27,    19,    40,    82,    83,    43,    15,     7,    19,    16,
      19,    25,     3,     4,     5,    34,    66,    67,    59,     3,
       4,    59,    36,    61,     0,    63,    76,    41,    66,    67,
      49,    50,    22,    71,     4,    73,    18,    19,    76,     8,
       9,    79,    80,    81,    82,    83,    84,    24,    17,    87,
       3,    10,    11,    12,    14,    15,    16,    25,    96,    18,
      19,    46,    47,    48,    79,    80,    81,     4,     5,    18,
      19,     6,    26,    20,    20,    27,    27,    22,    -1,    27,
      23
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,     7,    29,    30,    31,     0,    16,    32,    22,    24,
       8,     9,    17,    34,    35,    36,    37,     4,    33,    50,
       3,    38,    50,    39,    50,    38,     6,    34,    34,    34,
      23,    50,    25,     3,    19,    40,    41,    42,    43,    50,
      26,    26,    40,    20,    42,    40,    10,    11,    12,    18,
      19,    38,    40,    50,    43,    43,    43,    42,    42,    27,
       3,     5,    15,    19,    38,    44,    45,    47,    48,    49,
      50,    20,    50,    22,    48,    50,    27,    44,    44,    10,
      11,    12,    18,    19,     5,    50,    46,    50,    44,    49,
      49,    49,    48,    48,    50,    23,    27,    46,    46
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_int8 yyr1[] =
{
       0,    28,    29,    31,    30,    32,    32,    33,    33,    34,
      34,    34,    34,    34,    34,    35,    35,    36,    36,    37,
      37,    38,    39,    40,    40,    41,    41,    41,    42,    42,
      42,    43,    43,    43,    43,    44,    44,    44,    44,    45,
      46,    46,    46,    47,    47,    47,    48,    48,    48,    48,
      48,    49,    49,    49,    49,    50
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     4,     0,     5,     4,     0,     2,     1,     2,
       2,     1,     1,     2,     1,     2,     3,     8,     6,     3,
       4,     1,     1,     2,     1,     3,     3,     3,     1,     1,
       3,     1,     3,     3,     2,     2,     1,     1,     2,     4,
       2,     3,     1,     3,     3,     3,     1,     2,     1,     3,
       4,     1,     3,     3,     2,     1
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyoutput = yyo;
  YYUSE (yyoutput);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyo, yytoknum[yytype], *yyvaluep);
# endif
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyo, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyo, yytype, yyvaluep);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[+yyssp[yyi + 1 - yynrhs]],
                       &yyvsp[(yyi + 1) - (yynrhs)]
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
#  else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            else
              goto append;

          append:
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                yy_state_t *yyssp, int yytoken)
{
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Actual size of YYARG. */
  int yycount = 0;
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[+*yyssp];
      YYPTRDIFF_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
      yysize = yysize0;
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYPTRDIFF_T yysize1
                    = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
                    yysize = yysize1;
                  else
                    return 2;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    /* Don't count the "%s"s in the final size, but reserve room for
       the terminator.  */
    YYPTRDIFF_T yysize1 = yysize + (yystrlen (yyformat) - 2 * yycount) + 1;
    if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
      yysize = yysize1;
    else
      return 2;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    yy_state_fast_t yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss;
    yy_state_t *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYPTRDIFF_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    goto yyexhaustedlab;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
# undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 2:
#line 196 "ltrtest.y"
                                                       {
   // just print it for the fun of it
}
#line 1571 "ltrtest.tab.c"
    break;

  case 3:
#line 200 "ltrtest.y"
                  {
}
#line 1578 "ltrtest.tab.c"
    break;

  case 4:
#line 201 "ltrtest.y"
                   {
   f=(yyvsp[-1].vi); // This is the main dimvector
   dimension=f->get_dimension();
}
#line 1587 "ltrtest.tab.c"
    break;

  case 5:
#line 207 "ltrtest.y"
                                     {
   prop_steps=(yyvsp[-1].integer);
   
}
#line 1596 "ltrtest.tab.c"
    break;

  case 6:
#line 210 "ltrtest.y"
    {}
#line 1602 "ltrtest.tab.c"
    break;

  case 7:
#line 213 "ltrtest.y"
                                {
   (yyval.vi)=(yyvsp[-1].vi);
   (yyval.vi)->search_and_insert((yyvsp[0].identifier));
}
#line 1611 "ltrtest.tab.c"
    break;

  case 8:
#line 217 "ltrtest.y"
             {
   (yyval.vi)=new var_info();
   (yyval.vi)->search_and_insert((yyvsp[0].identifier));
}
#line 1620 "ltrtest.tab.c"
    break;

  case 9:
#line 222 "ltrtest.y"
                                                       {
   
}
#line 1628 "ltrtest.tab.c"
    break;

  case 10:
#line 225 "ltrtest.y"
                                         {

}
#line 1636 "ltrtest.tab.c"
    break;

  case 11:
#line 228 "ltrtest.y"
                     {

}
#line 1644 "ltrtest.tab.c"
    break;

  case 12:
#line 231 "ltrtest.y"
                       {
   
}
#line 1652 "ltrtest.tab.c"
    break;

  case 13:
#line 234 "ltrtest.y"
                                        {}
#line 1658 "ltrtest.tab.c"
    break;

  case 14:
#line 235 "ltrtest.y"
                      {}
#line 1664 "ltrtest.tab.c"
    break;

  case 15:
#line 238 "ltrtest.y"
                                                 {
   (yyval.ll)=(yyvsp[0].ll);
}
#line 1672 "ltrtest.tab.c"
    break;

  case 16:
#line 241 "ltrtest.y"
                                               {
   (yyval.ll)=(yyvsp[-1].ll);
   (yyval.ll)->set_polyhedron((yyvsp[0].pp));
}
#line 1681 "ltrtest.tab.c"
    break;

  case 17:
#line 247 "ltrtest.y"
                                                                                                                                   {
   (yyval.tt)=(yyvsp[-6].tt);
   (yyval.tt)->set_locs((yyvsp[-4].ll),(yyvsp[-2].ll));
   (yyval.tt)->set_relation((yyvsp[0].pp));
    if (!(yyvsp[0].pp)->is_empty()){
      trlist->push_back((yyvsp[-6].tt));
    }
}
#line 1691 "ltrtest.tab.c"
    break;

  case 18:
#line 252 "ltrtest.y"
                                                                                       {
   (yyval.tt)=(yyvsp[-4].tt);
   (yyval.tt)->set_locs((yyvsp[-2].ll),(yyvsp[-2].ll));
   (yyval.tt)->set_relation((yyvsp[0].pp));
    if (!(yyvsp[0].pp)->is_empty()){
      trlist->push_back((yyvsp[-4].tt));
    }
}
#line 1701 "ltrtest.tab.c"
    break;

  case 19:
#line 259 "ltrtest.y"
                                                                     {
   (yyvsp[-1].ll)->set_invariant_polyhedron((yyvsp[0].pp));
}
#line 1709 "ltrtest.tab.c"
    break;

  case 20:
#line 262 "ltrtest.y"
                                                    {
     (yyvsp[-2].ll)->set_invariant_polyhedron((yyvsp[0].pp));
}
#line 1717 "ltrtest.tab.c"
    break;

  case 21:
#line 268 "ltrtest.y"
                               {
   // search loclist for the identifier
   Location * what;
   if (!search_location((yyvsp[0].identifier), &what)){
      (yyval.ll)=new Location(dimension,f,fd,fm,(yyvsp[0].identifier));
      loclist->push_back((yyval.ll));
   } else
      (yyval.ll)=what;
}
#line 1731 "ltrtest.tab.c"
    break;

  case 22:
#line 279 "ltrtest.y"
                                 {
      // search trlist for the identifier
   TransitionRelation * what;
   if (!search_transition_relation((yyvsp[0].identifier), &what)){
      (yyval.tt)=new TransitionRelation(dimension,f,fd,fm,(yyvsp[0].identifier));
      //trlist->push_back((yyval.tt));
   } else {
      cout<<"Error: Already Encountered transition name #"<<what<<(yyvsp[0].identifier);
      (yyval.tt)=what;
   }
}
#line 1747 "ltrtest.tab.c"
    break;

  case 23:
#line 291 "ltrtest.y"
                                                    {
   (yyval.pp)=(yyvsp[0].pp);
   //$$->add_constraint_and_minimize(*$1);
   (yyval.pp)->add_constraint(*(yyvsp[-1].cc));
   delete((yyvsp[-1].cc));
}
#line 1758 "ltrtest.tab.c"
    break;

  case 24:
#line 297 "ltrtest.y"
                   {
   (yyval.pp)= new C_Polyhedron(dimension, UNIVERSE);
   //$$->add_constraint_and_minimize(*$1);
   (yyval.pp)->add_constraint(*(yyvsp[0].cc));
   delete((yyvsp[0].cc));
}
#line 1769 "ltrtest.tab.c"
    break;

  case 25:
#line 304 "ltrtest.y"
                                                           {
   (yyval.cc)=new Constraint(*(yyvsp[-2].li) <= *(yyvsp[0].li));
   delete((yyvsp[-2].li));
   delete((yyvsp[0].li));
}
#line 1779 "ltrtest.tab.c"
    break;

  case 26:
#line 309 "ltrtest.y"
                                          {
   (yyval.cc)=new Constraint(*(yyvsp[-2].li) >= *(yyvsp[0].li));
   delete((yyvsp[-2].li));
   delete((yyvsp[0].li));
}
#line 1789 "ltrtest.tab.c"
    break;

  case 27:
#line 314 "ltrtest.y"
                                         {
   (yyval.cc)=new Constraint(*(yyvsp[-2].li) == *(yyvsp[0].li));
   delete((yyvsp[-2].li));
   delete((yyvsp[0].li));
   }
#line 1799 "ltrtest.tab.c"
    break;

  case 28:
#line 320 "ltrtest.y"
                        {
   int i =f->search((yyvsp[0].identifier));
   if (i==VAR_NOT_FOUND){
      string x=string("Error:: Variable ")+ (yyvsp[0].identifier) + string(" not found");
      yyerror(x);
      exit(1);
   }
   (yyval.li)=new Linear_Expression(Variable(i));
}
#line 1813 "ltrtest.tab.c"
    break;

  case 29:
#line 329 "ltrtest.y"
      {
   (yyval.li)= new Linear_Expression((yyvsp[0].integer));
}
#line 1821 "ltrtest.tab.c"
    break;

  case 30:
#line 332 "ltrtest.y"
                    {
   int i =f->search((yyvsp[0].identifier));
   if (i==VAR_NOT_FOUND){
      string x=string("Error:: Variable ")+ (yyvsp[0].identifier) + string(" not found");
      yyerror(x);
      exit(1);
   }
   (yyval.li)=new Linear_Expression((yyvsp[-2].integer) * Variable(i));
}
#line 1835 "ltrtest.tab.c"
    break;

  case 31:
#line 342 "ltrtest.y"
                              {
   (yyval.li)=(yyvsp[0].li);
}
#line 1843 "ltrtest.tab.c"
    break;

  case 32:
#line 345 "ltrtest.y"
                                    {
   (yyval.li)=(yyvsp[-2].li);
   (*(yyvsp[-2].li))+=(*(yyvsp[0].li));
   delete((yyvsp[0].li));
   
}
#line 1854 "ltrtest.tab.c"
    break;

  case 33:
#line 351 "ltrtest.y"
                                    {
   (yyval.li)=(yyvsp[-2].li);
   (*(yyvsp[-2].li))-=(*(yyvsp[0].li));
   delete((yyvsp[0].li));
}
#line 1864 "ltrtest.tab.c"
    break;

  case 34:
#line 356 "ltrtest.y"
                              {
   (yyval.li)=(yyvsp[0].li);
   (*(yyvsp[0].li))=-(*(yyvsp[0].li));
}
#line 1873 "ltrtest.tab.c"
    break;

  case 35:
#line 362 "ltrtest.y"
                                                                         {
   (yyval.pp)=(yyvsp[0].pp);
   //$$->add_constraint_and_minimize(*$1);
   (yyval.pp)->add_constraint(*(yyvsp[-1].cc));
   delete((yyvsp[-1].cc));
}
#line 1884 "ltrtest.tab.c"
    break;

  case 36:
#line 368 "ltrtest.y"
                          {
   (yyval.pp)= new C_Polyhedron(2*dimension,UNIVERSE);
   //$$->add_constraint_and_minimize(*$1);
   (yyval.pp)->add_constraint(*(yyvsp[0].cc));
   delete((yyvsp[0].cc));
}
#line 1895 "ltrtest.tab.c"
    break;

  case 37:
#line 374 "ltrtest.y"
              {
   (yyval.pp)=(yyvsp[0].pp);
}
#line 1903 "ltrtest.tab.c"
    break;

  case 38:
#line 377 "ltrtest.y"
                                      {
   (yyval.pp)=(yyvsp[0].pp);
   (yyval.pp)->intersection_assign(*(yyvsp[-1].pp));
   delete((yyvsp[-1].pp));
}
#line 1913 "ltrtest.tab.c"
    break;

  case 39:
#line 384 "ltrtest.y"
                                        {
   (yyval.pp)= new C_Polyhedron(2*dimension,UNIVERSE);
   vector<int>::iterator vi=(yyvsp[-1].vv)->begin();
   for (; vi < (yyvsp[-1].vv)->end(); ++vi){
      Linear_Expression ll=Variable((*vi)) - Variable((*vi)+dimension);
      //$$->add_constraint_and_minimize(ll ==0);
      (yyval.pp)->add_constraint(ll ==0);
   }

   delete((yyvsp[-1].vv));
   
}
#line 1930 "ltrtest.tab.c"
    break;

  case 40:
#line 398 "ltrtest.y"
                                        {
   int i=find_variable((yyvsp[-1].identifier));
   (yyval.vv)=(yyvsp[0].vv);
   (yyval.vv)->push_back(i);
}
#line 1940 "ltrtest.tab.c"
    break;

  case 41:
#line 403 "ltrtest.y"
                               {
   int i=find_variable((yyvsp[-2].identifier));
   (yyval.vv)=(yyvsp[0].vv);
   (yyval.vv)->push_back(i);
}
#line 1950 "ltrtest.tab.c"
    break;

  case 42:
#line 408 "ltrtest.y"
            {
   int i=find_variable((yyvsp[0].identifier));
   (yyval.vv)=new vector<int>();
   (yyval.vv)->push_back(i);
}
#line 1960 "ltrtest.tab.c"
    break;

  case 43:
#line 414 "ltrtest.y"
                                                                               {
   (yyval.cc)=new Constraint(*(yyvsp[-2].li) <= *(yyvsp[0].li));
   delete((yyvsp[-2].li));
   delete((yyvsp[0].li));
}
#line 1970 "ltrtest.tab.c"
    break;

  case 44:
#line 419 "ltrtest.y"
                                                       {
   (yyval.cc)=new Constraint(*(yyvsp[-2].li)== *(yyvsp[0].li));
   delete((yyvsp[-2].li));
   delete((yyvsp[0].li));
}
#line 1980 "ltrtest.tab.c"
    break;

  case 45:
#line 424 "ltrtest.y"
                                                        {
   (yyval.cc)= new Constraint(*(yyvsp[-2].li) >= *(yyvsp[0].li));
   delete((yyvsp[-2].li));
   delete((yyvsp[0].li));
}
#line 1990 "ltrtest.tab.c"
    break;

  case 46:
#line 430 "ltrtest.y"
                        {
   int i= find_variable((yyvsp[0].identifier));
   (yyval.li)=new Linear_Expression(Variable(i));
}
#line 1999 "ltrtest.tab.c"
    break;

  case 47:
#line 434 "ltrtest.y"
                  {
   int i= find_variable((yyvsp[0].identifier));
   (yyval.li)=new Linear_Expression(Variable(i+dimension));
}
#line 2008 "ltrtest.tab.c"
    break;

  case 48:
#line 438 "ltrtest.y"
      {
   (yyval.li)=new Linear_Expression((yyvsp[0].integer));
}
#line 2016 "ltrtest.tab.c"
    break;

  case 49:
#line 441 "ltrtest.y"
                    {
   int i= find_variable((yyvsp[0].identifier));
   (yyval.li)=new Linear_Expression((yyvsp[-2].integer) * Variable(i));
}
#line 2025 "ltrtest.tab.c"
    break;

  case 50:
#line 445 "ltrtest.y"
                          {
   int i= find_variable((yyvsp[0].identifier));
   (yyval.li)=new Linear_Expression((yyvsp[-3].integer) * Variable(i+dimension));
}
#line 2034 "ltrtest.tab.c"
    break;

  case 51:
#line 450 "ltrtest.y"
                                     {
   (yyval.li)=(yyvsp[0].li);
}
#line 2042 "ltrtest.tab.c"
    break;

  case 52:
#line 453 "ltrtest.y"
                                          {
   (yyval.li)=(yyvsp[-2].li);
   (*(yyvsp[-2].li))+= (*(yyvsp[0].li));
   delete((yyvsp[0].li));
}
#line 2052 "ltrtest.tab.c"
    break;

  case 53:
#line 459 "ltrtest.y"
                                           {
   (yyval.li)=(yyvsp[-2].li);
   (*(yyvsp[-2].li))-= (*(yyvsp[0].li));
   delete((yyvsp[0].li));
}
#line 2062 "ltrtest.tab.c"
    break;

  case 54:
#line 464 "ltrtest.y"
                              {
   (yyval.li)=(yyvsp[0].li);
   (*(yyvsp[0].li))= -(*(yyvsp[0].li));
}
#line 2071 "ltrtest.tab.c"
    break;

  case 55:
#line 470 "ltrtest.y"
                 {
  strcpy((yyval.identifier),(yyvsp[0].identifier));
}
#line 2079 "ltrtest.tab.c"
    break;


#line 2083 "ltrtest.tab.c"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *, YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;


#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif


/*-----------------------------------------------------.
| yyreturn -- parsing is finished, return the result.  |
`-----------------------------------------------------*/
yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[+*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 476 "ltrtest.y"


void do_some_propagation(){
   // try and fire each transition relation

   
   vector<TransitionRelation*>::iterator vi;
   int fired_up=0;
   int ntrans=trlist->size();


   while (fired_up < prop_steps * ntrans){
      for (vi=trlist->begin();vi < trlist->end(); vi++){
         (*vi)->fire();
         fired_up++;
      }
   }

}

int find_variable(char * what){
   int i=f->search(what);
   if (i==VAR_NOT_FOUND){
      string x=string("Error:: Variable ")+ what + string(" not found");
      yyerror(x);
      exit(1);
   }

   return i;
}

bool search_location( char * name, Location ** what){
   vector<Location*>::iterator vi;
   string nstr(name);
   for(vi=loclist->begin();vi< loclist->end();vi++){
      if ((*vi)->matches(nstr)){
         *what=(*vi);
         return true;
      }
   }

   return false;
}


bool search_transition_relation( char * name, TransitionRelation ** what){
   vector<TransitionRelation*>::iterator vi;
   string nstr(name);
   for(vi=trlist->begin();vi< trlist->end();vi++){
      if ((*vi)->matches(nstr)){
         *what=(*vi);
         return true;
      }
   }
   
   return false;
}

void yyerror(char const * x){
   yyerror(string(x));
}

void yyerror(string const & x){

   cerr<<x<<endl;
   cerr<<"Line number::"<<linenum<<endl;
   exit(1);
   
}

int parse_cmd_line(char * x){
   
   if (strcmp(x,"debug")==0) return DEBUG;
   if (strcmp(x,"debug_2")==0) return DEBUG_2;
   if (strcmp(x,"debug_3")==0) return DEBUG_3;
   if (strcmp(x,"no_print_tree")==0) return NO_PRINT_TREE;
   if (strcmp(x,"one")==0) return ONECONTEXT;
   if (strcmp(x,"many")==0) return MANYCONTEXT;
   if (strcmp(x,"new_many")==0) return NEW_MANYCONTEXT;
   if (strcmp(x,"new_2_many")==0) return NEW_2_MANYCONTEXT;
   if (strcmp(x,"new_3_many")==0) return NEW_3_MANYCONTEXT;
   if (strcmp(x,"newdfs")==0) return NEWDFS;
   if (strcmp(x,"newdfs_sequences")==0) return NEWDFS_SEQUENCES;
   if (strcmp(x,"newdfs_seq_propagation")==0) return NEWDFS_SEQ_PROPAGATION;
   if (strcmp(x,"noProjection")==0) return NO_PROJECTION;
   if (strcmp(x,"FEC")==0) return FARKAS_ELIMINATE_C;
   if (strcmp(x,"KEC")==0) return KOHLER_ELIMINATE_C;
   if (strcmp(x,"REC")==0) return FOUMOT_ELIMINATE_C;
   if (strcmp(x,"no_prior")==0) return NO_PRIOR;
   if (strcmp(x,"target_prior1")==0) return TARGET_PRIOR1;
   if (strcmp(x,"target_prior2")==0) return TARGET_PRIOR2;
   if (strcmp(x,"target_prior3")==0) return TARGET_PRIOR3;
   if (strcmp(x,"one_per_group")==0) return ONE_PER_GROUP;
   if (strcmp(x,"two_per_group")==0) return TWO_PER_GROUP;
   if (strcmp(x,"three_per_group")==0) return THREE_PER_GROUP;
   if (strcmp(x,"four_per_group")==0) return FOUR_PER_GROUP;
   if (strcmp(x,"gendrop")==0) return GENDROP;
   if (strcmp(x,"zero_only")==0) return ZERO_ONLY;
   if (strcmp(x,"one_only")==0) return ONE_ONLY;
   if (strcmp(x,"zero_one")==0) return ZERO_ONE;
   if (strcmp(x,"falsepath")==0) return YES_FALSEPATH;
   if (strcmp(x,"nofalsepath")==0) return NO_FALSEPATH;
   if (strcmp(x,"trsat")==0) return YES_TRSAT;
   if (strcmp(x,"notrsat")==0) return NO_TRSAT;
   if (strcmp(x,"exitpath")==0) return YES_EXITPATH;
   if (strcmp(x,"noexitpath")==0) return NO_EXITPATH;
   if (strcmp(x,"djinv")==0) return YES_DJINV;
   if (strcmp(x,"nodjinv")==0) return NO_DJINV;
   if (strcmp(x,"arrinv")==0) return YES_ARRINV;
   if (strcmp(x,"noarrinv")==0) return NO_ARRINV;
   if (strcmp(x,"noinst")==0) return NO_INSTANTIATION;
   if (strcmp(x,"noch79")==0) return NO_CH79;
   if (strcmp(x,"nobhrz03")==0) return NO_BHRZ03;
   if (strcmp(x,"dual")==0) return YES_DUAL;
   if (strcmp(x,"ch79")==0) return YES_CH79;
   if (strcmp(x,"bhrz03")==0) return YES_BHRZ03;
   if (strcmp(x,"nodual")==0) return NO_DUAL;
   if (strcmp(x,"invcheck")==0) return INV_CHECK;
   if (strcmp(x,"noinvcheck")==0) return NO_INV_CHECK;
   
  
   return BULLSHIT;
}
void Print_Location();
void collect_invariants(C_Polyhedron & cpoly, C_Polyhedron & invd){
  /*
   *  Collect invariants
   */
  vector<Location * >::iterator vl;
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);
  vl = loclist->begin();
  //tcout<<endl<<"- In collect_invariants(), cpoly is : "<<endl<<"  "<<cpoly<<endl;
  //Generator_System mgs = cpoly.minimized_generators();
  for (vl=loclist->begin();vl<loclist->end();vl++){
    (*vl)->extract_invariants_and_update(cpoly,invd);
    //(*vl)->extract_invariant_from_generator(mgs);
    //(*vl)->update_dual_constraints(invd);
    //tcout<<endl<<"5.";
    //Print_Location();
  }
  return;
}

void collect_invariants_for_initial_by_eliminating(C_Polyhedron & cpoly, C_Polyhedron & invd){
  //
  //  Collect invariants for initial
  //
  vector<Location * >::iterator vl;
  int loclist_size = loclist->size();
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);
  vl = loclist->begin();

  //    Firstly, collect invariants for initial location by eliminating
  //      for initial *vl, i.e. location, 
  //      use cpoly to update *vl->invariant and *vl->invariant updates invd.
  //for (vl=loclist->begin(); vl!=loclist->end(); vl++)
  (*vl)->extract_invariants_and_update_for_one_location_by_eliminating(cpoly,invd);
  /*
  //  Recursive Propagation
  //    Secondly, build the invariants from initial location by propagation
  int propagation_flag[loclist_size]={0};
  propagation_flag[0]=1;
  int i = 0;
  for ( vl = loclist->begin(); vl < loclist->end(); vl++ ){// propagate from i-th location
    for (int j=0; j<loclist_size; j++){
      if (propagation_flag[j] == 0){// the location without invariants needs to propagate
        if ( !location_matrix[i][j].empty() ){// find the non-empty vector of location_matrix
          tcout<<endl<<"Location "<<(*loclist)[j]->get_name()<<" at Propagation:";
          //  prepare the consatraints
          C_Polyhedron loc_i_inv = (*loclist)[i]->get_invariant();
          int trans_index = location_matrix[i][j][0];
          C_Polyhedron trans_relation = (*trlist)[trans_index]->get_relation();
          tcout<<endl<<"From Location invariant "<<(*loclist)[i]->get_name()<<endl<<"   "<<loc_i_inv;
          tcout<<endl<<"Through Transition relation "<<(*trlist)[trans_index]->get_name()<<": "<<endl<<"   "<<trans_relation;

          //  Propagation
          (*loclist)[j]->propagate_invariants_and_update_for_except_initial_by_propagation(loc_i_inv, trans_relation);
          //    Contains Test
          (*loclist)[j]->contains_test(cpoly, loc_i_inv, trans_relation);

          //  make flag for location has been added invariants
          propagation_flag[j]=1;
        }
      }
    }
    i++;
  }
  */
  return;
}

void collect_invariants_for_except_initial_by_propagation(){
  //
  //  Collect invariants for except initial
  //
  vector<Location * >::iterator vl;
  int loclist_size = loclist->size();
  tcout<<endl<<"> > > collect_invariants_for_except_initial_by_propagation()";

  //    Secondly, build the invariants from initial location by propagation
  int propagation_flag[loclist_size]={0};
  propagation_flag[0]=1;
  int i = 0;
  for ( vl = loclist->begin(); vl < loclist->end(); vl++ ){// propagate from i-th location
    //  The "int i" is the index of loclist,
    //  we just use vl = loclist->begin() to count for intuition
    //  but actually use "int i" to count in following index
    for (int j=0; j<loclist_size; j++){
      if (propagation_flag[j] == 0){// the location without invariants needs to propagate
        if ( !location_matrix[i][j].empty() ){// find the non-empty vector of location_matrix
          tcout<<endl<<"Location "<<(*loclist)[j]->get_name()<<" at Propagation:";
          
          //  prepare the constraints for location invariant and transition relation
          C_Polyhedron loc_i_inv = (*loclist)[i]->get_invariant();
          for (vector<int>::iterator trans_index=location_matrix[i][j].begin(); trans_index<location_matrix[i][j].end(); trans_index++){
            C_Polyhedron trans_relation = (*trlist)[*trans_index]->get_relation();
            tcout<<endl<<"From Location invariant "<<(*loclist)[i]->get_name()<<endl<<"   "<<loc_i_inv;
            tcout<<endl<<"Through Transition relation "<<(*trlist)[*trans_index]->get_name()<<": "<<endl<<"   "<<trans_relation;

            //  Propagation
            (*loclist)[j]->propagate_invariants_and_update_for_except_initial_by_propagation(loc_i_inv, trans_relation);
            //    Contains Test
            //(*loclist)[j]->contains_test(cpoly, loc_i_inv, trans_relation);
          }
          /*
          int trans_index = location_matrix[i][j][0];
          C_Polyhedron trans_relation = (*trlist)[trans_index]->get_relation();
          tcout<<endl<<"From Location invariant "<<(*loclist)[i]->get_name()<<endl<<"   "<<loc_i_inv;
          tcout<<endl<<"Through Transition relation "<<(*trlist)[trans_index]->get_name()<<": "<<endl<<"   "<<trans_relation;

          //  Propagation
          (*loclist)[j]->propagate_invariants_and_update_for_except_initial_by_propagation(loc_i_inv, trans_relation);
          //    Contains Test
          //(*loclist)[j]->contains_test(cpoly, loc_i_inv, trans_relation);
          */

          //  make flag for location has been added invariants
          propagation_flag[j]=1;
        }
      }
    }
    i++;
  }
  
  return;
}

void collect_invariants_for_initial_by_recursive_eliminating(C_Polyhedron & cpoly, C_Polyhedron & invd){
  /*
   *  Collect invariants
   */
  vector<Location * >::iterator vl;
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);

  //    Firstly, collect invariants for initial location by recursive eliminating
  vl = loclist->begin();
  (*vl)->extract_invariants_and_update_for_initial_by_recursive_eliminating(cpoly,invd);

  return;
}

void collect_invariants_for_one_location_by_eliminating(int target_index, C_Polyhedron & cpoly, C_Polyhedron & invd){
  //
  //  Collect invariants for initial
  //
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);
  //    Firstly, collect invariants for initial location by eliminating
  //      for initial *vl, i.e. location, 
  //      use cpoly to update *vl->invariant and *vl->invariant updates invd.
  (*loclist)[target_index]->extract_invariants_and_update_for_one_location_by_eliminating(cpoly,invd);

  return;
}

void binary_eliminating(C_Polyhedron & cpoly, C_Polyhedron & invd){
  //tcout<<endl<<"7.get here?";
  tcout<<endl<<"(int)(cpoly.space_dimension()) :"<<(int)(cpoly.space_dimension());
  tcout<<endl<<"( (*loclist)[0]->get_dimension()+1 ) : "<<( (*loclist)[0]->get_dimension()+1);
  if ( (int)(cpoly.space_dimension()) == ( (*loclist)[0]->get_dimension()+1 ) ){
    //tcout<<endl<<"8.get here?";
    (*loclist)[global_binary_i]->extract_invariants_and_update_by_binary_eliminating(cpoly, invd);
    global_binary_i++;
    tcout<<endl<<"global_binary_i : "<<global_binary_i;
    return;
  }
  //tcout<<endl<<"9.get here?";

  C_Polyhedron p_left = cpoly;
  C_Polyhedron p_right = cpoly;
  C_Polyhedron *cpoly_left = new C_Polyhedron(cpoly.space_dimension(), UNIVERSE); 
  *cpoly_left = p_left;
  C_Polyhedron *cpoly_right = new C_Polyhedron(cpoly.space_dimension(), UNIVERSE); 
  //*cpoly_right = swap2_index_and_divide_from(cpoly, cpoly.space_dimension()/2);
  *cpoly_right = p_right;
  //tcout<<endl<<"1.get here?";

  int l = 0;
  int m = cpoly.space_dimension()/2;
  int h = cpoly.space_dimension();
  Project_by_Kohler(*cpoly_left, l, m);
  Project_by_Kohler(*cpoly_right, m, h);
  //tcout<<endl<<"2.get here?";

  binary_eliminating(*cpoly_left, invd);
  //tcout<<endl<<"3.get here?";
  delete(cpoly_left);
  //tcout<<endl<<"4.get here?";
  binary_eliminating(*cpoly_right, invd);
  //tcout<<endl<<"5.get here?";
  delete(cpoly_right);
  //tcout<<endl<<"6.get here?";

  return;
}

void collect_invariants_by_binary_eliminating(C_Polyhedron & cpoly, C_Polyhedron & invd){
  /*
   *  Collect invariants
   */
  vector<Location * >::iterator vl;
  invd=C_Polyhedron(fd->get_dimension(),UNIVERSE);

  //    Firstly, collect invariants for initial location by recursive eliminating
  //vl = loclist->begin();
  //(*vl)->extract_invariants_and_update_for_initial_by_recursive_eliminating(cpoly,invd);
  
  binary_eliminating(cpoly, invd);
  global_binary_i=0;

  return;
}

void dfs_traverse_recursive(int depth, vector<Clump> & vcl, C_Polyhedron & cpoly, C_Polyhedron & invd){
   /*
   tcout<<endl;
   tcout<<endl<<"  "<<"depth "<<depth;
   tcout<<endl<<"  "<<"invd is ";
   tcout<<endl<<"    "<<invd;
   tcout<<endl<<"  "<<"cpoly is ";
   tcout<<endl<<"    "<<cpoly;
   tcout<<endl<<"  "<<"invd contains cpoly ? ";
   */
  //tcout<<endl<<"depth:"<<depth<<", cpoly:";
  //tcout<<endl<<cpoly;

   if (invd.contains(cpoly)){
      bang_count++;
      //tcout<<"banged";
      return;
   }
   
   if (depth==0){
      weave_count++;
      tcout<<endl<<"/-----------------------------";
      collect_timer.restart();
      collect_invariants(cpoly,invd);
      tcout<<endl<<"- Have Collected "<<weave_count<<" invariant(s) ";
      collect_timer.stop();
      tcout<<endl<<"- The collect_invariants Time Taken (0.01s) = "<<collect_timer.compute_time_elapsed()<<endl;
      collect_time = collect_time + collect_timer.compute_time_elapsed();
      tcout<<endl<<"\\-----------------------------"<<endl;
      //    prune_clumps(vcl);
      return;
   }

   if (weave_timer.compute_time_elapsed() >= weave_time){
      tcout<< "Time is up!"<<endl;
      return;
   }
   
   vcl[depth-1].clear();
   while(vcl[depth-1].has_next()){
      //tcout<<endl<<"in while...next()";
      //tcout<<endl<<"depth:"<<depth<<", cpoly:";
      //tcout<<endl<<cpoly;
      //tcout<<endl<<"vcl["<<depth-1<<"].size():"<<vcl[depth-1].get_count();
      C_Polyhedron p(cpoly);
      //Timer test_time_for_intersection;
      p.intersection_assign(vcl[depth-1].get_reference());
      //test_time_for_intersection.stop();
      //tcout<<endl<<"- Intersection Time Taken (0.01s) = "<<test_time_for_intersection.compute_time_elapsed()<<endl;

      dfs_traverse_recursive(depth-1,vcl,p,invd);

      vcl[depth-1].next();
   }
   return;
}

void dfs_traverse_recursive_for_initial_by_eliminating(int depth, vector<Clump> & vcl, C_Polyhedron & cpoly, C_Polyhedron & invd){
   if (invd.contains(cpoly)){
      bang_count++;
      return;
   }
   
   if (depth==0){
      weave_count++;
      tcout<<endl<<"/-----------------------------";
      //Timer test_time_for_minimized;
      collect_invariants_for_initial_by_eliminating(cpoly,invd);
      tcout<<endl<<"- Have Collected "<<weave_count<<" invariant(s)";
      //test_time_for_minimized.stop();
      //tcout<<endl<<"- The collect_invariants's function Time Taken (0.01s) = "<<test_time_for_minimized.compute_time_elapsed()<<endl;
      tcout<<endl<<"\\-----------------------------"<<endl;
      //    prune_clumps(vcl);
      return;
   }

   if (weave_timer.compute_time_elapsed() >= weave_time){
      tcout<< "Time is up!"<<endl;
      return;
   }
   
   vcl[depth-1].clear();
   while(vcl[depth-1].has_next()){
      
      C_Polyhedron p(cpoly);
      //Timer test_time_for_intersection;
      p.intersection_assign(vcl[depth-1].get_reference());
      //test_time_for_intersection.stop();
      //tcout<<endl<<"- Intersection Time Taken (0.01s) = "<<test_time_for_intersection.compute_time_elapsed()<<endl;

      dfs_traverse_recursive_for_initial_by_eliminating(depth-1,vcl,p,invd);

      vcl[depth-1].next();
   }
   return;
}

void dfs_traverse_recursive_for_initial_by_recursive_eliminating(int depth, vector<Clump> & vcl, C_Polyhedron & cpoly, C_Polyhedron & invd){
   
   if (invd.contains(cpoly)){
      bang_count++;
      return;
   }
   
   if (depth==0){
      weave_count++;
      tcout<<endl<<"/-----------------------------";
      Timer test_time_for_minimized;
      collect_invariants_for_initial_by_recursive_eliminating(cpoly,invd);
      test_time_for_minimized.stop();
      tcout<<endl<<"- The collect_invariants's function Time Taken (0.01s) = "<<test_time_for_minimized.compute_time_elapsed()<<endl;
      tcout<<"\\-----------------------------"<<endl;
      //    prune_clumps(vcl);
      return;
   }

   if (weave_timer.compute_time_elapsed() >= weave_time){
      tcout<< "Time is up!"<<endl;
      return;
   }
   
   vcl[depth-1].clear();
   while(vcl[depth-1].has_next()){
      
      C_Polyhedron p(cpoly);
      //Timer test_time_for_intersection;
      p.intersection_assign(vcl[depth-1].get_reference());
      //test_time_for_intersection.stop();
      //tcout<<endl<<"- Intersection Time Taken (0.01s) = "<<test_time_for_intersection.compute_time_elapsed()<<endl;

      dfs_traverse_recursive_for_initial_by_recursive_eliminating(depth-1,vcl,p,invd);

      vcl[depth-1].next();
   }
   return;
}

void dfs_traverse_recursive_for_binary_eliminating(int depth, vector<Clump> & vcl, C_Polyhedron & cpoly, C_Polyhedron & invd){
   
   //Timer test_time_for_contains;
   int contains=invd.contains(cpoly);
   //test_time_for_contains.stop();
   //tcout<<endl<<"- The contains function Time Taken (0.01s) = "<<test_time_for_contains.compute_time_elapsed();
   //global_contains_time+=test_time_for_contains.compute_time_elapsed();
   //tcout<<endl<<"- The global_contains_time Time Taken (0.01s) = "<<global_contains_time;
   if (contains){
      bang_count++;
      return;
   }
   
   if (depth==0){
      weave_count++;
      tcout<<endl<<"/-----------------------------";
      //Timer test_time_for_minimized;
      collect_invariants_by_binary_eliminating(cpoly,invd);
      tcout<<endl<<"- Have Collected "<<weave_count<<" invariant(s) ";
      //test_time_for_minimized.stop();
      //tcout<<endl<<"- The collect_invariants's function Time Taken (0.01s) = "<<test_time_for_minimized.compute_time_elapsed()<<endl;
      tcout<<endl<<"\\-----------------------------"<<endl;
      //    prune_clumps(vcl);
      return;
   }

   if (weave_timer.compute_time_elapsed() >= weave_time){
      tcout<< "Time is up!"<<endl;
      return;
   }
   
   vcl[depth-1].clear();
   while(vcl[depth-1].has_next()){
      
      C_Polyhedron p(cpoly);
      //Timer test_time_for_intersection;
      p.intersection_assign(vcl[depth-1].get_reference());
      //test_time_for_intersection.stop();
      //tcout<<endl<<"- Intersection Time Taken (0.01s) = "<<test_time_for_intersection.compute_time_elapsed()<<endl;

      dfs_traverse_recursive_for_binary_eliminating(depth-1,vcl,p,invd);

      vcl[depth-1].next();
   }
   return;
}

void dfs_traverse_recursive_for_one_location_by_eliminating(int target_index, int depth, Tree & tr, C_Polyhedron & cpoly, C_Polyhedron & invd){

   if (invd.contains(cpoly)){
      //tr.Print_Prune_Tree(depth,"Banged"); // print for debug and improve algorithm
      bang_count++;
      single_bang_count++;
      return;
   }

   if (depth==0){
      //backtrack_flag = true;
      weave_count++;
      single_weave_count++;
      tcout<<endl<<endl<<"/-----------------------------";
      tr.Print_Prune_Tree(depth,"Weaved"); // print for debug and improve algorithm
      collect_timer.restart();
      collect_invariants_for_one_location_by_eliminating(target_index, cpoly, invd);
      tcout<<endl;
      tcout<<endl<<"- Have Collected "<<weave_count<<" invariant(s)";
      collect_timer.stop();
      tcout<<endl<<"- The collect_invariants Time Taken (0.01s) = "<<collect_timer.compute_time_elapsed();
      collect_time = collect_time + collect_timer.compute_time_elapsed();
      single_collect_time = single_collect_time + collect_timer.compute_time_elapsed();
      tcout<<endl<<"\\-----------------------------"<<endl;
      prune_nodes_timer.restart();
      //tr.prune_node_self_inspection(target_index,invd);
      prune_nodes_timer.stop();
      prune_nodes_time += prune_nodes_timer.compute_time_elapsed();
      return;
   }

   if (total_timer.compute_time_elapsed() >= weave_time){
      tcout<< "Time is up!"<<endl;
      return;
   }
   
   tr.get_clump(depth-1).clear();
   while(tr.get_clump(depth-1).has_next()){
      
      C_Polyhedron p(cpoly);
      p.intersection_assign(tr.get_clump(depth-1).get_reference());

      dfs_traverse_recursive_for_one_location_by_eliminating(target_index,depth-1,tr,p,invd);
      
      backtrack_timer.restart(); // Timer On
      if (backtrack_flag == true){
        bool flag = invd.contains(cpoly);
        if (flag){
          backtrack_success++;
          tcout<<endl<<"Pruned by backtracking in depth "<<depth;
          tr.get_clump(depth-1).clear();
          return;
        }
        else {
          if (backtrack_success >= 1){
            backtrack_count++;
            backtrack_success = 0;
          }
          backtrack_flag = false;
        }
      }
      backtrack_timer.stop(); // Timer Off
      backtrack_time += backtrack_timer.compute_time_elapsed();
      
      // For prune_node_self_inspection
      if (depth-1 < tr.get_first_conflict()){
        return;
      }
      else if (depth-1 == tr.get_first_conflict()){
        tr.clear_first_conflict();
        backhere_flag = true;
      }

      if (backhere_flag == false){
        tr.get_clump(depth-1).next();
      }
      else {
        backhere_flag = false;
      }
   }
   return;
}

void dfs_traverse(vector<Clump> & vcl, C_Polyhedron & initp){
   // first find out the number of clumps
   // a polyhedron containing the solutions contained to date
   // initiate a dfs traversal.
   // write an invariant extraction function at depth 0

   C_Polyhedron  invd(*trivial);
   int ncl=0;
   vector<Clump>::iterator vi;
   for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
   }

   weave_timer.restart();

   /***/
   // modified and needed be deleted
   //tcout<<endl<<"test and set 'ncl'=? ";
   //ncl=0;
   //vector<Clump> test_vcl = vcl;
   //test_vcl[0] = vcl[3];
   /***/
  
   dfs_traverse_recursive(ncl,vcl,initp,invd);
   
}

void dfs_traverse_for_initial_by_eliminating(vector<Clump> & vcl, C_Polyhedron & initp){
  // Here is the function of "extract_invariant_by_eliminating()"
  C_Polyhedron  invd(*trivial);
  int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
  }
  weave_timer.restart();

  dfs_traverse_recursive_for_initial_by_eliminating(ncl,vcl,initp,invd);
}

void dfs_traverse_for_initial_by_recursive_eliminating(vector<Clump> & vcl, C_Polyhedron & initp){
  // Here is the function of "extract_invariant_by_eliminating()"
  C_Polyhedron  invd(*trivial);
  int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
  }
  weave_timer.restart();

  dfs_traverse_recursive_for_initial_by_recursive_eliminating(ncl,vcl,initp,invd);
}

void dfs_traverse_for_binary_eliminating(vector<Clump> & vcl, C_Polyhedron & initp){
  // Here is the function of "extract_invariant_by_eliminating()"
  C_Polyhedron  invd(*trivial);
  int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
  }
  weave_timer.restart();

  dfs_traverse_recursive_for_binary_eliminating(ncl,vcl,initp,invd);
}

void dfs_traverse_for_one_location_by_eliminating(int target_index, vector<Clump> & vcl, C_Polyhedron & initp){
  C_Polyhedron invd(*trivial);
  Tree tr = Tree(); //empty tree
  tr.set_target_index(target_index);
  int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      ncl++;
      (*vi).clear();
  }

  tcout<<endl<<endl<<"/ Start to solve Location "<<(*loclist)[target_index]->get_name();
  if (tree_prior == "target_prior1"){
    tcout<<endl<<"/ Using target_prior1";
    tr.Reorder_Target_Prior_1(vcl);
  }
  else if (tree_prior == "target_prior2"){
    tcout<<endl<<"/ Using target_prior2";
    tr.Reorder_Target_Prior_2(vcl);
  }
  else if (tree_prior == "target_prior3"){
    tcout<<endl<<"/ Using target_prior3";
    tr.Reorder_Target_Prior_3(vcl);
  }
  else {
    tcout<<endl<<"Wrong Type: "<<tree_prior;
  }

  //tr.prune_clumps_by_hierarchy_inclusion();

  dfs_traverse_recursive_for_one_location_by_eliminating(target_index,ncl,tr,initp,invd);
}

void dfs_sequences_generation_traverse(vector<vector<vector<vector<int>>>> & target_sequences, int target_index, vector<Clump> & vcl, C_Polyhedron & initp){
  //C_Polyhedron invd(*trivial);
  Tree tr = Tree(); //empty tree
  tr.set_target_index(target_index);
  //int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      //ncl++;
      (*vi).clear();
  }

  tcout<<endl<<endl<<"/ Start to solve Location "<<(*loclist)[target_index]->get_name();
  if (tree_prior == "no_prior"){
    tcout<<endl<<"/ Using no_prior";
    tr.Original_Prior(vcl);
  }
  else if (tree_prior == "target_prior1"){
    tcout<<endl<<"/ Using target_prior1";
    tr.Reorder_Target_Prior_1(vcl);
  }
  else if (tree_prior == "target_prior2"){
    tcout<<endl<<"/ Using target_prior2";
    tr.Reorder_Target_Prior_2(vcl);
  }
  else if (tree_prior == "target_prior3"){
    tcout<<endl<<"/ Using target_prior3";
    tr.Reorder_Target_Prior_3(vcl);
  }
  else {
    tcout<<endl<<"Wrong Type: "<<tree_prior;
  }

  tr.set_max_clump_count();
  //tr.prune_clumps_by_hierarchy_inclusion();
  //dfs_traverse_recursive_for_one_location_by_eliminating(target_index,ncl,tr,initp,invd);

  tcout<<endl<<"/ Generate Sequences";
  vector<vector<vector<int>>> sequences;
  sequences = tr.sequences_generation(some_per_group, initp);
  target_sequences.push_back(sequences);

}

void dfs_sequences_generation_traverse_for_one_location_from_intra(vector<vector<vector<vector<int>>>> & target_sequences, int target_index, vector<Clump> & vcl, C_Polyhedron & initp){
  //C_Polyhedron invd(*trivial);
  Tree tr = Tree(); //empty tree
  tr.set_target_index(target_index);
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      (*vi).clear();
  }

  tcout<<endl<<endl<<"/ Start to solve Location "<<(*loclist)[target_index]->get_name();
  // extract only-one-vcl which is intra-transition about this location
  tr.extract_vcl_for_one_location_about_intra(vcl);

  tr.set_max_clump_count();

  tcout<<endl<<"/ Generate Sequences";
  vector<vector<vector<int>>> sequences;
  sequences = tr.sequences_generation("one_per_group", initp);
  target_sequences.push_back(sequences);

  tcout<<endl<<"\\ Generate Sequences";
  tcout<<endl<<"\\ End to solve Location "<<(*loclist)[target_index]->get_name();
}

void dfs_sequences_traverse_for_one_location_by_eliminating(vector<vector<vector<int>>> sequences, int target_index, vector<Clump> & vcl, C_Polyhedron & initp){
  C_Polyhedron invd(*trivial);
  Tree tr = Tree(); //empty tree
  tr.set_target_index(target_index);
  //int ncl=0;
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      //ncl++;
      (*vi).clear();
  }

  tcout<<endl<<endl<<"/ Start to solve Location "<<(*loclist)[target_index]->get_name();
  if (tree_prior == "no_prior"){
    tcout<<endl<<"/ Using no_prior";
    tr.Original_Prior(vcl);
  }
  else if (tree_prior == "target_prior1"){
    tcout<<endl<<"/ Using target_prior1";
    tr.Reorder_Target_Prior_1(vcl);
  }
  else if (tree_prior == "target_prior2"){
    tcout<<endl<<"/ Using target_prior2";
    tr.Reorder_Target_Prior_2(vcl);
  }
  else if (tree_prior == "target_prior3"){
    tcout<<endl<<"/ Using target_prior3";
    tr.Reorder_Target_Prior_3(vcl);
  }
  else {
    tcout<<endl<<"Wrong Type: "<<tree_prior;
  }

  tr.set_max_clump_count();
  //tr.prune_clumps_by_hierarchy_inclusion();
  //dfs_traverse_recursive_for_one_location_by_eliminating(target_index,ncl,tr,initp,invd);

  //tcout<<endl;
  tcout<<endl<<"/ Read(Traverse) Sequences";
  tr.dfs_sequences_traverse(sequences, initp, invd);
}

void dfs_sequences_traverse_for_one_location_from_intra_by_eliminating(vector<vector<vector<int>>> sequences, int target_index, vector<Clump> & vcl, C_Polyhedron & initp){
  C_Polyhedron invd(*trivial);
  Tree tr = Tree(); //empty tree
  tr.set_target_index(target_index);
  vector<Clump>::iterator vi;
  for (vi=vcl.begin();vi < vcl.end();vi++){
      (*vi).clear();
  }

  tcout<<endl<<endl<<"/ Start to solve Location "<<(*loclist)[target_index]->get_name();
  // extract only-one-vcl which is intra-transition about this location
  tr.extract_vcl_for_one_location_about_intra(vcl);

  tr.set_max_clump_count();

  tcout<<endl<<"/ Read(Traverse) Sequences";
  tr.dfs_sequences_traverse(sequences, initp, invd);

  tcout<<endl<<"\\ Read(Traverse) Sequences";
  tcout<<endl<<"\\ End to solve Location "<<(*loclist)[target_index]->get_name();
}

// compute invariants by farkas for this one location from intra-transition
void collect_invariants_for_one_location_from_intra(vector<Clump> & vcl, int loc_index){
  // initialize
  int lid = loc_index;
  vector<vector<vector<vector<int>>>> target_sequences;
  int nd = fd->get_dimension();
  C_Polyhedron local_initp(nd, UNIVERSE);

  /*
   * Generate Sequences
   */
  if (debug_3){
    tcout<<endl;
    tcout<<endl<<"- id (Generate Sequences): "<<lid<<", Location::"<<(*loclist)[lid]->get_name();
  }
  single_pre_prune_bang_count = 0;
  counter.set_location_index_and_init_depth(lid, vcl.size());
  // compute invariants by using initial-value and intra-transition
  bool  has_initial_polyset = (*loclist)[lid]->has_initial();
  if(!has_initial_polyset){
    tcout<<endl<<"- ( !has_initial_polyset ) in Location::"<<(*loclist)[lid]->get_name();
    vector<vector<vector<int>>> empty_sequences;
    target_sequences.push_back(empty_sequences);
  }
  else{
    (*loclist)[lid]->compute_dual_constraints(local_initp);
    dfs_sequences_generation_traverse_for_one_location_from_intra(target_sequences, lid, vcl, local_initp);
  }

  /*
   * Read Sequences
   */
  if (debug_3){
    tcout<<endl;
    tcout<<endl<<"- id (Read Sequences): "<<lid<<", Location::"<<(*loclist)[lid]->get_name();
  }
  single_weave_count = 0;
  single_collect_time = 0;
  single_post_prune_bang_count = 0;
  // compute invariants by using initial-value and intra-transition
  if(!has_initial_polyset){
    tcout<<endl<<"- ( !has_initial_polyset ) in Location::"<<(*loclist)[lid]->get_name();
  }
  else {
    vector<vector<vector<int>>> sequences;
    if(target_sequences.size()==1){
      sequences = target_sequences[0];
    }
    else{
      tcout<<endl<<"Error: There are more than one sequences";
    }
    dfs_sequences_traverse_for_one_location_from_intra_by_eliminating(sequences, lid, vcl, local_initp);
  }

  return;
}

void Initialize_before_Parser(){

  tcout<<endl<<"- Initialize_before_Parser doing...";
   weave_count=bang_count=backtrack_count=0;
   backtrack_success = 0;
   backtrack_flag = false;
   merge_count = 0;
   linenum=0;
   inv_check=false;
   clump_prune_count=prune_count=0;
   context_count=0;
   fm=new var_info();
   fd=new var_info();
   loclist= new vector<Location *>();
   trlist=new vector<TransitionRelation *>();
   debug=0;
   debug_2=0;
   debug_3=0;
   print_tree=true;
   num_context=2;
   projection = "kohler_improvement_eliminate_c";
   tree_prior = "target_prior2";
   some_per_group="two_per_group";
   gendrop=false;
   global_sub_system_list=new vector<System *> ();
   zero=one=true;
   falsepath=true;
   trsat=true;
   noexitpath=false;
   djinv=false;
   arrinv=false;
   prop_steps=2;
   weave_time=360000;
   total_time=360000;
   ch79=false;
   bhrz03=false;
   dual=false;
  tcout<<"Done!"<<endl;
}

void Scan_Input(int argc, char * argv[]){
  tcout<<endl<<"- Scan_Input doing...";

  // print argc and argc
  tcout<<endl<<"argc: "<<argc<<endl;
  for (int i = 0; i < argc; i++){
    tcout<<"argv: "<<argv[i]<<endl;
  }

  if (argc<=1){
    // by default one context and no gendrop
    debug=0;
    debug_2=0;
    debug_3=0;
    print_tree=true;
    num_context=2;
    projection = "kohler_improvement_eliminate_c";
    tree_prior = "target_prior2";
    some_per_group="two_per_group";
    falsepath=true;
    trsat=true;
    noexitpath=false;
    djinv=false;
    arrinv=false;
    gendrop=false;
  } else {
    for (int k=1;k<argc;k++){
      switch(parse_cmd_line(argv[k])){
        case GENDROP:
          gendrop=true;
          break;
        case DEBUG:
          debug=1;
          break;
        case DEBUG_2:
          debug_2=1;
          break;
        case DEBUG_3:
          debug_3=1;
          break;
        case NO_PRINT_TREE:
          print_tree=false;
          break;
        case ONECONTEXT: //Option: one
          num_context=1;
          break;
        case MANYCONTEXT: //Option: many
          num_context=2;
          break;
        case NEW_MANYCONTEXT: //Option: new method for many, eliminate C
          num_context=3;
          break;
        case NEW_2_MANYCONTEXT: //Option: new method for many, recursive eliminate
          num_context=4;
          break;
        case NEW_3_MANYCONTEXT:
          num_context=5;
          break;
        case NEWDFS:
          num_context=6;
          break;
        case NEWDFS_SEQUENCES:
          num_context=7;
          break;
        case NEWDFS_SEQ_PROPAGATION:
          num_context=8;
          noexitpath=true;
          djinv=true;
          break;
        case NO_PROJECTION:
          projection = "no_projection";
          break;
        case KOHLER_ELIMINATE_C:
          projection = "kohler_improvement_eliminate_c";
          break;
        case FARKAS_ELIMINATE_C:
          projection = "farkas_eliminate_c";
          break;
        case FOUMOT_ELIMINATE_C:
          projection = "foumot_eliminate_c";
          break;
        case NO_PRIOR:
          tree_prior = "no_prior";
          break;
        case TARGET_PRIOR1:
          tree_prior = "target_prior1";
          break;
        case TARGET_PRIOR2:
          tree_prior = "target_prior2";
          break;
        case TARGET_PRIOR3:
          tree_prior = "target_prior3";
          break;
        case ONE_PER_GROUP:
          some_per_group="one_per_group";
          break;
        case TWO_PER_GROUP:
          some_per_group="two_per_group";
          break;
        case THREE_PER_GROUP:
          some_per_group="three_per_group";
          break;
        case FOUR_PER_GROUP:
          some_per_group="four_per_group";
          break;
        case ZERO_ONLY:
          one=false;
          zero=true;
          break;
        case ONE_ONLY:
          one=true;
          zero=false;
          break;
        case ZERO_ONE:
          zero=one=true;
          break;
        case YES_FALSEPATH:
          falsepath=true;
          break;
        case NO_FALSEPATH:
          falsepath=false;
          break;
        case YES_TRSAT:
          trsat=true;
          break;
        case NO_TRSAT:
          trsat=false;
          break;
        case YES_EXITPATH:
          noexitpath=false;
          break;
        case NO_EXITPATH:
          noexitpath=true;
          break;
        case YES_DJINV:
          djinv=true;
          break;
        case NO_DJINV:
          djinv=false;
          break;
        case YES_ARRINV:
          arrinv=true;
          break;
        case NO_ARRINV:
          arrinv=false;
          break;
        case NO_INSTANTIATION:
          zero=one=false;
          break;
        case NO_CH79: //Option: noch79(on): Do not do ch79
          ch79=false;
          break;
        case YES_CH79:
          ch79=true;
          break;

        case NO_BHRZ03: //Option: nobhrz03(on): Do not do bhrz03
          bhrz03=false;
          break;
        case YES_BHRZ03:
          bhrz03=true;
          break;

        case NO_DUAL:
          dual=false;
          break;
        case YES_DUAL:
          dual=true;
          break;
        case INV_CHECK:
          inv_check=true;
          break;
        case NO_INV_CHECK:
          inv_check=false;
          break;
        default:
          cerr<<"Illegal option:"<<argv[k]<<" ignored."<<endl;
          cerr<<"Usage:"<<argv[0]<<" [one,many,dual,nodual,ch79,noch79,bhrz03,nobhrz03,invcheck,noinvcheck] [ < input file ] [> output file ] "<<endl;
          break;
      }
    }
  }
  tcout<<"Done!"<<endl;
}

void Print_Location_and_Transition(){
   tcout<<endl;
   tcout<<"----------------------------- "<<endl;
   tcout<<"| The Locations read in are: "<<endl;
   tcout<<"----------------------------- "<<endl;
   for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
      tcout<<*(*vi);
   }
   tcout<<"----------------------------- "<<endl;
   tcout<<"| The Transitions read in are: "<<endl;
   tcout<<"----------------------------- "<<endl;
   for (vector<TransitionRelation *>::iterator vj=trlist->begin();vj< trlist->end();vj++){
      tcout<<*(*vj);
   }
}

void Print_Location(){
   tcout<<endl;
   tcout<<"----------------------------- "<<endl;
   tcout<<"| The Locations read in are: "<<endl;
   tcout<<"----------------------------- "<<endl;
   for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
      tcout<<*(*vi);
   }
}

void print_disjunctive_inv_before_program(){
  tcout<<endl<<"/---------------------------------------- ";
  tcout<<endl<<"| Disjunctive Invariants before Program: ";
  tcout<<endl<<"----------------------------------------- ";
  int i=0;
  for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
    if ((*vi)->get_name()!=EXIT_LOCATION && !(*vi)->get_invariant().is_empty()){
      if (i!=0){
        tcout<<endl<<"\\/";
      }
      print_pure_polyhedron((*vi)->get_invariant(), (*vi)->get_var_info());
      i++;
    }
  }
  tcout<<endl<<"\\---------------------------------------- ";
  tcout<<endl;
}

void print_array_inv_before_program(){
  tcout<<endl<<"/---------------------------------------- ";
  tcout<<endl<<"| Array Invariants before Program: ";
  tcout<<endl<<"----------------------------------------- ";
  int i=0;
  for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
    if ((*vi)->get_name()!=EXIT_LOCATION && !(*vi)->get_invariant().is_empty()){
      if (i!=0){
        tcout<<endl<<"\\/";
      }
      print_pure_polyhedron_for_arrayinv((*vi)->get_invariant(), (*vi)->get_var_info());
      i++;
    }
  }
  tcout<<endl<<"\\---------------------------------------- ";
  tcout<<endl;
}

void Print_Status_before_Solver(){
  tcout<<endl;
  tcout<<"/----------------------------- "<<endl;
  tcout<<"| Status before Solver: "<<endl;
  tcout<<"----------------------------- "<<endl;
  tcout<<"| Debug ID # "<<debug<<endl;
  tcout<<"| Debug_2 ID # "<<debug_2<<endl;
  tcout<<"| Debug_3 ID # "<<debug_3<<endl;
  tcout<<"| Print Tree : "<<print_tree<<endl;
  tcout<<"| Strategy ID # "<<num_context<<endl;
  tcout<<"| Strategy name : ";
  switch(num_context){
    case 1:tcout<<"one"<<endl;break;
    case 2:tcout<<"many"<<endl;break;
    case 6:tcout<<"newdfs"<<endl;break;
    case 7:tcout<<"newdfs_sequences"<<endl;break;
    case 8:tcout<<"newdfs_seq_propagation"<<endl;break;
    default:tcout<<endl;break;
  }

  if (num_context == 6){
    tcout<<"| DFS Search method : "<<tree_prior<<endl;
    tcout<<"| Projection method : "<<projection<<endl;
  }

  if (num_context == 7){
    tcout<<"| DFS Search method : "<<tree_prior<<endl;
    tcout<<"| Sequences Divide method : "<<some_per_group<<endl;
    tcout<<"| Projection method : "<<projection<<endl;
  }

  if (num_context == 8){
    tcout<<"| DFS Search method : "<<tree_prior<<endl;
    tcout<<"| Sequences Divide method : "<<some_per_group<<endl;
    tcout<<"| Projection method : "<<projection<<endl;
  }

  tcout<<"| Local invariants to be generated : "<<zero<<endl;
  tcout<<"| Increasing invariants to be generated : "<<one<<endl;
  tcout<<"| Falsepath to be enabled : "<<falsepath<<endl;
  tcout<<"| Transition-sat to be enabled : "<<trsat<<endl;
  tcout<<"| Exit-Transition is computed : "<<(!noexitpath)<<endl;
  tcout<<"| Display Disjunctive Invariants : "<<djinv<<endl;
  tcout<<"| Display Array Invariants : "<<arrinv<<endl;
  tcout<<"| Weave time allowed : "<<weave_time<<endl;
  tcout<<"\\----------------------------- "<<endl;
}

void Print_Status_after_Solver(){
  tcout<<endl;
  tcout<<"/----------------------------- "<<endl;
  tcout<<"| Status after Solver: "<<endl;
  tcout<<"----------------------------- "<<endl;
  tcout<<"| Time Taken Unit: (0.01s)"<<endl;
  tcout<<"| # of Contexts generated = "<<context_count<<endl;
  tcout<<"|"<<endl;


  tcout<<"| # of pruned vcl in intra-transition = "<<prune_count<<endl;
  tcout<<"| # of pruned nodes by self inspection = "<<clump_prune_count<<", Time = "<<prune_nodes_time<<endl;
  tcout<<"| # of pruned by backtracking = "<<backtrack_count<<", Time = "<<backtrack_time<<endl;
  tcout<<"| # of merged for sub sequences = "<<merge_count<<endl;
  tcout<<"|"<<endl;


  tcout<<"| t: collect_invariant Time"<<endl;
  tcout<<"| w: invariants *weav*ed"<<endl;
  for (vector<int>::size_type i = 0; i < vector_single_collect_time.size(); ++i){
    tcout<<"| LOC "<<i<<": t = "<<vector_single_collect_time[i]<<", w = "<<vector_single_weave_count[i]<<endl;
  }
  tcout<<"| TOTAL: t = "<<collect_time<<", w = "<<weave_count<<endl;
  tcout<<"|"<<endl;


  tcout<<"| t: dfs_traverse Time"<<endl;
  tcout<<"| b: path *bang*ed"<<endl;
  if (num_context != 1){
    /*
     * Following record message for "newdfs" (i.e., without
     * divide_into_group):
     *   LOC, 
     *   vector_single_bang_count
     */
    for (vector<int>::size_type i = 0; i < vector_single_dfs_traverse_time.size(); ++i){
      tcout<<"| LOC_"<<i<<": t = "<<vector_single_dfs_traverse_time[i]<<", b = "<<vector_single_bang_count[i]<<endl;
    }
    /*
     * Following record message for "newdfs_sequences" (i.e., without
     * divide_into_group):
     *   PRE,
     *   vector_single_pre_prune_bang_count,
     *   PST,
     *   vector_single_post_prune_bang_count
     */
    for (vector<int>::size_type i = 0; i < vector_single_pre_prune_bang_count.size(); ++i){
      tcout<<"| PRE_"<<i<<": t = "<<vector_single_dfs_sequences_generation_time[i]<<", b = "<<vector_single_pre_prune_bang_count[i]<<endl;
    }
    for (vector<int>::size_type i = 0; i < vector_single_post_prune_bang_count.size(); ++i){
      tcout<<"| PST_"<<i<<": t = "<<vector_single_dfs_sequences_traverse_time[i]<<", b = "<<vector_single_post_prune_bang_count[i]<<endl;
    }
    tcout<<"| TOTAL: t = "<<dfs_traverse_time<<", b = "<<bang_count<<endl;
  }
  tcout<<"|"<<endl;


  tcout<<"| TOTAL Time = "<<total_timer.compute_time_elapsed()<<endl;
  tcout<<"\\----------------------------- "<<endl;
}

int get_index_of_location(string loc_name){
  int i=0;
  for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
    if ((*vi)->get_name() == loc_name){
      return i;
    }
    i++;
  }
}

int get_index_of_transition(string name){
  int i=0;
  for (vector<TransitionRelation *>::iterator vi=trlist->begin();vi< trlist->end();vi++){
    if ((*vi)->get_name() == name){
      return i;
    }
    i++;
  }
}

// return the transition-index which is start from this pre-location-index
vector<int> get_tid_from_prelid(int prelid){
  vector<int> tid;
  int trlist_size = trlist->size();

  for(int ti=0; ti<trlist_size; ti++){
    if((*trlist)[ti]->get_preloc_index() == prelid){
      tid.push_back(ti);
    }
  }

  return tid;
}

// return the transition-index which is start from this pre-location-index except intra-transition
vector<int> get_intertid_from_prelid(int prelid){
  vector<int> tid;
  int trlist_size = trlist->size();

  for(int ti=0; ti<trlist_size; ti++){
    if((*trlist)[ti]->get_preloc_index() == prelid && (*trlist)[ti]->get_postloc_index() != prelid){
      tid.push_back(ti);
    }
  }

  return tid;
}

// return the transition-index 
// which is start from this pre-location-index except intra-transition
// and except someother transition-index
vector<int> get_intertid_from_prelid_without_some(int prelid, string some){
  vector<int> tid;
  int trlist_size = trlist->size();

  for(int ti=0; ti<trlist_size; ti++){
    if((*trlist)[ti]->get_preloc_index() == prelid && (*trlist)[ti]->get_postloc_index() != prelid && (*trlist)[ti]->get_postloc_name() != some){
      tid.push_back(ti);
    }
  }

  return tid;
}

// return the inter-transition-index which is end at this post-location-index
vector<int> get_intertid_to_postlid(int postlid){
  vector<int> tid;
  int trlist_size = trlist->size();

  for(int ti=0; ti<trlist_size; ti++){
    if((*trlist)[ti]->get_postloc_index() == postlid && (*trlist)[ti]->get_preloc_index() != postlid){
      tid.push_back(ti);
    }
  }

  return tid;
}

void Create_Adjacency_Matrix_for_Location_and_Transition(){
  //  matrix initialization
  //    count the number of locations, i.e. length of matrix
  int loclist_size = loclist->size();
  //    count the number of transitions and push back to the vector
  //vector<int> location_matrix[loclist_size][loclist_size];
  location_matrix = new vector<int>*[loclist_size];
  for (int i=0; i<loclist_size; i++){
    location_matrix[i] = new vector<int>[loclist_size];
  }

  int j=0, j1=0;
  for (vector<TransitionRelation *>::iterator vj=trlist->begin();vj< trlist->end();vj++){
    if (trsat){
      if (!(*vj)->get_relation().is_empty()){
        location_matrix[get_index_of_location((*vj)->get_preloc_name())][get_index_of_location((*vj)->get_postloc_name())].push_back(j);
        j1++;
      }
      j++;
    }
    else {
      location_matrix[get_index_of_location((*vj)->get_preloc_name())][get_index_of_location((*vj)->get_postloc_name())].push_back(j);
      j1++;
      j++;
    }
  }

  //  print the matrix
  tcout;
  tcout<<endl<<"/----------------------------- ";
  tcout<<endl<<"| Adjacency Matrix for Location and Transition: ";
  tcout<<endl<<"----------------------------- ";
  tcout<<endl<<"| Input: "<<trlist->size()<<" transitions";
  tcout<<endl<<"----------------------------- ";
  tcout<<endl<<"| [#] is transition_index";
  for (int i=0; i<loclist_size; i++){
    tcout<<endl<<"| "<<(*loclist)[i]->get_name()<<": ";
    for (int j=0; j<loclist_size; j++){
      tcout<<"[";
      for (vector<int>::iterator it=location_matrix[i][j].begin(); it<location_matrix[i][j].end(); it++){
        tcout<<" "<< *it <<" ";
      }
      tcout<<"]->"<<(*loclist)[j]->get_name()<<";  ";
    }
  }
  tcout<<endl<<"----------------------------- ";
  tcout<<endl<<"| Output: "<<j1<<" transitions";
  tcout<<endl<<"\\----------------------------- ";
}

void Clear_Location_Invariant(){
  for (vector<Location * >::iterator vl=loclist->begin();vl<loclist->end();vl++){
    tcout<<endl<<"- Location "<<(*vl)->get_name()<<": initialize invariant";
    (*vl)->initialize_invariant();
  }
}

int main(int argc, char * argv[]){
  ios::sync_with_stdio(false);
  total_timer.restart();
  Initialize_before_Parser();  
  Scan_Input(argc, argv);
  int yyp = yyparse();
  tcout<<endl<<"- Is yacc parsing done? "<<yyp<<endl;
  add_preloc_invariants_to_transitions();
  Print_Status_before_Solver();
  Print_Location_and_Transition();
  Create_Adjacency_Matrix_for_Location_and_Transition();
  
  global_system = new System(f, fd, fm);
  for (vector<Location *>::iterator vi = loclist->begin(); vi< loclist->end(); vi++){
    global_system->add_location((*vi));  
  }
  for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj< trlist->end(); vj++){
    global_system->add_transition((*vj));
  }
  global_system->compute_duals();
  tt = new int[fm->get_dimension()];

  if (num_context == 1){
    //  Implementation for Convert_CNF_to_DNF_and_Print() function
    //    due to num_context == 1, 
    //    i.e. intra-location / single-location

    glc = global_system->get_context();
    //Print_Location_and_Transition();
    trivial = new C_Polyhedron(fd->get_dimension(),UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    invd = new C_Polyhedron(*trivial);
    tcout<<endl;
    //tcout<<"- The Convert_CNF_to_DNF_and_Print(): "<<endl;
    //tcout<<"- The Root Context: "<<endl<<(*glc)<<endl;
    glc->Convert_CNF_to_DNF_and_Print(loclist, invd, weave_time, true);
  } // if (num_context == 1)
  else if (num_context == 2){
    //  Implementation for Eliminate_c_through_inter_Location() function
    //  compared with num_context == 3, here is no elimination.
    //    due to num_context == 2, 
    //    i.e. inter-location / many-locations
    //  output_file: **many**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial); // Later, use this "trivial" to build (initial) "invd"
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp); // Later, use this "initp" to build (initial) "cpoly"
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      //    this also should trigger the simplification of the context
    }
    dfs_traverse_timer.restart();
    dfs_traverse(vcl, initp);
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();
  } //    else if (num_context == 2)
  else if (num_context == 3){
    //  Implementation for Eliminate_c_through_inter_Location() function
    //  compared with num_context == 2, here is elimination!
    //    due to num_context == 3, 
    //    i.e. inter-location / many-locations
    //  output_file: **new_many**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      //    this also should trigger the simplification of the context
    }

    dfs_traverse_timer.restart();
    dfs_traverse_for_initial_by_eliminating(vcl, initp);
    collect_invariants_for_except_initial_by_propagation();
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  } //    else if (num_context == 3)
  else if (num_context == 4){
    //  Implementation for Recursive_Eliminate_c_through_inter_Location() function
    //  compared with num_context == 3, here is recursive elimination!
    //    due to num_context == 4, 
    //    i.e. inter-location / many-locations
    //  output_file: **new_2_many**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      //    this also should trigger the simplification of the context
    }
    //  Here is the function of "extract_invariant_by_eliminating()"
    dfs_traverse_timer.restart();
    dfs_traverse_for_initial_by_recursive_eliminating(vcl, initp);
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  }//    else if (num_context == 4)
  else if (num_context == 5){
    //  Implementation for ...() function
    //  compared with num_context == 4, here is recursive elimination!
    //    due to num_context == 5, 
    //    i.e. inter-location / many-locations
    //  output_file: **new_3_many**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      //    this also should trigger the simplification of the context
    }
    //  Here is the function of "extract_invariant_by_eliminating()"
    dfs_traverse_timer.restart();
    dfs_traverse_for_binary_eliminating(vcl, initp);
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  } //    else if (num_context == 5)
  else if (num_context == 6){
    //  Implementation for Eliminate_c_through_inter_Location() function
    //  compared with num_context == 3, here is elimination!
    //    due to num_context == 6, 
    //    i.e. inter-location / many-locations
    //  output_file: **newdfs**

    //    dualize using a clump
    int nd = fd->get_dimension();
    //    obtain a polyhedron characterizing "trivial"
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //    now dualize each location
    C_Polyhedron initp(nd, UNIVERSE); // for the dualized initial conditions
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }

    //    now dualize the transition systems and collect the "clumps"
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
      if (total_timer.compute_time_elapsed() >= weave_time){
          tcout<< "Time is up!"<<endl;
          break;
      }
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      if (total_timer.compute_time_elapsed() >= weave_time){
          tcout<< "Time is up!"<<endl;
          break;
      }
      //    this also should trigger the simplification of the context
    }

    dfs_traverse_timer.restart();
    for (int target_index=0; target_index<loclist->size(); target_index++){

      single_weave_count = 0;
      single_bang_count = 0;
      single_collect_time = 0;
      single_dfs_traverse_timer.restart();

      dfs_traverse_for_one_location_by_eliminating(target_index, vcl, initp);

      single_dfs_traverse_timer.stop();
      vector_single_dfs_traverse_time.push_back(single_dfs_traverse_timer.compute_time_elapsed());
      vector_single_weave_count.push_back(single_weave_count);
      vector_single_bang_count.push_back(single_bang_count);
      vector_single_collect_time.push_back(single_collect_time);
    }
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  }//    else if (num_context == 6)
  else if (num_context == 7){
    //  output_file: **newdfs_sequences**

    //  nd
    int nd = fd->get_dimension();
    //  trivial
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //  initp
    C_Polyhedron initp(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }
    //  vcl
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
      if (total_timer.compute_time_elapsed() >= weave_time){
          tcout<< "Time is up!"<<endl;
          break;
      }
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      if (total_timer.compute_time_elapsed() >= weave_time){
          tcout<< "Time is up!"<<endl;
          break;
      }
      //    this also should trigger the simplification of the context
    }

    /*
     * The main body of CNF-to-DNF Conversion
     *   dfs_sequences_generation_traverse
     *   dfs_sequences_traverse_for_one_location_by_eliminating
     */
    dfs_traverse_timer.restart();
    vector<vector<vector<vector<int>>>> target_sequences;
    for (int target_index=0; target_index<loclist->size(); target_index++){
      if (total_timer.compute_time_elapsed() >= total_time){
          tcout<<endl<<"Time is up!";
          break;
      }

      single_pre_prune_bang_count = 0;
      counter.set_location_index_and_init_depth(target_index, vcl.size());
      single_dfs_sequences_generation_timer.restart();

      dfs_sequences_generation_traverse(target_sequences, target_index, vcl, initp);

      single_dfs_sequences_generation_timer.stop();
      vector_single_dfs_sequences_generation_time.push_back(single_dfs_sequences_generation_timer.compute_time_elapsed());
      vector_single_pre_prune_bang_count.push_back(single_pre_prune_bang_count);
    }
    //Clear_Location_Invariant();
    for (int target_index=0; target_index<loclist->size(); target_index++){
      if (total_timer.compute_time_elapsed() >= total_time){
          tcout<<endl<<"Time is up!";
          break;
      }

      single_weave_count = 0;
      single_collect_time = 0;
      single_post_prune_bang_count = 0;
      single_dfs_sequences_traverse_timer.restart();

      vector<vector<vector<int>>> sequences = target_sequences[target_index];
      dfs_sequences_traverse_for_one_location_by_eliminating(sequences, target_index, vcl, initp);

      single_dfs_sequences_traverse_timer.stop();
      vector_single_dfs_sequences_traverse_time.push_back(single_dfs_sequences_traverse_timer.compute_time_elapsed());
      vector_single_weave_count.push_back(single_weave_count);
      vector_single_collect_time.push_back(single_collect_time);
      vector_single_post_prune_bang_count.push_back(single_post_prune_bang_count);
    }
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

  }//    else if (num_context == 7)
  else if (num_context == 8){
    //  output_file: **newdfs_seq_propagation**
    //  nd
    int nd = fd->get_dimension();
    //  trivial
    trivial = new C_Polyhedron(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_to_trivial(trivial);
    }
    //  initp
    C_Polyhedron initp(nd, UNIVERSE);
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->make_context();
      (*vi)->compute_dual_constraints(initp);
    }
    //  vcl
    vector<Clump> vcl;
    for (vector<TransitionRelation *>::iterator vj = trlist->begin(); vj < trlist->end(); vj++){
      (*vj)->compute_consecution_constraints(vcl, initp);
      if (total_timer.compute_time_elapsed() >= weave_time){
          tcout<< "Time is up!"<<endl;
          break;
      }
    }
    for (vector<Location *>::iterator vi = loclist->begin(); vi < loclist->end(); vi++){
      (*vi)->add_clump(vcl);
      if (total_timer.compute_time_elapsed() >= weave_time){
          tcout<< "Time is up!"<<endl;
          break;
      }
      //    this also should trigger the simplification of the context
    }

    /*
     * The main body of CNF-to-DNF Conversion
     *   dfs_sequences_generation_traverse
     *   dfs_sequences_traverse_for_one_location_by_eliminating
     */
    // Generate Sequences
    dfs_traverse_timer.restart();
    vector<vector<vector<vector<int>>>> target_sequences;
    for (int target_index=0; target_index<loclist->size(); target_index++){
      if (debug_3){
        tcout<<endl<<"- target_index (Generate Sequences): "<<target_index<<", Location::"<<(*loclist)[target_index]->get_name();
      }
      single_pre_prune_bang_count = 0;
      counter.set_location_index_and_init_depth(target_index, vcl.size());
      single_dfs_sequences_generation_timer.restart();

      // only compute invariants at initial location
      bool has_initial_poly_set = (*loclist)[target_index]->initial_poly_set();
      if (!has_initial_poly_set) {
        tcout<<endl<<"- ( !has_initial_poly_set ) in Location::"<<(*loclist)[target_index]->get_name();
        vector<vector<vector<int>>> empty_sequences;
        target_sequences.push_back(empty_sequences);
      }
      else {
        dfs_sequences_generation_traverse(target_sequences, target_index, vcl, initp);
      }

      single_dfs_sequences_generation_timer.stop();
      vector_single_dfs_sequences_generation_time.push_back(single_dfs_sequences_generation_timer.compute_time_elapsed());
      vector_single_pre_prune_bang_count.push_back(single_pre_prune_bang_count);
    }
    // Read Sequences
    for (int target_index=0; target_index<loclist->size(); target_index++){
      if (debug_3){
        tcout<<endl<<"- target_index (Read Sequences): "<<target_index<<", Location::"<<(*loclist)[target_index]->get_name();
      }
      single_weave_count = 0;
      single_collect_time = 0;
      single_post_prune_bang_count = 0;
      single_dfs_sequences_traverse_timer.restart();

      // only compute invariants at initial location
      bool has_initial_poly_set = (*loclist)[target_index]->initial_poly_set();
      if (!has_initial_poly_set) {
        tcout<<endl<<"- ( !has_initial_poly_set ) in Location::"<<(*loclist)[target_index]->get_name();
      }
      else {
        vector<vector<vector<int>>> sequences = target_sequences[target_index];
        dfs_sequences_traverse_for_one_location_by_eliminating(sequences, target_index, vcl, initp);
      }

      single_dfs_sequences_traverse_timer.stop();
      vector_single_dfs_sequences_traverse_time.push_back(single_dfs_sequences_traverse_timer.compute_time_elapsed());
      vector_single_weave_count.push_back(single_weave_count);
      vector_single_collect_time.push_back(single_collect_time);
      vector_single_post_prune_bang_count.push_back(single_post_prune_bang_count);
    }
    dfs_traverse_timer.stop();
    dfs_traverse_time = dfs_traverse_timer.compute_time_elapsed();

    /*
     * The main body of Propagation
     */

    // Test1: propagate invariants from initial location to all others
    //propagate_invariants_from_initial_location_to_all_others();

    // compute other invariants by propagation with Farkas
    // ::First, compute other location except Initial & Exit-Location
    // ::Second, compute Exit-Location
    compute_invariants_by_propagation_with_farkas(vcl);

  }//    else if (num_context == 8)
  total_timer.stop();
  Print_Location();
  if (djinv){
    print_disjunctive_inv_before_program();
  }
  if(arrinv){
    print_array_inv_before_program();
  }
  Print_Status_after_Solver();
  #ifndef TRACE
    // only print exit-location
    for (vector<Location *>::iterator vi=loclist->begin();vi< loclist->end();vi++){
      if ((*vi)->get_name() == EXIT_LOCATION){
        if((*vi)->get_vp_inv_flag()){
          cout<<"Location: "<<(*vi)->get_name();
          cout<<endl;
          nt_print_pure_clump((*vi)->get_vp_inv(), (*vi)->get_var_info());
        }
        else{
          cout<<"Location: "<<(*vi)->get_name();
          nt_print_pure_polyhedron((*vi)->get_invariant(), (*vi)->get_var_info());
        }
      }
    }
  #endif
  if (inv_check){
    check_invariant_ok();
  }
  
  /*
  tcout<<endl<<"Doing Initial Propagation"<<endl;
  Timer prop_timer;
  do_some_propagation();
  prop_timer.stop();
  tcout<<"Propagation done -- Time Taken (0.01S):" <<prop_timer.compute_time_elapsed()<<endl;
  
  if (dual){
    tcout<<endl<<"---- Running Cousot-Halbwachs dual propagation/narrowing----"<<endl;
    Timer dual_time;
    
    InvariantMap dualmap(f, *loclist);
    global_system->compute_dual_invariant(dualmap);
    
    dual_time.stop();
    tcout<<endl<<"Time taken for Dual (0.01 S)"<<dual_time.compute_time_elapsed()<<endl;
    tcout<<"--------------------------------------------------------"<<endl;
  }

  InvariantMap h79map(f, *loclist);
  if (ch79){
    tcout<<endl<<"---- Running Cousot-Halbwachs with H79 widening ----"<<endl;
    Timer h79_time;
    
    global_system->compute_invariant_h79(h79map);
    
    h79_time.stop();
    tcout<<"Time taken for Cousot-Halbwachs Widening (0.01 S)"<<h79_time.compute_time_elapsed()<<endl;
    tcout<<"The bake-off results vs. CH79"<<endl;
    print_bake_off(h79map);
    if (inv_check){
      tcout<<"Checking...."<<endl;
      h79map.check_consecution(trlist);
      tcout<<"Done!"<<endl;
    }
    tcout<<"--------------------------------------------------------"<<endl;
  }
   
  InvariantMap bhrz03map(f, *loclist);
  if (bhrz03){
    tcout<<endl<<"---- Running Cousot-Halbwachs with BHRZ03 widening ----"<<endl;
    Timer bhrz03_time;
    
    global_system->compute_invariant(bhrz03map);
    
    bhrz03_time.stop();
    tcout<<"Time taken for BHRZ03 (0.01 S)"<<bhrz03_time.compute_time_elapsed()<<endl;
    tcout<<"The bake-off results vs. BHRZ03"<<endl;
    print_bake_off(bhrz03map);
    if (inv_check){
      tcout<<"Checking...."<<endl;
      bhrz03map.check_consecution(trlist);
      tcout<<"Done!"<<endl;
    }
    tcout<<"--------------------------------------------------------"<<endl;
  }
  */
   
  return 0;
}


void collect_generators(vector<Context *> * children , Generator_System & g){
   vector<Context *>::iterator vk;
    for(vk=children->begin();vk < children->end(); vk++){
       (*vk)->collect_generators(g);
    }
}


void add_preloc_invariants_to_transitions(){
   vector<TransitionRelation *>::iterator vtr;
   for (vtr=trlist->begin(); vtr < trlist->end(); ++vtr){
      (*vtr)->add_preloc_invariant();
   }
   return;
}

void print_status(){

   tcout<<"---------------------------------------------------"<<endl;
   tcout<<" Local invariants to be generated : "<<zero<<endl;
   tcout<<" Increasing invariants to be generated : "<<one<<endl;
   tcout<<" Strategy ID #"<<num_context<<endl;
   tcout<<" # of initial propagation steps:"<<prop_steps<<endl;
   tcout<<" Weave Time allowed:"<<weave_time<<endl;
   tcout<<" Cousot-Halbwachs to be performed:"<<ch79<<endl;
   tcout<<" BHRZ03 to be performed:"<<bhrz03<<endl;
   tcout<<"----------------------------------------------------"<<endl;
}

void print_bake_off( InvariantMap const & invmap){
   bool disjoint;
   int r2;

   vector<Location *>::iterator vl;
   
   for (vl=loclist->begin(); vl <loclist->end(); vl ++){
      r2=0;
      disjoint=true;
      
      string const & what=(*vl)->get_name();
      C_Polyhedron & loc_inv= (*vl)->invariant_reference();
      C_Polyhedron const & other_inv = invmap(what);
      
      tcout<<"Location :"<<what<<" ";
      
      // Am I stronger   
      if (other_inv.contains(loc_inv)){
         r2++; // I am one up
         disjoint=false;
      }
      // Is the other_inv stronger?
      
      if (loc_inv.contains(other_inv)){
            r2--; // h79 is one up
            disjoint=false;
      }

      if (disjoint) {
         tcout<<"Disjoint"<<endl;
      } else if (r2 > 0){
         tcout<<" + "<<endl;
      } else if (r2 <0 ){
         tcout<<" - "<<endl;
      } else if (r2==0){
         tcout<<" == "<<endl;
      } else {
         // this is unreachable (or is it? :-)
         tcout<<" <<Unknown Relation>>"<<endl;
      }
        
   }
}

void check_invariant_ok(){
  tcout<<endl<<"> > > In check_invariant_ok()";
   cerr<<"Checking for invariant..."<<endl;
   vector<TransitionRelation *>::iterator vi;
   for (vi=trlist->begin(); vi != trlist->end(); ++vi){
      (*vi)->check_map();
   }
   cerr<<"Done!"<<endl;
  tcout<<endl<<"< < < Out of check_invariant_ok()";
}
