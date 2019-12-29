#include <iostream>
// This is the first gcc header to be included
#include "gcc-plugin.h"
#include "plugin-version.h"

#include "cfgloop.h"
#include "et-forest.h"

#include "tree-pass.h"
#include "context.h"
#include "function.h"
#include "tree.h"
#include "tree-ssa-alias.h"
#include "internal-fn.h"
#include "is-a.h"
#include "predict.h"
#include "basic-block.h"
#include "gimple-expr.h"
#include "gimple.h"
#include "gimple-pretty-print.h"
#include "gimple-iterator.h"
#include "gimple-walk.h"

#define INDENT(SPACE)           \
  do                            \
  {                             \
    int i;                      \
    for (i = 0; i < SPACE; i++) \
      pp_space(buffer);         \
  } while (0)

// We must assert that this plugin is GPL compatible
int plugin_is_GPL_compatible;

static struct plugin_info my_gcc_plugin_info = {"1.0", "This is a very simple plugin"};

//###################################################################################################

static void
dump_gimple_seq_custom(pretty_printer *buffer, gimple_seq seq, int spc,
                       dump_flags_t flags)
{
  gimple_stmt_iterator i;
  for (i = gsi_start(seq); !gsi_end_p(i); gsi_next(&i))
  {
    gimple *gs = gsi_stmt(i);
    INDENT(spc);
    pp_gimple_stmt_1(buffer, gs, spc, flags);
    if (!gsi_one_before_end_p(i))
      pp_newline(buffer);
  }
}

void print_gimple_seq_custom(FILE *file, gimple_seq seq, int spc, dump_flags_t flags)
{
  pretty_printer buffer;
  pp_needs_newline(&buffer) = true;
  buffer.buffer->stream = file;
  dump_gimple_seq_custom(&buffer, seq, spc, flags);
  pp_newline_and_flush(&buffer);
}

//###################################################################################################
const int MAX_FT = 56;
int ft[MAX_FT]; //Armazena todas as features de acordo com a tabela
int number_of_instructions_by_block = 0;
int number_of_phiNodes_by_block = 0;

void show()
{

  for (int i = 1; i < MAX_FT; i++)
  {
    std::cerr << "FT " << i << " = " << ft[i] << "\n";
  }
}

//Mostra a localiaçao da istrução encontrada
void showLocale(gimple *g)
{

  location_t l = gimple_location(g);
  enum gimple_code code = gimple_code(g);
  fprintf(stderr, "Declaracao do tipo: %s no arquivo %s:%d\n",
          gimple_code_name[code],
          LOCATION_FILE(l),
          LOCATION_LINE(l));
}

void showTreeCode(tree t)
{
  fprintf(stderr, "TREE_CODE: %s\n", get_tree_code_name(TREE_CODE(t)));
  fprintf(stderr, "TREE_CODE_CLASS: %s\n", TREE_CODE_CLASS_STRING(TREE_CODE_CLASS(TREE_CODE(t))));
  // Deliberately similar to the code in tree-cfg.c

  switch (TREE_CODE(t))
  {
  case FIX_TRUNC_EXPR:
  case FLOAT_EXPR:
  case NEGATE_EXPR:
  case ABS_EXPR:
  case PAREN_EXPR:
  case CONVERT_EXPR:
  case ADDR_SPACE_CONVERT_EXPR:
  case FIXED_CONVERT_EXPR:
  case NOP_EXPR:
  case NON_LVALUE_EXPR:
  case CONJ_EXPR:
  case VEC_UNPACK_HI_EXPR:
  case VEC_UNPACK_LO_EXPR:
  case VEC_UNPACK_FLOAT_HI_EXPR:
  case VEC_UNPACK_FLOAT_LO_EXPR:
    ft[35]++;
    break;
  case VAR_DECL:
    fprintf(stderr, "VAR_DECL\n");

    break;
  case ARRAY_TYPE:
    fprintf(stderr, "ARRAY_TYPE\n");

    break;
  case COMPONENT_REF:
    fprintf(stderr, "COMPONENT_REF\n");
    break;
  case INTEGER_TYPE:
    fprintf(stderr, "INTEGER_TYPE\n");
    break;
  case INTEGER_CST:
    fprintf(stderr, "INTEGER_CST\n");
    break;
  case REAL_CST:
    fprintf(stderr, "REAL_CST\n");
    break;
  case RESULT_DECL:
    fprintf(stderr, "RESULT_DECL\n");
    break;
  case COND_EXPR:
    fprintf(stderr, "COND_EXPR\n");
    break;

  default:
  {
    // TODO: are there more cases?
    break;
  }
  }
}
static inline bool
two_succ_p (const_basic_block bb)
{
	return EDGE_COUNT (bb->succs) == 2;
}

static inline bool
more_two_succ_p (const_basic_block bb)
{
	return EDGE_COUNT (bb->succs) > 2;
}
static inline bool
two_pred_p (const_basic_block bb)
{
	return EDGE_COUNT (bb->succs) == 2;
}

static inline bool
more_two_pred_p (const_basic_block bb)
{
	return EDGE_COUNT (bb->succs) > 2;
}

//Chega a quantidade de predecessores e sucessores
void checkPredAndSuccess(basic_block bb)
{

  if (single_succ_p(bb))
    ft[2]++;
  if (two_succ_p(bb))
    ft[3]++;
  if (more_two_succ_p(bb))
    ft[4]++;
  if (single_pred_p(bb))
    ft[5]++;
  if (two_pred_p(bb))
    ft[6]++;
  if (more_two_pred_p(bb))
    ft[7]++;
  if (single_pred_p(bb) && single_succ_p(bb))
    ft[8]++;
  if (single_pred_p(bb) && two_succ_p(bb))
    ft[9]++;
  if (two_pred_p(bb) && single_succ_p(bb))
    ft[10]++;
  if (two_pred_p(bb) && two_succ_p(bb))
    ft[11]++;
  if (more_two_pred_p(bb) && more_two_succ_p(bb))
    ft[12]++;
  /*vec<edge, va_gc> *preds = bb->preds; //armazena os predecessores do bloco
  vec<edge, va_gc> *succs = bb->succs; //armazena os sucessores do bloco
  //Capturando as 12 primeiras features #####################################
  if (single_succ_p(bb))
    ft[2]++;
  if (succs->length() == 2)
    ft[3]++;
  if (succs->length() > 2)
    ft[4]++;
  if (single_pred_p(bb))
    ft[5]++;
  if (preds->length() == 2)
    ft[6]++;
  if (preds->length() > 2)
    ft[7]++;
  if (succs->length() == 1 && preds->length() == 1)
    ft[8]++;
  if (succs->length() == 2 && preds->length() == 1)
    ft[9]++;
  if (succs->length() == 1 && preds->length() == 2)
    ft[10]++;
  if (succs->length() == 2 && preds->length() == 2)
    ft[11]++;
  if (succs->length() > 2 && preds->length() > 2)
    ft[12]++;*/
  //Fim das 12 primeiras features #####################################
}

void countInstructionsByBlock()
{
  if (number_of_instructions_by_block < 15)
    ft[13]++;
  if (number_of_instructions_by_block >= 15 && number_of_instructions_by_block <= 500)
    ft[14]++;
  if (number_of_instructions_by_block > 500)
    ft[15]++;
  number_of_instructions_by_block = 0; //a cada bloco novo, zera o contador
}

void countPhiNodesByBlock(basic_block bb)
{

  gphi_iterator pi;
  for (pi = gsi_start_phis(bb); !gsi_end_p(pi); gsi_next(&pi))
  {
    gphi *phi = pi.phi();
    fprintf(stderr, "PHI\n");
    print_gimple_stmt(dump_file, phi, 0, TDF_SLIM);
  }

  if (phi_nodes(bb) == NULL)
    ft[29]++;
  if (number_of_phiNodes_by_block >= 0 && number_of_phiNodes_by_block <= 3)
    ft[30]++;
  else if (number_of_phiNodes_by_block > 3)
    ft[31]++;
  number_of_phiNodes_by_block = 0;
}

namespace
{
const pass_data my_first_pass_data =
    {
        GIMPLE_PASS,
        "my_first_pass", /* name */
        OPTGROUP_NONE,   /* optinfo_flags */
        TV_NONE,         /* tv_id */
        PROP_gimple_any, /* properties_required */
        0,               /* properties_provided */
        0,               /* properties_destroyed */
        0,               /* todo_flags_start */
        0                /* todo_flags_finish */
};

struct my_first_pass : gimple_opt_pass
{
  my_first_pass(gcc::context *ctx)
      : gimple_opt_pass(my_first_pass_data, ctx)
  {
  }

  virtual unsigned int execute(function *fun) override
  {

    std::cerr << "MÉTODO: '" << function_name(fun) << "\n";
    ft[1]++; //incrementa a ft1

    basic_block bb;
    struct walk_stmt_info walk_stmt_info;
    //memset(&walk_stmt_info, 0, sizeof(walk_stmt_info));
    //walk_gimple_seq(fun->gimple_body, callback_stmt, callback_op, &walk_stmt_info);

    fprintf(stderr, "Nº de basico blocks por método: %d\n", n_basic_blocks_for_fn(fun));
    fprintf(stderr, "Nº de edges por método: %d\n", n_edges_for_fn(fun));

    //ITERAÇÃO PELA QUANTIDADE DE BLOCOS BÁSICOS
    FOR_EACH_BB_FN(bb, fun)
    {

      gimple_stmt_iterator gsi;
      checkPredAndSuccess(bb);

      //LOOP que passa por cada instrução dentro de um bloco
      for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi))
      {
        gimple *stmt = gsi_stmt(gsi);
        ft[25]++;
        //showLocale(stmt);
        //walk_gimple_op(stmt, callback_op, &walk_stmt_info);

        showLocale(stmt); //mosra informações sobre a linha

        switch (gimple_code(stmt))
        {
        case GIMPLE_OMP_FOR: //
        {
          break;
        }
        case GIMPLE_ASM: //GIMPLE_ASM
        {
          break;
        }
        case GIMPLE_PHI:
        {
          number_of_phiNodes_by_block++;
          break;
        }
        case GIMPLE_CALL: //Chamada de função
        {
          ft[19]++;
          break;
        }
        case GIMPLE_RETURN: //Retorno
        {
          break;
        }
        case GIMPLE_COND: //CondicaoGIMPLE_GOTO
        {
          ft[20]++;
          break;
        }
        case GIMPLE_GOTO: //unconnditional branches
        {
          ft[22]++;
          break;
        }
        case GIMPLE_LABEL: //LABEL
        {
          break;
        }
        case GIMPLE_SWITCH:
        {
          ft[34]++;
          break;
        }
        case GIMPLE_ASSIGN: //Atribuição GIMPLE_LABEL
        {

          fprintf(stderr, "ASSIGN\n");
          fprintf(stderr, "Num operandos: %d\n", gimple_num_ops(stmt));

          tree rhs1 = gimple_assign_rhs1(stmt);
          showTreeCode(rhs1);

          tree rhs2 = gimple_assign_rhs2(stmt);
          if (rhs2 != NULL)
            showTreeCode(rhs2);

          tree rhs3 = gimple_assign_rhs3(stmt);
          if (rhs3 != NULL)
            showTreeCode(rhs3);
          //walk_gimple_op(stmt, callback_op, &walk_stmt_info);

          ft[21]++;
          break;
        }
        default:
          // do nothing
          break;
        }
      }

      edge e;
      edge_iterator ei;
      //control flow-graph
      FOR_EACH_EDGE(e, ei, bb->succs)
      {
        basic_block dest = e->dest;
        ft[16]++; //ft[16+=EDGE_COUNT (bb->succs);
        if (EDGE_CRITICAL_P(e) != 0)
        {
          ft[17]++;
        }
        if (e->flags & EDGE_ABNORMAL)
        {
          ft[18]++;
        }
      }

      countInstructionsByBlock();
      countPhiNodesByBlock(bb);
    }

    show();
    // Nothing special todo
    return 0;
  }

  virtual my_first_pass *clone() override
  {
    // We do not clone ourselves
    return this;
  }

private:
  static tree callback_stmt(gimple_stmt_iterator *gsi, bool *handled_all_ops, struct walk_stmt_info *wi)
  {
    gimple *g = gsi_stmt(*gsi);

    location_t l = gimple_location(g);
    enum gimple_code code = gimple_code(g);

    fprintf(stderr, "DDD do tipo: %s no arquivo %s:%d\n",
            gimple_code_name[code],
            LOCATION_FILE(l),
            LOCATION_LINE(l));

    return NULL;
  }

  static tree callback_op(tree *t, int *, void *data)
  {
    enum tree_code code = TREE_CODE(*t);

    if (code == RESULT_DECL ||
        code == PARM_DECL ||
        code == LABEL_DECL ||
        code == VAR_DECL ||
        code == FUNCTION_DECL)
    {

      // Get DECL_NAME for this declaration
      tree id = DECL_NAME(*t);
      tree idType = TYPE_IDENTIFIER(*t);

      // print name of declaration..
      const char *name = id ? IDENTIFIER_POINTER(id) : "<unnamed>";
      printf("Nome declaração: %s : %s \n", get_tree_code_name(code), name);
    }

    if (BINARY_CLASS_P(*t) != 0)
    {
      fprintf(stderr, "BINARY OPERATION\n");
    }

    if (UNARY_CLASS_P(*t) != 0)
    {
      fprintf(stderr, "UNARY OPERATION\n");
    }

    switch (code)
    {
    case PARM_DECL:
      fprintf(stderr, "VAR_DECL\n");
      break;
    case SSA_NAME:
      fprintf(stderr, "VAR_DECL\n");

      break;
    case VAR_DECL:
      fprintf(stderr, "VAR_DECL\n");
      break;
    default:
      break;
    }

    fprintf(stderr, "   Operando: %s\n", get_tree_code_name(code));
    return NULL;
  }
};
} // namespace

int plugin_init(struct plugin_name_args *plugin_info,
                struct plugin_gcc_version *version)
{
  // We check the current gcc loading this plugin against the gcc we used to
  // created this plugin
  if (!plugin_default_version_check(version, &gcc_version))
  {
    std::cerr << "This GCC plugin is for version " << GCCPLUGIN_VERSION_MAJOR << "." << GCCPLUGIN_VERSION_MINOR << "\n";
    return 1;
  }

  register_callback(plugin_info->base_name,
                    /* event */ PLUGIN_INFO,
                    /* callback */ NULL, /* user_data */ &my_gcc_plugin_info);

  // Register the phase right after cfg
  struct register_pass_info pass_info;

  pass_info.pass = new my_first_pass(g);
  pass_info.reference_pass_name = "cfg";
  pass_info.ref_pass_instance_number = 1;
  pass_info.pos_op = PASS_POS_INSERT_AFTER;

  register_callback(plugin_info->base_name, PLUGIN_PASS_MANAGER_SETUP, NULL, &pass_info);

  return 0;
}
