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
#include "cfgexpand.h"

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
//INICIALIZANDO VARIAVEIS
const int MAX_FT = 57;
float ft[MAX_FT];        //Armazena todas as features de acordo com a tabela
float ft_global[MAX_FT]; //Armazena o somatório de todas a feature do arquivo
float number_of_instructions_by_block = 0;
float number_of_phiNodes_by_block = 0;
float number_of_phiNodes_beginning_block = 0;
bool arguments_phi_nodes_is_greather_5 = false;
bool arguments_phi_nodes_is_interval_1_to_5 = false;
float sum_arguments_for_phi_nodes = 0;
float sum_basic_blocks = 0;

//Mostra as caracteristicas finais
void show()
{
  for (int i = 1; i < MAX_FT; i++)
  {
    std::cerr << "FT" << i << " = " << ft[i] << "| ";
    ft_global[i] += ft[i];
  }
  std::cerr << "\n";
}

void showGlobal()
{
  std::cerr << "Features globais\n";
  for (int i = 1; i < MAX_FT; i++)
  {
    std::cerr << "FT" << i << " = " << ft_global[i] << " | ";
  }
  std::cerr << "\n";
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
  fprintf(stderr, "TREE_CODE_CLASS: %s\n", TREE_CODE_CLASS_STRING(TREE_CODE_CLASS(TREE_CODE(t))));
  fprintf(stderr, "TREE_TYPE: %s\n", get_tree_code_name(TREE_CODE(TREE_TYPE(t))));
  fprintf(stderr, "TREE_CODE: %s\n", get_tree_code_name(TREE_CODE(t)));
}

void countOcurrencesOfConstantZero(tree t, tree lhs, tree rhs1, tree rhs2, tree rhs3)
{
  if (integer_zerop(lhs))
    ft[47]++;
  if (integer_zerop(t))
    ft[47]++;
  if (integer_zerop(rhs1))
    ft[47]++;
  if (rhs2 && integer_zerop(rhs2))
    ft[47]++;
  if (rhs3 && integer_zerop(rhs3))
    ft[47]++;
}

void countOcurrencesOfConstantOne(tree t, tree lhs, tree rhs1, tree rhs2, tree rhs3)
{
  if (integer_onep(lhs))
    ft[49]++;
  if (integer_onep(t))
    ft[49]++;
  if (integer_onep(rhs1))
    ft[49]++;
  if (rhs2 && integer_onep(rhs2))
    ft[49]++;
  if (rhs3 && integer_onep(rhs3))
    ft[49]++;
}

void checkTreeCode(gimple *stmt)
{
  tree t = gimple_assign_rhs_to_tree(stmt);
  tree lhs = gimple_assign_lhs(stmt);
  tree rhs1 = gimple_assign_rhs1(stmt);
  tree rhs2 = gimple_assign_rhs2(stmt);
  tree rhs3 = gimple_assign_rhs3(stmt);

  countOcurrencesOfConstantZero(t, lhs, rhs1, rhs2, rhs3);
  countOcurrencesOfConstantOne(t, lhs, rhs1, rhs2, rhs3);

  if (TREE_CODE(t) == INTEGER_CST)
  {

    if (TYPE_PRECISION(TREE_TYPE(t)) == 32)
    {
      ft[48]++;
    }
    if (TYPE_PRECISION(TREE_TYPE(t)) == 64)
    {
      ft[50]++;
    }
  }

  if (TREE_CODE_CLASS(TREE_CODE(t)) == tcc_binary)
  {
    if (TREE_CODE(TREE_TYPE(t)) == INTEGER_TYPE)
      ft[23]++;
    if (TREE_CODE(TREE_TYPE(t)) == REAL_TYPE)
      ft[24]++;

    if (TREE_CODE(rhs1) == INTEGER_CST || (rhs2 && TREE_CODE(rhs2) == INTEGER_CST) || (rhs3 && TREE_CODE(rhs3) == INTEGER_CST))
    {
      ft[42]++;
    }
  }
  else if (TREE_CODE_CLASS(TREE_CODE(t)) == tcc_unary)
  {
    if (TREE_CODE(t) == INDIRECT_REF)
      ft[37]++;
  }
}

static inline bool
two_succ_p(const_basic_block bb)
{
  return EDGE_COUNT(bb->succs) == 2;
}

static inline bool
more_two_succ_p(const_basic_block bb)
{
  return EDGE_COUNT(bb->succs) > 2;
}
static inline bool
two_pred_p(const_basic_block bb)
{
  return EDGE_COUNT(bb->preds) == 2;
}

static inline bool
more_two_pred_p(const_basic_block bb)
{
  return EDGE_COUNT(bb->preds) > 2;
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
}

void countEdgesByBlock(basic_block bb)
{
  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE(e, ei, bb->succs)
  {
    ft[16]++;
    if (EDGE_CRITICAL_P(e) != 0)
    {
      ft[17]++;
    }
    if (e->flags & EDGE_ABNORMAL)
    {
      ft[18]++;
    }
  }
}

void countLocalVariable(function *fun)
{
  int i;
  tree var;
  FOR_EACH_LOCAL_DECL(fun, i, var)
  {
    ft[51]++;
    tree type = TREE_TYPE(var);
    enum tree_code code = TREE_CODE(type);
    if (TREE_STATIC(var) != 0 || DECL_EXTERNAL(var) != 0)
    {
      ft[52]++;
      if (code == POINTER_TYPE)
        ft[56]++;
      if (REFERENCE_CLASS_P(var))
        ft[54]++;
    }

    if (code == POINTER_TYPE)
      ft[55]++;

    if (REFERENCE_CLASS_P(var) != 0)
      ft[53]++;
  }
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
  if (phi_nodes(bb) == NULL)
    ft[29]++;
  else
  {
    if (number_of_phiNodes_by_block > 0 && number_of_phiNodes_by_block <= 3)
      ft[30]++;
    else if (number_of_phiNodes_by_block > 3)
      ft[31]++;
  }

  if (arguments_phi_nodes_is_greather_5)
    ft[32]++;
  if (arguments_phi_nodes_is_interval_1_to_5)
    ft[33]++;

  number_of_phiNodes_by_block = 0;
  arguments_phi_nodes_is_greather_5 = false;
  arguments_phi_nodes_is_interval_1_to_5 = false;
}

void calculateAverageArgumentsForPhiNode()
{
  float sum = ft[30] + ft[31];
  ft[28] = sum_arguments_for_phi_nodes / sum != 0 ? sum : 1;
  sum_arguments_for_phi_nodes = 0;
}

void calculateAverageNumberInstructionsByBlock()
{
  ft[26] = ft[25] / ft[1];
}

void calculateAveragePhiNodesBeginningBasicBlock()
{
  
  ft[27] = number_of_phiNodes_beginning_block / sum_basic_blocks != 0 ? sum_basic_blocks : 1;
  number_of_phiNodes_beginning_block = 0;
  sum_basic_blocks = 0;
}

void countFt38AndFt39(gimple *g)
{
  tree lhsop = gimple_assign_lhs(g);
  tree rhsop1 = gimple_assign_rhs1(g);
  tree rhsop2 = gimple_assign_rhs2(g);
  tree rhsop3 = gimple_assign_rhs3(g);
  if ((lhsop && POINTER_TYPE_P(TREE_TYPE(lhsop))) || (rhsop1 && POINTER_TYPE_P(TREE_TYPE(rhsop1))) || (rhsop2 && POINTER_TYPE_P(TREE_TYPE(rhsop2))) || (rhsop3 && POINTER_TYPE_P(TREE_TYPE(rhsop3))))
    ft[38]++;
  if ((lhsop && FUNCTION_POINTER_TYPE_P(TREE_TYPE(lhsop))) || (rhsop1 && FUNCTION_POINTER_TYPE_P(TREE_TYPE(rhsop1))) || (rhsop2 && FUNCTION_POINTER_TYPE_P(TREE_TYPE(rhsop2))) || (rhsop3 && FUNCTION_POINTER_TYPE_P(TREE_TYPE(rhsop3))))
    ft[39]++;
}

void reset()
{
  for (int i = 0; i < MAX_FT; i++)
    ft[i] = 0;
  number_of_instructions_by_block = 0;
  number_of_phiNodes_by_block = 0;
  number_of_phiNodes_beginning_block = 0;
  arguments_phi_nodes_is_greather_5 = false;
  arguments_phi_nodes_is_interval_1_to_5 = false;
  sum_arguments_for_phi_nodes = 0;
  sum_basic_blocks = 0;
}

void checkGimplePhi(basic_block bb, gimple *stmt)
{
  if (bb->index == 0)
  {
    sum_basic_blocks++;
    number_of_phiNodes_beginning_block++;
  }

  number_of_phiNodes_by_block++;
  int num_args = gimple_phi_num_args(stmt);
  sum_arguments_for_phi_nodes += num_args;
  if (num_args > 5)
    arguments_phi_nodes_is_greather_5 = true;
  if (num_args >= 1 && num_args <= 5)
    arguments_phi_nodes_is_interval_1_to_5 = true;
}

void checkGimpleCall(gimple *stmt)
{
  ft[19]++;
  const gcall *call_stmt = as_a<const gcall *>(stmt);
  gcall *call_stmt2 = as_a<gcall *>(stmt);

  if (gimple_call_by_descriptor_p(call_stmt2))
    ft[40]++;
  if (TREE_CODE(gimple_call_return_type(call_stmt)) == POINTER_TYPE)
    ft[46]++;
  if (TREE_CODE(gimple_call_return_type(call_stmt)) == INTEGER_TYPE)
    ft[45]++;
  int num_args = gimple_call_num_args(stmt);
  if (num_args > 4)
    ft[44]++;
  if (num_args > 0)
  {
    for (int i = 0; i < num_args; i++)
    {
      tree arg = gimple_call_arg(stmt, i);
      if (TREE_CODE(TREE_TYPE(arg)) == POINTER_TYPE)
        ft[43]++;
    }
  }
}

void checkGimpleAssign(gimple *stmt)
{
  countFt38AndFt39(stmt);
  checkTreeCode(stmt);
  tree rhs1 = gimple_assign_rhs1(stmt);
  if (TREE_CODE(rhs1) == INTEGER_CST)
    ft[41]++;
  if (get_gimple_rhs_class(gimple_assign_rhs_code(stmt)) == GIMPLE_UNARY_RHS)
    ft[35]++;
  ft[21]++;
}

namespace
{
const pass_data plugin_alan_pass_data =
    {
        GIMPLE_PASS,
        "plugin_alan_pass", /* name */
        OPTGROUP_NONE,      /* optinfo_flags */
        TV_NONE,            /* tv_id */
        PROP_gimple_any,    /* properties_required */
        0,                  /* properties_provided */
        0,                  /* properties_destroyed */
        0,                  /* todo_flags_start */
        0                   /* todo_flags_finish */
};

struct plugin_alan_pass : gimple_opt_pass
{
  plugin_alan_pass(gcc::context *ctx)
      : gimple_opt_pass(plugin_alan_pass_data, ctx)
  {
  }

  virtual unsigned int execute(function *fun) override
  {

    std::cerr << "MÉTODO: '" << function_name(fun) << "\n";
    reset();

    basic_block bb;
    //fprintf(stderr, "Nº de basico blocks por método: %d\n", n_basic_blocks_for_fn(fun));
    //fprintf(stderr, "Nº de edges por método: %d\n", n_edges_for_fn(fun));

    ft[1] = n_basic_blocks_for_fn(fun) - 2;

    //ITERAÇÃO PELA QUANTIDADE DE BLOCOS BÁSICOS
    FOR_EACH_BB_FN(bb, fun)
    {

      gimple_stmt_iterator gsi;
      checkPredAndSuccess(bb);

      for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi))
      {
        gimple *stmt = gsi_stmt(gsi);
        ft[25]++;
        number_of_instructions_by_block++;
        //showLocale(stmt);
        switch (gimple_code(stmt))
        {
        case GIMPLE_PHI:
        {
          checkGimplePhi(bb, stmt);
          break;
        }
        case GIMPLE_CALL:
        {
          checkGimpleCall(stmt);
          break;
        }
        case GIMPLE_COND:
        {
          ft[20]++;
          break;
        }
        case GIMPLE_GOTO:
        {
          ft[22]++;
          break;
        }
        case GIMPLE_SWITCH:
        {
          ft[34]++;
          break;
        }
        case GIMPLE_ASSIGN:
        {
          checkGimpleAssign(stmt);
          break;
        }
        default:
          // do nothing
          break;
        }
      }
      countEdgesByBlock(bb);
      countInstructionsByBlock();
      countPhiNodesByBlock(bb);
    }
    calculateAverageNumberInstructionsByBlock();
    calculateAverageArgumentsForPhiNode();
    calculateAveragePhiNodesBeginningBasicBlock();
    countLocalVariable(fun);
    show();
    return 0;
  }
  virtual plugin_alan_pass *clone() override
  {
    return this;
  }
};
} // namespace

int plugin_init(struct plugin_name_args *plugin_info,
                struct plugin_gcc_version *version)
{
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

  pass_info.pass = new plugin_alan_pass(g);
  pass_info.reference_pass_name = "cfg";
  pass_info.ref_pass_instance_number = 1;
  pass_info.pos_op = PASS_POS_INSERT_AFTER;

  register_callback(plugin_info->base_name, PLUGIN_PASS_MANAGER_SETUP, NULL, &pass_info);

  return 0;
}
