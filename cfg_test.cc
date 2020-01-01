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
const int MAX_FT = 57;
float ft[MAX_FT]; //Armazena todas as features de acordo com a tabela
float number_of_instructions_by_block = 0;
float number_of_phiNodes_by_block = 0;
bool arguments_phi_nodes_is_greather_5 = false;
bool arguments_phi_nodes_is_interval_1_to_5 = false;
float sum_arguments_for_phi_nodes = 0;

void show()
{

  for (int i = 1; i < MAX_FT; i++)
  {
    std::cerr << "FT" << i << " = " << ft[i] << "| ";
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
  fprintf(stderr, "TREE_CODE: %s\n", get_tree_code_name(TREE_CODE(t)));
  fprintf(stderr, "TREE_TYPE: %s\n", get_tree_code_name(TREE_CODE(TREE_TYPE(t))));

  fprintf(stderr, "TREE_CODE_CLASS: %s\n", TREE_CODE_CLASS_STRING(TREE_CODE_CLASS(TREE_CODE(t))));
  // Deliberately similar to the code in tree-cfg.c

  switch (TREE_CODE(t))
  {
  case FIX_TRUNC_EXPR: //Operações unárias
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
    fprintf(stderr, "UNARY\n");
    //ft[35]++;
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
  case VAR_DECL:
    fprintf(stderr, "TREE_TYPE: %s\n", get_tree_code_name(TREE_CODE(TREE_TYPE(t))));

    fprintf(stderr, "VAR_DECL\n");
    break;

  default:
  {
    // TODO: are there more cases?
    break;
  }
  }
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
  fprintf(stderr, "C TREE_CODE_CLASS: %s\n", TREE_CODE_CLASS_STRING(TREE_CODE_CLASS(TREE_CODE(t))));
  fprintf(stderr, "C TREE_TYPE: %s\n", get_tree_code_name(TREE_CODE(TREE_TYPE(t))));
  fprintf(stderr, "C TREE_CODE: %s\n", get_tree_code_name(TREE_CODE(t)));
  if (TREE_CODE(t) == INTEGER_CST)
  {
    if (TYPE_MAIN_VARIANT(TREE_TYPE(t)) == long_integer_type_node || TYPE_MAIN_VARIANT(TREE_TYPE(lhs)) == long_integer_type_node)
      ft[50]++;
    if (TYPE_MAIN_VARIANT(TREE_TYPE(t)) == integer_type_node || TYPE_MAIN_VARIANT(TREE_TYPE(lhs)) == integer_type_node)
      ft[48]++;
  }

  countOcurrencesOfConstantZero(t, lhs, rhs1, rhs2, rhs3);
  countOcurrencesOfConstantOne(t, lhs, rhs1, rhs2, rhs3);

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

  gphi_iterator pi;
  for (pi = gsi_start_phis(bb); !gsi_end_p(pi); gsi_next(&pi))
  {
    gphi *phi = pi.phi();
  }

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
}

void calculateAverageArgumentsForPhiNode()
{
  ft[28] = sum_arguments_for_phi_nodes / (ft[30] + ft[31]);
  sum_arguments_for_phi_nodes = 0;
}

void calculateAverageNumberInstructionsByBlock()
{
  ft[26] = ft[25] / ft[1];
}

void checkPointer(gimple *g)
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

    basic_block bb;
    fprintf(stderr, "Nº de basico blocks por método: %d\n", n_basic_blocks_for_fn(fun));
    fprintf(stderr, "Nº de edges por método: %d\n", n_edges_for_fn(fun));

    ft[1] = n_basic_blocks_for_fn(fun);

    //ITERAÇÃO PELA QUANTIDADE DE BLOCOS BÁSICOS
    FOR_EACH_BB_FN(bb, fun)
    {

      gimple_stmt_iterator gsi;
      arguments_phi_nodes_is_greather_5 = false;
      arguments_phi_nodes_is_interval_1_to_5 = false;
      checkPredAndSuccess(bb);

      //LOOP que passa por cada instrução dentro de um bloco
      for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi))
      {
        gimple *stmt = gsi_stmt(gsi);
        ft[25]++;
        number_of_instructions_by_block++;
        showLocale(stmt); //mosra informações sobre a linha
        switch (gimple_code(stmt))
        {
        case GIMPLE_PHI:
        {
          number_of_phiNodes_by_block++;
          int num_args = gimple_phi_num_args(stmt);
          sum_arguments_for_phi_nodes += num_args;
          if (num_args > 5)
            arguments_phi_nodes_is_greather_5 = true;
          if (num_args >= 1 && num_args <= 5)
            arguments_phi_nodes_is_interval_1_to_5 = true;
          break;
        }
        case GIMPLE_CALL: //Chamada de função
        {
          ft[19]++;
          const gcall *call_stmt = as_a<const gcall *>(stmt);
          gcall *call_stmt2 = as_a<gcall *>(stmt);
          tree fndecl = gimple_call_fndecl(call_stmt);
          //fprintf(stderr, "FNDECL TREE_CODE_CLASS: %s\n", TREE_CODE_CLASS_STRING(TREE_CODE_CLASS(TREE_CODE(fndecl))));
          //fprintf(stderr, "FNDECL TREE_TYPE: %s\n", get_tree_code_name(TREE_CODE(TREE_TYPE(fndecl))));
          //fprintf(stderr, "FNDECL TREE_CODE: %s\n", get_tree_code_name(TREE_CODE(fndecl)));
          //fprintf(stderr, "FNDECL TREE_CODE: %s\n", CALL_EXPR_BY_DESCRIPTOR(fndecl));

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

          //fprintf(stderr, "ASSIGN\n");
          //fprintf(stderr, "Num operandos: %d\n", gimple_num_ops(stmt));
          //tree lhs = gimple_assign_lhs(stmt);
          //showTreeCode(lhs);
          //tree rhs = gimple_assign_rhs_to_tree (stmt);
          //showTreeCode(rhs);
          checkPointer(stmt);
          checkTreeCode(stmt);
          tree rhs1 = gimple_assign_rhs1(stmt);
          if (TREE_CODE(rhs1) == INTEGER_CST)
            ft[41]++;
          if (get_gimple_rhs_class(gimple_assign_rhs_code(stmt)) == GIMPLE_UNARY_RHS)
            ft[35]++;
          if (get_gimple_rhs_class(gimple_assign_rhs_code(stmt)) == GIMPLE_BINARY_RHS)
          {
            //checkTreeCode(stmt);
          }
          if (get_gimple_rhs_class(gimple_assign_rhs_code(stmt)) == GIMPLE_SINGLE_RHS)
          {
          }

          //walk_gimple_op(stmt, callback_op, &walk_stmt_info);

          ft[21]++;
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
    countLocalVariable(fun);

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
    fprintf(stderr, "CC TREE_CODE_CLASS: %s\n", TREE_CODE_CLASS_STRING(TREE_CODE_CLASS(TREE_CODE(*t))));
    fprintf(stderr, "CC TREE_TYPE: %s\n", get_tree_code_name(TREE_CODE(TREE_TYPE(*t))));
    fprintf(stderr, "CC TREE_CODE: %s\n", get_tree_code_name(TREE_CODE(*t)));

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
