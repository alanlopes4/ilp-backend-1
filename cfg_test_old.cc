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


#define INDENT(SPACE)							\
  do { int i; for (i = 0; i < SPACE; i++) pp_space (buffer); } while (0)

// We must assert that this plugin is GPL compatible
int plugin_is_GPL_compatible;

static struct plugin_info my_gcc_plugin_info = { "1.0", "This is a very simple plugin" };



//###################################################################################################



static void
dump_gimple_seq_custom (pretty_printer *buffer, gimple_seq seq, int spc,
		 dump_flags_t flags)
{
  gimple_stmt_iterator i;
  for (i = gsi_start (seq); !gsi_end_p (i); gsi_next (&i))
    {
      gimple *gs = gsi_stmt (i);
      INDENT (spc);
      pp_gimple_stmt_1 (buffer, gs, spc, flags);
      if (!gsi_one_before_end_p (i))
	pp_newline (buffer);
    }
}

void
print_gimple_seq_custom(FILE *file, gimple_seq seq, int spc, dump_flags_t flags)
{
  pretty_printer buffer;
  pp_needs_newline (&buffer) = true;
  buffer.buffer->stream = file;
  dump_gimple_seq_custom(&buffer, seq, spc, flags);
  pp_newline_and_flush (&buffer);
}





//###################################################################################################
const int MAX_FT = 56;
int ft[MAX_FT]; //Armazena todas as features de acordo com a tabela
int number_of_instructions_by_block = 0;


void show(){
    
     for( int i = 1; i < MAX_FT; i++){
         std::cerr << "FT " << i << " = " << ft[i] << "\n";
        }
}



namespace
{
    const pass_data my_first_pass_data =
    {
        GIMPLE_PASS,
        "my_first_pass",        /* name */
        OPTGROUP_NONE,          /* optinfo_flags */
        TV_NONE,                /* tv_id */
        PROP_gimple_any,        /* properties_required */
        0,                      /* properties_provided */
        0,                      /* properties_destroyed */
        0,                      /* todo_flags_start */
        0                       /* todo_flags_finish */
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
            ft[1]++;//incrementa a ft1


            basic_block bb;

            //ITERAÇÃO PELA QUANTIDADE DE BLOCOS BÁSICOS
            FOR_EACH_BB_FN(bb, fun)
            {
                vec<edge, va_gc> *preds = bb->preds;
                vec<edge, va_gc> *succs = bb->succs;

                if(succs->length() == 1) ft[2]++;
                if(succs->length() == 2) ft[3]++;
                if(succs->length() > 2) ft[4]++;
                if(preds->length() == 1) ft[5]++;
                if(preds->length() == 2) ft[6]++;
                if(preds->length() > 2) ft[7]++;
                if(succs->length() == 1 && preds->length() == 1) ft[8]++;
                if(succs->length() == 2 && preds->length() == 1) ft[9]++;
                if(succs->length() == 1 && preds->length() == 2) ft[10]++;
                if(succs->length() == 2 && preds->length() == 2) ft[11]++;
                if(succs->length() > 2 && preds->length() > 2) ft[12]++;
                

                
                fprintf(stderr, "Bloco básico %d\n", bb->index);
                gimple_bb_info *bb_info = &bb->il.gimple;



                print_gimple_seq_custom(stderr, bb_info->seq, 0, TDF_NONE);
                fprintf(stderr, "Predecessores: %d\n", preds->length());
                fprintf(stderr, "Sucessores: %d\n", succs->length());
                fprintf(stderr, "Num nodes: %d\n", bb->loop_father->num_nodes);
                fprintf(stderr, "Operacoes: %d\n", bb_info->seq->num_ops);


                struct walk_stmt_info walk_stmt_info;
                memset(&walk_stmt_info, 0, sizeof(walk_stmt_info));

                walk_gimple_seq(bb_info->seq, callback_stmt, callback_op, &walk_stmt_info);


                fprintf(stderr, "\n");


                 
                if(number_of_instructions_by_block < 15) ft[13]++;
                if(number_of_instructions_by_block >= 15 && number_of_instructions_by_block <= 500)ft[14]++;
                if(number_of_instructions_by_block > 500) ft[15]++;
                number_of_instructions_by_block = 0;
            }
           


            

            //show();
            // Nothing special todo
            return 0;
        }

        virtual my_first_pass* clone() override
        {
            // We do not clone ourselves
            return this;
        }

        private:

        //Método acionando por quantidade de instruções
        static tree callback_stmt(gimple_stmt_iterator * gsi, bool *handled_all_ops, struct walk_stmt_info *wi)
        {
            gimple* g = gsi_stmt(*gsi);

            location_t l = gimple_location(g);
            enum gimple_code code = gimple_code(g);
            
            number_of_instructions_by_block++;

            fprintf(stderr, "Declaracao do tipo: %s no arquivo %s:%d\n",
                    gimple_code_name[code],
                    LOCATION_FILE(l),
                    LOCATION_LINE(l));

            return NULL;
        }

        static tree callback_op(tree *t, int *, void *data)
        {
            enum tree_code code = TREE_CODE(*t);
            
            const char * code_name = get_tree_code_name(code);

            if(strcmp(code_name, "") == 0){}

            

            fprintf(stderr, "   Operando: %s\n", get_tree_code_name(code));
            return NULL;
        }
    };
}


int plugin_init (struct plugin_name_args *plugin_info,
		struct plugin_gcc_version *version)
{
	// We check the current gcc loading this plugin against the gcc we used to
	// created this plugin
	if (!plugin_default_version_check (version, &gcc_version))
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

    register_callback (plugin_info->base_name, PLUGIN_PASS_MANAGER_SETUP, NULL, &pass_info);

    return 0;
}
