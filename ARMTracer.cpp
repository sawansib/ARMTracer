#include <string.h>
#include <stdio.h>
#include <iostream>
#include <sstream>
#include <iomanip>
#include <stdlib.h>
#include <deque>
#include <fstream>
#include <memory>
#include "zstr.hpp"
#include <unordered_set>
#include <assert.h>

#include "dr_api.h"
#include "drmgr.h"
#include "drx.h"
#include "drreg.h"
#include "drutil.h"
#include "dr_tools.h"
#include "utils.h"

static void trace_memory_write(instr_t *instr);
static void trace_memory_read(instr_t *instr);
static void trace_branch(instr_t *instr);
static void trace_other(instr_t *instr);
static uint64_t getPCdiff(instr_t *instr);

bool new_line = false;

static void event_init(void);
static void event_exit(void);
static dr_emit_flags_t event_app_instruction(void *drcontext, void *tag, instrlist_t *bb, instr_t *instr,
                      bool for_trace, bool translating, void *user_data);

std::unique_ptr<std::ostream> _deptrace_f;

DR_EXPORT void dr_client_main(client_id_t id, int argc, const char *argv[])
{
    dr_set_client_name("ARMTracer",
                       "http://dynamorio.org/issues");
    if (!drmgr_init())
        DR_ASSERT(false);
    drx_init();

    dr_register_exit_event(event_exit);
    event_init();
    if (!drmgr_register_bb_instrumentation_event(NULL, event_app_instruction, NULL))
        DR_ASSERT(false);

}

static void event_init(void)
{
  void *drcontext = dr_get_current_drcontext();
  dr_mcontext_t mc = {sizeof(mc), DR_MC_ALL};
  _deptrace_f = std::unique_ptr<std::ostream>(new std::ofstream("ARM.trace.trc"));
}

static void event_exit(void)
{
  std::ostream& deptrace_f = *_deptrace_f;
  deptrace_f << "END\n" <<std::flush;
  if (!drmgr_unregister_bb_insertion_event(event_app_instruction))
    DR_ASSERT(false);
  drx_exit();
  drmgr_exit();
}

static dr_emit_flags_t event_app_instruction(void *drcontext, void *tag, instrlist_t *bb, instr_t *instr,
                      bool for_trace, bool translating, void *user_data)
{
 	int i;
    if (instr_writes_memory(instr)) {
      trace_memory_write(instr);
    }
    else if (instr_reads_memory(instr)) {
      trace_memory_read(instr);
    }
    else if (instr_is_cbr(instr)){
      trace_branch(instr);
    }
    else
    	trace_other(instr);
    	
    if (!instr_is_app(instr))
        return DR_EMIT_DEFAULT;
    if (!instr_reads_memory(instr) && !instr_writes_memory(instr))
        return DR_EMIT_DEFAULT;
}

static void trace_memory_write(instr_t *instr)
{ 
  std::ostream& deptrace_f = *_deptrace_f;
  void *drcontext = dr_get_current_drcontext();
  dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL, };
  dr_get_mcontext(drcontext, &mcontext);
  size_t size;
  app_pc address;
  opnd_t ref;
  for (int i = 0; i < instr_num_dsts(instr); ++i) {
    opnd_t dst = instr_get_dst(instr, i);
    if (opnd_is_memory_reference(dst)) {
      size = drutil_opnd_mem_size_in_bytes(dst, instr);
      address = opnd_compute_address(dst,&mcontext );
      }
      }
  //size = instr_memory_reference_size(instr);
  //address = instr_get_app_pc(instr);
  deptrace_f << "S" << getPCdiff << " " << std::hex << (ptr_uint_t)address << std::dec << " " << size <<"\n";
}

static void trace_memory_read(instr_t *instr)
{
  std::ostream& deptrace_f = *_deptrace_f;
  uint size = instr_memory_reference_size(instr);
  opnd_t ref;
  app_pc address = instr_get_app_pc(instr);
  deptrace_f << "L" << getPCdiff << " " << std::hex << (ptr_uint_t)address << std::dec << " " << size <<"\n";
}

static void trace_branch(instr_t *instr)
{
  std::ostream& deptrace_f = *_deptrace_f;
  opnd_t target = instr_get_target(instr);
  app_pc target_pc = opnd_get_pc(target);
  deptrace_f << "B" << getPCdiff << " " << std::hex << (ptr_uint_t)target_pc << std::dec;
  void *drcontext = dr_get_current_drcontext();
  dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL, };
  dr_get_mcontext(drcontext, &mcontext);	
  if(instr_jcc_taken(instr,mcontext.xflags))
    deptrace_f << "*\n";
  else
    deptrace_f << "\n";
}

static void trace_other(instr_t *instr)
{
  std::ostream& deptrace_f = *_deptrace_f;
  deptrace_f << " O ";
}

static uint64_t getPCdiff(instr_t *instr)
{
  app_pc curr_pc = instr_get_app_pc(instr);
  instr_t *prev_instr = instr_get_prev(instr);
  app_pc prev_pc = instr_get_app_pc(prev_instr);
  uint64_t diff =  (ptr_uint_t)curr_pc - (ptr_uint_t)prev_pc;
  if(diff < 0)
    DR_ASSERT(false);
  return diff;
}
