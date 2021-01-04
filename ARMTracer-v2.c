/* **********************************************************
 * Copyright (c) 2014-2018 Google, Inc.  All rights reserved.
 * Copyright (c) 2003-2010 VMware, Inc.  All rights reserved.
 * **********************************************************/
/*
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of VMware, Inc. nor the names of its contributors may be
 *   used to endorse or promote products derived from this software without
 *   specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL VMWARE, INC. OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
 * DAMAGE.
 */
/* ******************************************************************************
 * ARM TRACE GENERATOR
 * It generates the trace with the following format:-
 * [L|LA]<PC_diff_in_decimal>(d<dep>)(m<mem_dep>) <hex_addr> <size>
 * [S|SA]<PC_diff_in_decimal>(d<dep>)(m<mem_dep>)(a<addr_dep>) <hex_addr> <size>
 * B<PC_diff_in_decimal>(d<dep>)(m<dep>)(t<target_addr>)(*)?
 * [A|M|D|Q|]<PC_diff_in_decimal>(d<dep>)(m<dep>)
 * Legend:
 * L=load, LA=load of atomic, S=store, SA=store of atomic, 
 * B=conditional branch, A=fp_addsub, M=fp_mul, D=fp_div, Q=fp_sqrt, []=generic
 * d=reg dependence, m=mem dependence, a=addr dependence, t=target address, *=taken  
 * Example: 
 * 2 A0 3d1 B2d2t-120* L5d1 fff0 4
 * Sawan Singh (singh.sawan@um.es) CAPS Group, University of Murcia, ES.
 * ******************************************************************************/

#include <stdio.h>
#include <stddef.h> /* for offsetof */
#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "drutil.h"
#include "utils.h"

static void trace_branch(instr_t *instr);
static void trace_other(instr_t *instr);
static void event_init(void);
static void event_exit(void);
static uint getPCdiff(app_pc pc);

enum {
    REF_TYPE_READ = 0,
    REF_TYPE_WRITE = 1,
};

typedef struct _mem_ref_t {
  ushort type;
  ushort size; 
  app_pc addr;
  app_pc pc;
  ushort opcode;
  bool instr_mem;
  bool is_branch;
  app_pc target;
  bool taken;
  bool instr_other;
} mem_ref_t;


#define MAX_NUM_MEM_REFS 4096
#define MEM_BUF_SIZE (sizeof(mem_ref_t) * MAX_NUM_MEM_REFS)

typedef struct {
    byte *seg_base;
    mem_ref_t *buf_base;
    file_t log;
    FILE *logf;
    uint64 num_refs;
} per_thread_t;

static client_id_t client_id;
static void *mutex;     
static uint64 num_refs; 

enum {
    MEMTRACE_TLS_OFFS_BUF_PTR,
    MEMTRACE_TLS_COUNT, 
};

static app_pc curr_pc = 0;
static reg_id_t tls_seg;
static uint tls_offs;
static int tls_idx;
#define TLS_SLOT(tls_base, enum_val) (void **)((byte *)(tls_base) + tls_offs + (enum_val))
#define BUF_PTR(tls_base) *(mem_ref_t **)TLS_SLOT(tls_base, MEMTRACE_TLS_OFFS_BUF_PTR)

#define MINSERT instrlist_meta_preinsert

static void
memtrace(void *drcontext)
{  
    per_thread_t *data;
    mem_ref_t *mem_ref, *buf_ptr;
    data = drmgr_get_tls_field(drcontext, tls_idx);
    buf_ptr = BUF_PTR(data->seg_base);
    for (mem_ref = (mem_ref_t *)data->buf_base; mem_ref < buf_ptr; mem_ref++) {
      //printf("%d\n",mem_ref->instr_other);
      uint pcdiff = getPCdiff(mem_ref->addr);
      if ((mem_ref->type == REF_TYPE_WRITE || mem_ref->type == REF_TYPE_READ)
	  && !mem_ref->is_branch){
	if(mem_ref->type == REF_TYPE_WRITE)
	  fprintf(data->logf, "S%d "PIFX" %d\n", pcdiff,(ptr_uint_t)mem_ref->addr,mem_ref->size);
	else if(mem_ref->type == REF_TYPE_READ)
	  fprintf(data->logf, "L%d "PIFX" %d\n", pcdiff,(ptr_uint_t)mem_ref->addr,mem_ref->size);
      }
      else if(mem_ref->is_branch){
	//printf("%d %d %x %d\n",mem_ref->is_branch, mem_ref->taken, mem_ref->target,mem_ref->instr_mem);
	if(mem_ref->taken)
	  fprintf(data->logf, "B%d "PIFX"*\n", pcdiff, (ptr_uint_t)mem_ref->target);
	else
	  fprintf(data->logf, "B%d "PIFX"\n", pcdiff, (ptr_uint_t)mem_ref->target);
      }
      else if(mem_ref->instr_other){
	//printf("%d\n",mem_ref->instr_other);
	fprintf(data->logf, "OI%d\n", pcdiff);
      }
      data->num_refs++;
    }
    BUF_PTR(data->seg_base) = data->buf_base;
}

static void
clean_call(void)
{
    void *drcontext = dr_get_current_drcontext();
    memtrace(drcontext);
}

static void
insert_save_opcode(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
                   reg_id_t scratch, int opcode)
{
    scratch = reg_resize_to_opsz(scratch, OPSZ_2);
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
                                  OPND_CREATE_INT16(opcode)));
    MINSERT(ilist, where,
            XINST_CREATE_store_2bytes(
                drcontext, OPND_CREATE_MEM16(base, offsetof(mem_ref_t, opcode)),
                opnd_create_reg(scratch)));
}


static void
insert_load_buf_ptr(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t reg_ptr)
{
    dr_insert_read_raw_tls(drcontext, ilist, where, tls_seg,
                           tls_offs + MEMTRACE_TLS_OFFS_BUF_PTR, reg_ptr);
}

static void
insert_update_buf_ptr(void *drcontext, instrlist_t *ilist, instr_t *where,
                      reg_id_t reg_ptr, int adjust)
{
    MINSERT(
        ilist, where,
        XINST_CREATE_add(drcontext, opnd_create_reg(reg_ptr), OPND_CREATE_INT16(adjust)));
    dr_insert_write_raw_tls(drcontext, ilist, where, tls_seg,
                            tls_offs + MEMTRACE_TLS_OFFS_BUF_PTR, reg_ptr);
}

static void
insert_save_type(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
                 reg_id_t scratch, ushort type)
{
    scratch = reg_resize_to_opsz(scratch, OPSZ_2);
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
                                  OPND_CREATE_INT16(type)));
    MINSERT(ilist, where,
            XINST_CREATE_store_2bytes(drcontext,
                                      OPND_CREATE_MEM16(base, offsetof(mem_ref_t, type)),
                                      opnd_create_reg(scratch)));
}

static void
insert_save_other(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
                 reg_id_t scratch, bool instr_other)
{
    scratch = reg_resize_to_opsz(scratch, OPSZ_2);
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
                                  OPND_CREATE_INT16(instr_other)));
    MINSERT(ilist, where,
            XINST_CREATE_store_2bytes(drcontext,
                                      OPND_CREATE_MEM16(base, offsetof(mem_ref_t, instr_other)),
                                      opnd_create_reg(scratch)));
}

static void
insert_save_size(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
                 reg_id_t scratch, ushort size)
{
    scratch = reg_resize_to_opsz(scratch, OPSZ_2);
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
                                  OPND_CREATE_INT16(size)));
    MINSERT(ilist, where,
            XINST_CREATE_store_2bytes(drcontext,
                                      OPND_CREATE_MEM16(base, offsetof(mem_ref_t, size)),
                                      opnd_create_reg(scratch)));
}

static void
insert_save_operation_type(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
                 reg_id_t scratch, bool instr_mem)
{
    scratch = reg_resize_to_opsz(scratch, OPSZ_2);
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
                                  OPND_CREATE_INT16(instr_mem)));
    MINSERT(ilist, where,
            XINST_CREATE_store_2bytes(drcontext,
                                      OPND_CREATE_MEM16(base, offsetof(mem_ref_t, instr_mem)),
                                      opnd_create_reg(scratch)));
}

static void
insert_save_branch(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
                 reg_id_t scratch, bool is_branch)
{
    scratch = reg_resize_to_opsz(scratch, OPSZ_2);
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
                                  OPND_CREATE_INT16(is_branch)));
    MINSERT(ilist, where,
            XINST_CREATE_store_2bytes(drcontext,
                                      OPND_CREATE_MEM16(base, offsetof(mem_ref_t, is_branch)),
                                      opnd_create_reg(scratch)));
}

static void
insert_save_branch_info(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
                 reg_id_t scratch, bool taken)
{
    scratch = reg_resize_to_opsz(scratch, OPSZ_2);
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
                                  OPND_CREATE_INT16(taken)));
    MINSERT(ilist, where,
            XINST_CREATE_store_2bytes(drcontext,
                                      OPND_CREATE_MEM16(base, offsetof(mem_ref_t, taken)),
                                      opnd_create_reg(scratch)));
}


static void
insert_save_branch_target(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
                 reg_id_t scratch, app_pc target)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  instrlist_insert_mov_immed_ptrsz(drcontext, (ptr_int_t)target, opnd_create_reg(scratch),
				   ilist, where, NULL, NULL);
  MINSERT(ilist, where,
	  XINST_CREATE_store(drcontext,
			     OPND_CREATE_MEMPTR(base, offsetof(mem_ref_t, target)),
			     opnd_create_reg(scratch)));
}


static void
insert_save_pc(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
               reg_id_t scratch, app_pc pc)
{
    instrlist_insert_mov_immed_ptrsz(drcontext, (ptr_int_t)pc, opnd_create_reg(scratch),
                                     ilist, where, NULL, NULL);
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext,
                               OPND_CREATE_MEMPTR(base, offsetof(mem_ref_t, pc)),
                               opnd_create_reg(scratch)));
}

static void
insert_save_addr(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref,
                 reg_id_t reg_ptr, reg_id_t reg_addr)
{
    bool ok;
    ok = drutil_insert_get_mem_addr(drcontext, ilist, where, ref, reg_addr, reg_ptr);
    DR_ASSERT(ok);
    insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext,
                               OPND_CREATE_MEMPTR(reg_ptr, offsetof(mem_ref_t, addr)),
                               opnd_create_reg(reg_addr)));
}

static void
instrument_other(void *drcontext, instrlist_t *ilist, instr_t *where)
{
   /* We need two scratch registers */
    reg_id_t reg_ptr, reg_tmp;
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
            DRREG_SUCCESS) {
        DR_ASSERT(false); /* cannot recover */
        return;
    }

    insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
    insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp, true);
    insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
    insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
                       instr_get_opcode(where));
    insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(mem_ref_t));

    /* Restore scratch registers */
    if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
        DR_ASSERT(false);
}

static void
instrument_branch(void *drcontext, instrlist_t *ilist, instr_t *where)
{
  DR_ASSERT(instr_is_cbr(where));
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                  DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false);
    return;
  }
  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_branch(drcontext, ilist, where, reg_ptr, reg_tmp, true);
  /* //FIXME:: instr_get_target works for all the control flow instructions and returns the first source operand */
  opnd_t target = instr_get_target(where);
  //DR_ASSERT(opnd_is_pc(target));
  //app_pc target_pc = 0;
  app_pc target_pc = opnd_get_pc(target);
  insert_save_branch_target(drcontext, ilist, where, reg_ptr, reg_tmp, target_pc);
  dr_mcontext_t mcontext = { sizeof(mcontext), DR_MC_ALL, };
  dr_get_mcontext(drcontext, &mcontext);
  //FIXME:: instr_cbr_taken/instr_jcc_taken is not implimented for ARM yet
  insert_save_branch_info(drcontext, ilist, where, reg_ptr, reg_tmp, false);
  //insert_save_branch_info(drcontext, ilist, where, reg_ptr, reg_tmp,false);
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(mem_ref_t));
  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}

static void
instrument_instr(void *drcontext, instrlist_t *ilist, instr_t *where)
{
    reg_id_t reg_ptr, reg_tmp;
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
            DRREG_SUCCESS) {
        DR_ASSERT(false); 
        return;
    }
    insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
    insert_save_type(drcontext, ilist, where, reg_ptr, reg_tmp,
                     (ushort)instr_get_opcode(where));
    insert_save_size(drcontext, ilist, where, reg_ptr, reg_tmp,
                     (ushort)instr_length(drcontext, where));
    insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
    insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(mem_ref_t));
    if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
        DR_ASSERT(false);
}

static void
instrument_mem(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref,
               bool write)
{
    reg_id_t reg_ptr, reg_tmp;
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
            DRREG_SUCCESS) {
        DR_ASSERT(false); 
        return;
    }
    insert_save_addr(drcontext, ilist, where, ref, reg_ptr, reg_tmp);
    insert_save_type(drcontext, ilist, where, reg_ptr, reg_tmp,
                     write ? REF_TYPE_WRITE : REF_TYPE_READ);
    insert_save_size(drcontext, ilist, where, reg_ptr, reg_tmp,
                     (ushort)drutil_opnd_mem_size_in_bytes(ref, where));
    //bool mem_use = (instr_writes_memory(where) && instr_reads_memory(where));
    //FIXME::We instrument every opcode having a memory ref we can change it just for load and store as well
    insert_save_operation_type(drcontext, ilist, where, reg_ptr, reg_tmp, true);
    insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(mem_ref_t));
    if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
        DR_ASSERT(false);
    
}

static dr_emit_flags_t
event_app_instruction(void *drcontext, void *tag, instrlist_t *bb, instr_t *instr,
                      bool for_trace, bool translating, void *user_data)
{
  drmgr_disable_auto_predication(drcontext, bb);
  int i;
  if (!instr_is_app(instr))
    return DR_EMIT_DEFAULT;
  //if (!instr_reads_memory(instr) && !instr_writes_memory(instr)
  //  && !instr_is_cbr(instr))
  //return DR_EMIT_DEFAULT;

  //printf("%s\n",instr_get_opcode(instr));
 
  if(instr_is_cbr(instr)){
    instrument_branch(drcontext, bb, instr);
  }
  else if(instr_reads_memory(instr) || instr_writes_memory(instr)){
    //FIXME::
    //instrument_instr(drcontext, bb, instr); //to instrument mem operation other then load store
    //printf("%d\n",instr_is_cbr(instr));
    for (i = 0; i < instr_num_srcs(instr); i++) {
      if (opnd_is_memory_reference(instr_get_src(instr, i)))
	instrument_mem(drcontext, bb, instr, instr_get_src(instr, i), false);
    }
    
    for (i = 0; i < instr_num_dsts(instr); i++) {
      if (opnd_is_memory_reference(instr_get_dst(instr, i)))
	instrument_mem(drcontext, bb, instr, instr_get_dst(instr, i), true);
    }
  }
  else{ 
   instrument_other(drcontext, bb, instr); 
  } 
  if (/* XXX i#1698: there are constraints for code between ldrex/strex pairs,
       * so we minimize the instrumentation in between by skipping the clean call.
       * As we're only inserting instrumentation on a memory reference, and the
       * app should be avoiding memory accesses in between the ldrex...strex,
       * the only problematic point should be before the strex.
       * However, there is still a chance that the instrumentation code may clear the
       * exclusive monitor state.
       * Using a fault to handle a full buffer should be more robust, and the
       * forthcoming buffer filling API (i#513) will provide that.
         */
      IF_AARCHXX_ELSE(!instr_is_exclusive_store(instr), true))
    dr_insert_clean_call(drcontext, bb, instr, (void *)clean_call, false, 0);
  
  return DR_EMIT_DEFAULT;
}

static dr_emit_flags_t
event_bb_app2app(void *drcontext, void *tag, instrlist_t *bb, bool for_trace,
                 bool translating)
{
    if (!drutil_expand_rep_string(drcontext, bb)) {
        DR_ASSERT(false);
    }
    return DR_EMIT_DEFAULT;
}

static void
event_thread_init(void *drcontext)
{
    per_thread_t *data = dr_thread_alloc(drcontext, sizeof(per_thread_t));
    DR_ASSERT(data != NULL);
    drmgr_set_tls_field(drcontext, tls_idx, data);
    data->seg_base = dr_get_dr_segment_base(tls_seg);
    data->buf_base =
        dr_raw_mem_alloc(MEM_BUF_SIZE, DR_MEMPROT_READ | DR_MEMPROT_WRITE, NULL);
    DR_ASSERT(data->seg_base != NULL && data->buf_base != NULL);
    /* put buf_base to TLS as starting buf_ptr */
    BUF_PTR(data->seg_base) = data->buf_base;

    data->num_refs = 0;
    data->log =
        log_file_open(client_id, drcontext, NULL /* using client lib path */, "ARMTracer",
#ifndef WINDOWS
                      DR_FILE_CLOSE_ON_FORK |
#endif
		      DR_FILE_ALLOW_LARGE);
    data->logf = log_stream_from_file(data->log);
    fprintf(data->logf, "INITIAL PC HERE\n");
}

static void
event_thread_exit(void *drcontext)
{
  per_thread_t *data;
  memtrace(drcontext); /* dump any remaining buffer entries */
  data = drmgr_get_tls_field(drcontext, tls_idx);
  dr_mutex_lock(mutex);
  num_refs += data->num_refs;
  dr_mutex_unlock(mutex);
  fprintf(data->logf,"END");
  log_stream_close(data->logf); /* closes fd too */
  dr_raw_mem_free(data->buf_base, MEM_BUF_SIZE);
  dr_thread_free(drcontext, data, sizeof(per_thread_t));
}

static void
event_exit(void)
{
    dr_log(NULL, DR_LOG_ALL, 1, "Client 'memtrace' num refs seen: " SZFMT "\n", num_refs);
    if (!dr_raw_tls_cfree(tls_offs, MEMTRACE_TLS_COUNT))
        DR_ASSERT(false);

    if (!drmgr_unregister_tls_field(tls_idx) ||
        !drmgr_unregister_thread_init_event(event_thread_init) ||
        !drmgr_unregister_thread_exit_event(event_thread_exit) ||
        !drmgr_unregister_bb_app2app_event(event_bb_app2app) ||
        !drmgr_unregister_bb_insertion_event(event_app_instruction) ||
        drreg_exit() != DRREG_SUCCESS)
        DR_ASSERT(false);

    dr_mutex_destroy(mutex);
    drutil_exit();
    drmgr_exit();
}


DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    drreg_options_t ops = { sizeof(ops), 3, false };
    dr_set_client_name("DynamoRIO Sample Client 'memtrace'",
                       "http://dynamorio.org/issues");
    if (!drmgr_init() || drreg_init(&ops) != DRREG_SUCCESS || !drutil_init())
        DR_ASSERT(false);

    dr_register_exit_event(event_exit);
    if (!drmgr_register_thread_init_event(event_thread_init) ||
        !drmgr_register_thread_exit_event(event_thread_exit) ||
        !drmgr_register_bb_app2app_event(event_bb_app2app, NULL) ||
        !drmgr_register_bb_instrumentation_event(NULL /*analysis_func*/,
                                                 event_app_instruction, NULL))
        DR_ASSERT(false);

    client_id = id;
    mutex = dr_mutex_create();

    tls_idx = drmgr_register_tls_field();
    DR_ASSERT(tls_idx != -1);
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, MEMTRACE_TLS_COUNT, 0))
        DR_ASSERT(false);
    dr_log(NULL, DR_LOG_ALL, 1, "Client 'memtrace' initializing\n");
}

static void event_init(void)
{
  void *drcontext = dr_get_current_drcontext();
  dr_mcontext_t mc = {sizeof(mc), DR_MC_ALL};
}

static uint getPCdiff(app_pc pc)
{
  uint diff =  (ptr_uint_t)pc -  (ptr_uint_t)curr_pc;
  curr_pc = pc;
  return diff;
}
