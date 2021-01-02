/* ******************************************************************************
 * Copyright (c) 2011-2018 Google, Inc.  All rights reserved.
 * Copyright (c) 2010 Massachusetts Institute of Technology  All rights reserved.
 * ******************************************************************************/

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

#include<string.h> 
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h> /* for offsetof */
#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "utils.h"
#include "drutil.h"

typedef struct _ins_ref_t {
  app_pc pc;
  int opcode; //1. Read 2. Write 3. Branch 4. FP_add/sub 5. FP_mul 6. FP_div 7. FP_sqrt 8. Other 9. Marker Begin 10. Marker End 11. Marker_value
  int opcode_br;
  int opcode_mem;
  int marker_value;
  //int opcode_MEM;
  //int opcode_mem_load;
  //int opcode_fp_addsub;
  //int opcode_fb_mul;
  //int opcode_fb_div;
  //int opcode_fb_sqrt;
  int opcode_other;
  ushort type;
  ushort size;
  app_pc addr;
  bool instr_mem;
  bool is_branch;
  app_pc target;
  bool taken;
  bool instr_other;
  app_pc br_pending_pc;
  app_pc br_pending_target;
} ins_ref_t;

enum {
  REF_TYPE_READ = 0,
  REF_TYPE_WRITE = 1,
};

#define MAX_NUM_INS_REFS 8192
#define MEM_BUF_SIZE (sizeof(ins_ref_t) * MAX_NUM_INS_REFS)
#define MINSERT instrlist_meta_preinsert

typedef struct {
    byte *seg_base;
    ins_ref_t *buf_base;
    file_t log;
    FILE *logf;
    uint64 num_refs;
} per_thread_t;

char marker_value[] = "";
bool marker = false;
static client_id_t client_id;
static void *mutex;    
static uint64 num_refs;

enum {
    INSTRACE_TLS_OFFS_BUF_PTR,
    INSTRACE_TLS_COUNT, 
};
app_pc curr_pc = 0;
static reg_id_t tls_seg;
static uint tls_offs;
static int tls_idx;
bool instr_first = false;
#define TLS_SLOT(tls_base, enum_val) (void **)((byte *)(tls_base) + tls_offs + (enum_val))
#define BUF_PTR(tls_base) *(ins_ref_t **)TLS_SLOT(tls_base, INSTRACE_TLS_OFFS_BUF_PTR)

#define MINSERT instrlist_meta_preinsert

static uint getPCdiff(app_pc pc)
{
  uint diff =  (ptr_uint_t)pc -  (ptr_uint_t)curr_pc;
  curr_pc = pc;
  return diff;
}

app_pc br_pending_pc = 0;
app_pc br_pending_target = 0;
bool br_pending = false;
uint br_pending_pcdiff = 0;
bool marker_begin = false;
bool marker_end = false;
bool marker_dep = false;
bool marker_next_load = false;
int final_marker_value = 0;

static void
instrace(void *drcontext)
{
    per_thread_t *data;
    ins_ref_t *ins_ref, *buf_ptr;
    
    data = drmgr_get_tls_field(drcontext, tls_idx);
    buf_ptr = BUF_PTR(data->seg_base);
    for (ins_ref = (ins_ref_t *)data->buf_base; ins_ref < buf_ptr; ins_ref++) {
      DR_ASSERT(ins_ref->opcode > 0 && ins_ref->opcode < 12);
      uint pcdiff = getPCdiff(ins_ref->pc);
      if(br_pending){
	fprintf(data->logf, "B%d "PIFX"", br_pending_pcdiff, (ptr_uint_t)br_pending_target);
	if(((ptr_uint_t)ins_ref->pc - (ptr_uint_t)br_pending_pc) == 4)
	  fprintf(data->logf,"\n");
	else
	  fprintf(data->logf,"*\n");
	br_pending = false;
      }
      if(ins_ref->opcode == 1 || ins_ref->opcode == 2){ //read or write
	if(ins_ref->opcode == 1) //read
	  fprintf(data->logf, "L%d "PIFX" %d\n", pcdiff,(ptr_uint_t)ins_ref->addr,ins_ref->size);
	else if(ins_ref->opcode == 2) //write
	  fprintf(data->logf, "S%d "PIFX" %d\n", pcdiff,(ptr_uint_t)ins_ref->addr,ins_ref->size);
      }
      else if (ins_ref->opcode == 3){ //Branch
	DR_ASSERT(!br_pending);
	br_pending = true;
	br_pending_target = ins_ref->target;
	br_pending_pc = ins_ref->pc;
	br_pending_pcdiff = pcdiff;
      }
      else if (ins_ref->opcode == 8){ //other isntruction
	fprintf(data->logf, "OI%d\n", pcdiff);
      }
      else if (ins_ref->opcode == 4){ //floating add/sub
	fprintf(data->logf, "A%d\n", pcdiff);
      }
      else if (ins_ref->opcode == 5){ //floating Mul
	fprintf(data->logf, "M%d\n", pcdiff);
      }
      else if (ins_ref->opcode == 6){ //floating Div
	fprintf(data->logf, "D%d\n", pcdiff);
      }
      else if (ins_ref->opcode == 7){ //floating sqrt
	fprintf(data->logf, "Q%d\n", pcdiff);
      }
      else if (ins_ref->opcode == 9){//marker begin 
	DR_ASSERT(marker_next_load == false);
	marker_begin = true;
	char str[] = ""; 
	strcat(marker_value, str); //reset marker value FIXME: Its global have to change it for per thread 
      }
      else if (ins_ref->opcode == 10){//marker end
	DR_ASSERT(marker_begin);
	marker_end = true;
	final_marker_value = atoi(marker_value);
	marker_next_load = true;
      }
      else if (ins_ref->opcode == 11){//marker dep
	DR_ASSERT(marker_begin);
	char str[] = "";
	sprintf(str, "%d", ins_ref->marker_value);
	//strcat(str, ins_ref->marker_value);
	//str = ins_ref->marker_value;
	strcat(marker_value, str);
      }
      
      data->num_refs++;
    }
    BUF_PTR(data->seg_base) = data->buf_base;
}

static void
clean_call(void)
{
    void *drcontext = dr_get_current_drcontext();
    instrace(drcontext);
}

static void
insert_load_buf_ptr(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t reg_ptr)
{
    dr_insert_read_raw_tls(drcontext, ilist, where, tls_seg,
                           tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_ptr);
}

static void
insert_update_buf_ptr(void *drcontext, instrlist_t *ilist, instr_t *where,
                      reg_id_t reg_ptr, int adjust)
{
    MINSERT(
        ilist, where,
        XINST_CREATE_add(drcontext, opnd_create_reg(reg_ptr), OPND_CREATE_INT16(adjust)));
    dr_insert_write_raw_tls(drcontext, ilist, where, tls_seg,
                            tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_ptr);
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
                drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, opcode)),
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
                               OPND_CREATE_MEMPTR(base, offsetof(ins_ref_t, pc)),
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
			     OPND_CREATE_MEMPTR(reg_ptr, offsetof(ins_ref_t, addr)),
			     opnd_create_reg(reg_addr)));
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
				    OPND_CREATE_MEM16(base, offsetof(ins_ref_t, size)),
				    opnd_create_reg(scratch)));
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
				    OPND_CREATE_MEM16(base, offsetof(ins_ref_t, type)),
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
				    OPND_CREATE_MEM16(base, offsetof(ins_ref_t, instr_mem)),
				    opnd_create_reg(scratch)));
}

static void
insert_save_branch_target(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			  reg_id_t scratch, app_pc target)
{
  instrlist_insert_mov_immed_ptrsz(drcontext, (ptr_int_t)target, opnd_create_reg(scratch),
				   ilist, where, NULL, NULL);
  MINSERT(ilist, where,
	  XINST_CREATE_store(drcontext,
			     OPND_CREATE_MEMPTR(base, offsetof(ins_ref_t, target)),
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
				    OPND_CREATE_MEM16(base, offsetof(ins_ref_t, taken)),
				    opnd_create_reg(scratch)));
}
static void
insert_save_branch(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
		   reg_id_t scratch, int opcode_br)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(opcode_br)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, opcode_br)),
				    opnd_create_reg(scratch)));
}

static void
insert_save_mem(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
		   reg_id_t scratch, int opcode_mem)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(opcode_mem)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, opcode_mem)),
				    opnd_create_reg(scratch)));
}

static void
insert_save_other(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
		reg_id_t scratch, int opcode_other)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(opcode_other)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, opcode_other)),
				    opnd_create_reg(scratch)));
}

static void
insert_marker_value(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
		  reg_id_t scratch, int marker_value)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(marker_value)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, marker_value)),
				    opnd_create_reg(scratch)));
}


static void
instrument_marker_end(void *drcontext, instrlist_t *ilist, instr_t *where)
{
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                        DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false); /* cannot recover */
    return;
  }

  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  //insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
  //                  instr_get_opcode(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     10);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    1);
  //insert_marker_value(drcontext, ilist, where, reg_ptr, reg_tmp,
  //		      marker_value);
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}

static void
instrument_marker_value(void *drcontext, instrlist_t *ilist, instr_t *where, int marker_value)
{
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                              DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false); /* cannot recover */
    return;
  }

  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  //insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
  //                  instr_get_opcode(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     11);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    1);
  insert_marker_value(drcontext, ilist, where, reg_ptr, reg_tmp,
                    marker_value);
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}


static void
instrument_marker_begin(void *drcontext, instrlist_t *ilist, instr_t *where)
{
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                  DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false); /* cannot recover */
    return;
  }

  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  //insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
  //                  instr_get_opcode(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     9);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    1);
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

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
        DR_ASSERT(false); /* cannot recover */
        return;
    }

    insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
    insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
    //insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
    //                  instr_get_opcode(where));
    insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		       8);
    insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		       1);
    insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

    if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
        DR_ASSERT(false);
}


static void
instrument_fp_addsub(void *drcontext, instrlist_t *ilist, instr_t *where)
{
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                  DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false); /* cannot recover */
    return;
    
  }
  
  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     4);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    2); //fadd fsub
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));
  
  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}

static void
instrument_fp_mul(void *drcontext, instrlist_t *ilist, instr_t *where)
{
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                        DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false); /* cannot recover */
    return;

  }

  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     5);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    3); //fmul
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}


static void
instrument_fp_div(void *drcontext, instrlist_t *ilist, instr_t *where)
{
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                        DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false); /* cannot recover */
    return;

  }
  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     6);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    4); //fdiv
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}


static void
instrument_fp_sqrt(void *drcontext, instrlist_t *ilist, instr_t *where)
{
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                        DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false); /* cannot recover */
    return;

  }

  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     7);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    5); //fsqrt
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

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
    DR_ASSERT(false); /* cannot recover */
    return;
  }

  insert_save_addr(drcontext, ilist, where, ref, reg_ptr, reg_tmp);
  if(write){
    insert_save_type(drcontext, ilist, where, reg_ptr, reg_tmp,
		     REF_TYPE_WRITE);
    insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		       2);
  }
  else{
    insert_save_type(drcontext, ilist, where, reg_ptr, reg_tmp,
		     REF_TYPE_READ);
    insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		       1);
  }
  insert_save_size(drcontext, ilist, where, reg_ptr, reg_tmp,
		   (ushort)drutil_opnd_mem_size_in_bytes(ref, where));
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  insert_save_operation_type(drcontext, ilist, where, reg_ptr, reg_tmp, true);
  //insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
  //		     instr_get_opcode(where));
  insert_save_mem(drcontext, ilist, where, reg_ptr, reg_tmp,
		     1);
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}

static void
instrument_branch(void *drcontext, instrlist_t *ilist, instr_t *where)
{
  reg_id_t reg_ptr, reg_tmp;
  if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
                  DRREG_SUCCESS ||
      drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
      DRREG_SUCCESS) {
    DR_ASSERT(false); /* cannot recover */
    return;
  }

  opnd_t target = instr_get_target(where);
  app_pc target_pc = opnd_get_pc(target);
  
  insert_load_buf_ptr(drcontext, ilist, where, reg_ptr);
  insert_save_pc(drcontext, ilist, where, reg_ptr, reg_tmp, instr_get_app_pc(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     3);
  insert_save_branch(drcontext, ilist, where, reg_ptr, reg_tmp, 1);
  insert_save_branch_target(drcontext, ilist, where, reg_ptr, reg_tmp, target_pc);
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}

static dr_emit_flags_t
event_app_instruction(void *drcontext, void *tag, instrlist_t *bb, instr_t *instr,
                      bool for_trace, bool translating, void *user_data)
{
  int i;
  drmgr_disable_auto_predication(drcontext, bb);
  
  if (!instr_is_app(instr))
    return DR_EMIT_DEFAULT;
  if(instr_is_cbr(instr)){
      instrument_branch(drcontext, bb, instr);
  }
  else if(instr_reads_memory(instr) || instr_writes_memory(instr)){
    //FIXME::
    //instrument_instr(drcontext, bb, instr); //to instrument mem operation other then load store
    for (i = 0; i < instr_num_srcs(instr); i++) {
      if (opnd_is_memory_reference(instr_get_src(instr, i)))
	instrument_mem(drcontext, bb, instr, instr_get_src(instr, i), false);
    }
    
    for (i = 0; i < instr_num_dsts(instr); i++) {
      if (opnd_is_memory_reference(instr_get_dst(instr, i)))
	instrument_mem(drcontext, bb, instr, instr_get_dst(instr, i), true);
    }
  }
  else if(!strcmp(decode_opcode_name(instr_get_opcode(instr)), "fadd") || !strcmp(decode_opcode_name(instr_get_opcode(instr)),"fsub"))
    { //fadd fsub
      instrument_fp_addsub(drcontext, bb, instr);
    }
  else if(!strcmp(decode_opcode_name(instr_get_opcode(instr)), "fmul")) //fmul
    {
      instrument_fp_mul(drcontext, bb, instr);
    }
  else if(!strcmp(decode_opcode_name(instr_get_opcode(instr)), "fdiv")) //fdiv
    {
      instrument_fp_div(drcontext, bb, instr);
    }
  else if(!strcmp(decode_opcode_name(instr_get_opcode(instr)), "fsqrt")) //sqrt 
    {
      instrument_fp_sqrt(drcontext, bb, instr);
    }
  else if (!strcmp(decode_opcode_name(instr_get_opcode(instr)), "orr"))
    {
      if(instr_num_srcs(instr) == 4){
	opnd_t src_opnd = instr_get_src(instr, 0); //first operand
	DR_ASSERT(opnd_is_reg(src_opnd));
	reg_id_t reg_id = opnd_get_reg(src_opnd); //get register
	//if(strcmp(get_register_name(reg_id), "wzr") && strcmp(get_register_name(reg_id), "xzr"))
	// printf("C%s\n", get_register_name(reg_id));
	
	if(!strcmp(get_register_name(reg_id), "x11")){
	  printf("%s\n", get_register_name(reg_id));
	  //instrument_marker_begin(drcontext, bb, instr);
	  marker = true; //set marker
	  char str[] = "";
	  strcat(marker_value, str); //reset it
	}
	if(!strcmp(get_register_name(reg_id), "x10") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  //DR_ASSERT(marker);
	  marker = false;
	  //instrument_marker_end(drcontext, bb, instr);
	}
	if(!strcmp(get_register_name(reg_id), "x0") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "1";
	  //instrument_marker_value(drcontext, bb, instr, 1);
	  strcat(marker_value, str);
	}
	
	if(!strcmp(get_register_name(reg_id), "x1") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "1";
	  //instrument_marker_value(drcontext, bb, instr, 1);
	  strcat(marker_value, str);
	}
	if (!strcmp(get_register_name(reg_id), "x2") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "2";
	  //instrument_marker_value(drcontext, bb, instr, 2);
	  strcat(marker_value, str);
	}
	if (!strcmp(get_register_name(reg_id), "x3") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "3";
	  //instrument_marker_value(drcontext, bb, instr, 3);
	  strcat(marker_value, str);
	}
	if (!strcmp(get_register_name(reg_id), "x4") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "4";
	  //instrument_marker_value(drcontext, bb, instr, 4);
	  strcat(marker_value, str);
	}
	if (!strcmp(get_register_name(reg_id), "x5") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "5";
	  //instrument_marker_value(drcontext, bb, instr, 5);
	  strcat(marker_value, str);
	}
	if (!strcmp(get_register_name(reg_id), "x6") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "6";
	  //instrument_marker_value(drcontext, bb, instr, 6);
	  strcat(marker_value, str);
	}
	if (!strcmp(get_register_name(reg_id), "x7") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "7";
	  //instrument_marker_value(drcontext, bb, instr, 7);
	  strcat(marker_value, str);
	}
	if (!strcmp(get_register_name(reg_id), "x9") && marker){
	  printf("%s\n", get_register_name(reg_id));
	  char str[] = "8";
	  //instrument_marker_value(drcontext, bb, instr, 9);
	  strcat(marker_value, str);
	}
      }
    }
  else
    instrument_instr(drcontext, bb, instr);
  /* insert code once per bb to call clean_call for processing the buffer */
  if (drmgr_is_first_instr(drcontext, instr)
      /* XXX i#1698: there are constraints for code between ldrex/strex pairs,
       * so we minimize the instrumentation in between by skipping the clean call.
       * We're relying a bit on the typical code sequence with either ldrex..strex
       * in the same bb, in which case our call at the start of the bb is fine,
       * or with a branch in between and the strex at the start of the next bb.
       * However, there is still a chance that the instrumentation code may clear the
       * exclusive monitor state.
       * Using a fault to handle a full buffer should be more robust, and the
       * forthcoming buffer filling API (i#513) will provide that.
       */
      IF_AARCHXX(&&!instr_is_exclusive_store(instr)))
    dr_insert_clean_call(drcontext, bb, instr, (void *)clean_call, false, 0);
  
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
    BUF_PTR(data->seg_base) = data->buf_base;

    data->num_refs = 0;

    /* We're going to dump our data to a per-thread file.
     * On Windows we need an absolute path so we place it in
     * the same directory as our library. We could also pass
     * in a path as a client argument.
     */
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
    instrace(drcontext); /* dump any remaining buffer entries */
    data = drmgr_get_tls_field(drcontext, tls_idx);
    dr_mutex_lock(mutex);
    num_refs += data->num_refs;
    dr_mutex_unlock(mutex);
    log_stream_close(data->logf); /* closes fd too */
    dr_raw_mem_free(data->buf_base, MEM_BUF_SIZE);
    dr_thread_free(drcontext, data, sizeof(per_thread_t));
}

static void
event_exit(void)
{
    dr_log(NULL, DR_LOG_ALL, 1, "Client 'instrace' num refs seen: " SZFMT "\n", num_refs);
    if (!dr_raw_tls_cfree(tls_offs, INSTRACE_TLS_COUNT))
        DR_ASSERT(false);

    if (!drmgr_unregister_tls_field(tls_idx) ||
        !drmgr_unregister_thread_init_event(event_thread_init) ||
        !drmgr_unregister_thread_exit_event(event_thread_exit) ||
        !drmgr_unregister_bb_insertion_event(event_app_instruction) ||
        drreg_exit() != DRREG_SUCCESS)
        DR_ASSERT(false);

    dr_mutex_destroy(mutex);
    drmgr_exit();
}

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    drreg_options_t ops = { sizeof(ops), 3, false };
    dr_set_client_name("DynamoRIO Sample Client 'ARM Tracer'",
                       "http://dynamorio.org/issues");
    if (!drmgr_init() || drreg_init(&ops) != DRREG_SUCCESS)
        DR_ASSERT(false);

    /* register events */
    dr_register_exit_event(event_exit);
    if (!drmgr_register_thread_init_event(event_thread_init) ||
        !drmgr_register_thread_exit_event(event_thread_exit) ||
        !drmgr_register_bb_instrumentation_event(NULL /*analysis_func*/,
                                                 event_app_instruction, NULL))
        DR_ASSERT(false);

    client_id = id;
    mutex = dr_mutex_create();

    tls_idx = drmgr_register_tls_field();
    DR_ASSERT(tls_idx != -1);
    /* The TLS field provided by DR cannot be directly accessed from the code cache.
     * For better performance, we allocate raw TLS so that we can directly
     * access and update it with a single instruction.
     */
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, INSTRACE_TLS_COUNT, 0))
        DR_ASSERT(false);

    dr_log(NULL, DR_LOG_ALL, 1, "Client 'instrace' initializing\n");
}
