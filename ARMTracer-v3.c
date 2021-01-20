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
#include <inttypes.h>
#include <string.h> 
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h> /* for offsetof */
#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "utils.h"
#include "drutil.h"
#include "drx.h"
#include "FIFO.h"
#include <zlib.h>
#include "reg2reg.h"

typedef struct _ins_ref_t {
  app_pc pc;
  int opcode; //1. Read 2. Write 3. Branch 4. FP_add/sub 5. FP_mul 6. FP_div 7. FP_sqrt 8. Other 9. Marker Begin 10. Marker End 11. Marker_value
  int opcode_br;
  int opcode_mem;
  int marker_value;
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
  int read_registers;
  int write_registers;
  int w_reg_1;
  int w_reg_2;
  int w_reg_3;
  int w_reg_4;
  int r_reg_1;
  int r_reg_2;
  int r_reg_3;
  int r_reg_4;
  int is_cb;
} ins_ref_t;

enum {
  REF_TYPE_READ = 0,
  REF_TYPE_WRITE = 1,
};

#define MAX_STORE_ADDR 100
#define LOOP_NOALIAS_DIST -999
#define DISPLAY_STRING(msg) dr_printf("%s\n", msg);
#define MAX_NUM_INS_REFS 8192
#define MEM_BUF_SIZE (sizeof(ins_ref_t) * MAX_NUM_INS_REFS)
#define MINSERT instrlist_meta_preinsert

typedef struct {
  byte *seg_base;
  ins_ref_t *buf_base;
  file_t log;
  FILE *logf;
  gzFile deptrace;
  uint64 num_refs;
} per_thread_t;

char marker_value[] = "";
bool marker = false;
static client_id_t client_id;
static void *mutex;    
static uint64 num_refs;
static int stat_load;
static int stat_marked;
static int stat_marked0;
static int stat_marked1;
static int stat_marked2;
static int stat_markedp2;
static uint64 stat_incorrect = 0;

FILE *logs;

enum {
    INSTRACE_TLS_OFFS_BUF_PTR,
    INSTRACE_TLS_COUNT, 
};

app_pc curr_pc = 0;
static reg_id_t tls_seg;
static uint tls_offs;
static int tls_idx;
bool first_instr = true;
app_pc endpc = 0;

#define TLS_SLOT(tls_base, enum_val) (void **)((byte *)(tls_base) + tls_offs + (enum_val))
#define BUF_PTR(tls_base) *(ins_ref_t **)TLS_SLOT(tls_base, INSTRACE_TLS_OFFS_BUF_PTR)

#define MINSERT instrlist_meta_preinsert

static uint getPCdiff(app_pc pc)
{
  uint diff =  (ptr_uint_t)pc - (ptr_uint_t)curr_pc;
  curr_pc = pc;
  return diff;
}

int array_to_num(int arr[],int n){
  char str[6][3];
  int i;
  char number[13] = {'\n'};
  for(i=0;i<n;i++) sprintf(str[i],"%d",arr[i]);
  for(i=0;i<n;i++)strcat(number,str[i]);
  i = atoi(number);
  return i;
} 

uint br_pending_r_reg = 0;
uint br_pending_r_reg_1 = 0;
uint br_pending_r_reg_2 = 0;
uint br_pending_r_reg_3 = 0;
uint br_pending_r_reg_4 = 0;

uint br_pending_w_reg = 0;
uint br_pending_w_reg_1 = 0;
uint br_pending_w_reg_2 = 0;
uint br_pending_w_reg_3 = 0;
uint br_pending_w_reg_4 = 0;

app_pc br_pending_pc = 0;
app_pc br_pending_target = 0;
bool br_pending_cb = false;
bool br_pending_ncb = false;
uint br_pending_pcdiff = 0;
bool marker_begin = false;
bool marker_end = false;
bool marker_dep = false;
bool marker_next_load = false;
int final_marker_value[2] = {0}; //MAX 999
int f_marker = 0;
int marker_index = 0;

struct AddressInfo {
  uint64 icount;
  app_pc pc;
  app_pc address;
};

static uint64 icount = 0;
static uint64 marked_alias_distances[MAX_STORE_ADDR + 1] = {};
static uint64 expected_alias_distances[MAX_STORE_ADDR + 1] = {};
static int last_alias_dist = 0;
static app_pc last_load_addr;
static app_pc last_load_pc;
static uint64 last_load_icount;
struct AddressInfo last_store_addrs[MAX_STORE_ADDR];
static app_pc last_store_addrs_size = 0;
static uint64 last_store_addrs_begin = 0;
static app_pc marked_instr_begin = 0;
static app_pc marked_instr_end = 0;
static uint64 load_mark_pessimistic_count = 0;
static uint64 load_mark_incorrect_count = 0;

void addAddress(app_pc pc, app_pc addr) {
  last_store_addrs[last_store_addrs_begin].icount = icount;
  last_store_addrs[last_store_addrs_begin].pc =  pc;
  last_store_addrs[last_store_addrs_begin].address = addr;
  last_store_addrs_begin = (last_store_addrs_begin + 1) % MAX_STORE_ADDR;
  if (last_store_addrs_size < MAX_STORE_ADDR) {
    last_store_addrs_size++;
  }
}

bool checkMarkedLoad(uint64 marker, app_pc ld_addr){
  // for(int i = 90; i < getSBindex(); i++)
  // printf("DEBUG: SB index %d st_addr "PIFX" \n",i, StoreBuffer[i].address);
  //printf("DEBUG: checkMarked marker %d ld_addr "PIFX" \n",marker, ld_addr);
  int distance = getSBindex() - marker;
  //printf("distance %d\n",distance);
  for (int i = getSBindex() - 1; i >= distance; i--){
    //printf("DEBUG: checking.... index %d st_addr "PIFX" \n",i, StoreBuffer[i].address);
    if(StoreBuffer[i].address == ld_addr){
      return false;
    }
  }
  return true;
}

bool checkMarkCorrect(app_pc addr, int distance, int expected_dist, app_pc store_pc) {
  assert((distance >= 0 && distance < MAX_STORE_ADDR) ||
	 distance == LOOP_NOALIAS_DIST);

  struct AddressInfo addrInfo;

  int c = 0;
  for (int i = (last_store_addrs_begin + MAX_STORE_ADDR - 1) % MAX_STORE_ADDR,
	 end = MAX_STORE_ADDR - 1;
       c < end; i = (i + MAX_STORE_ADDR - 1) % MAX_STORE_ADDR, ++c) {
    if (last_store_addrs[i].address == addr) {
      store_pc = last_store_addrs[i].pc;
      break;
    }
  }
  if (distance >= 0 && distance < c)
    load_mark_pessimistic_count += 1;
  expected_dist = c;

  assert(expected_dist < MAX_STORE_ADDR);
  expected_alias_distances[expected_dist] += 1;

  for (int i = (last_store_addrs_begin + MAX_STORE_ADDR - 1) % MAX_STORE_ADDR,
	 end = distance < 0 ? MAX_STORE_ADDR - 1 : distance, count = 0;
       count < end; i = (i + MAX_STORE_ADDR - 1) % MAX_STORE_ADDR, ++count) {
    if (last_store_addrs[i].address == addr) {
      addrInfo = last_store_addrs[i];
      break;
    }
  }

  if (addrInfo.icount == 0)
    return true;
  else if (distance >= 0)
    return false;
}

static void
ARMTracer(void *drcontext)
{
    per_thread_t *data;
    ins_ref_t *ins_ref, *buf_ptr;
    
    data = drmgr_get_tls_field(drcontext, tls_idx);
    buf_ptr = BUF_PTR(data->seg_base);
    for (ins_ref = (ins_ref_t *)data->buf_base; ins_ref < buf_ptr; ins_ref++) {
      DR_ASSERT(ins_ref->opcode > 0 && ins_ref->opcode < 12);
      if(first_instr){
	gzprintf(data->deptrace,""PIFX"\n",ins_ref->pc);
	first_instr = false;
      }
      uint pcdiff = getPCdiff(ins_ref->pc);
      endpc = endpc + pcdiff;
      if(br_pending_cb){
	//gzprintf(data->deptrace, "B%d "PIFX"", br_pending_pcdiff, (ptr_uint_t)br_pending_target);
	gzprintf(data->deptrace, "B%d", br_pending_pcdiff);
	if(br_pending_r_reg == 1)  // read printing
	  gzprintf(data->deptrace, "r%d",br_pending_r_reg_1);
	else if(br_pending_r_reg == 2)
	  gzprintf(data->deptrace, "r%dr%d", br_pending_r_reg_1, br_pending_r_reg_2);
	else if(br_pending_r_reg == 3)
	  gzprintf(data->deptrace, "r%dr%dr%d", br_pending_r_reg_1, br_pending_r_reg_2, br_pending_r_reg_3);
	else if(br_pending_r_reg == 4)
	  gzprintf(data->deptrace, "r%dr%dr%dr%d", br_pending_r_reg_1, br_pending_r_reg_2, br_pending_r_reg_3, br_pending_r_reg_4);
	else if(br_pending_r_reg != 0)
	  DR_ASSERT(false);
	if(br_pending_w_reg == 1)  // write printing
	  gzprintf(data->deptrace, "w%d",br_pending_w_reg_1);
	else if(br_pending_w_reg == 2)
	  gzprintf(data->deptrace, "w%dw%d", br_pending_w_reg_1, br_pending_w_reg_2);
	else if(br_pending_w_reg == 3)
	  gzprintf(data->deptrace, "w%dw%dw%d", br_pending_w_reg_1, br_pending_w_reg_2, br_pending_w_reg_3);
	else if(br_pending_w_reg == 4)
	  gzprintf(data->deptrace, "w%dw%dw%dw%d", br_pending_w_reg_1, br_pending_w_reg_2, br_pending_w_reg_3, br_pending_w_reg_4);
	else if(br_pending_w_reg != 0)
	  DR_ASSERT(false);
	gzprintf(data->deptrace,"t%d", (ptr_uint_t)br_pending_target - (ptr_uint_t)br_pending_pc); 
	if(((ptr_uint_t)ins_ref->pc - (ptr_uint_t)br_pending_pc) == 4)
	  gzprintf(data->deptrace,"\n");
	else
	  gzprintf(data->deptrace,"*\n");
	br_pending_cb = false;
	br_pending_r_reg = 0;
	br_pending_r_reg_1 = 0;
	br_pending_r_reg_2 = 0;
	br_pending_r_reg_3 = 0;
	br_pending_r_reg_4 = 0;
	
	br_pending_w_reg = 0;
	br_pending_w_reg_1 = 0;
	br_pending_w_reg_2 = 0;
	br_pending_w_reg_3 = 0;
	br_pending_w_reg_4 = 0;
      }
      
      if(br_pending_ncb){
	//gzprintf(data->deptrace, "J%d "PIFX"", br_pending_pcdiff, (ptr_uint_t)br_pending_target);
	gzprintf(data->deptrace, "J%d", br_pending_pcdiff);
	if(br_pending_r_reg == 1)  // read printing
	  gzprintf(data->deptrace, "r%d",br_pending_r_reg_1);
	else if(br_pending_r_reg == 2)
	  gzprintf(data->deptrace, "r%dr%d", br_pending_r_reg_1, br_pending_r_reg_2);
	else if(br_pending_r_reg == 3)
	  gzprintf(data->deptrace, "r%dr%dr%d", br_pending_r_reg_1, br_pending_r_reg_2, br_pending_r_reg_3);
	else if(br_pending_r_reg == 4)
	  gzprintf(data->deptrace, "r%dr%dr%dr%d", br_pending_r_reg_1, br_pending_r_reg_2, br_pending_r_reg_3, br_pending_r_reg_4);
	else if(br_pending_r_reg != 0)
	  DR_ASSERT(false);
	if(br_pending_w_reg == 1)  // write printing
	  gzprintf(data->deptrace, "w%d",br_pending_w_reg_1);
	else if(br_pending_w_reg == 2)
	  gzprintf(data->deptrace, "w%dw%d", br_pending_w_reg_1, br_pending_w_reg_2);
	else if(br_pending_w_reg == 3)
	  gzprintf(data->deptrace, "w%dw%dw%d", br_pending_w_reg_1, br_pending_w_reg_2, br_pending_w_reg_3);
	else if(br_pending_w_reg == 4)
	  gzprintf(data->deptrace, "w%dw%dw%dw%d", br_pending_w_reg_1, br_pending_w_reg_2, br_pending_w_reg_3, br_pending_w_reg_4);
	else if(br_pending_w_reg != 0)
	  DR_ASSERT(false);
	gzprintf(data->deptrace, "t%d", (ptr_uint_t)br_pending_target - (ptr_uint_t)br_pending_pc);   
	//if(((ptr_uint_t)ins_ref->pc - (ptr_uint_t)br_pending_pc) == 4)
	gzprintf(data->deptrace,"\n");
	  //else
	  //gzprintf(data->deptrace,"*\n");
	br_pending_ncb = false;
	br_pending_r_reg = 0;
	br_pending_r_reg_1 = 0;
	br_pending_r_reg_2 = 0;
	br_pending_r_reg_3 = 0;
	br_pending_r_reg_4 = 0;

	br_pending_w_reg = 0;
	br_pending_w_reg_1 = 0;
	br_pending_w_reg_2 = 0;
	br_pending_w_reg_3 = 0;
	br_pending_w_reg_4 = 0;
      }
      
      if(ins_ref->opcode == 1 || ins_ref->opcode == 2){ //read or write
	if(ins_ref->opcode == 1){ //read
	  stat_load++;
	  if(marker_next_load){
	    app_pc store_pc;
	    int expected_dist;
	    //bool marked_ok = checkMarkCorrect(ins_ref->addr, f_marker,
	    //expected_dist, store_pc);
	    if(f_marker != 0){
	      if(!checkMarkedLoad(f_marker,ins_ref->addr))
		stat_incorrect++;
	    }
	    gzprintf(data->deptrace, "L%ds%d",pcdiff,f_marker);
	    if(ins_ref->read_registers == 1)  // read printing
	      gzprintf(data->deptrace, "r%d", ins_ref->r_reg_1);
	    else if(ins_ref->read_registers == 2)
	      gzprintf(data->deptrace, "r%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2);
	    else if(ins_ref->read_registers == 3)
	      gzprintf(data->deptrace, "r%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3);
	    else if(ins_ref->read_registers == 4)
	      gzprintf(data->deptrace, "r%dr%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3, ins_ref->r_reg_4);
	    else if(ins_ref->read_registers != 0)
	      DR_ASSERT(false);
	    if(ins_ref->write_registers == 1)  // write printing
	      gzprintf(data->deptrace, "w%d", ins_ref->w_reg_1);
	    else if(ins_ref->write_registers == 2)
	      gzprintf(data->deptrace, "w%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2);
	    else if(ins_ref->write_registers == 3)
	      gzprintf(data->deptrace, "w%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3);
	    else if(ins_ref->write_registers == 4)
	      gzprintf(data->deptrace, "w%dw%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3, ins_ref->w_reg_4);
	    else if(ins_ref->read_registers != 0)
	      DR_ASSERT(false);
	    gzprintf(data->deptrace, " "PIFX" %d\n", (ptr_uint_t)ins_ref->addr,ins_ref->size);
	    marker_next_load = false;
	    f_marker = 0;
	    stat_marked++;
	  }
	  else{
	    gzprintf(data->deptrace, "L%d",pcdiff);
	    if(ins_ref->read_registers == 1)  // read printing
	      gzprintf(data->deptrace, "r%d", ins_ref->r_reg_1);
	    else if(ins_ref->read_registers == 2)
	      gzprintf(data->deptrace, "r%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2);
	    else if(ins_ref->read_registers == 3)
	      gzprintf(data->deptrace, "r%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3);
	    else if(ins_ref->read_registers == 4)
	      gzprintf(data->deptrace, "r%dr%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3, ins_ref->r_reg_4);
	    else if(ins_ref->read_registers != 0)
	      DR_ASSERT(false);
	    if(ins_ref->write_registers == 1)  // write printing
	      gzprintf(data->deptrace, "w%d", ins_ref->w_reg_1);
	    else if(ins_ref->write_registers == 2)
	      gzprintf(data->deptrace, "w%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2);
	    else if(ins_ref->write_registers == 3)
	      gzprintf(data->deptrace, "w%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3);
	    else if(ins_ref->write_registers == 4)
	      gzprintf(data->deptrace, "w%dw%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3, ins_ref->w_reg_4);
	    else if(ins_ref->read_registers != 0)
	      DR_ASSERT(false);
	    gzprintf(data->deptrace, " "PIFX" %d\n", (ptr_uint_t)ins_ref->addr,ins_ref->size);
	  }
	}
	else if(ins_ref->opcode == 2){ //write
	  addStore(ins_ref->pc,ins_ref->addr);
	  addAddress(ins_ref->pc, ins_ref->addr);
	  gzprintf(data->deptrace, "S%d",pcdiff);
	  if(ins_ref->read_registers == 1)  // read printing
	    gzprintf(data->deptrace, "r%d", ins_ref->r_reg_1);
	  else if(ins_ref->read_registers == 2)
	    gzprintf(data->deptrace, "r%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2);
	  else if(ins_ref->read_registers == 3)
	    gzprintf(data->deptrace, "r%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3);
	  else if(ins_ref->read_registers == 4)
	    gzprintf(data->deptrace, "r%dr%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3, ins_ref->r_reg_4);
	  else if(ins_ref->read_registers != 0)
	    DR_ASSERT(false);
	  if(ins_ref->write_registers == 1)  // write printing
	    gzprintf(data->deptrace, "w%d", ins_ref->w_reg_1);
	  else if(ins_ref->write_registers == 2)
	    gzprintf(data->deptrace, "w%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2);
	  else if(ins_ref->write_registers == 3)
	    gzprintf(data->deptrace, "w%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3);
	  else if(ins_ref->write_registers == 4)
	    gzprintf(data->deptrace, "w%dw%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3, ins_ref->w_reg_4);
	  else if(ins_ref->write_registers != 0){
	    printf("read_register:: %d\n",ins_ref->read_registers);
	    DR_ASSERT(false);
	  }
	  gzprintf(data->deptrace," "PIFX" %d\n", (ptr_uint_t)ins_ref->addr,ins_ref->size);
	}
      }
      else if (ins_ref->opcode == 3){ //Branch
	DR_ASSERT(!br_pending_cb || !br_pending_ncb);
	if(ins_ref->is_cb)
	  br_pending_cb = true;
	else
	  br_pending_ncb = true;
	br_pending_target = ins_ref->target;
	br_pending_pc = ins_ref->pc;
	br_pending_pcdiff = pcdiff;
	br_pending_r_reg = ins_ref->read_registers;
	br_pending_r_reg_1 = ins_ref->r_reg_1;
	br_pending_r_reg_2 = ins_ref->r_reg_2;
	br_pending_r_reg_3 = ins_ref->r_reg_3;
	br_pending_r_reg_4 = ins_ref->r_reg_4;
	
	br_pending_w_reg = ins_ref->write_registers;
	br_pending_w_reg_1 = ins_ref->w_reg_1;
	br_pending_w_reg_2 = ins_ref->w_reg_2;
	br_pending_w_reg_3 = ins_ref->w_reg_3;
	br_pending_w_reg_4 = ins_ref->w_reg_4;
      }
      else if (ins_ref->opcode == 8){ //other isntruction
	gzprintf(data->deptrace, "%d", pcdiff);
	if(ins_ref->read_registers == 1)  // read printing
	  gzprintf(data->deptrace, "r%d", ins_ref->r_reg_1);
	else if(ins_ref->read_registers == 2)
	  gzprintf(data->deptrace, "r%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2);
	else if(ins_ref->read_registers == 3)
	  gzprintf(data->deptrace, "r%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3);
	else if(ins_ref->read_registers == 4)
	  gzprintf(data->deptrace, "r%dr%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3, ins_ref->r_reg_4);
	else if(ins_ref->read_registers != 0)
	  DR_ASSERT(false);
	if(ins_ref->write_registers == 1)  // write printing
	  gzprintf(data->deptrace, "w%d", ins_ref->w_reg_1);
	else if(ins_ref->write_registers == 2)
	  gzprintf(data->deptrace, "w%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2);
	else if(ins_ref->write_registers == 3)
	  gzprintf(data->deptrace, "w%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3);
	else if(ins_ref->write_registers == 4)
	  gzprintf(data->deptrace, "w%dw%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3, ins_ref->w_reg_4);
	else if(ins_ref->write_registers != 0)
	  DR_ASSERT(false);
	gzprintf(data->deptrace, "\n");
      }
      else if (ins_ref->opcode == 4){ //floating add/sub
	gzprintf(data->deptrace, "A%d", pcdiff);
	if(ins_ref->read_registers == 1)  // read printing
	  gzprintf(data->deptrace, "r%d", ins_ref->r_reg_1);
	else if(ins_ref->read_registers == 2)
	  gzprintf(data->deptrace, "r%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2);
	else if(ins_ref->read_registers == 3)
	  gzprintf(data->deptrace, "r%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3);
	else if(ins_ref->read_registers == 4)
	  gzprintf(data->deptrace, "r%dr%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3, ins_ref->r_reg_4);
	else if(ins_ref->read_registers != 0)
	  DR_ASSERT(false);
	if(ins_ref->write_registers == 1)  // write printing
	  gzprintf(data->deptrace, "w%d", ins_ref->w_reg_1);
	else if(ins_ref->write_registers == 2)
	  gzprintf(data->deptrace, "w%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2);
	else if(ins_ref->write_registers == 3)
	  gzprintf(data->deptrace, "w%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3);
	else if(ins_ref->write_registers == 4)
	  gzprintf(data->deptrace, "w%dw%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3, ins_ref->w_reg_4);
	else if(ins_ref->write_registers != 0)
	  DR_ASSERT(false);
	gzprintf(data->deptrace, "\n");
      }
      else if (ins_ref->opcode == 5){ //floating Mul
	gzprintf(data->deptrace, "M%d", pcdiff);
	if(ins_ref->read_registers == 1)  // read printing
	  gzprintf(data->deptrace, "r%d", ins_ref->r_reg_1);
	else if(ins_ref->read_registers == 2)
	  gzprintf(data->deptrace, "r%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2);
	else if(ins_ref->read_registers == 3)
	  gzprintf(data->deptrace, "r%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3);
	else if(ins_ref->read_registers == 4)
	  gzprintf(data->deptrace, "r%dr%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3, ins_ref->r_reg_4);
	else if(ins_ref->read_registers != 0)
	  DR_ASSERT(false);
	if(ins_ref->write_registers == 1)  // write printing
	  gzprintf(data->deptrace, "w%d", ins_ref->w_reg_1);
	else if(ins_ref->write_registers == 2)
	  gzprintf(data->deptrace, "w%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2);
	else if(ins_ref->write_registers == 3)
	  gzprintf(data->deptrace, "w%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3);
	else if(ins_ref->write_registers == 4)
	  gzprintf(data->deptrace, "w%dw%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3, ins_ref->w_reg_4);
	else if(ins_ref->write_registers != 0)
	  DR_ASSERT(false);
	gzprintf(data->deptrace, "\n");
	
      }
      else if (ins_ref->opcode == 6){ //floating Div
	gzprintf(data->deptrace, "D%d", pcdiff);
	if(ins_ref->read_registers == 1)  // read printing
	  gzprintf(data->deptrace, "r%d", ins_ref->r_reg_1);
	else if(ins_ref->read_registers == 2)
	  gzprintf(data->deptrace, "r%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2);
	else if(ins_ref->read_registers == 3)
	  gzprintf(data->deptrace, "r%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3);
	else if(ins_ref->read_registers == 4)
	  gzprintf(data->deptrace, "r%dr%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3, ins_ref->r_reg_4);
	else if(ins_ref->read_registers != 0)
	  DR_ASSERT(false);
	if(ins_ref->write_registers == 1)  // write printing
	  gzprintf(data->deptrace, "w%d", ins_ref->w_reg_1);
	else if(ins_ref->write_registers == 2)
	  gzprintf(data->deptrace, "w%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2);
	else if(ins_ref->write_registers == 3)
	  gzprintf(data->deptrace, "w%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3);
	else if(ins_ref->write_registers == 4)
	  gzprintf(data->deptrace, "w%dw%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3, ins_ref->w_reg_4);
	else if(ins_ref->write_registers != 0)
	  DR_ASSERT(false);
	gzprintf(data->deptrace, "\n");
	
      }
      else if (ins_ref->opcode == 7){ //floating sqrt
	gzprintf(data->deptrace, "Q%d", pcdiff);
	if(ins_ref->read_registers == 1)  // read printing
	  gzprintf(data->deptrace, "r%d", ins_ref->r_reg_1);
	else if(ins_ref->read_registers == 2)
	  gzprintf(data->deptrace, "r%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2);
	else if(ins_ref->read_registers == 3)
	  gzprintf(data->deptrace, "r%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3);
	else if(ins_ref->read_registers == 4)
	  gzprintf(data->deptrace, "r%dr%dr%dr%d", ins_ref->r_reg_1, ins_ref->r_reg_2, ins_ref->r_reg_3, ins_ref->r_reg_4);
	else if(ins_ref->read_registers != 0)
	  DR_ASSERT(false);
	if(ins_ref->write_registers == 1)  // write printing
	  gzprintf(data->deptrace, "w%d", ins_ref->w_reg_1);
	else if(ins_ref->write_registers == 2)
	  gzprintf(data->deptrace, "w%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2);
	else if(ins_ref->write_registers == 3)
	  gzprintf(data->deptrace, "w%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3);
	else if(ins_ref->write_registers == 4)
	  gzprintf(data->deptrace, "w%dw%dw%dw%d", ins_ref->w_reg_1, ins_ref->w_reg_2, ins_ref->w_reg_3, ins_ref->w_reg_4);
	else if(ins_ref->write_registers != 0)
	  DR_ASSERT(false);
	gzprintf(data->deptrace, "\n");
	
      }
      else if (ins_ref->opcode == 9){//marker begin 
	//printf("R11\n");
	marker_begin = true;
	marker_index = 0;//set index to 0
	for(int i = 0; i < 2;  i++) //set all values to 0
	  final_marker_value[i] = 0;
      }
      else if (ins_ref->opcode == 10){//marker end
	//printf("R10\n");
	DR_ASSERT(marker_begin);
	marker_end = true;
	f_marker = array_to_num(final_marker_value, marker_index);
	if(f_marker == 0)
	  stat_marked0++;
	else if(f_marker == 1)
	  stat_marked1++;
	else if(f_marker == 2)
	  stat_marked2++;
	else if(f_marker > 2)
	  stat_markedp2++;
	//printf("%d %d %d %d\n",stat_marked0, stat_marked1,stat_marked2,stat_markedp2);
	marker_next_load = true;
      }
      else if (ins_ref->opcode == 11){//marker dep
	//printf("%d\n",ins_ref->marker_value);
	//DR_ASSERT(marker_begin);
	final_marker_value[marker_index] = ins_ref->marker_value;
	marker_index++;
	DR_ASSERT(marker_index < (int)sizeof(final_marker_value));
      }
      
      data->num_refs++;
    }
    BUF_PTR(data->seg_base) = data->buf_base;
}

static void
clean_call(void)
{
    void *drcontext = dr_get_current_drcontext();
    ARMTracer(drcontext);
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
insert_save_write_registers(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			    reg_id_t scratch, int write_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(write_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, write_registers)),
				    opnd_create_reg(scratch)));
}

static void
insert_save_write_registers1(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			    reg_id_t scratch, int write_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(write_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, w_reg_1)),
				    opnd_create_reg(scratch)));
}

static void
insert_save_write_registers2(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			     reg_id_t scratch, int write_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(write_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, w_reg_2)),
				    opnd_create_reg(scratch)));
}
static void
insert_save_write_registers3(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			     reg_id_t scratch, int write_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(write_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, w_reg_3)),
				    opnd_create_reg(scratch)));
}
static void
insert_save_write_registers4(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			     reg_id_t scratch, int write_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(write_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, w_reg_4)),
				    opnd_create_reg(scratch)));
}


static void
insert_save_read_registers(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			   reg_id_t scratch, int read_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(read_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, read_registers)),
				    opnd_create_reg(scratch)));
}

static void
insert_save_read_registers1(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			   reg_id_t scratch, int read_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(read_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, r_reg_1)),
				    opnd_create_reg(scratch)));
}

static void
insert_save_read_registers2(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			    reg_id_t scratch, int read_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(read_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, r_reg_2)),
				    opnd_create_reg(scratch)));
}
static void
insert_save_read_registers3(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			    reg_id_t scratch, int read_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(read_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, r_reg_3)),
				    opnd_create_reg(scratch)));
}
static void
insert_save_read_registers4(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			    reg_id_t scratch, int read_registers)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(read_registers)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, r_reg_4)),
				    opnd_create_reg(scratch)));
}

static void
insert_save_branch_type(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
			    reg_id_t scratch, int is_cb)
{
  scratch = reg_resize_to_opsz(scratch, OPSZ_2);
  MINSERT(ilist, where,
	  XINST_CREATE_load_int(drcontext, opnd_create_reg(scratch),
				OPND_CREATE_INT16(is_cb)));
  MINSERT(ilist, where,
	  XINST_CREATE_store_2bytes(
				    drcontext, OPND_CREATE_MEM16(base, offsetof(ins_ref_t, is_cb)),
				    opnd_create_reg(scratch)));
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
insert_save_marker_value(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t base,
	       reg_id_t scratch, int marker_value)
{
  instrlist_insert_mov_immed_ptrsz(drcontext, marker_value, opnd_create_reg(scratch),
				   ilist, where, NULL, NULL);
  MINSERT(ilist, where,
	  XINST_CREATE_store(drcontext,
			     OPND_CREATE_MEMPTR(base, offsetof(ins_ref_t, marker_value)),
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
instrument_marker_end(void *drcontext, instrlist_t *ilist, instr_t *where, int marker_value, int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);

  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  

  //insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
  //                  instr_get_opcode(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     10);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    1);
  insert_save_marker_value(drcontext, ilist, where, reg_ptr, reg_tmp,
  		      marker_value);
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}

static void
instrument_marker_value(void *drcontext, instrlist_t *ilist, instr_t *where, int marker_value, int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  
  //insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
  //                  instr_get_opcode(where));
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     11);
  insert_save_other(drcontext, ilist, where, reg_ptr, reg_tmp,
		    1);
  insert_save_marker_value(drcontext, ilist, where, reg_ptr, reg_tmp,
                    marker_value);
  insert_update_buf_ptr(drcontext, ilist, where, reg_ptr, sizeof(ins_ref_t));

  if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS ||
      drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
    DR_ASSERT(false);
}


static void
instrument_marker_begin(void *drcontext, instrlist_t *ilist, instr_t *where , int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  
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
instrument_instr(void *drcontext, instrlist_t *ilist, instr_t *where, int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
    insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
    insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
    insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
    insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

    insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
    insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

    insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
    insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

    insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
    insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
    
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
instrument_fp_addsub(void *drcontext, instrlist_t *ilist, instr_t *where, int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  
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
instrument_fp_mul(void *drcontext, instrlist_t *ilist, instr_t *where, int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  
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
instrument_fp_div(void *drcontext, instrlist_t *ilist, instr_t *where, int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  
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
instrument_fp_sqrt(void *drcontext, instrlist_t *ilist, instr_t *where, int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  
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
	       bool write, int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  
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
instrument_branch(void *drcontext, instrlist_t *ilist, instr_t *where, int is_cb,  int write_registers, int read_registers, int w_arr[3], int r_arr[3])
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
  insert_save_read_registers(drcontext, ilist, where, reg_ptr, reg_tmp, read_registers);
  insert_save_write_registers(drcontext, ilist, where, reg_ptr, reg_tmp, write_registers);
  insert_save_read_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[0]);
  insert_save_write_registers1(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[0]);

  insert_save_read_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[1]);
  insert_save_write_registers2(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[1]);

  insert_save_read_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[2]);
  insert_save_write_registers3(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[2]);

  insert_save_read_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, r_arr[3]);
  insert_save_write_registers4(drcontext, ilist, where, reg_ptr, reg_tmp, w_arr[3]);
  
  insert_save_opcode(drcontext, ilist, where, reg_ptr, reg_tmp,
		     3);
  insert_save_branch_type(drcontext, ilist, where, reg_ptr, reg_tmp, is_cb);
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

  int w_arr[3] = {0}; //MAX 4
  int r_arr[4] = {0}; //MAX 4
  
  int w_reg = 0;
  int r_reg = 0;
  for (int i = 0; i < instr_num_srcs(instr); i++) {
    if(opnd_is_reg(instr_get_src(instr, i))){
      const char *reg_name_src = get_register_name(opnd_get_reg(instr_get_src(instr,i)));
      if(!strcmp(reg_name_src, "xzr") || !strcmp(reg_name_src, "wzr")){
	r_arr[r_reg] = 63; // 0-30 31 int GPR 31-62 32 fp/vector GPR
	r_reg++;
	DR_ASSERT(r_reg <= 4);
      }
      else if(reg_name_src[1] == '0' || reg_name_src[1] == '1' ||
      	 reg_name_src[1] == '2' || reg_name_src[1] == '3' ||
      	 reg_name_src[1] == '4' || reg_name_src[1] == '5' ||
      	 reg_name_src[1] == '6' || reg_name_src[1] == '7' ||
      	 reg_name_src[1] == '8' || reg_name_src[1] == '9' )
	{
	  if(reg_name_src[0] == 'w' || reg_name_src[0] == 'x')
	    r_arr[r_reg] = reg2reg(reg_name_src);
	  else if(reg_name_src[0] == 'b' || reg_name_src[0] == 'h' ||
		  reg_name_src[0] == 's' || reg_name_src[0] == 'd' ||
		  reg_name_src[0] == 'q')
	    r_arr[r_reg] = reg2regfp(reg_name_src);
	  else
	    DR_ASSERT(false);
	  //printf("SCR %d %d %s\n",instr_num_srcs(instr),r_arr[r_reg],get_register_name(opnd_get_reg(instr_get_src(instr,i))));
	  r_reg++;
	  DR_ASSERT(r_reg <= 4);
	}
    }
  }
  for (int i = 0; i < instr_num_dsts(instr); i++) {
    if(opnd_is_reg(instr_get_dst(instr, i))){
      const char *reg_name_dst = get_register_name(opnd_get_reg(instr_get_dst(instr,i)));
      if(!strcmp(reg_name_dst, "xzr") || !strcmp(reg_name_dst, "wzr")){
	w_arr[w_reg] = 63;
	w_reg++;
	DR_ASSERT(w_reg <= 4);
      }
      else if(reg_name_dst[1] == '0' || reg_name_dst[1] == '1' ||
	 reg_name_dst[1] == '2' || reg_name_dst[1] == '3' ||
	 reg_name_dst[1] == '4' || reg_name_dst[1] == '5' ||
	 reg_name_dst[1] == '6' || reg_name_dst[1] == '7' ||
	 reg_name_dst[1] == '8' || reg_name_dst[1] == '9' )
	{
	  if(reg_name_dst[0] == 'w' || reg_name_dst[0] == 'x')
	    w_arr[w_reg] = reg2reg(reg_name_dst);
	  else if(reg_name_dst[0] == 'b' || reg_name_dst[0] == 'h' ||
		  reg_name_dst[0] == 's' || reg_name_dst[0] == 'd' ||
		  reg_name_dst[0] == 'q')
	    w_arr[w_reg] = reg2regfp(reg_name_dst);
	  else
	    DR_ASSERT(false);
	  w_reg++;
	  DR_ASSERT(w_reg <= 4);
	  //printf("DST %d %d %s\n",instr_num_dsts(instr),w_arr[w_reg],get_register_name(opnd_get_reg(instr_get_dst(instr,i))));
	}
    }
  }

  if(instr_is_cti(instr)){
    if(instr_is_cbr(instr)){ //conditional branches
      instrument_branch(drcontext, bb, instr, 1, w_reg, r_reg, w_arr, r_arr);
    }
    else //all other branches 
      instrument_branch(drcontext, bb, instr, 0, w_reg, r_reg, w_arr, r_arr);
  }
  else if(instr_reads_memory(instr) || instr_writes_memory(instr)){
    //FIXME::
    //instrument_instr(drcontext, bb, instr); //to instrument mem operation other then load store
    for (i = 0; i < instr_num_srcs(instr); i++) {
      if (opnd_is_memory_reference(instr_get_src(instr, i)))
	instrument_mem(drcontext, bb, instr, instr_get_src(instr, i), false, w_reg, r_reg, w_arr, r_arr);
    }
    
    for (i = 0; i < instr_num_dsts(instr); i++) {
      if (opnd_is_memory_reference(instr_get_dst(instr, i)))
	instrument_mem(drcontext, bb, instr, instr_get_dst(instr, i), true, w_reg, r_reg, w_arr, r_arr);
    }
  }
  else if(!strcmp(decode_opcode_name(instr_get_opcode(instr)), "fadd") || !strcmp(decode_opcode_name(instr_get_opcode(instr)),"fsub"))
    { //fadd fsub
      instrument_fp_addsub(drcontext, bb, instr, w_reg, r_reg, w_arr, r_arr);
    }
  else if(!strcmp(decode_opcode_name(instr_get_opcode(instr)), "fmul")) //fmul
    {
      instrument_fp_mul(drcontext, bb, instr, w_reg, r_reg, w_arr, r_arr);
    }
  else if(!strcmp(decode_opcode_name(instr_get_opcode(instr)), "fdiv")) //fdiv
    {
      instrument_fp_div(drcontext, bb, instr, w_reg, r_reg, w_arr, r_arr);
    }
  else if(!strcmp(decode_opcode_name(instr_get_opcode(instr)), "fsqrt")) //sqrt 
    {
      instrument_fp_sqrt(drcontext, bb, instr, w_reg, r_reg, w_arr, r_arr);
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
	  instrument_marker_begin(drcontext, bb, instr, w_reg, r_reg, w_arr, r_arr);
	  marker = true; //set marker
	}
	if(!strcmp(get_register_name(reg_id), "x10") && marker){
	  DR_ASSERT(marker);
	  marker = false;
	  instrument_marker_end(drcontext, bb, instr, atoi(marker_value), w_reg, r_reg, w_arr, r_arr);
	}
	if(!strcmp(get_register_name(reg_id), "x0") && marker){
	  instrument_marker_value(drcontext, bb, instr, 0, w_reg, r_reg, w_arr, r_arr);
	}
	if(!strcmp(get_register_name(reg_id), "x1") && marker){
	  instrument_marker_value(drcontext, bb, instr, 1, w_reg, r_reg, w_arr, r_arr);
	}
	if (!strcmp(get_register_name(reg_id), "x2") && marker){
	  instrument_marker_value(drcontext, bb, instr, 2, w_reg, r_reg, w_arr, r_arr);
	}
	if (!strcmp(get_register_name(reg_id), "x3") && marker){
	  instrument_marker_value(drcontext, bb, instr, 3, w_reg, r_reg, w_arr, r_arr);
	}
	if (!strcmp(get_register_name(reg_id), "x4") && marker){
	  instrument_marker_value(drcontext, bb, instr, 4, w_reg, r_reg, w_arr, r_arr);
	}
	if (!strcmp(get_register_name(reg_id), "x5") && marker){
	  instrument_marker_value(drcontext, bb, instr, 5, w_reg, r_reg, w_arr, r_arr);
	}
	if (!strcmp(get_register_name(reg_id), "x6") && marker){
	  instrument_marker_value(drcontext, bb, instr, 6, w_reg, r_reg, w_arr, r_arr);
	}
	if (!strcmp(get_register_name(reg_id), "x7") && marker){
	  instrument_marker_value(drcontext, bb, instr, 7, w_reg, r_reg, w_arr, r_arr);
	}
	if (!strcmp(get_register_name(reg_id), "x9") && marker){
	  instrument_marker_value(drcontext, bb, instr, 9, w_reg, r_reg, w_arr, r_arr);
	}
      }
    }
  else
    instrument_instr(drcontext, bb, instr, w_reg, r_reg, w_arr, r_arr);
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
    per_thread_t *log = dr_thread_alloc(drcontext, sizeof(per_thread_t));
    
    DR_ASSERT(data != NULL);
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
    //data->log =
    // log_file_open(client_id, drcontext, NULL /* using client lib path */, "ARMTracer",
    //	    DR_FILE_ALLOW_LARGE); //trace file .trc
        
    //data->logf = log_stream_from_file(data->log);
    data->deptrace = trace_file_open(client_id, drcontext, NULL /* using client lib path */, "ARMTracer",
				     DR_FILE_ALLOW_LARGE);
    //gzprintf(data->deptrace, "INITIAL PC HERE\n");
    //fprintf(data->logf, "INITIAL PC HERE\n");

    logs = log_stream_from_file(log_file_open(client_id, drcontext, NULL /* using client lib path */, "ARMTracer-log",
					      DR_FILE_ALLOW_LARGE)); //log file .log
    fprintf(logs, "SMDA stats file\n");
    
}

static void
event_thread_exit(void *drcontext)
{
    per_thread_t *data;
    ARMTracer(drcontext); /* dump any remaining buffer entries */
    data = drmgr_get_tls_field(drcontext, tls_idx);
    dr_mutex_lock(mutex);
    num_refs += data->num_refs;
    dr_mutex_unlock(mutex);
    //log_stream_close(data->logf); /* closes fd too */
    dr_raw_mem_free(data->buf_base, MEM_BUF_SIZE);
    dr_thread_free(drcontext, data, sizeof(per_thread_t));
    gzprintf(data->deptrace, ""PIFX"\n", endpc);
    gzclose(data->deptrace);
    
}

static void
event_exit(void)
{
    dr_log(NULL, DR_LOG_ALL, 1, "Client 'ARMTracer' num refs seen: " SZFMT "\n", num_refs);
    if (!dr_raw_tls_cfree(tls_offs, INSTRACE_TLS_COUNT))
        DR_ASSERT(false);

    if (!drmgr_unregister_tls_field(tls_idx) ||
        !drmgr_unregister_thread_init_event(event_thread_init) ||
        !drmgr_unregister_thread_exit_event(event_thread_exit) ||
        !drmgr_unregister_bb_insertion_event(event_app_instruction) ||
        drreg_exit() != DRREG_SUCCESS)
        DR_ASSERT(false);
    float lmarked = (((float)stat_marked/stat_load)*100);
    float lmarked0 = (((float)stat_marked0/stat_marked)*100);
    float lmarked1 = (((float)stat_marked1/stat_marked)*100);
    float lmarked2 = (((float)stat_marked2/stat_marked)*100);
    float lmarkedp2 = (((float)stat_markedp2/stat_marked)*100);
    float lincorrect = (((float)stat_incorrect/stat_marked)*100);
    
    //printSB(90,100);
    //printLB(0,10);
    
    fprintf(logs,
	    "Loads Executed: %d\n" 
	    "Loads Marked: %d (%.4f%)\n"
	    "Marked at 0: %d (%.4f%)\n"
	    "Marked at 1: %d (%.4f%)\n"
	    "Marked at 2: %d (%.4f%)\n"
	    "Marked at 2+: %d (%.4f%)\n"
	    "Marked incorrect: %d (%.4f%)\n",
	    stat_load,
	    stat_marked,lmarked,
	    stat_marked0,lmarked0,
	    stat_marked1,lmarked1,
	    stat_marked2,lmarked2,
	    stat_markedp2,lmarkedp2,
	    stat_incorrect,lincorrect
	    );
    log_stream_close(logs);
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

    dr_log(NULL, DR_LOG_ALL, 1, "Client 'ARMTracer' initializing\n");
}
