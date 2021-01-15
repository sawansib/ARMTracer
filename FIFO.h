#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "utils.h"
#include "drutil.h"
#include "drx.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define STORE_BUFFER_SIZE 100
#define MARKED_LOAD_BUFFER_SIZE 100


struct SB {
  app_pc pc;
  app_pc address;
};

struct MLB {
  app_pc pc;
  app_pc address;
  int marker;
  bool checked;
};

struct SB StoreBuffer[STORE_BUFFER_SIZE];
static int last_store_size = 0;
static int last_store_begin = 0;


struct MLB LoadBuffer[MARKED_LOAD_BUFFER_SIZE];
static int last_load_size = 0;
static int last_load_begin = 0;

void addStore(app_pc pc, app_pc addr) {
  StoreBuffer[last_store_begin].pc = pc;
  StoreBuffer[last_store_begin].address = addr;
  if(last_store_begin >= STORE_BUFFER_SIZE - 1 ){
    for(int i = 0; i < STORE_BUFFER_SIZE ; i++){
      StoreBuffer[i].pc = StoreBuffer[i+1].pc;
    }
    last_store_begin = STORE_BUFFER_SIZE - 1;
  }
  else
    last_store_begin++;
}

void addLoad(app_pc pc, app_pc addr, int marker) {
  LoadBuffer[last_load_begin].pc = pc;
  LoadBuffer[last_load_begin].address = addr;
  LoadBuffer[last_load_begin].marker = marker;
  if(last_load_begin >= MARKED_LOAD_BUFFER_SIZE - 1 ){
    for(int i = 0; i < MARKED_LOAD_BUFFER_SIZE ; i++){
      LoadBuffer[i].pc = LoadBuffer[i+1].pc;
    }
    last_load_begin = MARKED_LOAD_BUFFER_SIZE - 1;
  }
  else
    last_load_begin++;
}

int getSBindex(){return last_store_begin;}
int getLBindex(){return last_load_begin;}

void printSB(int here, int there){
  DR_ASSERT(there <= STORE_BUFFER_SIZE);
  for (int i = here ; i < there ; i++)
    printf("SB: PC "PIFX" ADD "PIFX"\n",StoreBuffer[i].pc,StoreBuffer[i].address);
}
void printLB(int here, int there){
  DR_ASSERT(there <= MARKED_LOAD_BUFFER_SIZE);
  for (int i = here ; i < there ; i++)
    printf("LB: PC "PIFX" ADD "PIFX" MARK %d\n",LoadBuffer[i].pc,LoadBuffer[i].address,LoadBuffer[i].marker);
}
