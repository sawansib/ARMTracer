#include <inttypes.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h> 
#include <assert.h>

int reg2reg(const char *reg_name){

  if (strcmp(reg_name, "w0") == 0 || strcmp(reg_name, "x0") == 0)
    return 0;
  else if (strcmp(reg_name, "w1") == 0 || strcmp(reg_name, "x1") == 0)
    return 1;
  else if (strcmp(reg_name, "w2") == 0 || strcmp(reg_name, "x2") == 0)
    return 2;
  else if (strcmp(reg_name, "w3") == 0 || strcmp(reg_name, "x3") == 0)
    return 3;
  else if (strcmp(reg_name, "w4") == 0 || strcmp(reg_name, "x4") == 0)
    return 4;
  else if (strcmp(reg_name, "w5") == 0 || strcmp(reg_name, "x5") == 0)
    return 5;
  else if (strcmp(reg_name, "w6") == 0 || strcmp(reg_name, "x6") == 0)
    return 6;
  else if (strcmp(reg_name, "w7") == 0 || strcmp(reg_name, "x7") == 0)
    return 7;
  else if (strcmp(reg_name, "w8") == 0 || strcmp(reg_name, "x8") == 0)
    return 8;
  else if (strcmp(reg_name, "w9") == 0 || strcmp(reg_name, "x9") == 0)
    return 9;
  else if (strcmp(reg_name, "w10") == 0 || strcmp(reg_name, "x10") == 0)
    return 10;
  else if (strcmp(reg_name, "w11") == 0 || strcmp(reg_name, "x11") == 0)
    return 11;
  else if (strcmp(reg_name, "w12") == 0 || strcmp(reg_name, "x12") == 0)
    return 12;
  else if (strcmp(reg_name, "w13") == 0 || strcmp(reg_name, "x13") == 0)
    return 13;
  else if (strcmp(reg_name, "w14") == 0 || strcmp(reg_name, "x14") == 0)
    return 14;
  else if (strcmp(reg_name, "w15") == 0 || strcmp(reg_name, "x15") == 0)
    return 15;
  else if (strcmp(reg_name, "w16") == 0 || strcmp(reg_name, "x16") == 0)
    return 16;
  else if (strcmp(reg_name, "w17") == 0 || strcmp(reg_name, "x17") == 0)
    return 17;
  else if (strcmp(reg_name, "w18") == 0 || strcmp(reg_name, "x18") == 0)
    return 18;
  else if (strcmp(reg_name, "w19") == 0 || strcmp(reg_name, "x19") == 0)
    return 19;
  else if (strcmp(reg_name, "w20") == 0 || strcmp(reg_name, "x20") == 0)
    return 20;
  else if (strcmp(reg_name, "w21") == 0 || strcmp(reg_name, "x21") == 0)
    return 21;
  else if (strcmp(reg_name, "w22") == 0 || strcmp(reg_name, "x22") == 0)
    return 22;
  else if (strcmp(reg_name, "w23") == 0 || strcmp(reg_name, "x23") == 0)
    return 23;
  else if (strcmp(reg_name, "w24") == 0 || strcmp(reg_name, "x24") == 0)
    return 24;
  else if (strcmp(reg_name, "w25") == 0 || strcmp(reg_name, "x25") == 0)
    return 25;
  else if (strcmp(reg_name, "w26") == 0 || strcmp(reg_name, "x26") == 0)
    return 26;
  else if (strcmp(reg_name, "w27") == 0 || strcmp(reg_name, "x27") == 0)
    return 27;
  else if (strcmp(reg_name, "w28") == 0 || strcmp(reg_name, "x28") == 0)
    return 28;
  else if (strcmp(reg_name, "w29") == 0 || strcmp(reg_name, "x29") == 0)
    return 29;
  else if (strcmp(reg_name, "w30") == 0 || strcmp(reg_name, "x30") == 0)
    return 30;
  //else if (strcmp(reg_name, "w31") == 0 || strcmp(reg_name, "x31") == 0)
  // return 31;
  else
    {
      printf("REG_NAME: %s not found! \n",reg_name);
      assert(false);
    }
}

int reg2regfp(const char *reg_name){

  if (strcmp(reg_name, "b0") == 0 || strcmp(reg_name, "h0") == 0 || strcmp(reg_name, "s0") == 0 || strcmp(reg_name, "d0") == 0 || strcmp(reg_name, "q0") == 0 )
    return 31;
  else if (strcmp(reg_name, "b1") == 0 || strcmp(reg_name, "h1") == 0 || strcmp(reg_name, "s1") == 0 || strcmp(reg_name, "d1") == 0 || strcmp(reg_name, "q1") == 0 )
    return 32;
  else if (strcmp(reg_name, "b2") == 0 || strcmp(reg_name, "h2") == 0 || strcmp(reg_name, "s2") == 0 || strcmp(reg_name, "d2") == 0 || strcmp(reg_name, "q2") == 0 )
    return 33;
  else if (strcmp(reg_name, "b3") == 0 || strcmp(reg_name, "h3") == 0 || strcmp(reg_name, "s3") == 0 || strcmp(reg_name, "d3") == 0 || strcmp(reg_name, "q3") == 0 )
    return 34;
  else if (strcmp(reg_name, "b4") == 0 || strcmp(reg_name, "h4") == 0 || strcmp(reg_name, "s4") == 0 || strcmp(reg_name, "d4") == 0 || strcmp(reg_name, "q4") == 0 )
    return 35;
  else if (strcmp(reg_name, "b5") == 0 || strcmp(reg_name, "h5") == 0 || strcmp(reg_name, "s5") == 0 || strcmp(reg_name, "d5") == 0 || strcmp(reg_name, "q5") == 0 )
    return 36;
  else if (strcmp(reg_name, "b6") == 0 || strcmp(reg_name, "h6") == 0 || strcmp(reg_name, "s6") == 0 || strcmp(reg_name, "d6") == 0 || strcmp(reg_name, "q6") == 0 )
    return 37;
  else if (strcmp(reg_name, "b7") == 0 || strcmp(reg_name, "h7") == 0 || strcmp(reg_name, "s7") == 0 || strcmp(reg_name, "d7") == 0 || strcmp(reg_name, "q7") == 0 )
    return 38;
  else if (strcmp(reg_name, "b8") == 0 || strcmp(reg_name, "h8") == 0 || strcmp(reg_name, "s8") == 0 || strcmp(reg_name, "d8") == 0 || strcmp(reg_name, "q8") == 0 )
    return 39;
  else if (strcmp(reg_name, "b9") == 0 || strcmp(reg_name, "h9") == 0 || strcmp(reg_name, "s9") == 0 || strcmp(reg_name, "d9") == 0 || strcmp(reg_name, "q9") == 0 )
    return 40;
  else if (strcmp(reg_name, "b10") == 0 || strcmp(reg_name, "h10") == 0 || strcmp(reg_name, "s10") == 0 || strcmp(reg_name, "d10") == 0 || strcmp(reg_name, "q10") == 0)
    return 41;
  else if (strcmp(reg_name, "b11") == 0 || strcmp(reg_name, "h11") == 0 || strcmp(reg_name, "s11") == 0 || strcmp(reg_name, "d11") == 0 || strcmp(reg_name, "q11") == 0)
    return 42;
  else if (strcmp(reg_name, "b12") == 0 || strcmp(reg_name, "h12") == 0 || strcmp(reg_name, "s12") == 0 || strcmp(reg_name, "d12") == 0 || strcmp(reg_name, "q12") == 0)
    return 43;
  else if (strcmp(reg_name, "b13") == 0 || strcmp(reg_name, "h13") == 0 || strcmp(reg_name, "s13") == 0 || strcmp(reg_name, "d13") == 0 || strcmp(reg_name, "q13") == 0)
    return 44;
  else if (strcmp(reg_name, "b14") == 0 || strcmp(reg_name, "h14") == 0 || strcmp(reg_name, "s14") == 0 || strcmp(reg_name, "d14") == 0 || strcmp(reg_name, "q14") == 0)
    return 45;
  else if (strcmp(reg_name, "b15") == 0 || strcmp(reg_name, "h15") == 0 || strcmp(reg_name, "s15") == 0 || strcmp(reg_name, "d15") == 0 || strcmp(reg_name, "q15") == 0)
    return 46;
  else if (strcmp(reg_name, "b16") == 0 || strcmp(reg_name, "h16") == 0 || strcmp(reg_name, "s16") == 0 || strcmp(reg_name, "d16") == 0 || strcmp(reg_name, "q16") == 0)
    return 47;
  else if (strcmp(reg_name, "b17") == 0 || strcmp(reg_name, "h17") == 0 || strcmp(reg_name, "s17") == 0 || strcmp(reg_name, "d17") == 0 || strcmp(reg_name, "q17") == 0)
    return 48;
  else if (strcmp(reg_name, "b18") == 0 || strcmp(reg_name, "h18") == 0 || strcmp(reg_name, "s18") == 0 || strcmp(reg_name, "d18") == 0 || strcmp(reg_name, "q18") == 0)
    return 49;
  else if (strcmp(reg_name, "b19") == 0 || strcmp(reg_name, "h19") == 0 || strcmp(reg_name, "s19") == 0 || strcmp(reg_name, "d19") == 0 || strcmp(reg_name, "q19") == 0)
    return 50;
  else if (strcmp(reg_name, "b20") == 0 || strcmp(reg_name, "h20") == 0 || strcmp(reg_name, "s20") == 0 || strcmp(reg_name, "d20") == 0 || strcmp(reg_name, "q20") == 0)
    return 51;
  else if (strcmp(reg_name, "b21") == 0 || strcmp(reg_name, "h21") == 0 || strcmp(reg_name, "s21") == 0 || strcmp(reg_name, "d21") == 0 || strcmp(reg_name, "q21") == 0)
    return 52;
  else if (strcmp(reg_name, "b22") == 0 || strcmp(reg_name, "h22") == 0 || strcmp(reg_name, "s22") == 0 || strcmp(reg_name, "d22") == 0 || strcmp(reg_name, "q22") == 0)
    return 53;
  else if (strcmp(reg_name, "b23") == 0 || strcmp(reg_name, "h23") == 0 || strcmp(reg_name, "s23") == 0 || strcmp(reg_name, "d23") == 0 || strcmp(reg_name, "q23") == 0)
    return 54;
  else if (strcmp(reg_name, "b24") == 0 || strcmp(reg_name, "h24") == 0 || strcmp(reg_name, "s24") == 0 || strcmp(reg_name, "d24") == 0 || strcmp(reg_name, "q24") == 0)
    return 55;
  else if (strcmp(reg_name, "b25") == 0 || strcmp(reg_name, "h25") == 0 || strcmp(reg_name, "s25") == 0 || strcmp(reg_name, "d25") == 0 || strcmp(reg_name, "q25") == 0)
    return 56;
  else if (strcmp(reg_name, "b26") == 0 || strcmp(reg_name, "h26") == 0 || strcmp(reg_name, "s26") == 0 || strcmp(reg_name, "d26") == 0 || strcmp(reg_name, "q26") == 0)
    return 57;
  else if (strcmp(reg_name, "b27") == 0 || strcmp(reg_name, "h27") == 0 || strcmp(reg_name, "s27") == 0 || strcmp(reg_name, "d27") == 0 || strcmp(reg_name, "q27") == 0)
    return 58;
  else if (strcmp(reg_name, "b28") == 0 || strcmp(reg_name, "h28") == 0 || strcmp(reg_name, "s28") == 0 || strcmp(reg_name, "d28") == 0 || strcmp(reg_name, "q28") == 0)
    return 59;
  else if (strcmp(reg_name, "b29") == 0 || strcmp(reg_name, "h29") == 0 || strcmp(reg_name, "s29") == 0 || strcmp(reg_name, "d29") == 0 || strcmp(reg_name, "q29") == 0)
    return 60;
  else if (strcmp(reg_name, "b30") == 0 || strcmp(reg_name, "h30") == 0 || strcmp(reg_name, "s30") == 0 || strcmp(reg_name, "d30") == 0 || strcmp(reg_name, "q30") == 0)
    return 61;
  else if (strcmp(reg_name, "b31") == 0 || strcmp(reg_name, "h31") == 0 || strcmp(reg_name, "s31") == 0 || strcmp(reg_name, "d31") == 0 || strcmp(reg_name, "q31") == 0)
    return 62;
  else
    {
      printf("REG_NAME: %s not found! \n",reg_name);
      assert(false);
    }
}
