## ARM TRACE GENERATOR                                                                                                 
# Trace Format
It generates the trace with the following format:-                                                                                                        
[L|LA]<PC_diff_in_decimal>(d<dep>)(m<mem_dep>) <hex_addr> <size>                                                                                               
[S|SA]<PC_diff_in_decimal>(d<dep>)(m<mem_dep>)(a<addr_dep>) <hex_addr> <size>                                                                           
B<PC_diff_in_decimal>(d<dep>)(m<dep>)(t<target_addr>)(*)?                                                                                                          
[A|M|D|Q|]<PC_diff_in_decimal>(d<dep>)(m<dep>)                                                                                                                       
Legend:                                                                                                                                                           
L=load, LA=load of atomic, S=store, SA=store of atomic,                                                                                                             
B=conditional branch, A=fp_addsub, M=fp_mul, D=fp_div, Q=fp_sqrt, []=generic                                                                                         
d=reg dependence, m=mem dependence, a=addr dependence, t=target address, *=taken                                                                                    
>Example:                                                                                                                                                           
2 A0 3d1 B2d2t-120* L5d1 fff0 4    
  
Sawan Singh (singh.sawan@um.es) CAPS Group, University of Murcia, ES.                                                                                                 
# How to build?
```sh
mkdir build
cd build
cmake ../ARMTracer
make
```
# How to use it?
```sh
drrun -c /path/to/build/bin/ARMTracer-v3.so -- binary
```
