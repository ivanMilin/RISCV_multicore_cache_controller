# Digital Design of RISC-V Multicore CPU and Formal Verification Using Cadence JasperGold
- Two RISC-V (RV32) CPU cores, each core has its own L1 (direct-mapped) data cache 
- Instruction types implemeneted inside each core : R, I, S, L, B, J, U
- Cores share L2 (2-way set associative) cache and mass memory. 
- MESI protocol and Snooping mechanism ensures that each core maintains a coherent view of the shared data across multiple cores. 
- Design and verification of the system are implemented in SystemVerilog, with the intention to develop it further into a master thesis.
- Project created in collaboration with the company Veriest Venture Serbian, mentor Tivadar Mako

## System overview :

![top_module](https://github.com/user-attachments/assets/797874b8-bdf8-472e-bbbd-0521b15bd7ab)

## Implemented instructions :
<img width="849" height="790" alt="implementirane_instrukcije" src="https://github.com/user-attachments/assets/f2bcc9da-621c-489f-aa74-5293dea0017f" />

## MESI cache coherency protocol :
<img width="419" height="705" alt="MESI" src="https://github.com/user-attachments/assets/60cef74a-fddc-4120-93a7-388405476531" />

## L1 and L2 cache memory :
<img width="1055" height="327" alt="image" src="https://github.com/user-attachments/assets/837df6d0-eddd-488a-9fa0-3e09e523935b" />
