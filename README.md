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
