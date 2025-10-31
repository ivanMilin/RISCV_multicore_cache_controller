# Digital Design of RISC-V Multicore CPU and Formal Verification Using Cadence JasperGold
- System has two RISC-V (RV32) CPU cores, each core has its own L1 (direct-mapped) data cache, cores share L2 (2-way setassociative) cache and mass memory. MESI protocol and Snooping mechanism ensures that each core maintains a coherent view of
the shared data across multiple cores. Design and verification of the system are implemented in SystemVerilog, with the intention
to develop it further into a master thesis.
- Project created in collaboration with the company Veriest Venture Serbian, mentor Tivadar Mako
## System overview :

![top_module](https://github.com/user-attachments/assets/797874b8-bdf8-472e-bbbd-0521b15bd7ab)

