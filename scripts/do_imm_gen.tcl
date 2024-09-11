clear -all 

analyze -sv09 ../verif/immediate_checking/ImmediateGenerator_clk.sv ../verif/immediate_checking/checker_imm_gen.sv  ../verif/immediate_checking/bind_imm_gen.sv

elaborate -top ImmediateGenerator

clock clk -factor 1 -phase 1
reset -expression {reset}

prove -all
