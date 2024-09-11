clear -all 

analyze -sv09 ../verif/branch_checking/BranchCondition_clk.sv ../verif/branch_checking/checker_branch.sv  ../verif/branch_checking/bind_branch.sv

elaborate -top BranchCondition

clock clk -factor 1 -phase 1
reset -expression {reset}

prove -all
