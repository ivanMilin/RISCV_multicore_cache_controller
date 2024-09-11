clear -all 

analyze -sv09 ../verif/Controller_clk.sv ../verif/checker_controller.sv  ../verif/bind_controller.sv

elaborate -top Controller

clock clk -factor 1 -phase 1
reset -expression {reset}

prove -all
