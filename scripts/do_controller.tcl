clear -all 

analyze -sv09 ../verif/controller_checking/Controller_clk.sv ../verif/controller_checking/checker_controller.sv  ../verif/controller_checking/bind_controller.sv

elaborate -top Controller

clock clk -factor 1 -phase 1
reset -expression {reset}

prove -all
