clear -all 

analyze -sv09 ../verif/controlller_checking/Controller_clk.sv ../verif/controlller_checking/checker_controller.sv  ../verif/controlller_checking/bind_controller.sv

elaborate -top Controller

clock clk -factor 1 -phase 1
reset -expression {reset}

prove -all
