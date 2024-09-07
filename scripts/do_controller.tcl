clear -all 

analyze -sv09 ../verif/checker_controller.sv  ../verif/bind_controller.sv
analyze -sv09 ../hdl/Controller.sv

elaborate -top Controller

prove -all
