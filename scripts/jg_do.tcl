clear -all 

analyze -sv09 ../hdl/ALU.sv ../hdl/Add4.sv ../hdl/BranchCondition.sv ../hdl/Controller.sv ../hdl/DataMemory.sv ../hdl/ImmediateGenerator.sv ../hdl/InstructionMemory.sv ../hdl/Mux2.sv ../hdl/PC.sv ../hdl/Processor.sv ../hdl/RegisterFile.sv ../hdl/WriteBack.sv

elaborate -top Processor

clock clk -both_edges -factor 1 -phase 1
reset -expression {reset}

#prove -all
