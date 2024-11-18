# ===================================================================================
# Definisanje direktorijuma u kojem ce biti projekat
# ===================================================================================
cd ..
set root_dir [pwd]
cd scripts
set resultDir ../vivado_project

file mkdir $resultDir

create_project RISCV_CPU $resultDir -part xc7z020clg400-1
set_property board_part digilentinc.com:zybo-z7-10:part0:1.2 [current_project]

# ===================================================================================
# Ukljucivanje svih izvornih i simulacionih fajlova u projekat
# ===================================================================================
add_files -norecurse ../hdl/Add4.sv
add_files -norecurse ../hdl/add_immediate.sv
add_files -norecurse ../hdl/ALU.sv
add_files -norecurse ../hdl/BranchCondition.sv
add_files -norecurse ../hdl/Controller.sv
add_files -norecurse ../hdl/DataMemory.sv
add_files -norecurse ../hdl/ImmediateGenerator.sv
add_files -norecurse ../hdl/InstructionMemory.sv
add_files -norecurse ../hdl/Mux2.sv
add_files -norecurse ../hdl/mux2to1.sv
add_files -norecurse ../hdl/PC.sv
add_files -norecurse ../hdl/cache_subsystem_L1.sv
add_files -norecurse ../hdl/RegisterFile.sv
add_files -norecurse ../hdl/WriteBack.sv
add_files -norecurse ../hdl/Processor.sv
add_files -norecurse ../hdl/bus_controller.sv
add_files -norecurse ../hdl/top.sv

update_compile_order -fileset sources_1
add_files -norecurse ../hdl/code1.mem
add_files -norecurse ../hdl/code2.mem

update_compile_order -fileset sources_1

set_property SOURCE_SET sources_1 [get_filesets sim_1]
set_property -name {STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS} -value {-mode out_of_context} -objects [get_runs synth_1]

add_files -fileset sim_1 -norecurse ../tb/Processor_TB.sv
#add_files -fileset sim_1 -norecurse ../tb/controller_TB.sv
#add_files -fileset sim_1 -norecurse ../tb/waveform/r7_isNull_shouldBe_0xac.wcfg

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1