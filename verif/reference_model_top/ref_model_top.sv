`include "defines.sv"

module ref_model_top
(
	input clk,
	input reset
);
	`include "structs.sv"	
	
	// Constant parametes - opcodes for each instruction type
	parameter[6:0] instruction_R_type_opcode = `TYPE_R;
	parameter[6:0] instruction_I_type_opcode = `TYPE_I;
	parameter[6:0] instruction_L_type_opcode = `TYPE_L;
	parameter[6:0] instruction_S_type_opcode = `TYPE_S;
	parameter[6:0] instruction_B_type_opcode = `TYPE_B;
	parameter[6:0] instruction_U_type_opcode = `TYPE_U;
	parameter[6:0] instruction_J_type_opcode = `TYPE_J;
	
	// Structes declaration - will be assigned later in the code
	struct_instruction_R   struct_assignment_R;
	struct_instruction_I_L struct_assignment_I;
	struct_instruction_I_L struct_assignment_L;
	struct_instruction_S_B struct_assignment_S;
	struct_instruction_S_B struct_assignment_B;
	struct_instruction_U_J struct_assignment_U;
	struct_instruction_U_J struct_assignment_J;
	
	// ================= ASSUMES SECTION ================// 
	// Every assume has its "clone" - due to using both positive and negative edge of clock signal

	// Assumptions for instructions - which opcodes will tool feed? 
	property assume_opcodes;
		@(posedge clk) disable iff(reset) 
		top.cpu1.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode};
	endproperty 

	property assume_opcodes_neg;
		@(negedge clk) disable iff(reset) 
		top.cpu1.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode};
	endproperty 
	
	// Assumptions for R , I and U type - None of these can write values to x0 register	
	property assume_cant_write_to_x0;
		@(posedge clk) disable iff(reset) 
		top.cpu1.instruction[6:0] == instruction_R_type_opcode || top.cpu1.instruction[6:0] == instruction_I_type_opcode || top.cpu1.instruction[6:0] == instruction_U_type_opcode |-> 
		top.cpu1.instruction[11:7] != 0;
	endproperty
	
	property assume_cant_write_to_x0_neg;
		@(negedge clk) disable iff(reset) 
		top.cpu1.instruction[6:0] == instruction_R_type_opcode || top.cpu1.instruction[6:0] == instruction_I_type_opcode || top.cpu1.instruction[6:0] == instruction_U_type_opcode |-> 
		top.cpu1.instruction[11:7] != 0;
	endproperty
	
	// Assumptions for free variable to be same during verification process and smaller than memory size limit
	property assume_fvar_limit;
		@(posedge clk) disable iff(reset) 
		fvar_specific_addr < 256;
	endproperty
	
	property assume_fvar_limit_neg;
		@(negedge clk) disable iff(reset) 
		fvar_specific_addr < 256;
	endproperty
	
	property assume_fvar_stable;
		@(posedge clk) disable iff(reset) 
		!reset ##1 fvar_specific_addr_q == fvar_specific_addr;
	endproperty
	
	property assume_fvar_stable_neg;
		@(negedge clk) disable iff(reset) 
		!reset ##1 fvar_specific_addr_q_neg == fvar_specific_addr;
	endproperty
	
	
	// Check in vivado on how much cycles is needed in case of L1 and L2 misses!
	property assume_if_stall_not_null;
		//gb_stall |-> $stable(top.cpu1..instruction);
		@(posedge clk) disable iff(reset)
		gb_stall == 1'b1 |-> $stable(top.cpu1.instruction)[*2];    //https://verificationacademy.com/forums/t/assertion-using-stable-with/37547/2
	endproperty

	property assume_if_stall_not_null_neg;
		//gb_stall |-> $stable(top.cpu1..instruction);
		@(negedge clk) disable iff(reset)
		gb_stall == 1'b1 |-> $stable(top.cpu1.instruction)[*2];
	endproperty
	
	// Assumptions for LOAD - Can not load into x0 register and limit address size due to memory limitations
	property assume_load_rs2_not_NULL;
		@(posedge clk) disable iff(reset) 
		top.cpu1.instruction[6:0] == instruction_L_type_opcode |-> 
		top.cpu1.instruction[11:7] != 'b0 && top.cpu1.instruction[31:20] + Processor.rf.registerfile[top.cpu1.instruction[19:15]] < 1024 && top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
	endproperty
	
	property assume_load_rs2_not_NULL_neg;
		@(negedge clk) disable iff(reset) 
		top.cpu1.instruction[6:0] == instruction_L_type_opcode |-> 
		top.cpu1.instruction[11:7] != 'b0 && top.cpu1.instruction[31:20] + Processor.rf.registerfile[top.cpu1.instruction[19:15]] < 1024 && top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
	endproperty
	
	
	// Assumptions for STORE - Can not use address larger than memory size limit 
	property assume_store_less_than_1024;
		@(posedge clk) disable iff(reset)  
		top.cpu1.instruction[6:0] == instruction_S_type_opcode |-> 
		{{20{top.cpu1.instruction[31]}} , top.cpu1.instruction[31:25] , top.cpu1.instruction[11:7]} + Processor.rf.registerfile[top.cpu1.instruction[19:15]] < 1024;
	endproperty

	property assume_store_less_than_1024_neg;
		@(negedge clk) disable iff(reset)  
		top.cpu1.instruction[6:0] == instruction_S_type_opcode |-> 
		{{20{top.cpu1.instruction[31]}} , top.cpu1.instruction[31:25] , top.cpu1.instruction[11:7]} + Processor.rf.registerfile[top.cpu1.instruction[19:15]] < 1024;
	endproperty
	
	property assume_funct3_S_type_opcode;
		@(posedge clk) disable iff(reset)
		top.cpu1.instruction[6:0] == instruction_S_type_opcode |-> top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010};
	endproperty
	
	property assume_funct3_S_type_opcode_neg;
		@(negedge clk) disable iff(reset)
		top.cpu1.instruction[6:0] == instruction_S_type_opcode |-> top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010};
	endproperty
	
	property assume_funct3_L_type_opcode;
		@(posedge clk) disable iff(reset)
		top.cpu1.instruction[6:0] == instruction_L_type_opcode |-> top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
	endproperty
	
	property assume_funct3_L_type_opcode_neg;
		@(negedge clk) disable iff(reset)
		top.cpu1.instruction[6:0] == instruction_L_type_opcode |-> top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
	endproperty
	
	// Assumptions for instructions - which opcodes will tool feed
	all_types_active             : assume property(assume_opcodes);
	all_types_active_neg         : assume property(assume_opcodes_neg);
		
	// Cant load into x0 register
	load_rs2_not_NULL            : assume property(assume_load_rs2_not_NULL);
	load_rs2_not_NULL_neg        : assume property(assume_load_rs2_not_NULL_neg);
	
	// Memory size limit - set to 1024
	store_less_than_1024         : assume property(assume_store_less_than_1024);
	store_less_than_1024_neg     : assume property(assume_store_less_than_1024_neg);

	// When R or I type are active, you cant write in the x0 register
	cant_write_to_x0             : assume property (assume_cant_write_to_x0);
	cant_write_to_x0_neg         : assume property (assume_cant_write_to_x0_neg);

	// Stabilize the free variable and set it accordingly to memory limitations
	asm_fvar_limit           	 : assume property(assume_fvar_limit);
	asm_fvar_limit_neg       	 : assume property(assume_fvar_limit_neg);
	
	asm_fvar_stable          	 : assume property (assume_fvar_stable);
	asm_fvar_stable_neg      	 : assume property (assume_fvar_stable_neg);

	asm_if_stall_not_null	  	 : assume property (assume_if_stall_not_null);
	asm_if_stall_not_null_neg 	 : assume property (assume_if_stall_not_null_neg);

	asm_funct3_S_type_opcode     : assume property (assume_funct3_S_type_opcode);
	asm_funct3_S_type_opcode_neg : assume property (assume_funct3_S_type_opcode_neg);
	
	asm_funct3_L_type_opcode     : assume property (assume_funct3_L_type_opcode);
	asm_funct3_L_type_opcode_neg : assume property (assume_funct3_L_type_opcode_neg);
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	