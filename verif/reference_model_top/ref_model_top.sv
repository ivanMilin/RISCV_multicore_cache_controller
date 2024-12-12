`include "../reference_model/defines.sv"

module ref_model_top
(
	input clk,
	input reset
);
	`include "../reference_model/structs.sv"
	
	// Constant parametes - opcodes for each instruction type
	parameter[6:0] instruction_R_type_opcode = `TYPE_R;
	parameter[6:0] instruction_I_type_opcode = `TYPE_I;
	parameter[6:0] instruction_L_type_opcode = `TYPE_L;
	parameter[6:0] instruction_S_type_opcode = `TYPE_S;
	parameter[6:0] instruction_B_type_opcode = `TYPE_B;
	parameter[6:0] instruction_U_type_opcode = `TYPE_U;
	parameter[6:0] instruction_J_type_opcode = `TYPE_J;
	
	// Free variables
	logic [31:0] fvar_specific_addr, fvar_specific_addr_q, fvar_specific_addr_q_neg;
		
	logic [31:0] gb_data_from_L1_cpu1_q_neg, gb_data_from_L1_cpu2_q_neg;
	logic [31:0] gb_data_from_L2_1, gb_data_from_L2_2;
	logic gb_stall1, gb_stall2;
	
	struct_instruction_R   struct_assignment_R1, struct_assignment_R2;
	struct_instruction_I_L struct_assignment_I1, struct_assignment_I2;
	struct_instruction_I_L struct_assignment_L1, struct_assignment_L2;
	struct_instruction_S_B struct_assignment_S1, struct_assignment_S2;
	struct_instruction_S_B struct_assignment_B1, struct_assignment_B2;
	struct_instruction_U_J struct_assignment_U1, struct_assignment_U2;
	struct_instruction_U_J struct_assignment_J1, struct_assignment_J2;
	
	// ================= ASSUMES SECTION ================// 
	// Every assume has its "clone" - due to using both positive and negative edge of clock signal
	// Assumptions for instructions for CPU1 and CPU2- which opcodes will tool feed 
	`include "properties_for_assumes.sv"
	
	//===============================================================================================================================================================================================================================
	// Assumptions for instructions - which opcodes will tool feed
	all_types_active_cpu1      : assume property(assume_opcodes_cpu1);
	all_types_active_cpu2      : assume property(assume_opcodes_cpu2);
	all_types_active_neg_cpu1  : assume property(assume_opcodes_neg_cpu1);
	all_types_active_neg_cpu2  : assume property(assume_opcodes_neg_cpu2);
	
	// Cant load into x0 register
	load_rs2_not_NULL_cpu1     : assume property(assume_load_rs2_not_NULL_cpu1);
	load_rs2_not_NULL_cpu2     : assume property(assume_load_rs2_not_NULL_cpu2);
	load_rs2_not_NULL_neg_cpu1 : assume property(assume_load_rs2_not_NULL_neg_cpu1);
	load_rs2_not_NULL_neg_cpu2 : assume property(assume_load_rs2_not_NULL_neg_cpu2);
	
	// When R or I of U type are active, you cant write in the x0 register
	cant_write_to_x0_cpu1      : assume property (assume_cant_write_to_x0_cpu1);
	cant_write_to_x0_cpu2      : assume property (assume_cant_write_to_x0_cpu1);
	cant_write_to_x0_neg_cpu1  : assume property (assume_cant_write_to_x0_neg_cpu1);
	cant_write_to_x0_neg_cpu2  : assume property (assume_cant_write_to_x0_neg_cpu2);
	
	// Stabilize the free variable and set it accordingly to memory limitations
	asm_fvar_stable            : assume property (assume_fvar_stable);
	asm_fvar_stable_neg        : assume property (assume_fvar_stable_neg);
	
	//If stall is ONE keep same operation as long as stall is ONE
	asm_if_stall_not_null_load_from_cpu2_to_cpu1	 : assume property (assume_if_stall_not_null_load_from_cpu2_to_cpu1);
	asm_if_stall_not_null_load_from_cpu1_to_cpu2	 : assume property (assume_if_stall_not_null_load_from_cpu1_to_cpu2);
	asm_if_stall_not_null_load_from_cpu2_to_cpu1_neg : assume property (assume_if_stall_not_null_load_from_cpu2_to_cpu1_neg);
	asm_if_stall_not_null_load_from_cpu1_to_cpu2_neg : assume property (assume_if_stall_not_null_load_from_cpu1_to_cpu2_neg);
	
	// If opcode is STORE, then keep mask value inside limit
	asm_funct3_S_type_opcode_cpu1     : assume property (assume_funct3_S_type_opcode_cpu1);
	asm_funct3_S_type_opcode_cpu2     : assume property (assume_funct3_S_type_opcode_cpu2);
	asm_funct3_S_type_opcode_neg_cpu1 : assume property (assume_funct3_S_type_opcode_neg_cpu1);
	asm_funct3_S_type_opcode_neg_cpu2 : assume property (assume_funct3_S_type_opcode_neg_cpu2);
	
	// If opcode is LOAD, then keep mask value inside limit
	asm_funct3_L_type_opcode_cpu1     : assume property (assume_funct3_L_type_opcode_cpu1);
	asm_funct3_L_type_opcode_cpu2     : assume property (assume_funct3_L_type_opcode_cpu2);
	asm_funct3_L_type_opcode_neg_cpu1 : assume property (assume_funct3_L_type_opcode_neg_cpu1);
	asm_funct3_L_type_opcode_neg_cpu2 : assume property (assume_funct3_L_type_opcode_neg_cpu2);
	//===============================================================================================================================================================================================================================

	

	assign struct_assignment_R1 = top.cpu1.instruction; 
	assign struct_assignment_I1 = top.cpu1.instruction;  
	assign struct_assignment_L1 = top.cpu1.instruction; 
	assign struct_assignment_S1 = '{{top.cpu1.instruction[31:25],top.cpu1.instruction[11:7]},top.cpu1.instruction[24:20],top.cpu1.instruction[19:15],top.cpu1.instruction[14:12],top.cpu1.instruction[6:0]}; 
	assign struct_assignment_B1 = '{{top.cpu1.instruction[31], top.cpu1.instruction[7], top.cpu1.instruction[30:25], top.cpu1.instruction[11:8]}, top.cpu1.instruction[24:20], top.cpu1.instruction[19:15],
					top.cpu1.instruction[14:12], top.cpu1.instruction[6:0]}; 
	assign struct_assignment_U1 = top.cpu1.instruction;
	assign struct_assignment_J1 = '{{top.cpu1.instruction[31] , top.cpu1.instruction[19:12] , top.cpu1.instruction[20] , top.cpu1.instruction[30:21]} , top.cpu1.instruction[11:7] , top.cpu1.instruction[6:0]};
	
	assign struct_assignment_R2 = top.cpu2.instruction; 
	assign struct_assignment_I2 = top.cpu2.instruction;  
	assign struct_assignment_L2 = top.cpu2.instruction; 
	assign struct_assignment_S2 = '{{top.cpu2.instruction[31:25],top.cpu2.instruction[11:7]},top.cpu2.instruction[24:20],top.cpu2.instruction[19:15],top.cpu2.instruction[14:12],top.cpu2.instruction[6:0]}; 
	assign struct_assignment_B2 = '{{top.cpu2.instruction[31], top.cpu2.instruction[7], top.cpu2.instruction[30:25], top.cpu2.instruction[11:8]}, top.cpu2.instruction[24:20], top.cpu2.instruction[19:15],
					top.cpu2.instruction[14:12], top.cpu2.instruction[6:0]}; 
	assign struct_assignment_U2 = top.cpu2.instruction;
	assign struct_assignment_J2 = '{{top.cpu2.instruction[31] , top.cpu2.instruction[19:12] , top.cpu2.instruction[20] , top.cpu2.instruction[30:21]} , top.cpu2.instruction[11:7] , top.cpu2.instruction[6:0]};
	
	assign gb_stall1 = top.cpu1.stall;
	assign gb_stall2 = top.cpu2.stall;
	
	always_ff @(negedge clk) begin
		if(reset) begin
			fvar_specific_addr_q_neg   <= 'b0;
			gb_data_from_L1_cpu1_q_neg <= 'b0;
			gb_data_from_L1_cpu2_q_neg <= 'b0;
			gb_data_from_L2_1          <= 'b0;
			gb_data_from_L2_2          <= 'b0;
		end 
		else begin
			fvar_specific_addr_q_neg <= fvar_specific_addr;
			if(top.cpu1.controller_and_cache.state == 2'b01 && top.cpu1.controller_and_cache.cache_hit == 2'b01 && top.bus_ctrl.cache_hit_out1 == 2'b01 && top.cpu1.controller_and_cache.mask_in == 3'b010) begin
				gb_data_from_L1_cpu2_q_neg <= top.cpu2.controller_and_cache.cache_memory_L1[top.cpu2.controller_and_cache.bus_address_in[7:2]].data;
			end
			else if(top.cpu2.controller_and_cache.state == 2'b01 && top.cpu2.controller_and_cache.cache_hit == 2'b01 && top.bus_ctrl.cache_hit_out2 == 2'b01 && top.cpu2.controller_and_cache.mask_in == 3'b010) begin
				gb_data_from_L1_cpu1_q_neg <= top.cpu1.controller_and_cache.cache_memory_L1[top.cpu1.controller_and_cache.bus_address_in[7:2]].data;
			end
			else if(top.cpu1.controller_and_cache.state == 2'b01 && top.cpu1.controller_and_cache.cache_hit == 2'b01 && top.bus_ctrl.cache_hit_out1 == 2'b10 && top.cpu1.controller_and_cache.mask_in == 3'b010) begin
				gb_data_from_L2_1 <= top.cache_L2.data_from_L2;
			end
			else if(top.cpu2.controller_and_cache.state == 2'b01 && top.cpu2.controller_and_cache.cache_hit == 2'b01 && top.bus_ctrl.cache_hit_out2 == 2'b10 && top.cpu2.controller_and_cache.mask_in == 3'b010) begin
				gb_data_from_L2_2 <= top.cache_L2.data_from_L2;
			end
			else begin
				gb_data_from_L1_cpu1_q_neg <= gb_data_from_L1_cpu1_q_neg;
				gb_data_from_L1_cpu2_q_neg <= gb_data_from_L1_cpu2_q_neg;
				gb_data_from_L2_1 	   <= gb_data_from_L2_1;
				gb_data_from_L2_2 	   <= gb_data_from_L2_2;
			end
		
		end
	end
	
	always_ff @(posedge clk) begin
		if(reset) begin
			fvar_specific_addr_q <= 'b0;
		end 
		else begin
			fvar_specific_addr_q <= fvar_specific_addr;
		end
	end
	// =============== PROPERTIES SECTION ================ 
	
	
	// --------- BUS CONTROLLER - PROPERTIES ---------
	// When both of requests are HIGH and stall of CPU2 is LOW then chech grants for both CPU
	property check_toggle_when_both_req_grant2;
		(top.bus_ctrl.req_core1 && top.bus_ctrl.req_core2) && top.bus_ctrl.grant_core_toggle && top.bus_ctrl.stall_core2 == 1'b0 |-> 
		top.bus_ctrl.grant_core1 == 1'b0 && top.bus_ctrl.grant_core2 == 1'b1 && top.bus_ctrl.grant_core_toggle_next != top.bus_ctrl.grant_core_toggle ;   
	endproperty

	// When both of requests are HIGH and stall of CPU1 is LOW then chech grants for both CPU
	property check_toggle_when_both_req_grant1;
		(top.bus_ctrl.req_core1 && top.bus_ctrl.req_core2) && !top.bus_ctrl.grant_core_toggle && top.bus_ctrl.stall_core1 == 1'b0 |-> 
		top.bus_ctrl.grant_core1 == 1'b1 && top.bus_ctrl.grant_core2 == 1'b0 && top.bus_ctrl.grant_core_toggle_next != top.bus_ctrl.grant_core_toggle ;   
	endproperty

	property chech_when_reqs_are_not_high;
		!(top.bus_ctrl.req_core1 && top.bus_ctrl.req_core2) |-> top.bus_ctrl.grant_core1 == 1'b1 && top.bus_ctrl.grant_core2 == 1'b1;
	endproperty	
	//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
	property data_forwarding_from_cpu1_to_cpu2;
		top.bus_ctrl.req_core1 && top.bus_ctrl.grant_core1 && top.bus_ctrl.bus_operation_in1 != 2'b11 && top.bus_ctrl.cache_hit_in2 |-> 
		top.bus_ctrl.bus_data_out1 == top.bus_ctrl.bus_data_in2 && top.bus_ctrl.cache_hit_out1 == 2'b01 &&  
		top.bus_ctrl.bus_operation_out2 == top.bus_ctrl.bus_operation_in1 && 
		top.bus_ctrl.bus_address_out2   == top.bus_ctrl.bus_address_in1   && 
		top.bus_ctrl.address_to_L2 	== top.bus_ctrl.bus_address_in1   && 
		top.bus_ctrl.opcode_out 	== top.bus_ctrl.opcode_in1;  
	endproperty	

	property data_forwarding_from_L2_to_cpu1;
		top.bus_ctrl.req_core1 && top.bus_ctrl.grant_core1 && top.bus_ctrl.bus_operation_in1 != 2'b11 && top.bus_ctrl.cache_hit_L2 == 2'b10 && !top.bus_ctrl.cache_hit_in2 |-> 
		top.bus_ctrl.bus_data_out1 == top.bus_ctrl.data_from_L2 && top.bus_ctrl.cache_hit_out1 == 2'b10;
	endproperty
	
	property data_forwarding_no_operation1;
		(top.bus_ctrl.req_core1 && top.bus_ctrl.grant_core1) && top.bus_ctrl.bus_operation_in1 != 2'b11 && !top.bus_ctrl.cache_hit_in2 && top.bus_ctrl.cache_hit_L2 != 2'b10  |->
		top.bus_ctrl.bus_data_out1 == 'b0 && top.bus_ctrl.cache_hit_out1 == 2'b11;
	endproperty
	//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
	property data_forwarding_from_cpu2_to_cpu1;
		top.bus_ctrl.req_core2 && top.bus_ctrl.grant_core2 && top.bus_ctrl.bus_operation_in2 != 2'b11 && top.bus_ctrl.cache_hit_in1 |-> 
		top.bus_ctrl.bus_data_out2 	== top.bus_ctrl.bus_data_in1 	  && top.bus_ctrl.cache_hit_out2 == 2'b01 &&  
		top.bus_ctrl.bus_operation_out1 == top.bus_ctrl.bus_operation_in2 && 
		top.bus_ctrl.bus_address_out1   == top.bus_ctrl.bus_address_in2   && 
		top.bus_ctrl.address_to_L2 	== top.bus_ctrl.bus_address_in2   && 
		top.bus_ctrl.opcode_out 	== top.bus_ctrl.opcode_in2;  
	endproperty
	
	property data_forwarding_from_L2_to_cpu2;
		top.bus_ctrl.req_core2 && top.bus_ctrl.grant_core2 && top.bus_ctrl.bus_operation_in2 != 2'b11 && top.bus_ctrl.cache_hit_L2 == 2'b10 && !top.bus_ctrl.cache_hit_in1 |-> 
		top.bus_ctrl.bus_data_out2 == top.bus_ctrl.data_from_L2 && top.bus_ctrl.cache_hit_out2 == 2'b10;
	endproperty
	
	property data_forwarding_no_operation2;
		(top.bus_ctrl.req_core2 && top.bus_ctrl.grant_core2) && top.bus_ctrl.bus_operation_in2 != 2'b11 && !top.bus_ctrl.cache_hit_in1 && top.bus_ctrl.cache_hit_L2 != 2'b10  |->
		top.bus_ctrl.bus_data_out2 == 'b0 && top.bus_ctrl.cache_hit_out2 == 2'b11;
	endproperty
	//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
	property forwaring_data_when_flush_happens;
		top.bus_ctrl.flush_in1 || top.bus_ctrl.flush_in2 |->
		top.bus_ctrl.flush_out 	    == 1'b1 && 
		top.bus_ctrl.data_to_L2_out == top.bus_ctrl.data_to_L2_input && 
		top.bus_ctrl.tag_to_L2_out  == top.bus_ctrl.tag_to_L2_in;
	endproperty
	
	property not_forwaring_data_when_flush_doesnt_happens;
		!top.bus_ctrl.flush_in1 && !top.bus_ctrl.flush_in2 |->
		top.bus_ctrl.flush_out      == 1'b0 && 
		top.bus_ctrl.data_to_L2_out == 'b0 && 
		top.bus_ctrl.tag_to_L2_out  == 'b0;
	endproperty
	//==================================================================================================================================================================================
	
	// --------- L2 CACHE CONTROLLER AND L2 MEMORY - PROPERTIES ---------
	property checking_transition_from_IDLE_to_DMEM_WRITE;
		top.cache_L2.state == 2'b00 && top.cache_L2.cache_hit_out == 2'b01 |=> 
		top.cache_L2.state == 2'b01; 
	endproperty
	
	property checking_transition_from_DMEM_WRITE_to_IDLE;
		top.cache_L2.state == 2'b01 && top.cache_L2.cache_hit_out == 2'b10 |=> 
		top.cache_L2.state == 2'b00;
	endproperty
	//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
	property checking_way0_hit;
		top.cache_L2.cache_memory_L2[top.cache_L2.set_index][0].valid && (top.cache_L2.cache_memory_L2[top.cache_L2.set_index][0].tag == top.cache_L2.tag) |->
		top.cache_L2.way0_hit == 1'b1;
	endproperty
	
	property checking_way1_hit;
		top.cache_L2.cache_memory_L2[top.cache_L2.set_index][1].valid && (top.cache_L2.cache_memory_L2[top.cache_L2.set_index][1].tag == top.cache_L2.tag) |->
		top.cache_L2.way1_hit == 1'b1;
	endproperty
	//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
	property load_word_from_cpu2_to_cpu1;
		top.opcode_out1 == 7'b0000011 && top.bus_ctrl.cache_hit_out1 == 2'b01 && top.cpu1.controller_and_cache.mask_in == 3'b010 && 
		top.cpu1.controller_and_cache.cache_hit == 2'b01 ##1 top.cpu1.controller_and_cache.cache_hit == 2'b10|-> 
		top.cpu1.controller_and_cache.cache_memory_L1[$past(top.cpu1.controller_and_cache.index_in[7:2])].data       == gb_data_from_L1_cpu2_q_neg &&
		top.cpu1.controller_and_cache.cache_memory_L1[$past(top.cpu1.controller_and_cache.index_in[7:2])].mesi_state == 2'b10;
	endproperty

	property load_word_from_cpu1_to_cpu2;
		top.opcode_out2 == 7'b0000011 && top.bus_ctrl.cache_hit_out2 == 2'b01 && top.cpu2.controller_and_cache.mask_in == 3'b010 &&
		top.cpu2.controller_and_cache.cache_hit == 2'b01 ##1 top.cpu2.controller_and_cache.cache_hit == 2'b10|-> 
		top.cpu2.controller_and_cache.cache_memory_L1[$past(top.cpu2.controller_and_cache.index_in[7:2])].data == gb_data_from_L1_cpu1_q_neg &&
		top.cpu2.controller_and_cache.cache_memory_L1[$past(top.cpu2.controller_and_cache.index_in[7:2])].mesi_state == 2'b10;
	endproperty
	//----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
	property load_word_from_L2_to_cpu1_way0_hit;
		top.opcode_out1 == 7'b0000011 && top.bus_ctrl.cache_hit_out1 == 2'b10 && top.cpu1.controller_and_cache.mask_in == 3'b010 && top.cache_L2.way0_hit &&
		top.cpu1.controller_and_cache.cache_hit == 2'b01 ##1 top.cpu1.controller_and_cache.cache_hit == 2'b10|-> 
		top.cpu1.controller_and_cache.cache_memory_L1[$past(top.cpu1.controller_and_cache.index_in[7:2])].data == gb_data_from_L2_1;
	endproperty
	
	property load_word_from_L2_to_cpu1_way1_hit;
		top.opcode_out1 == 7'b0000011 && top.bus_ctrl.cache_hit_out1 == 2'b10 && top.cpu1.controller_and_cache.mask_in == 3'b010 && top.cache_L2.way1_hit &&
		top.cpu1.controller_and_cache.cache_hit == 2'b01 ##1 top.cpu1.controller_and_cache.cache_hit == 2'b10|-> 
		top.cpu1.controller_and_cache.cache_memory_L1[$past(top.cpu1.controller_and_cache.index_in[7:2])].data == gb_data_from_L2_1;
	endproperty
	
	property load_word_from_L2_to_cpu2_way0_hit;
		top.opcode_out2 == 7'b0000011 && top.bus_ctrl.cache_hit_out2 == 2'b10 && top.cpu2.controller_and_cache.mask_in == 3'b010 && top.cache_L2.way0_hit &&
		top.cpu2.controller_and_cache.cache_hit == 2'b01 ##1 top.cpu2.controller_and_cache.cache_hit == 2'b10|-> 
		top.cpu2.controller_and_cache.cache_memory_L1[$past(top.cpu2.controller_and_cache.index_in[7:2])].data == gb_data_from_L2_2;
	endproperty
	
	property load_word_from_L2_to_cpu2_way1_hit;
		top.opcode_out2 == 7'b0000011 && top.bus_ctrl.cache_hit_out2 == 2'b10 && top.cpu2.controller_and_cache.mask_in == 3'b010 && top.cache_L2.way1_hit &&
		top.cpu2.controller_and_cache.cache_hit == 2'b01 ##1 top.cpu2.controller_and_cache.cache_hit == 2'b10|-> 
		top.cpu2.controller_and_cache.cache_memory_L1[$past(top.cpu2.controller_and_cache.index_in[7:2])].data == gb_data_from_L2_2;
	endproperty
	//==================================================================================================================================================================================
	property flushing_data_to_L2_both_ways_free; 
		top.cache_L2.flush == 1'b1 && top.cache_L2.cache_memory_L2[top.cache_L2.set_index][0].valid == 0 && top.cache_L2.cache_memory_L2[top.cache_L2.set_index][1].valid == 0 |=>
		top.cache_L2.cache_memory_L2[$past(top.cache_L2.set_index)][0].valid == 1 &&
		top.cache_L2.cache_memory_L2[$past(top.cache_L2.set_index)][0].lru   == 0 &&
		top.cache_L2.cache_memory_L2[$past(top.cache_L2.set_index)][1].lru   == 1 &&
		top.cache_L2.cache_memory_L2[$past(top.cache_L2.set_index)][0].data  == $past(top.cache_L2.bus_data_in) &&
		top.cache_L2.cache_memory_L2[$past(top.cache_L2.set_index)][0].tag   == $past(top.cache_L2.bus_tag_in[23:1]); 
	endproperty
	// ===================== ASSERTIONS SECTION ====================== 
	
	// --------- BUS CONTROLLER - ASSERTS ---------
	//ASSERT PASSED//assert_check_toggle_when_both_req_grant2 : assert property (@(posedge clk) check_toggle_when_both_req_grant2);
	//ASSERT PASSED//assert_check_toggle_when_both_req_grant1 : assert property (@(posedge clk) check_toggle_when_both_req_grant1);
	//ASSERT PASSED//assert_chech_when_reqs_are_not_high      : assert property (@(posedge clk) chech_when_reqs_are_not_high);
	//ASSERT PASSED//assert_data_forwarding_from_cpu1_to_cpu2 : assert property (@(posedge clk) data_forwarding_from_cpu1_to_cpu2);
	//ASSERT PASSED//assert_data_forwarding_from_L2_to_cpu1   : assert property (@(posedge clk) data_forwarding_from_L2_to_cpu1);
	//ASSERT PASSED//assert_data_forwarding_no_operation  	  : assert property (@(posedge clk) data_forwarding_no_operation);
	//ASSERT PASSED//assert_data_forwarding_from_cpu2_to_cpu1 : assert property (@(posedge clk) data_forwarding_from_cpu2_to_cpu1);
	//ASSERT PASSED//assert_data_forwarding_from_L2_to_cpu2   : assert property (@(posedge clk) data_forwarding_from_L2_to_cpu2);
	//ASSERT PASSED//assert_data_forwarding_no_operation2     : assert property (@(posedge clk) data_forwarding_no_operation2);
	//ASSERT PASSED//assert_forwaring_data_when_flush_happens : assert property (@(posedge clk) forwaring_data_when_flush_happens);
	//ASSERT PASSED//assert_not_forwaring_data_when_flush_doesnt_happens : assert property (@(posedge clk) not_forwaring_data_when_flush_doesnt_happens);
	
	// --------- L2 CACHE CONTROLLER AND L2 MEMORY - ASSERTS ---------
	//ASSERT PASSED//assert_checking_transition_from_IDLE_to_DMEM_WRITE : assert property (@(posedge clk) checking_transition_from_IDLE_to_DMEM_WRITE);
	//ASSERT PASSED//assert_checking_transition_from_DMEM_WRITE_to_IDLE : assert property (@(posedge clk) checking_transition_from_DMEM_WRITE_to_IDLE);
	//ASSERT PASSED//assert_checking_way0_hit : assert property (@(posedge clk) checking_way0_hit);
	//ASSERT PASSED//assert_checking_way1_hit : assert property (@(posedge clk) checking_way1_hit);
	
	//ASSERT PASSED//assert_load_word_from_cpu2_to_cpu1 : assert property (@(posedge clk) load_word_from_cpu2_to_cpu1);
	//ASSERT PASSED//assert_load_word_from_cpu1_to_cpu2 : assert property (@(posedge clk) load_word_from_cpu1_to_cpu2);
	
	//ASSERT PASSED//assert_load_word_from_L2_to_cpu1_way0_hit : assert property (@(posedge clk) load_word_from_L2_to_cpu1_way0_hit);
	//ASSERT PASSED//assert_load_word_from_L2_to_cpu1_way1_hit : assert property (@(posedge clk) load_word_from_L2_to_cpu1_way1_hit);
	
	//ASSERT PASSED//assert_load_word_from_L2_to_cpu2_way0_hit : assert property (@(posedge clk) load_word_from_L2_to_cpu2_way0_hit);
	//ASSERT PASSED//assert_load_word_from_L2_to_cpu2_way1_hit : assert property (@(posedge clk) load_word_from_L2_to_cpu2_way1_hit);
	
	assert_flushing_data_to_L2_both_ways_free : assert property (@(negedge clk) flushing_data_to_L2_both_ways_free);
	
	
	cover_bus_hit : cover property (@(negedge clk) top.opcode_out1 == 7'b0000011 && top.bus_ctrl.cache_hit_out1 == 2'b01 && top.cpu1.controller_and_cache.mask_in == 3'b010 && top.cpu1.controller_and_cache.cache_hit == 2'b01 ##1 
	top.cpu1.controller_and_cache.cache_hit == 2'b10 && top.cpu1.stall_out == 1'b0);
endmodule
