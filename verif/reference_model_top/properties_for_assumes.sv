property assume_opcodes_cpu1;
	@(posedge clk) disable iff(reset) 
	top.cpu1.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode};
endproperty 

property assume_opcodes_neg_cpu1;
	@(negedge clk) disable iff(reset) 
	top.cpu1.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode};
endproperty 	

property assume_opcodes_cpu2;
	@(posedge clk) disable iff(reset) 
	top.cpu2.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode};
endproperty 

property assume_opcodes_neg_cpu2;
	@(negedge clk) disable iff(reset) 
	top.cpu2.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode};
endproperty 
//===============================================================================================================================================================================================================================
// Assumptions for LOAD - Can not load into x0 register and limit address size due to memory limitations
property assume_load_rs2_not_NULL_cpu1;
	@(posedge clk) disable iff(reset) 
	top.cpu1.instruction[6:0] == instruction_L_type_opcode |-> 
	top.cpu1.instruction[11:7] != 'b0 && top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
endproperty

property assume_load_rs2_not_NULL_neg_cpu1;
	@(negedge clk) disable iff(reset) 
	top.cpu1.instruction[6:0] == instruction_L_type_opcode |-> 
	top.cpu1.instruction[11:7] != 'b0 && top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
endproperty

property assume_load_rs2_not_NULL_cpu2;
	@(posedge clk) disable iff(reset) 
	top.cpu2.instruction[6:0] == instruction_L_type_opcode |-> 
	top.cpu2.instruction[11:7] != 'b0 && top.cpu2.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
endproperty

property assume_load_rs2_not_NULL_neg_cpu2;
	@(negedge clk) disable iff(reset) 
	top.cpu2.instruction[6:0] == instruction_L_type_opcode |-> 
	top.cpu2.instruction[11:7] != 'b0 && top.cpu2.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
endproperty
//===============================================================================================================================================================================================================================
// Assumptions for R , I and U type - None of these can write values to x0 register	
property assume_cant_write_to_x0_cpu1;
	@(posedge clk) disable iff(reset) 
	top.cpu1.instruction[6:0] == instruction_R_type_opcode || top.cpu1.instruction[6:0] == instruction_I_type_opcode || top.cpu1.instruction[6:0] == instruction_U_type_opcode |-> 
	top.cpu1.instruction[11:7] != 0;
endproperty

property assume_cant_write_to_x0_neg_cpu1;
	@(negedge clk) disable iff(reset) 
	top.cpu1.instruction[6:0] == instruction_R_type_opcode || top.cpu1.instruction[6:0] == instruction_I_type_opcode || top.cpu1.instruction[6:0] == instruction_U_type_opcode |-> 
	top.cpu1.instruction[11:7] != 0;
endproperty

property assume_cant_write_to_x0_cpu2;
	@(posedge clk) disable iff(reset) 
	top.cpu2.instruction[6:0] == instruction_R_type_opcode || top.cpu2.instruction[6:0] == instruction_I_type_opcode || top.cpu2.instruction[6:0] == instruction_U_type_opcode |-> 
	top.cpu2.instruction[11:7] != 0;
endproperty

property assume_cant_write_to_x0_neg_cpu2;
	@(negedge clk) disable iff(reset) 
	top.cpu2.instruction[6:0] == instruction_R_type_opcode || top.cpu2.instruction[6:0] == instruction_I_type_opcode || top.cpu2.instruction[6:0] == instruction_U_type_opcode |-> 
	top.cpu2.instruction[11:7] != 0;
endproperty
//===============================================================================================================================================================================================================================
property assume_fvar_stable;
	@(posedge clk) disable iff(reset) 
	!reset ##1 fvar_specific_addr_q == fvar_specific_addr;
endproperty

property assume_fvar_stable_neg;
	@(negedge clk) disable iff(reset) 
	!reset ##1 fvar_specific_addr_q_neg == fvar_specific_addr;
endproperty
//===============================================================================================================================================================================================================================
// CHECK FOR THE NUMBER OF CYCLES 
property assume_if_stall_not_null_load_from_cpu2_to_cpu1;
	@(posedge clk) disable iff(reset)
	//gb_stall1 == 1'b1 && top.cpu1.cache_hit_in == 2'b01 |-> $stable(top.cpu1.instruction)[*2];    //https://verificationacademy.com/forums/t/assertion-using-stable-with/37547/2
	top.cpu1.controller_and_cache.state == 2'b01 |-> $stable(top.cpu1.instruction) s_until top.cpu1.controller_and_cache.state != 2'b01;
endproperty

property assume_if_stall_not_null_load_from_cpu2_to_cpu1_neg;
	@(negedge clk) disable iff(reset)
	//gb_stall1 == 1'b1 && top.cpu1.cache_hit_in == 2'b01 |-> $stable(top.cpu1.instruction)[*2];
	top.cpu1.controller_and_cache.state == 2'b01 |-> $stable(top.cpu1.instruction) s_until top.cpu1.controller_and_cache.state != 2'b01;
endproperty

property assume_if_stall_not_null_load_from_cpu1_to_cpu2;
	@(posedge clk) disable iff(reset)
	//gb_stall2== 1'b1 && top.cpu2.cache_hit_in == 2'b01 |-> $stable(top.cpu2.instruction)[*2];    //https://verificationacademy.com/forums/t/assertion-using-stable-with/37547/2
	top.cpu2.controller_and_cache.state == 2'b01 |-> $stable(top.cpu2.instruction) s_until top.cpu2.controller_and_cache.state != 2'b01;
endproperty

property assume_if_stall_not_null_load_from_cpu1_to_cpu2_neg;
	@(negedge clk) disable iff(reset)
	//gb_stall2 == 1'b1 && top.cpu2.cache_hit_in == 2'b01 |-> $stable(top.cpu2.instruction)[*2];
	top.cpu2.controller_and_cache.state == 2'b01 |-> $stable(top.cpu2.instruction) s_until top.cpu2.controller_and_cache.state != 2'b01;
endproperty
//===============================================================================================================================================================================================================================
property assume_funct3_S_type_opcode_cpu1;
	@(posedge clk) disable iff(reset)
	top.cpu1.instruction[6:0] == instruction_S_type_opcode |-> 
	top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010};
endproperty

property assume_funct3_S_type_opcode_neg_cpu1;
	@(negedge clk) disable iff(reset)
	top.cpu1.instruction[6:0] == instruction_S_type_opcode |-> 
	top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010};
endproperty

property assume_funct3_S_type_opcode_cpu2;
	@(posedge clk) disable iff(reset)
	top.cpu2.instruction[6:0] == instruction_S_type_opcode |-> 
	top.cpu2.instruction[14:12] inside {3'b000,3'b001,3'b010};
endproperty

property assume_funct3_S_type_opcode_neg_cpu2;
	@(negedge clk) disable iff(reset)
	top.cpu2.instruction[6:0] == instruction_S_type_opcode |-> 
	top.cpu2.instruction[14:12] inside {3'b000,3'b001,3'b010};
endproperty
//===============================================================================================================================================================================================================================
property assume_funct3_L_type_opcode_cpu1;
	@(posedge clk) disable iff(reset)
	top.cpu1.instruction[6:0] == instruction_L_type_opcode |-> 
	top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
endproperty

property assume_funct3_L_type_opcode_neg_cpu1;
	@(negedge clk) disable iff(reset)
	top.cpu1.instruction[6:0] == instruction_L_type_opcode |-> 
	top.cpu1.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
endproperty

	property assume_funct3_L_type_opcode_cpu2;
	@(posedge clk) disable iff(reset)
	top.cpu2.instruction[6:0] == instruction_L_type_opcode |-> 
	top.cpu2.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
endproperty

property assume_funct3_L_type_opcode_neg_cpu2;
	@(negedge clk) disable iff(reset)
	top.cpu2.instruction[6:0] == instruction_L_type_opcode |-> 
	top.cpu2.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
endproperty
