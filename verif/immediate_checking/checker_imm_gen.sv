module  checker_imm_gen 
(
	input clk,
	input reset,
        input logic [31:0] instruction,
	input logic [31:0] imm_out,
	input logic [31:0] instruction_previous
);

    // Parameters
	parameter[6:0] instruction_I_type_opcode = 7'b0010011;
	parameter[6:0] instruction_L_type_opcode = 7'b0000011;
	parameter[6:0] instruction_S_type_opcode = 7'b0100011;
	parameter[6:0] instruction_B_type_opcode = 7'b1100011;
	parameter[6:0] instruction_U_type_opcode = 7'b0110111;
	parameter[6:0] instruction_J_type_opcode = 7'b1101111;

	// Default clocking and reset
	default
	clocking @(posedge clk);
	endclocking

	default disable iff reset;
	
	// Assumes 
	asm_opcode: assume property(instruction[6:0] inside {instruction_I_type_opcode, instruction_L_type_opcode, instruction_S_type_opcode, instruction_B_type_opcode, instruction_U_type_opcode, instruction_J_type_opcode});
	//asm_opcode: assume property(instruction[6:0] inside {instruction_J_type_opcode,instruction_U_type_opcode});	
	//asm_opcode: assume property(instruction[6:0] inside {instruction_J_type_opcode});

	// Properties
	property check_I_type_srli_slli; 
		instruction[6:0] == instruction_I_type_opcode && (instruction[14:12] inside {1,5}) |=> imm_out == {27'b0,instruction_previous[24:20]} ;
	endproperty
	
	property check_I_type_others; 
		//(imm_out == instruction[31:20]) |-> ($past(instruction[6:0]) == instruction_I_type_opcode && $past(instruction[14:12]) inside {0,2,3,4,6,7});
		instruction[6:0] == instruction_I_type_opcode && instruction[14:12] inside {0,2,3,4,6,7} |=> imm_out == {20'b0,instruction_previous[31:20]};	
	endproperty
	
	property check_L; 
		//(imm_out == instruction[31:20]) |-> ($past(instruction[6:0]) == instruction_L_type_opcode);
		instruction[6:0] == instruction_L_type_opcode |=> imm_out == instruction_previous[31:20];	
	endproperty

	property check_S; 
		//(imm_out == {{20{instruction[31]}}, instruction[31:25], instruction[11:7]}) |=> ($past(instruction[6:0]) == instruction_S_type_opcode);
		instruction[6:0] == instruction_S_type_opcode |=> imm_out == {{20{instruction_previous[31]}}, instruction_previous[31:25], instruction_previous[11:7]};
	endproperty
	
	property check_B; 
		//(imm_out == {{20{instruction[31]}}, instruction[31:25], instruction[11:7]}) |=> ($past(instruction[6:0]) == instruction_B_type_opcode);
		instruction[6:0] == instruction_B_type_opcode |=> imm_out == {{20{instruction_previous[31]}}, instruction_previous[31:25], instruction_previous[11:7]};
	endproperty
	
	property check_U; 
		//(imm_out == {instruction[31:12], 12'b0}) |=> ($past(instruction[6:0]) == instruction_U_type_opcode);
		instruction[6:0] == instruction_U_type_opcode |=> imm_out == {instruction_previous[31:12], 12'b0};
	endproperty
	
	property check_J; 
		//(imm_out == {{12{instruction[31]}}, instruction[19:12], instruction[20], instruction[30:21], 1'b0}) |=> ($past(instruction[6:0]) == instruction_J_type_opcode);
		instruction[6:0] == instruction_J_type_opcode |=> imm_out == {{12{instruction_previous[31]}}, instruction_previous[19:12], instruction_previous[20], instruction_previous[30:21], 1'b0};
	endproperty
	
	
	// Asserts
	ast_check_i_srli_slli   : assert property (check_I_type_srli_slli);
	ast_check_I_type_others : assert property (check_I_type_others);
	ast_check_L 		: assert property (check_L);
	ast_check_S 		: assert property (check_S);
	ast_check_B 		: assert property (check_B);
	ast_check_U 		: assert property (check_U);
	ast_check_J 		: assert property (check_J);
	
endmodule
