module checker_branch(
	input logic clk,
	input logic reset,
	input logic [31:0] rs1, 
	input logic [31:0] rs2, 
	input logic [2:0] br_type, 
	input logic [6:0] opcode,
	input logic br_taken
);

	//logic jump;
	//logic branch;

	// Paremter section 
	parameter [6:0] instruction_B_opcode = 7'b1100011;
	parameter [6:0] instruction_J_opcode = 7'b1101111;

	// Default clokcing and reset
	default 
	clocking @(posedge clk); 
	endclocking
	default disable iff reset;

	asm_opcode      : assume property (opcode inside {instruction_B_opcode,instruction_J_opcode});
	asm_branch_type : assume property (br_type[2:0] inside {0,1,4,5,6,7});
	//asm_branch_type : assume property (br_type[2:0] == 4);

	// Additional assume
	//asm_rs1_rs2_small_values : assume property (rs1 == 2 && rs2 == 3); 

	// Grey box signal fetching
	assign jump = BranchCondition.jump;
	assign branch = BranchCondition.branch;

	property check_br_taken;
		(jump | branch) |-> br_taken;
		//!jump ##0 !branch |=> !br_taken;
		//(br_taken == 0) |-> $past(!jump) && $past(!branch);
	endproperty

	ast_check_br_taken : assert property (check_br_taken);

endmodule
