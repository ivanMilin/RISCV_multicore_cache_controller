module  checker_controller 
(
	input clk,
	input reset,
	input [31:0] instruction,
	input [3:0] alu_op,
	input [2:0] mask,
	input [2:0] br_type,
	input reg_wr,
	input sel_A,
	input sel_B,
	input rd_en,
	input wr_en,
	input [1:0] wb_sel
);

	parameter[6:0] instruction_R_type_opcode = 7'b0110011;
	parameter[6:0] instruction_I_type_opcode = 7'b0010011;
	parameter[6:0] instruction_L_type_opcode = 7'b0000011;
	parameter[6:0] instruction_S_type_opcode = 7'b0100011;
	parameter[6:0] instruction_B_type_opcode = 7'b1100011;
	parameter[6:0] instruction_U_type_opcode = 7'b0110111;
	parameter[6:0] instruction_J_type_opcode = 7'b1101111;

	default
	clocking @(posedge clk);
	endclocking

	default disable iff reset;
	
	assign func3_past = Controller.func3_past;

	
	//asm_opcode: assume property(instruction[6:0] == instruction_R_type_opcode);	
	asm_opcode: assume property(instruction[6:0] inside {instruction_R_type_opcode, instruction_I_type_opcode, instruction_L_type_opcode, instruction_S_type_opcode, instruction_B_type_opcode, instruction_U_type_opcode, instruction_J_type_opcode});
	
	property R_check_sra_sub;
		(instruction[6:0] == instruction_R_type_opcode && 
		 instruction[14:12] == 3'b000 && 
		 instruction[31:25] == 7'b0100000) |=>
		(alu_op inside {6, 9} && reg_wr == 1 && sel_A  == 1 && sel_B  == 0 && rd_en  == 0 &&  wb_sel == 0); 
	endproperty
	
	property R_check_others;
		(instruction[6:0] == instruction_R_type_opcode && 
		instruction[14:12] == 3'b000 && 
		instruction[31:25] == 7'b0000000) |=>
		(alu_op inside {0, 1, 2, 3, 4, 5, 7, 8} && reg_wr == 1 && sel_A  == 1 && sel_B  == 0 && rd_en  == 0 && wb_sel == 0);
	endproperty

	property I_check_srai;
		(instruction[6:0] == instruction_I_type_opcode && 
                 instruction[14:12] == 3'b101 && 
                 instruction[31:25] == 7'b0100000)|=>
   		 (alu_op == 6 && reg_wr  == 1 && sel_A == 1 && sel_B   == 1 && rd_en   == 0 &&  wb_sel  == 0);
	endproperty

	property I_check_others;
		(instruction[6:0] == instruction_I_type_opcode && 
		 instruction[14:12] == 3'b101 && 
                 instruction[31:25] == 7'b0000000) |=>
		 (alu_op inside {0, 1, 2, 3, 4, 5, 7, 8} && reg_wr  == 1 && sel_A   == 1 && sel_B   == 1 && rd_en   == 0 && wb_sel  == 0);
	endproperty

	property L_check;
		(instruction[6:0] == instruction_L_type_opcode) |=>
		(alu_op == 0 && 
		 reg_wr == 1 && 
		 sel_A  == 1 && 
		 sel_B  == 1 && 
		 rd_en  == 1 && 
		 wr_en  == 0 && 
		 wb_sel == 1 && 
		 //mask == func3_past);		 
		 (func3_past inside {0, 1, 2, 4, 5}));
	endproperty

	property S_check;
		(reset == 0 && instruction[6:0] == instruction_S_type_opcode) |=>
		(alu_op == 0 && 
		 reg_wr == 0 && 
		 sel_A  == 1 && 
		 sel_B  == 1 && 
		 rd_en  == 1 && 
		 wr_en  == 1 && 
		 wb_sel == 1 && 
		 //mask == func3_past);		 
		 (func3_past inside {0, 1, 2, 4, 5}));
	endproperty	
		
	property B_check;
		(reset == 0 && instruction[6:0] == instruction_B_type_opcode) |=>
		(alu_op == 0 && 
		 reg_wr == 0 && 
		 sel_A  == 0 && 
		 sel_B  == 1 && 
		 rd_en  == 0 && 
		 wr_en  == 0 && 
		 wb_sel == 0 && 
		 //br_type == func3_past);		 
		 (func3_past inside {0, 1, 4, 5, 6, 7}));
	endproperty

	property J_check;
		(instruction[6:0] == instruction_J_type_opcode) |=>
		(alu_op == 0 && 
		 reg_wr == 1 && 
		 sel_A  == 0 && 
		 sel_B  == 1 && 
		 rd_en  == 0 && 
		 wr_en  == 0 && 
		 wb_sel == 2);
	endproperty

	assert_R_check_sra_sub : assert property (@(posedge clk) R_check_sra_sub);
	assert_R_check_others  : assert property (@(posedge clk) R_check_others);
	assert_I_check_srai	   : assert property (@(posedge clk) I_check_srai);
	assert_I_check_others  : assert property (@(posedge clk) I_check_others);
	assert_L_check 		   : assert property (@(posedge clk) L_check);
	assert_S_check 		   : assert property (@(posedge clk) S_check);
	assert_B_check         : assert property (@(posedge clk) B_check);
	assert_J_check         : assert property (@(posedge clk) J_check);
endmodule
