module ref_model
(
	input clk,
	input reset,
	input[31:0] plus4,
	input[31:0] next_index,
	input[31:0] wdata,
	input[31:0] rdata,
	input[31:0] index,
	input[31:0] A,
	input[31:0] B,
	input[31:0] B_i,
	input[31:0] A_r,
	input[31:0] B_r,
	input[31:0] instruction,
	input[31:0] alu_out,
	input[3:0] alu_op,
	input[2:0] mask,
	input[2:0] br_type,
	input[1:0] wb_sel,
	logic reg_wr,
	logic rd_en,
	logic wr_en,
	logic sel_A,
	logic sel_B,
	logic br_taken 
);
endmodule
