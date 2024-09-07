module  checker_controller 
(
	instruction,
	alu_op,
	mask,
	br_type,
	reg_wr,
	sel_A,
	sel_B,
	rd_en,
	wr_en,
	wb_sel
);

parameter[6:0] instuction_R_type_opcode = 7'b0110011;
parameter[6:0] instuction_I_type_opcode = 7'b0010011;
parameter[6:0] instuction_L_type_opcode = 7'b0000011;
parameter[6:0] instuction_S_type_opcode = 7'b0100011;
parameter[6:0] instuction_B_type_opcode = 7'b1100011;
parameter[6:0] instuction_U_type_opcode = 7'b0110111;
parameter[6:0] instuction_J_type_opcode = 7'b1101111;

asm_opcode: assume property(instuction[6:0] inside {instuction_R_type_opcode, instuction_I_type_opcode, instuction_L_type_opcode, instuction_S_type_opcode, instuction_B_type_opcode, instuction_U_type_opcode, instuction_J_type_opcode});

property R_check_sub;
	if((instuction[6:0] == instuction_R_type_opcode) && (instuction[14:12] == 3'b000) && (instuction[31:25] == 7'b0100000)) 
		alu_op = 9;
		reg_wr = 1;
    		sel_A = 1;
		sel_B = 0;
		rd_en = 0;
		wb_sel = 0;
	end																				 
endproperty

ast_R_sub : assert property (R_check_sub);

endmodule
