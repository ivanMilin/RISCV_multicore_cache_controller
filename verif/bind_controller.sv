bind Controller checker_controller chk_controller 
(
	.instruction(instruction),
	.alu_op(alu_op),
	.mask(mask),
	.br_type(br_type),
	.reg_wr(reg_wr),
	.sel_A(sel_A),
	.sel_B(sel_B),
	.rd_en(rd_en),
	.wr_en(wr_en),
	.wb_sel(wb_sel)
);
