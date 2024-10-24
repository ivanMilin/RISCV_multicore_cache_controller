module Processor(input logic clk, reset);
    logic [31:0] plus4, next_index, wdata, rdata, index, A, B, B_i, A_r, B_r, instruction, alu_out, add_imm_s, data_from_cache, data_to_dmem;
    logic [9:0] dmem_address;
    logic [3:0] alu_op;
    logic [2:0] mask, br_type;
    logic [1:0] wb_sel;
    logic reg_wr, rd_en, wr_en, sel_A, sel_B, br_taken, stall, dmem_rd_en, dmem_wr_en;
    
    PC pc (.clk(clk), .reset(reset), .B(next_index), .A(index));
           
    Add4 add4 (.stall(stall), .reset(reset), .A(index), .B(plus4));
    add_immediate add_imm(.in1(index), .in2(B_i), .out(add_imm_s));
    Mux2 select_PC (.A(plus4), .B(add_imm_s), .sel(br_taken), .C(next_index));
    
    InstructionMemory im (.addr(index), .instruction(instruction));

    RegisterFile rf (.clk(clk), .reset(reset), .reg_wr(reg_wr), .raddr1(instruction[19:15]), .raddr2(instruction[24:20]), .waddr(instruction[11:7]), .wdata(wdata), .rdata1(A_r), .rdata2(B_r));
    ImmediateGenerator ig (.clk(clk), .instruction(instruction), .imm_out(B_i));

    Mux2 select_A (.A(index), .B(A_r), .sel(sel_A), .C(A));
    Mux2 select_B (.A(B_r), .B(B_i), .sel(sel_B), .C(B));
    BranchCondition bc (.rs1(A_r), .rs2(B_r), .br_type(br_type), .opcode(instruction[6:0]), .br_taken(br_taken));

    Controller controller (.instruction(instruction), .alu_op(alu_op), .mask(mask), .br_type(br_type), .reg_wr(reg_wr), .sel_A(sel_A), .sel_B(sel_B), .rd_en(rd_en), .wr_en(wr_en), .wb_sel(wb_sel));
    ALU alu (.A(A), .B(B), .alu_op(alu_op), .C(alu_out));
    
    DataMemory datamemory (.addr({22'b0,dmem_address}), .wdata(data_to_dmem), .mask(mask), .wr_en(wr_en || dmem_wr_en), .rd_en(rd_en || dmem_rd_en), .clk(clk), .reset(reset), .rdata(rdata));
    cache_subsystem_L1 controller_and_cache(.clk(clk), .reset(reset), .wr_en(wr_en), .rd_en(rd_en), .opcode_in(instruction[6:0]), .mask(mask), .data_in(B_r), .index_in(alu_out[7:0]), .tag_in(alu_out[9:8]), .stall(stall), .data_to_dmem(data_to_dmem), .data_from_dmem(rdata), .dmem_address(dmem_address), .data_from_cache(data_from_cache), .dmem_rd_en(dmem_rd_en), .dmem_wr_en(dmem_wr_en));
    WriteBack writeback (.A(alu_out), .B(data_from_cache), .C(index), .wb_sel(wb_sel), .wdata(wdata));
endmodule
