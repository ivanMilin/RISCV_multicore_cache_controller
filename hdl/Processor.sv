`timescale 1ns / 1ps

module Processor #
(
    parameter integer file_cpu = 1
)
(
    input logic clk, 
    input logic reset,
    
    input logic [31:0] bus_data_in,
    input logic [31:0] bus_address_in,
    input logic [ 1:0] bus_operation_in, //BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10
    
    // data will go to the shared bus
    output logic [31:0] data_to_L2,
    output logic [31:0] bus_data_out, 
    output logic [31:0] bus_address_out,
    output logic [ 1:0] bus_operation_out,//BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10, BusNoN == 2'b11

    input logic cache_hit_in,  
    output logic cache_hit_out,

    input  logic grant,
    output logic req_core,    
    output logic flush_out,
    output logic [6:0] opcode_out
);

    logic [31:0] plus4, next_index, wdata_s, rdata, index, A, B, B_i, A_r, B_r, instruction, alu_out, add_imm_s, data_out;
    logic [31:0] dmem_address;
    logic [9 :0] dmem_address_out;
    logic [3:0] alu_op;
    logic [2:0] mask, br_type;
    logic [1:0] wb_sel;
    logic reg_wr, rd_en, wr_en, sel_A, sel_B, br_taken, stall, dmem_rd_en, dmem_wr_en;
    
    PC pc (.clk(clk), .reset(reset), .B(next_index), .A(index));
           
    Add4 add4 (.stall(stall || ~grant), .reset(reset), .A(index), .B(plus4));
    add_immediate add_imm(.in1(index), .in2(B_i), .out(add_imm_s));
    Mux2 select_PC (.A(plus4), .B(add_imm_s), .sel(br_taken), .C(next_index));
    
    InstructionMemory #(.file_cpu(file_cpu)) im(.addr(index), .instruction(instruction));

    RegisterFile rf (.clk(clk), .reset(reset), .reg_wr(reg_wr && !stall), .raddr1(instruction[19:15]), .raddr2(instruction[24:20]), .waddr(instruction[11:7]), .wdata(wdata_s), .rdata1(A_r), .rdata2(B_r));
    ImmediateGenerator ig (.clk(clk), .instruction(instruction), .imm_out(B_i));

    Mux2 select_A (.A(index), .B(A_r), .sel(sel_A), .C(A));
    Mux2 select_B (.A(B_r), .B(B_i), .sel(sel_B), .C(B));
    BranchCondition bc (.rs1(A_r), .rs2(B_r), .br_type(br_type), .opcode(instruction[6:0]), .br_taken(br_taken));

    Controller controller (.instruction(instruction), .alu_op(alu_op), .mask(mask), .br_type(br_type), .reg_wr(reg_wr), .sel_A(sel_A), .sel_B(sel_B), .rd_en(rd_en), .wr_en(wr_en), .wb_sel(wb_sel));
    ALU alu (.A(A), .B(B), .alu_op(alu_op), .C(alu_out));
    
    cache_subsystem_L1 controller_and_cache
       (.clk(clk), .reset(reset), .wr_en(wr_en), .rd_en(rd_en), .grant(grant), .mask_in(mask), .opcode_in(instruction[6:0]), .data_in(B_r), .address_in(alu_out), 
        .bus_data_in(bus_data_in),  .bus_address_in(bus_address_in),   .bus_operation_in(bus_operation_in), 
        .bus_data_out(bus_data_out), .bus_address_out(bus_address_out), .bus_operation_out(bus_operation_out),
        .data_out(data_out), .cache_hit_in(cache_hit_in), .cache_hit_out(cache_hit_out), .stall(stall), 
        .req_core(req_core), .flush_out(flush_out), .opcode_out(opcode_out), .data_to_L2(data_to_L2));
        
    WriteBack writeback (.A(alu_out), .B(data_out), .C(index), .wb_sel(wb_sel), .wdata(wdata_s));

endmodule
