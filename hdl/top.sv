`timescale 1ns / 1ps

module top
(
    input logic clk,
    input logic reset
);
    logic [31:0] bus_data_in1, bus_address_in1;
    logic [ 1:0] bus_operation_in1, bus_operation_in2;
    logic [31:0] bus_data_in2, bus_address_in2; 

    logic [31:0] bus_data_out1, bus_address_out1;
    logic [1:0] bus_operation_out1, bus_operation_out2;
    logic [31:0] bus_data_out2, bus_address_out2;
    logic [6:0] opcode_out1, opcode_out2, opcode_from_bus;
    
    logic cache_hit_in1, cache_hit_in2; 
    logic cache_hit_out1, cache_hit_out2;
    
    logic grant_core1, grant_core2;
    logic req_core1, req_core2;
    logic flush_in1, flush_in2;
    logic stall_core1, stall_core2;
    
    logic [31:0] data_to_L2_1 , data_to_L2_2, data_to_L2_s;
    logic [31:0] data_from_L2, address_to_L2, data_to_L2;
    logic [1:0] cache_hit_L2;
    
    Processor # (.file_cpu(1))
    cpu1 
    (
        .clk(clk), 
        .reset(reset),
        
        .bus_data_in(bus_data_in1),
        .bus_address_in(bus_address_in1),
        .bus_operation_in(bus_operation_in1),
        
        .bus_data_out(bus_data_out1),
        .bus_address_out(bus_address_out1),
        .bus_operation_out(bus_operation_out1),
        
        .data_to_L2(data_to_L2_1),
        
        .cache_hit_in(cache_hit_in1),
        .cache_hit_out(cache_hit_out1),
        
        .grant(grant_core1),
        .req_core(req_core1),
        .stall_out(stall_core1),
        .flush_out(flush_in1),
        .opcode_out(opcode_out1) 
    );
    
    bus_controller bus_ctrl
    (
        .clk(clk),
        .reset(reset),
        //------------------------------------------------
        .grant_core1(grant_core1),
        .grant_core2(grant_core2),
        //------------------------------------------------
        .bus_data_in1(bus_data_out1),
        .bus_address_in1(bus_address_out1),
        .bus_operation_in1(bus_operation_out1),
        
        .bus_data_in2(bus_data_out2),
        .bus_address_in2(bus_address_out2),
        .bus_operation_in2(bus_operation_out2),
        //------------------------------------------------
        .bus_data_out1(bus_data_in1),
        .bus_address_out1(bus_address_in1),
        .bus_operation_out1(bus_operation_in1),
        
        .bus_data_out2(bus_data_in2),
        .bus_address_out2(bus_address_in2),
        .bus_operation_out2(bus_operation_in2),
        //------------------------------------------------
        .data_from_L2(data_from_L2), 
        .address_to_L2(address_to_L2),
        .data_to_L2_input(data_to_L2_s),
        .data_to_L2_out(data_to_L2),
        //------------------------------------------------
        .data_from_dmem(), 
        .address_to_dmem(),
        //------------------------------------------------
        .cache_hit_in1(cache_hit_out1),
        .cache_hit_in2(cache_hit_out2),
        
        .cache_hit_out1(cache_hit_in1),
        .cache_hit_out2(cache_hit_in2),
        //------------------------------------------------
        .cache_hit_L2(cache_hit_L2),
        //------------------------------------------------
        .req_core1(req_core1),
        .req_core2(req_core2),
        
        .stall_core1(stall_core1),
        .stall_core2(stall_core2),
        
        .flush_in1(flush_in1),
        .flush_in2(flush_in2),
        
        .opcode_in1(opcode_out1), 
        .opcode_in2(opcode_out2),
        .opcode_out(opcode_from_bus)
    );
    
    Processor # (.file_cpu(2))
    cpu2
    (
        .clk(clk), 
        .reset(reset),
        
        .bus_data_in(bus_data_in2),
        .bus_address_in(bus_address_in2),
        .bus_operation_in(bus_operation_in2),
        
        .bus_data_out(bus_data_out2),
        .bus_address_out(bus_address_out2),
        .bus_operation_out(bus_operation_out2),
        
        .data_to_L2(data_to_L2_2),
        
        .cache_hit_in(cache_hit_in2),
        .cache_hit_out(cache_hit_out2),
        
        .grant(grant_core2),
        .req_core(req_core2),
        .stall_out(stall_core2),
        .flush_out(flush_in2),
        .opcode_out(opcode_out2)        
    );
    
    cache_subsystem_L2 cache_L2
    (    
        .clk(clk),
        .reset(reset),
        .wr_en(wr_en),
        .rd_en(rd_en),
        .flush(),
        
        .opcode_in(opcode_from_bus),
        //.bus_operation_in(),
        
        .data_from_dmem(0),
        .bus_data_in(data_to_L2),
        .bus_address_in(address_to_L2),
        
        .data_from_L2(data_from_L2),
        
        .bus_address_out(),
    
        .cache_hit_out(cache_hit_L2)
    );
    
    always_comb begin 
    data_to_L2_s = 'b0;
        if(req_core1 && grant_core1 && opcode_out1 == 7'b0100011) begin 
            data_to_L2_s = data_to_L2_1;
        end 
        else if(req_core2 && grant_core2 && opcode_out2 == 7'b0100011) begin 
            data_to_L2_s = data_to_L2_2;
        end
    end
endmodule
