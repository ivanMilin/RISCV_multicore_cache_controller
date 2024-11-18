`timescale 1ns / 1ps

module top
(
    input logic clk,
    input logic reset
);
    logic [31:0] bus_data_in1, bus_address_in1;
    logic [1:0] bus_operation_in1, bus_operation_in2;
    logic [31:0] bus_data_in2, bus_address_in2; 

    logic [31:0] bus_data_out1, bus_address_out1;
    logic [1:0] bus_operation_out1, bus_operation_out2;
    logic [31:0] bus_data_out2, bus_address_out2;
    
    logic cache_hit_in1, cache_hit_in2; 
    logic cache_hit_out1, cache_hit_out2;
    
    logic grant_core1, grant_core2;
    logic req_core1, req_core2;
    logic flush_in1, flush_in2;
    
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
        
        .cache_hit_in(cache_hit_in1),
        .cache_hit_out(cache_hit_out1),
        
        .grant(grant_core1),
        .req_core(req_core1),
        .flush_out(flush_in1)
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
        .cache_hit_in1(cache_hit_out1),
        .cache_hit_in2(cache_hit_out2),
        
        .cache_hit_out1(cache_hit_in1),
        .cache_hit_out2(cache_hit_in2),
        //------------------------------------------------
        .req_core1(req_core1),
        .req_core2(req_core2),
        
        .flush_in1(flush_in1),
        .flush_in2(flush_in2)
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
        
        .cache_hit_in(cache_hit_in2),
        .cache_hit_out(cache_hit_out2),
        
        .grant(grant_core2),
        .req_core(req_core2),
        .flush_out(flush_in2)
    );
endmodule
