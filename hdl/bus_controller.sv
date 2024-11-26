`timescale 1ns / 1ps

module bus_controller
(
    input logic clk,
    input logic reset,
    //------------------------------------------------
    output logic grant_core1,
    output logic grant_core2,
    //------------------------------------------------
    input logic [31:0] bus_data_in1, 
    input logic [31:0] bus_address_in1,
    input logic [ 1:0] bus_operation_in1,//BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10, BusNoN == 2'b11
    
    input logic [31:0] bus_data_in2, 
    input logic [31:0] bus_address_in2,
    input logic [ 1:0] bus_operation_in2,//BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10, BusNoN == 2'b11
    //------------------------------------------------
    output logic [31:0] bus_data_out1,
    output logic [31:0] bus_address_out1,
    output logic [ 1:0] bus_operation_out1, //BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10

    output logic [31:0] bus_data_out2,
    output logic [31:0] bus_address_out2,
    output logic [ 1:0] bus_operation_out2, //BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10
    //------------------------------------------------
    input  logic [23:0] tag_to_L2_in,
    input  logic [31:0] data_from_L2,
    input  logic [31:0] data_to_L2_input, 
    output logic [31:0] data_to_L2_out,
    output logic [23:0] tag_to_L2_out,
    output logic [31:0] address_to_L2,
    //------------------------------------------------
    //input  logic [31:0] data_from_dmem, 
    //output logic [31:0] address_to_dmem,
    //------------------------------------------------
    input logic cache_hit_in1,
    input logic cache_hit_in2,
    
    output logic cache_hit_out1,
    output logic cache_hit_out2,  
    //------------------------------------------------
    input logic [1:0] cache_hit_L2,
    //------------------------------------------------
    input logic req_core1,    
    input logic req_core2,
    
    input logic stall_core1,
    input logic stall_core2,
    
    input logic flush_in1,
    input logic flush_in2,
    
    output logic flush_out,
    
    input logic  [6:0] opcode_in1, 
    input logic  [6:0] opcode_in2,
    output logic [6:0] opcode_out
);

    logic grant_core_toggle, grant_core_toggle_next;

    always_ff @(posedge clk) begin
        if (reset) begin
            grant_core_toggle <= 1'b0;
        end else begin
            grant_core_toggle <= grant_core_toggle_next;
        end
    end
    
    always_comb begin
        grant_core1 = 1'b1;
        grant_core2 = 1'b1;
        grant_core_toggle_next = grant_core_toggle;
    
        if (req_core1 && req_core2) begin      
            if (grant_core_toggle) begin
                grant_core1 = 1'b0;
                grant_core2 = 1'b1;
                if(stall_core2 == 0) begin 
                    grant_core_toggle_next = ~grant_core_toggle;
                end    
            end else begin
                grant_core1 = 1'b1;
                grant_core2 = 1'b0;
                if(stall_core1 == 0) begin 
                    grant_core_toggle_next = ~grant_core_toggle;
                end
            end
        end
        /*
        else if(req_core1 && !req_core2) begin
                grant_core1 = 1'b1;
                grant_core2 = 1'b0;
        end  
        else if(req_core2 && !req_core1) begin
                grant_core2 = 1'b1;
                grant_core1 = 1'b0;
        end
        */  
        else begin
            grant_core1 = 1'b1;
            grant_core2 = 1'b1;
        end
    end

    always_comb begin
        bus_data_out1      = 'b0;
        bus_address_out1   = 'b0;
        bus_operation_out1 = 2'b11;
        //bus_operation_out1 = 'b0;
    
        bus_data_out2       = 'b0;
        bus_address_out2    = 'b0;
        bus_operation_out2  = 2'b11;
        //bus_operation_out2 = 'b0;
        
        cache_hit_out1 = 'b0;
        cache_hit_out2 = 'b0;
        opcode_out     = 'b0;
        address_to_L2  = 'b0;
        
        ////BusRd == 2'b00, BusUpgr == 2'b01, BusRdX == 2'b10
        if(req_core1) begin
            if(bus_operation_in1 != 2'b11 && grant_core1) begin
                bus_operation_out2    = bus_operation_in1;
                bus_address_out2      = bus_address_in1;
                address_to_L2         = bus_address_in1;
                //data_to_L2_out        = data_to_L2_input;
                opcode_out            = opcode_in1;   
                
                if(cache_hit_in2) begin
                    bus_data_out1 = bus_data_in2;
                    //bus_data_out2 = bus_data_in2;   
                    cache_hit_out1 = cache_hit_in2; 
                end 
                else if(cache_hit_L2 == 2'b10 && !cache_hit_in2) begin
                    bus_data_out1 = data_from_L2;
                    cache_hit_out1 = 0;
                end
                /*  SITUACIJA KADA JE MISS U L2 ONDA UZM
                else if(cache_hit_L2 == 2'b01) begin
                end
                */
                else begin
                    bus_data_out1 = 'b0;
                    //opcode_out    = opcode_in1;                
                end
            end
        end 
        if (req_core2) begin
            if(bus_operation_in2 != 2'b11 && grant_core2) begin
                bus_operation_out1    = bus_operation_in2;
                bus_address_out1      = bus_address_in2;
                address_to_L2         = bus_address_in2;
                //data_to_L2_out        = data_to_L2_input;
                opcode_out            = opcode_in2;
                
                if(cache_hit_in1) begin
                    //bus_data_out1 = bus_data_in1;
                    bus_data_out2 = bus_data_in1;
                    cache_hit_out2 = cache_hit_in1;
                end 
                else if(cache_hit_L2 == 2'b10 && !cache_hit_in1) begin
                    bus_data_out2 = data_from_L2;
                    cache_hit_out2 = 0;
                end
                /*  SITUACIJA KADA JE MISS U L2 ONDA UZM
                else if(cache_hit_L2 == 2'b01) begin
                end
                */
                else begin
                    bus_data_out2 = 'b0;                
                    //opcode_out    = opcode_in2;
                end
            end
        end
    end
    
    always_comb begin
        flush_out = 1'b0;
        data_to_L2_out = 0;
        tag_to_L2_out = 0;
        
        if(flush_in1 || flush_in2) begin
            flush_out = 1'b1;
            data_to_L2_out = data_to_L2_input;
            tag_to_L2_out  = tag_to_L2_in;
        end
    end
    
    //CODE FOR FLUSH
    //
    //
endmodule
