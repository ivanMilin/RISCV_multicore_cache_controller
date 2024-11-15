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
    input logic cache_hit_in1,
    input logic cache_hit_in2,
    
    output logic cache_hit_out1,
    output logic cache_hit_out2,  
    //------------------------------------------------
    input logic req_core1,    
    input logic req_core2,
    
    input logic flush_in1,
    input logic flush_in2
);

    logic grant_core_toggle, grant_core_toggle_next;

    always_ff @(negedge clk) begin
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
                grant_core_toggle_next = ~grant_core_toggle;
            end else begin
                grant_core1 = 1'b1;
                grant_core2 = 1'b0;
                grant_core_toggle_next = ~grant_core_toggle;
            end
        end else begin
            grant_core1 = 1'b1;
            grant_core2 = 1'b1;
        end
    end

    always_comb begin
        bus_data_out1      = 'b0;
        bus_address_out1   = 'b0;
        bus_operation_out1 = 'b0;
    
        bus_data_out2       = 'b0;
        bus_address_out2    = 'b0;
        bus_operation_out2  = 'b0;
        
        cache_hit_out1 = 'b0;
        cache_hit_out2 = 'b0;
        
        ////BusRd == 2'b00, BusUpgr == 2'b01, BusRdX == 2'b10
        if(req_core1) begin
            if(bus_operation_in1 == 2'b00 || bus_operation_in1 == 2'b10) begin
                bus_operation_out2 = bus_operation_in1;
                bus_address_out2   = bus_address_in1;
                
                if(cache_hit_in2) begin
                    bus_data_out1 = bus_data_in2;   
                    cache_hit_out1 = cache_hit_in2; 
                end 
                else begin
                    bus_data_out1 = 'b0;                
                end
            end
        end 
        else if (req_core2) begin
            if(bus_operation_in2 == 2'b00 || bus_operation_in2 == 2'b10) begin
                bus_operation_out1 = bus_operation_in2;
                bus_address_out1   = bus_address_in2;
                
                if(cache_hit_in1) begin
                    bus_data_out2 = bus_data_in1;
                    cache_hit_out2 = cache_hit_in1;
                end 
                else begin
                    bus_data_out2 = 'b0;                
                end
            end
        end
    end
    
    
    //CODE FOR FLUSH
    //
    //
endmodule
