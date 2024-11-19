`timescale 1ns / 1ps

//WRITE NO-ALLOCATE cache
module cache_subsystem_L2(

    input  logic clk,
    input  logic reset,
    input  logic wr_en,
    input  logic rd_en,
    
    input logic [ 6:0] opcode_in,
    input logic [ 1:0] bus_operation_in1,
    
    input  logic [31:0] bus_data_in,
    input  logic [31:0] bus_address_in,
    
    input  logic [31:0] data_from_dmem,
    
    output  logic [31:0] bus_data_out,
    output  logic [31:0] bus_address_out,

    output logic cache_hit_out
);

    typedef struct packed {
        logic valid;
        logic lru;            
        logic [21:0] tag;
        logic [31:0] data;
    } cache_line_t;

    cache_line_t cache_memory_L2[1024:0];

    logic way0_hit, way1_hit;  
    logic way0_line, way1_line; 

    // Cache LOAD HIT/MISS detection
    always_comb begin
        way0_hit = 1'b0;
        way1_hit = 1'b0;
        cache_hit_out = 'b0; 
  
        way0_line = (bus_address_in[8:2] * 2);
        way1_line = (bus_address_in[8:2] * 2) + 1;

        if(opcode_in == 7'b0000011) begin
            if(cache_memory_L2[way0_line].valid && (cache_memory_L2[way0_line].tag == bus_address_in[31:9])) begin
                way0_hit = 1'b1;
                cache_hit_out = 2'b10; 
            end
            else if(cache_memory_L2[way1_line].valid && (cache_memory_L2[way1_line].tag == bus_address_in[31:9]))begin
                way1_hit = 1'b1;
                cache_hit_out = 2'b10; 
            end
            else begin
                cache_hit_out = 2'b01;
            end
        end   
        else begin             
            way0_hit = 1'b0;
            way1_hit = 1'b0;
            cache_hit_out = 'b0;
        end                  
    end

    //Reading data from L2 if hit happens
    always_comb begin
        bus_data_out = 'b0;
        
        if(way0_hit) begin
            bus_data_out = cache_memory_L2[way0_line].data;
        end
        else if(way1_hit)begin
            bus_data_out = cache_memory_L2[way1_line].data;
        end
        else begin
            bus_data_out = 'b0;
        end
    end

    always_ff @(negedge clk) begin
        if (reset) begin
            for (int i = 0; i < 1024; i ++) begin
                cache_memory_L2[i].valid <= 0;
                cache_memory_L2[i].lru   <= 0;
                cache_memory_L2[i].tag   <= 'b0;
                cache_memory_L2[i].data  <= 'b0;
            end
        end 
        else begin
            //STORE
            if (opcode_in == 7'b0100011) begin
                if (bus_address_in[9] == 1'b0) begin
                    cache_memory_L2[way0_line].lru  <= 0;               // Mark Way 0 as recently used
                    cache_memory_L2[way1_line].lru  <= 1;               // Mark Way 1 as least recently used
                    cache_memory_L2[way0_line].data <= bus_data_in;
                    cache_memory_L2[way0_line].tag  <= bus_address_in[31:9];
                end
                if (bus_address_in[9] == 1'b1) begin
                    cache_memory_L2[way0_line].lru   <= 1;              // Mark Way 1 as recently used
                    cache_memory_L2[way1_line].lru   <= 0;              // Mark Way 0 as least recently used
                    cache_memory_L2[way1_line].data  <= bus_data_in;
                    cache_memory_L2[way0_line].tag   <= bus_address_in[31:9];
                end
            end
            //In case of LOAD MISS scenario 
            if (cache_hit_out == 2'b01 && opcode_in == 7'b0000011) begin
                if (cache_memory_L2[way0_line].lru == 1) begin
                    // Replace Way 0
                    cache_memory_L2[way0_line].valid <= 1;
                    cache_memory_L2[way0_line].tag   <= bus_address_in[31:9];
                    cache_memory_L2[way0_line].data  <= data_from_dmem;
                    cache_memory_L2[way0_line].lru   <= 0;              // Mark Way 0 as recently used
                    cache_memory_L2[way1_line].lru   <= 1;              // Mark Way 1 as least recently used
                end 
                else begin                    
                    // Replace Way 1
                    cache_memory_L2[way1_line].valid <= 1;
                    cache_memory_L2[way1_line].tag   <= bus_address_in[31:9];
                    cache_memory_L2[way1_line].data  <= data_from_dmem;
                    cache_memory_L2[way1_line].lru   <= 0;              // Mark Way 1 as recently used
                    cache_memory_L2[way0_line].lru   <= 1;              // Mark Way 0 as least recently used
                end
            end 
        end
    end

endmodule

//PITANJA
/*
    1. Da li nam treba maskiranje u ovom modulu ?
    2. Sta sa adresom koja treba da se posalje ka dmem?
    3. Sta sa onim write-alocate / write-no-alocate      
*/