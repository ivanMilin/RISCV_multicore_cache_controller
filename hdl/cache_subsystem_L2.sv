`timescale 1ns / 1ps

//WRITE NO-ALLOCATE cache
module cache_subsystem_L2(

    input  logic clk,
    input  logic reset,
    input  logic wr_en,
    input  logic rd_en,
    input  logic flush,
    
    input logic [ 6:0] opcode_in,
    //input logic [ 1:0] bus_operation_in,
    
    input  logic [31:0] data_from_dmem,
    input  logic [31:0] bus_data_in,
    input  logic [31:0] bus_address_in,
    
    output  logic [31:0] data_from_L2,
    output  logic [31:0] bus_address_out,

    output  logic [1:0] cache_hit_out
);

    typedef struct packed {
        logic valid;
        logic lru;            
        logic [21:0] tag;
        logic [31:0] data;
    } cache_line_t;

    cache_line_t cache_memory_L2[1023:0];

    logic way0_hit, way1_hit;  
    logic [31:0] way0_line, way1_line; 

    assign way0_line = (bus_address_in >> 2);// & 9'b111111111;
    assign way1_line = (bus_address_in >> 2) + 1;

    /*
    always_comb begin
        if(bus_address_in < 256) begin
            way0_line = bus_address_in[9:2];
            way1_line = bus_address_in[9:2]+1;
        end 
        else begin
            way0_line = {bus_address_in[8:0],1'b0};
            way1_line = {bus_address_in[8:0],1'b1};
        end
    end
    */
    
    // Cache LOAD HIT/MISS detection
    always_comb begin
        way0_hit = 1'b0;
        way1_hit = 1'b0;
        cache_hit_out = 'b0; 
        data_from_L2 = 'b0;

        if(opcode_in == 7'b0000011) begin
            if(cache_memory_L2[way0_line].valid && (cache_memory_L2[way0_line].tag == bus_address_in[31:10])) begin
                way0_hit = 1'b1;
                way1_hit = 1'b0; 
                cache_hit_out = 2'b10;
                data_from_L2 = cache_memory_L2[way0_line].data;
            end
            else if(cache_memory_L2[way1_line].valid && (cache_memory_L2[way1_line].tag == bus_address_in[31:10]))begin
                way0_hit = 1'b0;
                way1_hit = 1'b1; 
                cache_hit_out = 2'b10;
                data_from_L2 = cache_memory_L2[way1_line].data;
            end
            else begin
                way0_hit = 1'b0;
                way1_hit = 1'b0;
                cache_hit_out = 2'b01;
                data_from_L2 = 'b0;
            end
        end
        /*   
        else begin             
            way0_hit = 1'b0;
            way1_hit = 1'b0;
            cache_hit_out = 'b0;
        end
        */                  
    end
    
    always_ff @(negedge clk) begin
        if (reset) begin
            for (integer i = 0; i < 1024; i++) begin
                if(i == 255) begin
                    cache_memory_L2[i].valid <= 1;
                    cache_memory_L2[i].lru   <= 0;
                    cache_memory_L2[i].tag   <= 0;//'b0;
                    cache_memory_L2[i].data  <= i;//'b0;
                end
                else begin
                    cache_memory_L2[i].valid <= 1;
                    cache_memory_L2[i].lru   <= 0;
                    cache_memory_L2[i].tag   <= 2;//'b0;
                    cache_memory_L2[i].data  <= i;//'b0;
                end
            end
        end 
        else begin
            //STORE WORD - ADD LOGIC FOR SAME TAG STORE - IF bus_addres_in[31:10] and cache_memory_L2[way0_line].tag are same 
            //             new data stores in L2, and previous moves to data memory. Add this also in way1 segment.
            if (opcode_in == 7'b0100011) begin
                if (bus_address_in[0] == 1'b1) begin
                    cache_memory_L2[way0_line].lru  <= 0;               // Mark Way 0 as recently used
                    cache_memory_L2[way1_line].lru  <= 1;               // Mark Way 1 as least recently used
                    cache_memory_L2[way0_line].data <= bus_data_in;
                    cache_memory_L2[way0_line].tag  <= bus_address_in[31:10];
                end
                if (bus_address_in[0] == 1'b0) begin
                    cache_memory_L2[way0_line].lru   <= 1;              // Mark Way 1 as recently used
                    cache_memory_L2[way1_line].lru   <= 0;              // Mark Way 0 as least recently used
                    cache_memory_L2[way1_line].data  <= bus_data_in;
                    cache_memory_L2[way0_line].tag   <= bus_address_in[31:10];
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