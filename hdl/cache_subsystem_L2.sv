`timescale 1ns / 1ps

module cache_subsystem_L2(

    input  logic clk,
    input  logic reset,
    input  logic wr_en,
    input  logic rd_en,
    input  logic flush,
    
    input  logic [ 6:0] opcode_in,    
    input  logic [31:0] data_from_dmem,

    input  logic [31:0] bus_data_in,
    input  logic [23:0] bus_tag_in,
    input  logic [31:0] bus_address_in,
    
    output logic [31:0] data_from_L2,

    output logic [31:0] data_to_dmem,
    output logic [31:0] address_to_dmem,
    output logic [ 1:0] cache_hit_out
);

    typedef struct packed {
        logic valid;
        logic lru;            
        logic [21:0] tag;
        logic [31:0] data;
    } cache_line_t;

    cache_line_t cache_memory_L2[1023:0];

    logic way0_hit;
    logic way1_hit;  
    logic [31:0] way0_line;
    logic [11:0] way1_line; 
    
    logic [31:0] way0_line_mod;
    logic [11:0] way1_line_mod; 
    logic [31:0] way0_line_mod_s;
    logic [11:0] way1_line_mod_s; 

    always_comb begin 
        way0_line_mod   = (bus_address_in[11:0] >> 2) % 2;
        way0_line_mod_s = (bus_address_in[11:0] >> 2) / 2;

        if(bus_address_in[2] == 0) begin 
            way0_line = bus_address_in[11:0] >> 2;
            way1_line = (bus_address_in[11:0] >> 2) + 1;
        end 
        else begin 
            way0_line = (bus_address_in[11:0] >> 2) - 1;
            way1_line = bus_address_in[11:0] >> 2;
        end
    end

    // Cache LOAD HIT/MISS detection
    always_comb begin
        way0_hit = 1'b0;
        way1_hit = 1'b0;
        cache_hit_out = 'b0; 
        data_from_L2 = 'b0;

        if(opcode_in == 7'b0000011) begin
            if(cache_memory_L2[way0_line].valid && (cache_memory_L2[way0_line].tag == bus_address_in[31:9])) begin
                way0_hit = 1'b1;
                way1_hit = 1'b0; 
                cache_hit_out = 2'b10;
                data_from_L2 = cache_memory_L2[way0_line].data;
            end
            else if(cache_memory_L2[way1_line].valid && (cache_memory_L2[way1_line].tag == bus_address_in[31:9]))begin
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
    end
    
    always_ff @(negedge clk) begin
        if (reset) begin
            data_to_dmem <= 'b0;
            address_to_dmem <= 'b0;            
            for (integer i = 0; i < 1024; i++) begin
                    cache_memory_L2[i].valid <= 0;
                    cache_memory_L2[i].lru   <= 0;
                    cache_memory_L2[i].tag   <= 0;//'b0;
                    cache_memory_L2[i].data  <= 0;//'b0;
            end
        end 
        else begin
            if (flush == 1'b1) begin
                //If tag does not exist in L2 just store in L2 cache
                if(cache_memory_L2[way0_line].tag != bus_address_in[31:9] || cache_memory_L2[way1_line].tag != bus_address_in[31:9]) begin
                    if (bus_address_in[2] == 1'b0) begin
                        cache_memory_L2[way0_line].valid <= 1;
                        cache_memory_L2[way0_line].lru   <= 0;               // Mark Way 0 as recently used
                        cache_memory_L2[way1_line].lru   <= 1;               // Mark Way 1 as least recently used
                        cache_memory_L2[way0_line].data  <= bus_data_in;
                        cache_memory_L2[way0_line].tag   <= bus_tag_in[23:2];//bus_address_in[31:9];
                    end
                    if (bus_address_in[2] == 1'b1) begin
                        cache_memory_L2[way1_line].valid <= 1;
                        cache_memory_L2[way0_line].lru   <= 1;              // Mark Way 1 as recently used
                        cache_memory_L2[way1_line].lru   <= 0;              // Mark Way 0 as least recently used
                        cache_memory_L2[way1_line].data  <= bus_data_in;
                        cache_memory_L2[way1_line].tag   <= bus_tag_in[23:2];//bus_address_in[31:9];
                    end
                end
                //If tag exists in L2 and you remove this tag, first store this data in dmem, 
                //and then store data with different tag in L2 cache      
                else begin  
                    if (bus_address_in[2] == 1'b0) begin
                        cache_memory_L2[way0_line].valid <= 1;
                        cache_memory_L2[way0_line].lru   <= 0;               // Mark Way 0 as recently used
                        cache_memory_L2[way1_line].lru   <= 1;               // Mark Way 1 as least recently used
                        cache_memory_L2[way0_line].data  <= bus_data_in;
                        cache_memory_L2[way0_line].tag   <= bus_tag_in[23:2];//bus_address_in[31:9];
                        data_to_dmem                     <= cache_memory_L2[way0_line].data;
                        address_to_dmem                  <= bus_address_in;
                    end
                    if (bus_address_in[2] == 1'b1) begin
                        cache_memory_L2[way1_line].valid <= 1;
                        cache_memory_L2[way0_line].lru   <= 1;              // Mark Way 1 as recently used
                        cache_memory_L2[way1_line].lru   <= 0;              // Mark Way 0 as least recently used
                        cache_memory_L2[way1_line].data  <= bus_data_in;
                        cache_memory_L2[way1_line].tag   <= bus_tag_in[23:2];//bus_address_in[31:9];
                        data_to_dmem                     <= cache_memory_L2[way1_line].data;
                        address_to_dmem                  <= bus_address_in;
                    end
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
                    cache_memory_L2[way1_line].lru   <= 1;              // Mark Way 0 as least recently used
                end
            end
            else if(cache_hit_out == 2'b10 && opcode_in == 7'b0000011) begin                                                
                if(way0_hit == 1) begin                                 // This else statement is dedicated for
                    cache_memory_L2[way1_line].lru   <= 1;              // scenario when LOAD-HIT happens
                    cache_memory_L2[way0_line].lru   <= 0;              // Depending on which way has hit, you      
                end                                                     // have to change LRU in both ways
                else if(way1_hit == 1) begin
                    cache_memory_L2[way0_line].lru   <= 1;
                    cache_memory_L2[way1_line].lru   <= 0;
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