`timescale 1ns / 1ps

module cache_subsystem_L2(

    input  logic clk,
    input  logic reset,
    input  logic wr_en, // NOT USED
    input  logic rd_en, // NOT USED
    input  logic flush,
    
    input  logic [ 6:0] opcode_in,    
    input  logic [31:0] data_from_dmem,

    input  logic [31:0] bus_data_in,
    input  logic [23:0] bus_tag_in,
    input  logic [31:0] bus_address_in,
    
    output logic [31:0] data_from_L2,

    output logic [31:0] data_to_dmem,
    output logic [31:0] address_to_dmem,
    output logic [ 6:0] opcode_out,
    output logic [ 1:0] cache_hit_out
);

    typedef struct packed {
        logic valid;
        logic lru;            // 1 for least recently used, 0 for most recently used
        logic [22:0] tag;
        logic [31:0] data;
    } cache_line_t;

    // 2-way set associative cache: 512 sets with 2 ways each
    cache_line_t cache_memory_L2[511:0][1:0];

    logic [8:0] set_index;  // Extract 9-bit set index from the address
    logic [22:0] tag;       // Extract 22-bit tag
    logic way0_hit, way1_hit;

    assign set_index = bus_address_in[8:0]; 
    assign tag = bus_address_in[31:9];  

    always_comb begin
        cache_hit_out = 'b0;
        data_from_L2 = 'b0;
        
        way0_hit = cache_memory_L2[set_index][0].valid && (cache_memory_L2[set_index][0].tag == tag);
        way1_hit = cache_memory_L2[set_index][1].valid && (cache_memory_L2[set_index][1].tag == tag);

        if (opcode_in == 7'b0000011) begin // LOAD instruction
            if (way0_hit) begin
                cache_hit_out = 2'b10;  // HIT
                data_from_L2 = cache_memory_L2[set_index][0].data;
            end else if (way1_hit) begin
                cache_hit_out = 2'b10;  // HIT
                data_from_L2 = cache_memory_L2[set_index][1].data;
            end else begin
                cache_hit_out = 2'b01;  // MISS
            end
        end
    end

    always_ff @(negedge clk) begin
    if (reset) begin
        data_to_dmem <= 'b0;
        address_to_dmem <= 'b0;
        opcode_out <= 'b0;
        for (integer i = 0; i < 512; i++) begin
            for (integer j = 0; j < 2; j++) begin
                cache_memory_L2[i][j].valid <= 0;
                cache_memory_L2[i][j].lru   <= 0;  // Way 0: LRU=0, Way 1: LRU=1
                cache_memory_L2[i][j].tag   <= 'b0;
                cache_memory_L2[i][j].data  <= 'b0;
            end
        end
    end 
    else begin
        if (flush == 1'b1) begin
           // Oba su slobodna
           if(cache_memory_L2[set_index][0].valid == 0 && cache_memory_L2[set_index][1].valid == 0) begin 
                // Smesti na nulti 
           end
           // Prvi je slobodan - Drugi je zauzet
           else if(cache_memory_L2[set_index][0].valid == 0 && cache_memory_L2[set_index][1].valid == 1 && 
                   cache_memory_L2[set_index][1].tag != tag) begin 
                // Smesti na nutli
           end  
           // Prvi je zauzet - Drugi je slobodan
           else if(cache_memory_L2[set_index][0].valid == 1 && cache_memory_L2[set_index][1].valid == 0 && 
                   cache_memory_L2[set_index][0].tag != tag) begin
                // Smesti na prvi
           end
           // Oba su zauzeta 
           else if(cache_memory_L2[set_index][0].valid == 1 && cache_memory_L2[set_index][1].valid == 1) begin 
                if(cache_memory_L2[set_index][0].tag == tag) begin
                    // Smesti na nulti i izbaci u DMEM
                end
                else if(cache_memory_L2[set_index][1].tag == tag) begin 
                    // Snesti na prvi i izbaci u DMEM
                end
                else if(cache_memory_L2[set_index][0].tag != tag && cache_memory_L2[set_index][1].tag != tag) begin
                    // LRU - Smesti na onaj ciji je LRU 1 i izbaci u DMEM
                end
           end
        end
        // Load Miss in L2 - Fetching data from data memory
        else if(cache_hit_out == 2'b01) begin 
            if(cache_memory_L2[set_index][0].lru == 0 && cache_memory_L2[set_index][1].lru == 0) begin 
                // Smesti na nulti
            end
            else if(cache_memory_L2[set_index][0].lru == 1) begin 
                // Smesti na nulti i trenutni podatak upisi u DMEM
            end
            else if(cache_memory_L2[set_index][1].lru == 1) begin 
                // Smesti na prvi i trenutni podatak upisi u DMEM
            end
        end
        // Load Hit in L2 - Only toggle LRU bits
        else if(cache_hit_out == 2'b10) begin
             // Handle LOAD HIT: update LRU
            if (way0_hit == 1) begin
                cache_memory_L2[set_index][0].lru <= 0; // Way 0 recently used
                cache_memory_L2[set_index][1].lru <= 1; // Way 1 least recently used
            end else if (way1_hit == 1) begin
                cache_memory_L2[set_index][0].lru <= 1; // Way 0 least recently used
                cache_memory_L2[set_index][1].lru <= 0; // Way 1 recently used
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