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
            // Check both ways for a matching tag
                if ((cache_memory_L2[set_index][0].tag != bus_address_in[31:9] && cache_memory_L2[set_index][1].tag != bus_address_in[31:9]) || 
                      cache_memory_L2[set_index][0].valid == 0 && cache_memory_L2[set_index][1].valid == 0) begin
                
                // Use LRU to decide which way to replace
                if(cache_memory_L2[set_index][0].lru == 0 && cache_memory_L2[set_index][1].lru == 0) begin
                    cache_memory_L2[set_index][0].valid <= 1;
                    cache_memory_L2[set_index][0].lru   <= 0; // Mark as recently used
                    cache_memory_L2[set_index][1].lru   <= 1; // Mark Way 1 as least recently used
                    cache_memory_L2[set_index][0].data  <= bus_data_in;
                    cache_memory_L2[set_index][0].tag   <= bus_tag_in[23:1];//bus_address_in[31:9];
                end
                else if (cache_memory_L2[set_index][0].lru == 1) begin
                    // Replace Way 0
                    cache_memory_L2[set_index][0].valid <= 1;
                    cache_memory_L2[set_index][0].lru   <= 0; // Mark as recently used
                    cache_memory_L2[set_index][1].lru   <= 1; // Mark Way 1 as least recently used
                    cache_memory_L2[set_index][0].data  <= bus_data_in;
                    cache_memory_L2[set_index][0].tag   <= bus_tag_in[23:1];//bus_address_in[31:9];
                end else begin
                    // Replace Way 1
                    cache_memory_L2[set_index][1].valid <= 1;
                    cache_memory_L2[set_index][1].lru   <= 0; // Mark as recently used
                    cache_memory_L2[set_index][0].lru   <= 1; // Mark Way 0 as least recently used
                    cache_memory_L2[set_index][1].data  <= bus_data_in;
                    cache_memory_L2[set_index][1].tag   <= bus_tag_in[23:1];//bus_address_in[31:9];
                end
            end 
            else begin
                // If tag exists in L2, evict it and write to dmem, then update L2
                if (cache_memory_L2[set_index][0].tag == bus_address_in[31:9] && cache_memory_L2[set_index][0].valid != 0) begin
                    data_to_dmem <= cache_memory_L2[set_index][0].data;
                    address_to_dmem <= {cache_memory_L2[set_index][0].tag, set_index};
                    cache_memory_L2[set_index][0].data <= bus_data_in;
                    cache_memory_L2[set_index][0].lru   <= 0;
                    cache_memory_L2[set_index][1].lru   <= 1;
                    opcode_out <= 7'b0100011;
                end 
                else if (cache_memory_L2[set_index][1].tag == bus_address_in[31:9] && cache_memory_L2[set_index][1].valid != 0) begin
                    data_to_dmem <= cache_memory_L2[set_index][1].data;
                    address_to_dmem <= {cache_memory_L2[set_index][1].tag, set_index};
                    cache_memory_L2[set_index][1].data <= bus_data_in;
                    cache_memory_L2[set_index][0].lru   <= 1;
                    cache_memory_L2[set_index][1].lru   <= 0;
                    opcode_out <= 7'b0100011;
                end
            end
        end
        
        // Handle LOAD MISS scenario
        if (cache_hit_out == 2'b01 && opcode_in == 7'b0000011) begin
            // Use LRU to decide which way to replace
            if (cache_memory_L2[set_index][0].lru == 1) begin
                // Replace Way 0
                cache_memory_L2[set_index][0].valid <= 1;
                cache_memory_L2[set_index][0].tag   <= bus_tag_in[23:1];//bus_address_in[31:9];
                cache_memory_L2[set_index][0].data  <= data_from_dmem;
                cache_memory_L2[set_index][0].lru   <= 0; // Mark as recently used
                cache_memory_L2[set_index][1].lru   <= 1; // Mark Way 1 as least recently used
            end else begin
                // Replace Way 1
                cache_memory_L2[set_index][1].valid <= 1;
                cache_memory_L2[set_index][1].tag   <= bus_tag_in[23:1];//bus_address_in[31:9];
                cache_memory_L2[set_index][1].data  <= data_from_dmem;
                cache_memory_L2[set_index][1].lru   <= 0; // Mark as recently used
                cache_memory_L2[set_index][0].lru   <= 1; // Mark Way 0 as least recently used
            end
        end 
        else if (cache_hit_out == 2'b10 && opcode_in == 7'b0000011) begin
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