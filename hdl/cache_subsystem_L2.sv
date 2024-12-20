`timescale 1ns / 1ps

module cache_subsystem_L2(

    input  logic clk,
    input  logic reset,
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
        logic lru;
        logic [22:0] tag;
        logic [31:0] data;
    } cache_line_t;

    cache_line_t cache_memory_L2[511:0][1:0]; // 512 sets with 2 ways each

    logic [8:0] set_index;  
    logic [22:0] tag;
    logic way0_hit, way1_hit;
    logic [1:0] hello, konichiwa;

    typedef enum logic [1:0] {IDLE, DMEM_WRITE} state_t;
    state_t state, next_state;

    assign set_index = bus_address_in[8:2]; 
    assign tag = bus_address_in[31:9];  


    // State machine for cache miss handling
    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
    next_state = IDLE;
        case (state)
            IDLE: begin
                if(cache_hit_out == 2'b01) begin   // MISS
                    next_state = DMEM_WRITE;
                end         
                else begin                         // HIT OR NEUTRAL
                    next_state = IDLE;
                end           
            end

            DMEM_WRITE : begin
                if(cache_hit_out == 2'b10) begin 
                    next_state = IDLE;
                end
                else begin 
                    next_state = DMEM_WRITE;
                end
            end
      endcase    
    end

    always_comb begin
        cache_hit_out = 'b0;
        data_from_L2 = 'b0;
        
        way0_hit = cache_memory_L2[set_index][0].valid && (cache_memory_L2[set_index][0].tag == tag);
	way1_hit = cache_memory_L2[set_index][1].valid && (cache_memory_L2[set_index][1].tag == tag); 

        if (opcode_in == 7'b0000011) begin      // LOAD instruction
            if (way0_hit) begin
                cache_hit_out = 2'b10;          // HIT
                data_from_L2 = cache_memory_L2[set_index][0].data;
            end else if (way1_hit) begin
                cache_hit_out = 2'b10;          // HIT
                data_from_L2 = cache_memory_L2[set_index][1].data;
            end else begin
                cache_hit_out = 2'b01;          // MISS
            end
        end
    end

    always_ff @(negedge clk) begin
        if (reset) begin
            data_to_dmem    <= 'b0;
            address_to_dmem <= 'b0;
            opcode_out      <= 'b0;
	    hello 	    <= 'b0;
	    konichiwa 	    <= 'b0;
            for (integer i = 0; i < 512; i++) begin
                for (integer j = 0; j < 2; j++) begin
                    cache_memory_L2[i][j].valid <= 0;
                    cache_memory_L2[i][j].lru   <= 0;  
                    cache_memory_L2[i][j].tag   <= 'b0;
                    cache_memory_L2[i][j].data  <= 'b0;
                end
            end
        end 
        else begin
            if (flush == 1'b1) begin
               // Oba su slobodna
               if(cache_memory_L2[set_index][0].valid == 0 && cache_memory_L2[set_index][1].valid == 0) begin 
                    // Smesti na nulti way
                    cache_memory_L2[set_index][0].valid <= 1;
                    cache_memory_L2[set_index][0].lru   <= 0;   // Mark as recently used
                    cache_memory_L2[set_index][1].lru   <= 1;   // Mark Way 1 as least recently used
                    cache_memory_L2[set_index][0].data  <= bus_data_in;
                    cache_memory_L2[set_index][0].tag   <= bus_tag_in[23:1];//bus_address_in[31:9]; 
               end
               // Nulti je slobodan - Prvi je zauzet
               /*else if(cache_memory_L2[set_index][0].valid == 0 && cache_memory_L2[set_index][1].valid) begin
                    if( cache_memory_L2[set_index][0].tag != bus_tag_in[23:1]) begin 
                        // Smesti na nutli
                        cache_memory_L2[set_index][0].valid <= 1;
                        cache_memory_L2[set_index][0].lru   <= 0;   // Mark as recently used
                        cache_memory_L2[set_index][1].lru   <= 1;   // Mark Way 1 as least recently used
                        cache_memory_L2[set_index][0].data  <= bus_data_in;
                        cache_memory_L2[set_index][0].tag   <= bus_tag_in[23:1];//bus_address_in[31:9]; 
                    end
                    else begin
                        cache_memory_L2[set_index][1].valid <= 1;
                        cache_memory_L2[set_index][1].lru   <= 0;   // Mark as recently used
                        cache_memory_L2[set_index][0].lru   <= 1;   // Mark Way 1 as least recently used
                        cache_memory_L2[set_index][1].data  <= bus_data_in;
                        cache_memory_L2[set_index][1].tag   <= bus_tag_in[23:1];//bus_address_in[31:9];
                        
                        address_to_dmem <= {cache_memory_L2[set_index][1].tag, set_index};
                        data_to_dmem <= cache_memory_L2[set_index][1].data;
                        opcode_out <= 7'b0100011; 
                    end                                    
               end 
               */ 
               // Nulti je zauzet - Prvi je slobodan
               else if(cache_memory_L2[set_index][0].valid == 1 && cache_memory_L2[set_index][1].valid == 0) begin
                    if(cache_memory_L2[set_index][0].tag != bus_tag_in[23:1]) begin
                        // Smesti na prvi
                        cache_memory_L2[set_index][1].valid <= 1;
                        cache_memory_L2[set_index][1].lru   <= 0;   // Mark as recently used
                        cache_memory_L2[set_index][0].lru   <= 1;   // Mark Way 1 as least recently used
                        cache_memory_L2[set_index][1].data  <= bus_data_in;
                        cache_memory_L2[set_index][1].tag   <= bus_tag_in[23:1];//bus_address_in[31:9]; 
                    end
                    else begin
                        // Smesti na nutli
                        cache_memory_L2[set_index][0].valid <= 1;
                        cache_memory_L2[set_index][0].lru   <= 0;   // Mark as recently used
                        cache_memory_L2[set_index][1].lru   <= 1;   // Mark Way 1 as least recently used
                        cache_memory_L2[set_index][0].data  <= bus_data_in;
                        cache_memory_L2[set_index][0].tag   <= bus_tag_in[23:1];//bus_address_in[31:9];
                        
                        address_to_dmem <= {cache_memory_L2[set_index][1].tag, set_index};
                        data_to_dmem    <= cache_memory_L2[set_index][0].data;
                        opcode_out      <= 7'b0100011; 
                    end
               end
               // Oba su zauzeta 
               else if(cache_memory_L2[set_index][0].valid == 1 && cache_memory_L2[set_index][1].valid == 1) begin 
                    if(cache_memory_L2[set_index][0].tag == bus_tag_in[23:1]) begin
						hello <= 1;
                        // Smesti na nulti i izbaci u DMEM
                        cache_memory_L2[set_index][0].data <= bus_data_in;
                        cache_memory_L2[set_index][0].lru  <= 0;
                        cache_memory_L2[set_index][1].lru  <= 1;
                        
                        address_to_dmem <= {cache_memory_L2[set_index][0].tag, set_index};
                        data_to_dmem    <= cache_memory_L2[set_index][0].data;
                        opcode_out      <= 7'b0100011;
                    end
                    else if(cache_memory_L2[set_index][1].tag == bus_tag_in[23:1]) begin
						hello <= 2; 
                        // Snesti na prvi i izbaci u DMEM
                        cache_memory_L2[set_index][1].data <= bus_data_in;
                        cache_memory_L2[set_index][1].lru  <= 0;
                        cache_memory_L2[set_index][0].lru  <= 1;
                        
                        address_to_dmem <= {cache_memory_L2[set_index][1].tag, set_index};
                        data_to_dmem    <= cache_memory_L2[set_index][1].data;
                        opcode_out      <= 7'b0100011;
                    end
                    else if(cache_memory_L2[set_index][0].tag != bus_tag_in[23:1] && cache_memory_L2[set_index][1].tag != bus_tag_in[23:1]) begin
						hello <= 3;
                        // LRU - Smesti na onaj ciji je LRU 1 i izbaci u DMEM
                        if(cache_memory_L2[set_index][0].lru == 1) begin
                            cache_memory_L2[set_index][0].data <= bus_data_in;
                            cache_memory_L2[set_index][0].tag  <= bus_tag_in[23:1];
                            cache_memory_L2[set_index][0].lru  <= 0;
                            cache_memory_L2[set_index][1].lru  <= 1;
                            
                            address_to_dmem <= {cache_memory_L2[set_index][0].tag, set_index};
                            data_to_dmem    <= cache_memory_L2[set_index][0].data;
                            opcode_out      <= 7'b0100011;
                        end
                        else if(cache_memory_L2[set_index][1].lru == 1) begin
                            cache_memory_L2[set_index][1].data <= bus_data_in;
			    cache_memory_L2[set_index][1].tag  <= bus_tag_in[23:1];
                            cache_memory_L2[set_index][1].lru  <= 0;
                            cache_memory_L2[set_index][0].lru  <= 1;
                            
                            address_to_dmem <= {cache_memory_L2[set_index][1].tag, set_index};
                            data_to_dmem    <= cache_memory_L2[set_index][1].data;
                            opcode_out      <= 7'b0100011;
                        end
                    end
               end
            end
            // Load Miss in L2 - Fetching data from data memory
            else if(cache_hit_out == 2'b01 && state == IDLE) begin 
                konichiwa 	    <= 2'b01;
                /*
                if(cache_memory_L2[set_index][0].lru == 0 && cache_memory_L2[set_index][1].lru == 0) begin
                    address_to_dmem <= {cache_memory_L2[set_index][0].tag, set_index};
                    konichiwa 	    <= 2'b10;
                end 
                else if(cache_memory_L2[set_index][0].lru == 1) begin
                    address_to_dmem <= {cache_memory_L2[set_index][0].tag, set_index};
                end  
                else if(cache_memory_L2[set_index][1].lru == 1) begin 
                    address_to_dmem <= {cache_memory_L2[set_index][1].tag, set_index};
                end
                */
                address_to_dmem <= bus_address_in;
            end 
            else if(state == DMEM_WRITE) begin 
                if(cache_memory_L2[set_index][0].lru == 0 && cache_memory_L2[set_index][1].lru == 0) begin 
                    // Smesti na nulti
                    cache_memory_L2[set_index][0].valid <= 1;
                    cache_memory_L2[set_index][0].tag   <= tag;//bus_address_in[31:9];
                    cache_memory_L2[set_index][0].data  <= data_from_dmem;
                    cache_memory_L2[set_index][0].lru   <= 0; // Mark as recently used
                    cache_memory_L2[set_index][1].lru   <= 1; // Mark Way 1 as least recently used
                end
                else if(cache_memory_L2[set_index][0].lru == 1 && cache_memory_L2[set_index][1].lru == 0) begin 
                    // Smesti na nulti i trenutni podatak upisi u DMEM
                    cache_memory_L2[set_index][0].data  <= data_from_dmem;
                    cache_memory_L2[set_index][0].tag   <= tag;//bus_address_in[31:9];
                    cache_memory_L2[set_index][0].lru   <= 0;
                    cache_memory_L2[set_index][1].lru   <= 1;
                    
                    data_to_dmem    <= cache_memory_L2[set_index][0].data;
                    opcode_out      <= 7'b0100011;   
                end
                else if(cache_memory_L2[set_index][1].lru == 1 && cache_memory_L2[set_index][0].lru == 0) begin 
                    // Smesti na prvi i trenutni podatak upisi u DMEM
                    cache_memory_L2[set_index][1].data  <= data_from_dmem;
                    cache_memory_L2[set_index][1].tag   <= tag;//bus_address_in[31:9];
                    cache_memory_L2[set_index][1].lru   <= 0;
                    cache_memory_L2[set_index][0].lru   <= 1;
                    
                    data_to_dmem    <= cache_memory_L2[set_index][1].data;
                    opcode_out      <= 7'b0100011;
                end
            end
            // Load Hit in L2 - Only toggle LRU bits
            else if(cache_hit_out == 2'b10) begin
                 // Handle LOAD HIT: update LRU
                if (way0_hit == 1) begin
                    cache_memory_L2[set_index][0].lru <= 0; // Way 0 recently used
                    cache_memory_L2[set_index][1].lru <= 1; // Way 1 least recently used
                end 
                else if (way1_hit == 1) begin
                    cache_memory_L2[set_index][0].lru <= 1; // Way 0 least recently used
                    cache_memory_L2[set_index][1].lru <= 0; // Way 1 recently used
                end
            end    
        end
    end



endmodule
