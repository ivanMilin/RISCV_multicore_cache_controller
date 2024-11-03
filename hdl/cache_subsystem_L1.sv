module cache_subsystem_L1
(
    input  logic clk,
    input  logic reset,
    input  logic wr_en,
    input  logic rd_en,
    input  logic [6 : 0] opcode_in,
    input  logic [2 : 0] mask,
    input logic [31: 0] data_in,
    input logic [9 : 0] address_in,
    
    output logic stall,
    input  logic [31: 0] data_from_dmem_in, //loading data from dmem when MISS happens
    output logic [31: 0] data_from_cache_out,  
    
    output logic [9 :0] dmem_address_out
);

    typedef struct packed 
    {
        logic        valid;  
        logic [1:0]  tag;    
        logic [31:0] data;   
    } cache_line_t;
    
    cache_line_t cache_memory_L1[255:0];
    
    logic [ 1:0] cache_hit;
    logic [31: 0] data_L1, write_L1, read_L1;
    logic [31: 0] data_in_s; //variable get value either from register file or from dmem
    
    logic [31:0] miss_address;
    
    logic [1 : 0] tag_in;
    logic [7 : 0] index_in;
    
	logic [1:0] test_flag;

    assign tag_in           = address_in[9 : 8];
    assign index_in         = address_in[7 : 0];
    
    typedef enum logic [1:0] {MAIN, WAIT_WRITE} state_t;
    state_t state, next_state;
    
    // ====================== CODE LOGIC IS BELOW ======================== // 
    
    // Cache hit detection
    always_comb begin
        if(opcode_in == 7'b0000011) begin
            if (cache_memory_L1[index_in[7:2]].valid && cache_memory_L1[index_in[7:2]].tag == tag_in) begin
                cache_hit = 2'b10;      // HIT 
            end else begin
                cache_hit = 2'b01;      // MISS
            end
        end      
        else begin
            cache_hit = 2'b00;          // NO REQUEST
        end
    end

    // State machine for cache miss handling
    always_ff @(posedge clk) begin
        if (reset) begin
            state <= MAIN;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
    next_state = MAIN;
	stall = 'b0;
	data_in_s = 'b0;
	dmem_address_out = 'b0;

        case (state)
            MAIN: begin
                if(opcode_in == 7'b0000011) begin   // LOAD
                    if (cache_hit == 2'b01) begin
                        next_state = WAIT_WRITE;    // Miss scenario - Next state has to fetch data from current address from data memory
                        stall = 'b1;
                    end else begin
                        next_state = MAIN;      
                        stall = 'b0;
                    end
                end         
                else if(opcode_in == 7'b0100011) begin  //STORE
                    stall = 'b0;
                    next_state = MAIN;      
                    data_in_s = data_in;
                end 
                else begin
                    next_state = MAIN;
                    stall = 'b0;
                    data_in_s = 'b0;
		    dmem_address_out = 'b0;
                end             
            end

            WAIT_WRITE: begin
                data_in_s = data_from_dmem_in;
                dmem_address_out = miss_address;
                stall = 'b1;
                next_state = MAIN;
            end
      endcase    
    end

    // What is the point of this block?
    always_comb begin
        if (rd_en) begin
            data_L1 = cache_memory_L1[index_in[7:2]].data;
        end 
        else begin // Cache miss: request data from memory
            data_L1 = 'b0;
        end
    end
    
    // LOAD instruction based on mask if HIT happens
    always_comb begin
        data_from_cache_out = 'b0;
        if (rd_en && cache_hit == 2'b10 && stall == 0) begin
            case (mask) 
                3'b000: begin   // Load byte (Signed)
                    case (index_in[1:0])
                        0: data_from_cache_out = {{24{data_L1[7]}},  data_L1[7:0]};
                        1: data_from_cache_out = {{24{data_L1[15]}}, data_L1[15:8]};
                        2: data_from_cache_out = {{24{data_L1[23]}}, data_L1[23:16]};
                        3: data_from_cache_out = {{24{data_L1[31]}}, data_L1[31:24]};
                    endcase
                end
                3'b001: begin   // Load halfword (Signed)
                    case (index_in[1])
                        0: data_from_cache_out = {{16{data_L1[15]}}, data_L1[15:0]};
                        1: data_from_cache_out = {{16{data_L1[31]}}, data_L1[31:16]};
                    endcase
                end
                3'b010: begin   // Load word
                    data_from_cache_out = data_L1;
                end
                3'b100: begin   // Load byte (Unsigned)
                    case (index_in[1:0])
                        0: data_from_cache_out = {24'b0, data_L1[7:0]};
                        1: data_from_cache_out = {24'b0, data_L1[15:8]};
                        2: data_from_cache_out = {24'b0, data_L1[23:16]};
                        3: data_from_cache_out = {24'b0, data_L1[31:24]};
                    endcase
                end
                3'b101: begin   // Load halfword (Unsigned)
                    case (index_in[1])
                        0: data_from_cache_out = {16'b0, data_L1[15:0]};
                        1: data_from_cache_out = {16'b0, data_L1[31:16]};
                    endcase
                end
            endcase   
        end
    end

    // Cache STORE logic and also situation when MISS happens store data from DMEM to cache
    always_comb begin
        case (mask)
            3'b000: begin   // Store byte
                case (index_in[1:0])
                    0: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFFFF00) | {24'b0, data_in_s[7:0]};
                    1: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFF00FF) | {16'b0, data_in_s[7:0], 8'b0};
                    2: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFF00FFFF) | {8'b0, data_in_s[7:0], 16'b0};
                    3: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'h00FFFFFF) | {data_in_s[7:0], 24'b0};
                    //default: write_L1 = 0;
                endcase
            end
            3'b001: begin   // Store halfword
                case (index_in[1])
                    0: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFF0000) | {16'b0, data_in_s[15:0]};
                    1: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'h0000FFFF) | {data_in_s[15:0], 16'b0};
                    //default: write_L1 = 0;
                endcase
            end
            3'b010: begin   // Store word
                write_L1 = data_in_s;
            end
            3'b100: begin   // Load byte (Unsigned)
                case (index_in[1:0])
                    0: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFFFF00) | {24'b0, data_in_s[7:0]};
                    1: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFF00FF) | {16'b0, data_in_s[7:0], 8'b0};
                    2: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFF00FFFF) | {8'b0, data_in_s[7:0], 16'b0};
                    3: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'h00FFFFFF) | {data_in_s[7:0], 24'b0};
                endcase
            end
            3'b101: begin   // Load halfword (Unsigned)
                case (index_in[1])
                    0: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFF0000) | {16'b0, data_in_s[15:0]};
                    1: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'h0000FFFF) | {data_in_s[15:0], 16'b0};
                endcase
            end
            //default: write_L1 = 0;
        endcase 
    end
    
    always_ff @(posedge clk) begin
        if(reset) begin
            miss_address <= 'b0;
        end
        else begin
            if(opcode_in == 7'b0000011) begin //LOAD
                miss_address <= address_in;
            end
            else begin
                miss_address <= miss_address;
            end
        end
    end
    
    always_ff @(negedge clk) begin
        if(reset) begin
            for(int i = 0; i < 256; i++) begin
				cache_memory_L1[i] = i+2;
            end
			test_flag = 2'b11;
        end 
		else begin
            if(opcode_in == 7'b0100011) begin
                cache_memory_L1[index_in[7:2]] <= '{valid: 1, tag: tag_in, data: write_L1};
            end
            else if(state == WAIT_WRITE) begin
                cache_memory_L1[miss_address[7:2]] <= '{valid: 1, tag: tag_in, data: write_L1};                
            end
        end
    end
endmodule
