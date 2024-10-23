module cache_subsystem_L1(
    input  logic clk,
    input  logic reset,
    input  logic wr_en,
    input  logic rd_en,
    input  logic [6 : 0] opcode_in,
    input  logic [2 : 0] mask,
    input  logic [31: 0] data_in,
    input  logic [7 : 0] index_in,    
    input  logic [1 : 0] tag_in,    
    
    output logic stall,
    output logic [31:0] data_from_cache,  
    
    output logic        dmem_rd_en,
    output logic        dmem_wr_en,
    output logic [31:0] data_to_dmem,
    output logic [9 :0] dmem_address,
    input  logic [31:0] data_from_dmem
);

    typedef struct packed 
    {
        logic        valid;  
        logic [1:0]  tag;    
        logic [31:0] data;   
    } cache_line_t;

    logic [ 1:0] cache_hit;
    logic ready_for_reg_flag;
    cache_line_t cache_memory_L1[255:0];
    logic [31:0] data_L1, write_L1, read_L1;
    logic [31:0] miss_address;
    
    // CHANGES HERE //
    logic [9:0] dm_address; 
    logic [7:0] cache_address;
    assign dm_address = {tag_in,index_in};
    assign dmem_address = {tag_in,index_in};
    assign cache_address = index_in;
    assign data_to_dmem = write_L1;
    
    typedef enum logic [1:0] {IDLE, MISS, WAIT_WRITE} state_t;
    state_t state, next_state;
    
    assign dmem_rd_en = (rd_en && cache_hit == 2'b10 && state == MISS);
    assign dmem_wr_en = (wr_en && cache_hit == 2'b10);

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
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    always_comb begin
        stall = 1'b0;
        
        case (state)
            IDLE: begin
                if (cache_hit == 2'b01) begin
                    next_state = MISS;      // Miss scenario - Next state has to fetch data from current address from data memory
                    stall = 'b1;
                end else begin
                    next_state = IDLE;      // Hit scenratio - no further action
                    stall = 'b0;
                    ready_for_reg_flag = 'b0;
                end
            end
            MISS: begin
                ready_for_reg_flag = 'b1;
                next_state = WAIT_WRITE;  
            end
            WAIT_WRITE: begin
                ready_for_reg_flag = 'b0;
                next_state = IDLE; 
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
    
    // Load instruction based on mask
    always_comb begin
        data_from_cache = 'b0;
        if (rd_en && cache_hit == 2'b10 && stall == 0 && ready_for_reg_flag == 0) begin
            case (mask) 
                3'b000: begin   // Load byte (Signed)
                    case (index_in[1:0])
                        0: data_from_cache = {{24{data_L1[7]}}, data_L1[7:0]};
                        1: data_from_cache = {{24{data_L1[15]}}, data_L1[15:8]};
                        2: data_from_cache = {{24{data_L1[23]}}, data_L1[23:16]};
                        3: data_from_cache = {{24{data_L1[31]}}, data_L1[31:24]};
                    endcase
                end
                3'b001: begin   // Load halfword (Signed)
                    case (index_in[1])
                        0: data_from_cache = {{16{data_L1[15]}}, data_L1[15:0]};
                        1: data_from_cache = {{16{data_L1[31]}}, data_L1[31:16]};
                    endcase
                end
                3'b010: begin   // Load word
                    data_from_cache = data_L1;
                end
                3'b100: begin   // Load byte (Unsigned)
                    case (index_in[1:0])
                        0: data_from_cache = {24'b0, data_L1[7:0]};
                        1: data_from_cache = {24'b0, data_L1[15:8]};
                        2: data_from_cache = {24'b0, data_L1[23:16]};
                        3: data_from_cache = {24'b0, data_L1[31:24]};
                    endcase
                end
                3'b101: begin   // Load halfword (Unsigned)
                    case (index_in[1])
                        0: data_from_cache = {16'b0, data_L1[15:0]};
                        1: data_from_cache = {16'b0, data_L1[31:16]};
                    endcase
                end
            endcase   
        end
        else if(ready_for_reg_flag == 'b1) begin 
            data_from_cache = data_from_dmem;
        end
        else begin 
            data_from_cache = 'b0;
        end 
    end

    // Cache write logic (when cache hit)
    always_comb begin
        //if (wr_en && cache_hit) begin
        write_L1 = 'b0;
        if (wr_en) begin
            case (mask)
                3'b000: begin   // Store byte
                    case (index_in[1:0])
                        0: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFFFF00) | {24'b0, data_in[7:0]};
                        1: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFF00FF) | {16'b0, data_in[7:0], 8'b0};
                        2: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFF00FFFF) | {8'b0, data_in[7:0], 16'b0};
                        3: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'h00FFFFFF) | {data_in[7:0], 24'b0};
                        default: write_L1 = 0;
                    endcase
                end
                3'b001: begin   // Store halfword
                    case (index_in[1])
                        0: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFF0000) | {16'b0, data_in[15:0]};
                        1: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'h0000FFFF) | {data_in[15:0], 16'b0};
                        default: write_L1 = 0;
                    endcase
                end
                3'b010: begin   // Store word
                    write_L1 = data_in;
                end
                default: write_L1 = 0;
            endcase
        end 
    end
    
    // Handle cache miss and memory interaction
    // On a miss, fetch data from memory and store it in a register
    always_ff @(negedge clk) begin
        if (reset) begin
            //dmem_data_reg <= 'b0;
            //dmem_address <= 'b0;
            miss_address <= 'b0;
            for(int i = 0; i < 256; i++) begin
                cache_memory_L1[i] <= '{valid: 0, tag: 'b0, data: 'b0};
            end
        end 
        else begin
            if (state == IDLE && wr_en) begin    
                cache_memory_L1[index_in[7:2]] <= '{valid: 1, tag: tag_in, data: write_L1};
                
                //dmem_address <= dm_address;
            end else if (cache_hit == 2'b01 && rd_en) begin
                miss_address <= dm_address;
            end else if (state == WAIT_WRITE && rd_en) begin
                cache_memory_L1[miss_address[7:0]] <= '{valid: 1, tag: tag_in, data: data_from_dmem};     
            end
        end
    end
endmodule