`timescale 1ns / 1ps

module cache_subsystem_L1
(
    input logic clk,
    input logic reset,
    input logic wr_en,
    input logic rd_en,
    input logic grant,

    input logic [ 2:0] mask_in,
    input logic [ 6:0] opcode_in,
    
    input logic [31:0] data_in,
    input logic [31:0] address_in,    

    // data will come from the shared bus
    input logic [31:0] bus_data_in,
    input logic [31:0] bus_address_in,
    input logic [ 1:0] bus_operation_in,
    
    // data will go to the shared bus
    output logic [31:0] bus_data_out, 
    output logic [24:0] tag_to_L2,
    output logic [31:0] bus_address_out,
    output logic [ 1:0] bus_operation_out,//BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10, BusNoN == 2'b11

    output logic [31:0] data_out,
    output logic [31:0] data_to_L2,
    
    input logic [1:0] cache_hit_in,  
    output logic cache_hit_out, 
    
    output logic stall,
    output logic req_core,
    output logic flush_out,
    
    output logic [6:0] opcode_out
);

    typedef struct packed 
    {
        logic [1:0]   mesi_state;  
        logic [23:0]  tag;
        logic [31:0]  data;   
    } cache_line_t;
    
    typedef enum logic [1:0] {
        I = 2'b00,      // Invalid
        E = 2'b01,      // Exclusive
        S = 2'b10,      // Shared
        M = 2'b11       // Modified
    } mesi_state_t;


    
    cache_line_t cache_memory_L1[255:0];
    mesi_state_t mesi_state_s, next_mesi_state; //signal for changing state inside of CPU
    mesi_state_t upgrade_mesi_state;          //signal for changing state recieved from other CPU
        
    logic [1:0]   cache_hit;
    logic [31: 0] data_L1, write_L1, read_L1;
    logic [31: 0] data_in_s;                  //variable get value either from register file or from dmem
    
    logic [31:0] miss_address;
    
    logic [23 : 0] tag_in;
    logic [7 : 0] index_in;

    assign tag_in   = address_in[31 : 8];
    assign index_in = address_in[ 7 : 0];
    
    typedef enum logic [1:0] {MAIN, WAIT_WRITE} state_t;
    state_t state, next_state;
    
    // ====================== CODE LOGIC IS BELOW ======================== // 
    
    // Cache hit detection
    always_comb begin
        cache_hit = 'b0;
        if(opcode_in == 7'b0000011) begin
            if (cache_memory_L1[index_in[7:2]].mesi_state != 2'b00 && cache_memory_L1[index_in[7:2]].tag == tag_in) begin
                cache_hit = 2'b10;      // HIT 
            end else begin
                cache_hit = 2'b01;      // MISS
            end
        end 
    end

    //Logic for sending request to bus
    always_comb begin
        req_core   = 1'b0;
        opcode_out = 'b0;
        
        if((opcode_in[6:0] == 7'b0000011 /*&& cache_hit == 2'b01*/) || opcode_in[6:0] == 7'b0100011) begin
           req_core = 1'b1;
           opcode_out = opcode_in[6:0];
        end
    end 

    // State machine for cache miss handling
    always_ff @(posedge clk) begin
        if (reset) begin
            state <= MAIN;
            //mesi_state_s <= I;
        end else begin
            state <= next_state;
            //mesi_state_s <= next_mesi_state;
        end
    end
    
    always_comb begin
    next_state = MAIN;
	stall = 'b0;
	data_in_s = 'b0;

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
                end             
            end

            WAIT_WRITE: begin
                data_in_s = bus_data_in;
                stall = 'b1;
                
                if(cache_hit == 2'b10) begin
                    next_state = MAIN;
                end else begin
                    next_state = WAIT_WRITE;
                end
            end
      endcase    
    end

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
        data_out = 'b0;
        if (rd_en && cache_hit == 2'b10 && stall == 0) begin
            case (mask_in) 
                3'b000: begin   // Load byte (Signed)
                    case (index_in[1:0])
                        0: data_out = {{24{data_L1[7]}},  data_L1[7:0]};
                        1: data_out = {{24{data_L1[15]}}, data_L1[15:8]};
                        2: data_out = {{24{data_L1[23]}}, data_L1[23:16]};
                        3: data_out = {{24{data_L1[31]}}, data_L1[31:24]};
                    endcase
                end
                3'b001: begin   // Load halfword (Signed)
                    case (index_in[1])
                        0: data_out = {{16{data_L1[15]}}, data_L1[15:0]};
                        1: data_out = {{16{data_L1[31]}}, data_L1[31:16]};
                    endcase
                end
                3'b010: begin   // Load word
                    data_out = data_L1;
                end
                3'b100: begin   // Load byte (Unsigned)
                    case (index_in[1:0])
                        0: data_out = {24'b0, data_L1[7:0]};
                        1: data_out = {24'b0, data_L1[15:8]};
                        2: data_out = {24'b0, data_L1[23:16]};
                        3: data_out = {24'b0, data_L1[31:24]};
                    endcase
                end
                3'b101: begin   // Load halfword (Unsigned)
                    case (index_in[1])
                        0: data_out = {16'b0, data_L1[15:0]};
                        1: data_out = {16'b0, data_L1[31:16]};
                    endcase
                end
            endcase   
        end
    end
    
    // Implementation of MESI FSM - processor side
    //BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10, BusNoN == 2'b11
    always_comb begin
        bus_operation_out = 2'b11;
        bus_address_out   = 'b0;
        next_mesi_state   = I;
    
        if(grant) begin
            case(cache_memory_L1[index_in[7:2]].mesi_state)
                M: begin
                    if(opcode_in == 7'b0100011 || opcode_in == 7'b0000011) begin //PrRd/- PrWr/-
                        next_mesi_state = M;
                        //bus_operation_out = 2'b11;
                    end
                end
                E: begin
                    if(opcode_in == 7'b0100011) begin //PrWr/-
                        next_mesi_state = M;
                        //bus_operation_out = 2'b11;
                    end
                    else if(opcode_in == 7'b0000011) begin //PrRd/-
                        next_mesi_state = E;
                        //bus_operation_out = 2'b11;
                    end
                end
                S: begin
                    if(opcode_in == 7'b0100011) begin        //PrWr/BusUpgr
                        bus_operation_out = 2'b01;
                        bus_address_out = address_in; 
                        next_mesi_state = M;     
                    end
                    else if(opcode_in == 7'b0000011) begin   //PrRd/-
                        next_mesi_state = S;
                        //bus_operation_out = 2'b11;
                    end
                end
                I: begin
                    if(opcode_in == 7'b0000011) begin       //PrRd/BusRd(C) or PrRd/BusRd(#C)
                        bus_operation_out = 2'b00;
                        bus_address_out = address_in;
                        if(cache_hit_in == 2'b01) begin
                            next_mesi_state = S;
                        end
                        else if(cache_hit_in == 2'b10) begin
                            next_mesi_state = E;
                        end
                        else begin 
                            next_mesi_state = I;
                        end
                    end
                    else if(opcode_in == 7'b0100011) begin  //PrWr/BusRdX
                        bus_operation_out = 2'b10;
                        bus_address_out = address_in;
                        next_mesi_state = M; 
                    end
                end
                default: next_mesi_state = I;
            endcase
        end        
    end

    // Implementation of MESI FSM - bus side
    //BusRD == 2'00, BusUpgr == 2'b01, BusRdX == 2'b10, BusNoN == 2'b11
    always_comb begin
        tag_to_L2     = 1'b0;      
        flush_out     = 1'b0;
        data_to_L2    = 'b0;
        bus_data_out  = 'b0;
        cache_hit_out = 'b0;
        upgrade_mesi_state = I;
        
        if(bus_operation_in == 2'b00) begin //BusRd == 2'b00
            if (cache_memory_L1[bus_address_in[7:2]].mesi_state != 2'b00 && cache_memory_L1[bus_address_in[7:2]].tag == bus_address_in[31:8]) begin
                bus_data_out = cache_memory_L1[bus_address_in[7:2]].data;
                cache_hit_out = 1'b1;
            end 
            else begin
                cache_hit_out = 1'b0;
            end
                   
            case(cache_memory_L1[bus_address_in[7:2]].mesi_state)
                M: begin
                    flush_out = 1'b1;
                    data_to_L2 = cache_memory_L1[bus_address_in[7:2]].data;
                    tag_to_L2  = cache_memory_L1[bus_address_in[7:2]].tag;
                    upgrade_mesi_state = S;
                end
                E: begin
                    flush_out = 1'b1;
                    data_to_L2 = cache_memory_L1[bus_address_in[7:2]].data;
                    tag_to_L2  = cache_memory_L1[bus_address_in[7:2]].tag;
                    upgrade_mesi_state = S; 
                end
                S: begin
                    flush_out = 1'b0;
                    upgrade_mesi_state = S; 
                end
            endcase
        end
        else if(bus_operation_in == 2'b01) begin //BusUpgr == 2'b01
            case(cache_memory_L1[bus_address_in[7:2]].mesi_state)
                M,E: begin
                    flush_out = 1'b0;
                    upgrade_mesi_state = I;    
                end
                S: begin
                    flush_out = 1'b0;
                    upgrade_mesi_state = I;    
                end
            endcase
        end     
        else if(bus_operation_in == 2'b10) begin //BusRdX == 2'b10
            if (cache_memory_L1[bus_address_in[7:2]].mesi_state != 2'b00 && cache_memory_L1[bus_address_in[7:2]].tag == bus_address_in[31:8]) begin
                bus_data_out = cache_memory_L1[bus_address_in[7:2]].data;
                cache_hit_out = 1'b1;
            end 
            else begin
                cache_hit_out = 1'b0;
            end
            
            case(cache_memory_L1[bus_address_in[7:2]].mesi_state)
                S: begin
                    flush_out = 1'b0;
                    upgrade_mesi_state = I; 
                end
                E: begin
                    flush_out = 1'b1;
                    data_to_L2 = cache_memory_L1[bus_address_in[7:2]].data;
                    tag_to_L2  = cache_memory_L1[bus_address_in[7:2]].tag;
                    upgrade_mesi_state = I; 
                end 
                M: begin
                    flush_out = 1'b1;
                    data_to_L2 = cache_memory_L1[bus_address_in[7:2]].data;
                    tag_to_L2  = cache_memory_L1[bus_address_in[7:2]].tag;
                    upgrade_mesi_state = I; 
                end
            endcase
        end
    end
    

    // Cache STORE logic and also situation when MISS happens store data from DMEM to cache
    always_comb begin
        write_L1 = 'b0;
        case (mask_in)
            3'b000: begin   // Store byte
                case (index_in[1:0])
                    0: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFFFF00) | {24'b0, data_in_s[7:0]};
                    1: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFF00FF) | {16'b0, data_in_s[7:0], 8'b0};
                    2: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFF00FFFF) | {8'b0, data_in_s[7:0], 16'b0};
                    3: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'h00FFFFFF) | {data_in_s[7:0], 24'b0};
                endcase
            end
            3'b001: begin   // Store halfword
                case (index_in[1])
                    0: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'hFFFF0000) | {16'b0, data_in_s[15:0]};
                    1: write_L1 = (cache_memory_L1[index_in[7:2]].data & 32'h0000FFFF) | {data_in_s[15:0], 16'b0};
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
				cache_memory_L1[i] = 0;
            end
        end 
		else begin
            if(opcode_in == 7'b0100011 && grant) begin
                cache_memory_L1[index_in[7:2]] <= '{mesi_state: M, tag: tag_in, data: write_L1};
            end
            else if(opcode_in == 7'b0000011 && state == MAIN && cache_hit == 2'b10) begin
                cache_memory_L1[index_in[7:2]].mesi_state <= next_mesi_state;
            end
            else if(state == WAIT_WRITE) begin
                cache_memory_L1[miss_address[7:2]] <= '{mesi_state: next_mesi_state, tag: tag_in, data: write_L1};                
            end
            else if(bus_operation_in != 2'b11) begin
                //Is bug happens, change it as a broadcast in bus_controller 
                //cache_memory_L1[bus_address_in[7:2]] <= '{mesi_state: upgrade_mesi_state, tag: bus_address_in[31:8], data: bus_data_in}; 
                cache_memory_L1[bus_address_in[7:2]] <= '{mesi_state: upgrade_mesi_state, tag: cache_memory_L1[bus_address_in[7:2]].tag, data: cache_memory_L1[bus_address_in[7:2]].data}; 
            end
        end
    end
endmodule
