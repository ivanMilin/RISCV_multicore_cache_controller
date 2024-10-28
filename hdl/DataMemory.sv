module DataMemory(input logic [31:0] addr, wdata, input logic [2:0] mask, input logic wr_en, rd_en, clk,reset,
				  output logic [31:0] rdata);
	logic [31:0] memory [1023:0] ;//= '{default:32'b0};		// 1 KB Memory size
	logic [31:0] data, write_data,read_data_from_memory;

	always_comb begin
		//data = 'b0;
		if (rd_en)
			data = memory[addr[31:2]];
			//data = memory[addr[31:0]];
		else
			data = 0;
	end

	always_comb begin
		rdata = 'b0;
		if (rd_en) begin		// Load instruction
			case (mask)
				3'b000: begin	// Load byte (Signed)
					case (addr[1:0])
						0: rdata = {{24{data[7]}}, data[7:0]};
						1: rdata = {{24{data[15]}}, data[15:8]};
						2: rdata = {{24{data[23]}}, data[23:16]};
						3: rdata = {{24{data[31]}}, data[31:24]};
					endcase
				end
				3'b001: begin	// Load halfword (Signed)
					case (addr[1])
						0: rdata = {{16{data[15]}}, data[15:0]};
						1: rdata = {{16{data[31]}}, data[31:16]};
					endcase
				end
				3'b010: begin	// Load word
					rdata = data;
				end
				3'b100: begin	// Load byte (Unsigned)
					case (addr[1:0])
						0: rdata = {24'b0, data[7:0]};
						1: rdata = {24'b0, data[15:8]};
						2: rdata = {24'b0, data[23:16]};
						3: rdata = {24'b0, data[31:24]};
					endcase
				end
				3'b101: begin	// Load halfword (Unsigned)
					case (addr[1])
						0: rdata = {16'b0, data[15:0]};
						1: rdata = {16'b0, data[31:16]};
					endcase
				end
			endcase
		end
	end
		
	always_comb begin
		write_data = 'b0;
		if (wr_en) begin		// S-type instruction
		    //read_data_from_memory = memory[addr[31:2]];
			
			case (mask)
				3'b000: begin	// Store byte
					case (addr[1:0])
						//0: write_data = {24'b0, wdata[7:0]};
						//1: write_data = {24'b0, wdata[15:8]};
						//2: write_data = {24'b0, wdata[23:16]};
						//3: write_data = {24'b0, wdata[31:24]};
				
						0: write_data = (memory[addr[31:2]] & 32'hFFFFFF00) | {24'b0, wdata[7:0]};
						1: write_data = (memory[addr[31:2]] & 32'hFFFF00FF) | {16'b0, wdata[7:0], 8'b0};
						2: write_data = (memory[addr[31:2]] & 32'hFF00FFFF) | {8'b0, wdata[7:0], 16'b0};
						3: write_data = (memory[addr[31:2]] & 32'h00FFFFFF) | {wdata[7:0], 24'b0};
					endcase
				end

				3'b001: begin	// Store halfword
					case (addr[1])
					    //0: write_data = {16'b0, wdata[15:0]};
						//1: write_data = {16'b0, wdata[31:16]};
						
						0: write_data = (memory[addr[31:2]] & 32'hFFFF0000) | {16'b0, wdata[15:0]};
						1: write_data = (memory[addr[31:2]] & 32'h0000FFFF) | {wdata[15:0],16'b0};
					endcase
				end
				3'b010: begin	// Store word
					write_data = wdata;
				end
			endcase
		end
	end
	
	always_ff @(negedge clk) begin
		if(reset) begin
          for (integer i = 0; i < 1024; i = i + 1) begin
            memory[i] <= 0;//32'b0;
          end
		end 
		else begin 
			if (wr_en) begin
				memory[addr[31:2]] <= write_data;
				//memory[addr[31:0]] <= write_data;
			end
		end
	end
endmodule
