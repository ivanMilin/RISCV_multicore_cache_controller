`timescale 1ns / 1ps

module DataMemory
(   
    input logic clk,
    input logic reset, 
	
	input logic [ 6:0] opcode_in,
	input logic [31:0] addr, 
	input logic [31:0] data_from_L2, 
	
    output logic [31:0] data_from_dmem
);

    logic [31:0] memory [1023:0];
	
	assign data_from_dmem = memory[addr];
	
	// LOAD data from DMEM
	/*
    always_comb begin
        if (opcode_in == 7'b0000011) begin
            data_from_dmem = memory[addr[31:2]];
        end
        else begin
            data_from_dmem = 0;
        end
    end
    */ 
    
    // STORE data in DMEM
	always_ff @(negedge clk) begin
		if(reset) begin
            for (integer i = 0; i < 1024; i = i + 1) begin
                memory[i] <= i+1;//32'b0;
            end
		end 
		else begin 
			if (opcode_in == 7'b0100011) begin
				memory[{addr[31:2],2'b00}] <= data_from_L2;
			end
		end
	end
endmodule