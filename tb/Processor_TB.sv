`timescale 1ns / 1ps

module Processor_TB;
	typedef enum logic [6:0] {
        TYPE_R = 7'b0110011,
        TYPE_I = 7'b0010011,
        TYPE_L = 7'b0000011,
        TYPE_S = 7'b0100011,
        TYPE_B = 7'b1100011,
        TYPE_U = 7'b0110111,
        TYPE_J = 7'b1101111
    } opcode_t;
	
	logic clk, reset;
	opcode_t opcode_cpu1, opcode_cpu2;
	//Processor UUT (clk, reset);
	top UUT (clk, reset);
	
	always_comb begin
        opcode_cpu1 = opcode_t'(UUT.cpu1.instruction[6:0]);
        opcode_cpu2 = opcode_t'(UUT.cpu2.instruction[6:0]); 
    end
	
	
	initial
		begin
			clk = 1;
			forever #1 clk = ~clk;
		end
	initial
		begin
			reset <= 1;
			#1
			wait(clk);
			reset <= 0;
			#1200
			$stop;
		end
endmodule
