`timescale 1ns / 1ps

module Processor_TB;
	logic clk, reset;
	logic [6 : 0] opcode_in_s;
	Processor UUT (clk, reset);
	
	assign opcode_in_s = UUT.instruction[6:0];
	
	initial
		begin
			clk = 1;
			forever #1 clk = ~clk;
		end
	initial
		begin
			reset = 1;
			#2;
			reset = 0;
			#1200
			$stop;
		end
endmodule
