`timescale 1ns / 1ps

module Processor_TB;
	logic clk, reset;
	logic [6 : 0] opcode_in_s;
	//Processor UUT (clk, reset);
	top UUT (clk, reset);
	//assign opcode_in_s = UUT.cpu1.instruction[6:0];
	
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
