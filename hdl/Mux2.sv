module Mux2
(
	input logic [31:0] A, B, 
	input logic sel,
	output logic [31:0] C
);
	
	always_comb begin
		//C = 'b0;
		if (sel) C = B;
		else C = A;
	end
endmodule
