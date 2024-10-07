module RegisterFile(
    input logic clk, reset, reg_wr, 
    input logic [4:0] raddr1, raddr2, waddr, 
    input logic [31:0] wdata,
    output logic [31:0] rdata1, rdata2
);
    logic [31:0] registerfile [31:0];  // Initialize all registers to zero

    always_comb begin
        rdata1 = registerfile[raddr1];
        rdata2 = registerfile[raddr2];
    end

    always_ff @(negedge clk) begin
	if(reset) begin 
	for (integer i = 0; i < 32; i = i + 1) begin
            registerfile[i] <= 'b0;
  	end
	end else begin
		if (reg_wr & (waddr != 0)) begin
		    registerfile[waddr] <= wdata;
		end
	end
    end

endmodule

