module mux2to1(
    input  logic [31:0] in1,
    input  logic [31:0] in2,
    input  logic [6:0] sel,
    output logic [31:0] out1
);

    always_comb begin
        if(sel == 7'b0100011) begin 
            out1 = in1;
        end
        else begin
            out1 = in2;
        end
    end

endmodule
