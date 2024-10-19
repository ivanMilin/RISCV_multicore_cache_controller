module Add4 (input stall, reset, input logic [31:0] A, output logic [31:0] B);
    
    always_comb begin
        if(stall == 0 && !reset) begin
            B = A + 4;
        end 
        else begin
            B = A + 'b0;
        end 
    end
endmodule
