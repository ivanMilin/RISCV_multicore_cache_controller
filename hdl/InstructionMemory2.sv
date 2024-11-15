`timescale 1ns / 1ps

module InstructionMemory2
(
    input logic [31:0] addr,
    output logic [31:0] instruction
);

    logic [31:0] instruction_memory2 [31:0];
    
    initial begin
        $readmemh("ecode.mem", instruction_memory2); // Use the parameter as the file name
    end   
    
    assign instruction = instruction_memory2[addr[31:2]];
endmodule
