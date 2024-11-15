`timescale 1ns / 1ps

module InstructionMemory1
(
    input logic [31:0] addr,
    output logic [31:0] instruction
);

    logic [31:0] instruction_memory1 [31:0];
    
    initial begin
        $readmemh("code.mem", instruction_memory1); // Use the parameter as the file name
    end   
    
    assign instruction = instruction_memory1[addr[31:2]];
endmodule
