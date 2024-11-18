`timescale 1ns / 1ps

module InstructionMemory #
(
    parameter integer file_cpu = 1
)
(
    input logic [31:0] addr,
    output logic [31:0] instruction
);

    logic [31:0] instruction_memory [31:0];
    
    if(file_cpu != 1) begin
        initial begin
            $readmemh("code2.mem", instruction_memory); // Use the parameter as the file name
        end  
    end   
    else begin
        initial begin
            $readmemh("code1.mem", instruction_memory); // Use the parameter as the file name
        end
    end   
    
    assign instruction = instruction_memory[addr[31:2]];
endmodule
