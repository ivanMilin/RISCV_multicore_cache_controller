`timescale 1ns/1ps

module controller_tb;

    //input
    logic [31:0] instruction;  

    //outputs
    logic [3:0] alu_op;        
    logic [2:0] mask;          
    logic [2:0] br_type;       
    logic reg_wr;              
    logic sel_A;               
    logic sel_B;                
    logic rd_en;               
    logic wr_en;               
    logic [1:0] wb_sel;        


    Controller dut(
        .instruction(instruction),
        .alu_op(alu_op),
        .mask(mask),
        .br_type(br_type),
        .reg_wr(reg_wr),
        .sel_A(sel_A),
        .sel_B(sel_B),
        .rd_en(rd_en),
        .wr_en(wr_en),
        .wb_sel(wb_sel)
    );

    // Test procedure
    initial begin
        $display("\n===============================================================================================================");
        $display("     R - type                    |                 Register-Register arithmetic operation                     |");
        $display("---------------------------------------------------------------------------------------------------------------");
        $display("     Instruction                 | ALU Op | Mask  | Br Type | Reg WR | Sel A | Sel B | RD EN | WR EN | WB Sel |");
        $display("---------------------------------------------------------------------------------------------------------------");
        // Test case 1: C <= A + B;
        //instruction = 32'b0000000_00000_00000_000_00000_0110011;  // add xC, xA, xB
        instruction = 32'b00000000000000000000000000110011;  // add xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | add xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 2: C <= A << B;
        //instruction = 32'b0000000_00000_00000_001_00000_0110011;  // sll xC, xA, xB
        instruction = 32'b00000000000000000001000000110011;         // sll xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | sll xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 3: C <= $signed(A) < $signed(B);
        //instruction = 32'b0000000_00000_00000_010_00000_0110011;  // slt xC, xA, xB
        instruction = 32'b00000000000000000010000000110011;         // slt xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | slt xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 4: C <= A < B;
        //instruction = 32'b0000000_00000_00000_011_00000_0110011;  // sltu xC, xA, xB
        instruction = 32'b00000000000000000011000000110011;         // sltu xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | sltu xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 5: C <= A ^ B;
        //instruction = 32'b0000000_00000_00000_100_00000_0110011;  // xor xC, xA, xB
        instruction = 32'b00000000000000000100000000110011;         // xor xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | xor xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 6: C <= A >> B;
        //instruction = 32'b0000000_00000_00000_101_00000_0110011;  // srl xC, xA, xB
        instruction = 32'b00000000000000000101000000110011;         // srl xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | srl xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 7: C <= A >>> B;
        //instruction = 32'b0100000_00000_00000_101_00000_0110011;  // sra xC, xA, xB
        instruction = 32'b01000000000000000101000000110011;         // sra xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | sra xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 8: C <= A | B;
        //instruction = 32'b0000000_00000_00000_110_00000_0110011;  // or xC, xA, xB
        instruction = 32'b00000000000000000110000000110011;         // or xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | or xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 9: C <= A & B;
        //instruction = 32'b0000000_00000_00000_111_00000_0110011;  // and xC, xA, xB
        instruction = 32'b00000000000000000111000000110011;         // and xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | and xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 10: C <= A - B;
        //instruction = 32'b0100000_00000_00000_000_00000_0110011;  // sub xC, xA, xB
        instruction = 32'b01000000000000000000000000110011;         // sub xC, xA, xB
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | sub xC, xA, xB",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // End simulation
        $display("===============================================================================================================");
        $display("     I - type                    |                Register-Immediate arithmetic Operation                     |");
        $display("---------------------------------------------------------------------------------------------------------------");
        $display("     Instruction                 | ALU Op | Mask  | Br Type | Reg WR | Sel A | Sel B | RD EN | WR EN | WB Sel |");
        $display("---------------------------------------------------------------------------------------------------------------");
        
        
        // Test case 1: ADDI - Adds an immediate value to a register
        instruction = 32'b000000000011001010000010100010011;  // addi x10, x5, 12
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | addi x10, x5, 12",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 2: SLLI - Shift left logical immediate
        instruction = 32'b000000000010001010010010100010011;  // slli x10, x5, 2
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | slli x10, x5, 2",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 3: SLTI - Set less than immediate
        instruction = 32'b000000000011001010100010100010011;  // slti x10, x5, 12
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | slti x10, x5, 12",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 4: SLTIU - Set less than immediate unsigned
        instruction = 32'b000000000011001010110010100010011;  // sltiu x10, x5, 12
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | sltiu x10, x5, 12",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 5: XORI - Exclusive OR immediate
        instruction = 32'b000000000011001011000010100010011;  // xori x10, x5, 12
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | xori x10, x5, 12",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 6: SRLI - Shift right logical immediate
        instruction = 32'b000000000010001011010010100010011;  // srli x10, x5, 2
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | srli x10, x5, 2",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 7: SRAI - Shift right arithmetic immediate
        instruction = 32'b010000000010001011010010100010011;  // srai x10, x5, 2
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | srai x10, x5, 2",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 8: ORI - OR immediate
        instruction = 32'b000000000011001011100010100010011;  // ori x10, x5, 12
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | ori x10, x5, 12",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 9: ANDI - AND immediate
        instruction = 32'b000000000011001011110010100010011;  // andi x10, x5, 12
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | andi x10, x5, 12",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);
        

        $display("===============================================================================================================");
        $display("     I - type                    |                           Loads                                            |");
        $display("---------------------------------------------------------------------------------------------------------------");
        $display("     Instruction                 | ALU Op | Mask  | Br Type | Reg WR | Sel A | Sel B | RD EN | WR EN | WB Sel |");
        $display("---------------------------------------------------------------------------------------------------------------");
        
        // Test case 1: LB - Load Byte
        instruction = 32'b00000000010000101000001010000011;  // lb x10, 4(x5)
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | lb x10, 4(x5)",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 2: LH - Load Halfword
        instruction = 32'b00000000010000101000101010000011;  // lh x10, 4(x5)
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | lh x10, 4(x5)",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 3: LW - Load Word
        instruction = 32'b00000000010000101001001010000011;  // lw x10, 4(x5)
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | lw x10, 4(x5)",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 4: LBU - Load Byte Unsigned
        instruction = 32'b00000000010000101010001010000011;  // lbu x10, 4(x5)
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | lbu x10, 4(x5)",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 5: LHU - Load Halfword Unsigned
        instruction = 32'b00000000010000101010101010000011;  // lhu x10, 4(x5)
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | lhu x10, 4(x5)",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        $display("===============================================================================================================");
        $display("     S - type                    |                           Store                                            |");
        $display("---------------------------------------------------------------------------------------------------------------");
        $display("     Instruction                 | ALU Op | Mask  | Br Type | Reg WR | Sel A | Sel B | RD EN | WR EN | WB Sel |");
        $display("---------------------------------------------------------------------------------------------------------------");
        
        // Test case 1: SB - Store Byte
        instruction = 32'b00000000010000101000000110100011;  // sb x7, 4(x5)
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | sb x7, 4(x5)",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 2: SH - Store Halfword
        instruction = 32'b00000000010000101001100110100011;  // sh x7, 4(x5)
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | sh x7, 4(x5)",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);

        // Test case 3: SW - Store Word
        instruction = 32'b00000000010000101010000110100011;  // sw x7, 4(x5)
        #10;
        $display("%b |  %b  |  %b  |   %b   |   %b    |   %b   |   %b   |   %b   |  %b    |   %b   | sw x7, 4(x5)",
                instruction, alu_op, mask, br_type, reg_wr, sel_A, sel_B, rd_en, wr_en, wb_sel);
        
        $display("===============================================================================================================");
        $finish;
    end
endmodule;