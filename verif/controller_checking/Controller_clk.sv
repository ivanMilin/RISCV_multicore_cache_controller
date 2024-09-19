module Controller
(
	input clk, reset,
	input logic [31:0] instruction,
	output logic [3:0] alu_op, 
	output logic [2:0] mask, br_type, 
	output logic reg_wr, sel_A, sel_B, rd_en, wr_en, 
	output logic [1:0] wb_sel 
);
	
	logic [2:0] func3;
	logic [6:0] func7;
	logic [6:0] opcode;
	
	logic [3:0] alu_op_next; 
	logic [2:0] mask_next; 
	logic [2:0] func3_past; 
	logic [2:0] br_type_next;
	logic [1:0] wb_sel_next; 
	logic reg_wr_next; 
	logic sel_A_next; 
	logic sel_B_next; 
	logic rd_en_next; 
	logic wr_en_next; 
	
	always_comb begin
		func3 <= instruction[14:12];
		func7 <= instruction[31:25];
		opcode <= instruction[6:0];
	end


    always_comb begin
    	case (opcode)
    		7'b0110011: begin	// R-type instructions
    			reg_wr_next <= 1;
    			sel_A_next <= 1;
    			sel_B_next <= 0;
    			rd_en_next <= 0;
    			wb_sel_next <= 0;
				case (func3)
					3'b000: begin if (func7 == 7'b0100000) alu_op_next <= 9; else alu_op_next <= 0; end 						//sub, add
					3'b001:	alu_op_next <= 1;													  								//sll
					3'b010:	alu_op_next <= 2;													  								//slt
					3'b011:	alu_op_next <= 3;                                                      							    //sltu
					3'b100:	alu_op_next <= 4;													  								//xor
					3'b101: begin if (func7 == 7'b0100000) alu_op_next <= 6; else alu_op_next <= 5; end 						//sra, srl
					3'b110:	alu_op_next <= 7;												      	  							//or
					3'b111:	alu_op_next <= 8;       												  							//and
				endcase
			end
			7'b0010011: begin	// I-type instructions
    			reg_wr_next <= 1;
    			sel_A_next <= 1;
    			sel_B_next <= 1;
    			rd_en_next <= 0;
    			wb_sel_next <= 0;
				case (func3)
					3'b000: alu_op_next <= 0;													  //addi
					3'b001:	alu_op_next <= 1;                                                      							  //slli 
					3'b010:	alu_op_next <= 2;													  //slti
					3'b011:	alu_op_next <= 3;													  //sltiu
					3'b100:	alu_op_next <= 4;													  //xori
					3'b101: begin if (func7 == 7'b0100000) alu_op_next <= 6; else alu_op_next <= 5; end 						  //srai, srli
					3'b110:	alu_op_next <= 7;													  //ori
					3'b111:	alu_op_next <= 8; 													  //andi
				endcase
			end
			7'b0000011: begin	// Load instructions
    			reg_wr_next <= 1;
    			sel_A_next <= 1;
    			sel_B_next <= 1;
    			rd_en_next <= 1;
    			wr_en_next <= 0;
    			wb_sel_next <= 1;
    			alu_op_next <= 0;
    			mask_next <= func3;
			end
			7'b0100011: begin	// S-type instructions
    			reg_wr_next <= 0;
    			sel_A_next <= 1;
    			sel_B_next <= 1;
    			rd_en_next <= 1;
    			//rd_en <= 1;
    			wr_en_next <= 1;
    			wb_sel_next <= 1;
    			alu_op_next <= 0;
    			mask_next <= func3;
			end			
			7'b1100011: begin	// B-type instructions
    			reg_wr_next <= 0;
    			sel_A_next <= 0;
    			sel_B_next <= 1;
    			rd_en_next <= 0;
    			wr_en_next <= 0;
    			wb_sel_next <= 0;
    			alu_op_next <= 0;
    			br_type_next <= func3;
			end			
			7'b0110111: begin	// U-type instructions
    			reg_wr_next <= 1;
    			sel_A_next <= 1;
    			sel_B_next <= 1;
    			rd_en_next <= 0;
    			wr_en_next <= 0;
    			wb_sel_next <= 0;
    			alu_op_next <= 0;
    		end
			7'b1101111: begin	// J-type instructions
    			reg_wr_next <= 1;
    			sel_A_next <= 0;
    			sel_B_next <= 1;
    			rd_en_next <= 0;
    			wr_en_next <= 0;
    			wb_sel_next <= 2;
    			alu_op_next <= 0;
    		end
		endcase
    end

    always_ff @(posedge clk) begin
		if(reset) begin
			alu_op  <= 0;
			mask    <= 0;
			br_type <= 0;
			wb_sel  <= 0; 
			reg_wr  <= 0; 
			sel_A   <= 0; 
			sel_B   <= 0; 
			rd_en   <= 0; 
			wr_en   <= 0; 		
			func3_past <= 0;	
		end 
	 	else begin 
			alu_op  <= alu_op_next;
			mask    <= mask_next; 
			func3_past <= func3;
			br_type <= br_type_next;
			wb_sel  <= wb_sel_next; 
			reg_wr  <= reg_wr_next; 
			sel_A   <= sel_A_next; 
			sel_B   <= sel_B_next; 
			rd_en   <= rd_en_next; 
			wr_en   <= wr_en_next; 
		end 	

    end 

	
endmodule
