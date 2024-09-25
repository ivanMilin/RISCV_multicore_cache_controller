module ref_model
(
	input clk,
	input reset
);

	parameter[6:0] instruction_R_type_opcode = 7'b0110011;
	parameter[6:0] instruction_I_type_opcode = 7'b0010011;
	parameter[6:0] instruction_L_type_opcode = 7'b0000011;
	parameter[6:0] instruction_S_type_opcode = 7'b0100011;
	parameter[6:0] instruction_B_type_opcode = 7'b1100011;
	parameter[6:0] instruction_U_type_opcode = 7'b0110111;
	parameter[6:0] instruction_J_type_opcode = 7'b1101111;

	//logic [31:0] instruction_ref;
	logic [3:0] alu_op_ref; 
	logic [2:0] mask_ref; 
	logic [2:0] br_type_ref;
	logic [1:0] wb_sel_ref; 
	logic reg_wr_ref; 
	logic sel_A_ref; 
	logic sel_B_ref; 
	logic rd_en_ref; 
	logic wr_en_ref; 
	//==========================
	logic [3:0] alu_op_ref_next; 
	logic [2:0] mask_ref_next;
	logic [2:0] mask_ref_next_s; 
	logic [2:0] br_type_ref_next;
	logic [1:0] wb_sel_ref_next; 
	logic reg_wr_ref_next; 
	logic sel_A_ref_next; 
	logic sel_B_ref_next; 
	logic rd_en_ref_next; 
	logic wr_en_ref_next; 
	//==========================
	logic[31:0] index_ref; //Signal for PC
	//==========================
	logic[31:0] index_ref_next; //Signal for PC

	logic[31:0] instruction_cpu,instruction_ref;
	logic[6:0] func7_ref;
	logic[2:0] func3_ref;	

	logic [31:0] pc_index;	
	logic [31:0] pc_index_next;

	default
	clocking @(posedge clk);
	endclocking

	default disable iff reset;

	//assign index = Processor.next_index;
	//assign instruction_ref = Processor.instruction;

	R_I_type : assume property(Processor.instruction[6:0] inside  {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode});
	//R_type : assume property(Processor.instruction[6:0] == instruction_R_type_opcode);
	//I_type : assume property(Processor.instruction[6:0] == instruction_I_type_opcode);
	
	assign instruction_ref = Processor.instruction;	
	assign func7_ref = Processor.instruction[31:25];	
	assign func3_ref = Processor.instruction[14:12];	
	assign pc_index = Processor.index;
	assign pc_index_next = Processor.next_index;
	
	always_ff @(posedge clk) begin	
		if(reset) begin
			index_ref   <= 'b0;	
			alu_op_ref  <= 'b0; 
			mask_ref    <= 'b0; 
			br_type_ref <= 'b0;
			wb_sel_ref  <= 'b0; 
			reg_wr_ref  <= 'b0; 
			sel_A_ref   <= 'b0; 
			sel_B_ref   <= 'b0; 
			rd_en_ref   <= 'b0; 
			wr_en_ref   <= 'b0;
		end
		else begin
			index_ref   <= index_ref_next;	
			alu_op_ref  <= alu_op_ref_next; 
			mask_ref    <= mask_ref_next; 
			br_type_ref <= br_type_ref_next;
			wb_sel_ref  <= wb_sel_ref_next; 
			reg_wr_ref  <= reg_wr_ref_next; 
			sel_A_ref   <= sel_A_ref_next; 
			sel_B_ref   <= sel_B_ref_next; 
			rd_en_ref   <= rd_en_ref_next; 
			wr_en_ref   <= wr_en_ref_next;
		end
	end
		
	always_comb begin
		index_ref_next   = index_ref;	
		alu_op_ref_next  = alu_op_ref; 
		mask_ref_next    = mask_ref; 
		br_type_ref_next = br_type_ref;
		wb_sel_ref_next  = wb_sel_ref; 
		reg_wr_ref_next  = reg_wr_ref; 
		sel_A_ref_next   = sel_A_ref; 
		sel_B_ref_next   = sel_B_ref; 
		rd_en_ref_next   = rd_en_ref; 
		wr_en_ref_next   = wr_en_ref;
		
		case(instruction_ref[6:0])
			7'b0110011: begin
				//index_ref = index_ref + 4;			
				reg_wr_ref_next = 1;
	    			sel_A_ref_next  = 1;
	    			sel_B_ref_next  = 0;
	    			rd_en_ref_next  = 0;
	    			wb_sel_ref_next = 0;
				
				case(func3_ref)										
					3'b000: begin if (func7_ref == 7'b0100000) alu_op_ref_next = 9; else alu_op_ref_next = 0; end//sub, add
					3'b001:	alu_op_ref_next = 1;//sll
					3'b010:	alu_op_ref_next = 2;//slt
					3'b011:	alu_op_ref_next = 3;//sltu
					3'b100:	alu_op_ref_next = 4;//xor
					3'b101: begin if (func7_ref == 7'b0100000) alu_op_ref_next = 6; else alu_op_ref_next = 5; end//sra, srl
					3'b110:	alu_op_ref_next = 7;//or
					3'b111:	alu_op_ref_next = 8;//and
				endcase
			end
			
			instruction_I_type_opcode: begin
				//index_ref = index_ref + 4;				
				reg_wr_ref_next  = 1;
	    			sel_A_ref_next   = 1;
	    			sel_B_ref_next   = 1;
	    			rd_en_ref_next   = 0;
	    			wb_sel_ref_next  = 0;
				
				case (Processor.instruction[14:12])
					3'b000: alu_op_ref_next  = 0;//addi
					3'b001:	alu_op_ref_next  = 1;//slli 
					3'b010:	alu_op_ref_next  = 2;//slti
					3'b011:	alu_op_ref_next  = 3;//sltiu
					3'b100:	alu_op_ref_next  = 4;//xori
					3'b101: begin if (Processor.instruction[31:25] == 7'b0100000) alu_op_ref_next  = 6; else alu_op_ref_next  = 5; end //srai, srli
					3'b110:	alu_op_ref_next  = 7;//ori
					3'b111:	alu_op_ref_next  = 8;//andi
				endcase
			end
			instruction_L_type_opcode: begin				
				reg_wr_ref_next = 1;
	    			sel_A_ref_next  = 1;
	    			sel_B_ref_next  = 1;
	    			rd_en_ref_next  = 1;
	    			wr_en_ref_next  = 0;
	    			wb_sel_ref_next = 1;
	    			alu_op_ref_next = 0;
	    			mask_ref_next   = Processor.instruction[14:12];			
			end
			
			instruction_S_type_opcode: begin
				reg_wr_ref_next = 0;
	    			sel_A_ref_next  = 1;
	    			sel_B_ref_next  = 1;
	    			rd_en_ref_next  = 1;
	    			wr_en_ref_next  = 1;
	    			wb_sel_ref_next = 1;
	    			alu_op_ref_next = 0;
	    			mask_ref_next   = Processor.instruction[14:12];			
			end
			instruction_B_type_opcode: begin
				//index_ref <= index_ref + Processor.instruction[31:12]; //???
	
				reg_wr_ref_next = 0;
	    			sel_A_ref_next  = 0;
	    			sel_B_ref_next  = 1;
	    			rd_en_ref_next  = 0;
	    			wr_en_ref_next  = 0;
	    			wb_sel_ref_next = 0;
	    			alu_op_ref_next = 0;
	    			br_type_ref_next = Processor.instruction[14:12];
			end
			instruction_U_type_opcode: begin
				//index_ref <= index_ref + 4;
	
				reg_wr_ref_next = 1;
	    			sel_A_ref_next  = 1;
	    			sel_B_ref_next  = 1;
	    			rd_en_ref_next  = 0;
	    			wr_en_ref_next  = 0;
	    			wb_sel_ref_next = 0;
	    			alu_op_ref_next = 0;
			end	
			instruction_J_type_opcode: begin
				//index_ref <= index_ref + {Processor.instruction[20],Processor.instruction[10:1], Processor.instruction[11], Processor.instruction[19:12]};
				
				reg_wr_ref_next = 1;
	    			sel_A_ref_next  = 0;
	    			sel_B_ref_next  = 1;
	    			rd_en_ref_next  = 0;
	    			wr_en_ref_next  = 0;
	    			wb_sel_ref_next = 2;
	    			alu_op_ref_next = 0;			
			end		
		endcase
	end

	


	property check_instruction_R_type_opcode;
		Processor.instruction[6:0]==instruction_R_type_opcode |=>
		Processor.controller.reg_wr == reg_wr_ref_next  && 
		Processor.controller.sel_A  == sel_A_ref_next   &&
		Processor.controller.sel_B  == sel_B_ref_next   &&
		Processor.controller.rd_en  == rd_en_ref_next   &&
		Processor.controller.wb_sel == wb_sel_ref_next  &&	
		Processor.controller.alu_op == alu_op_ref_next;
	endproperty

	property check_instruction_I_type_opcode;
		Processor.instruction[6:0] == instruction_I_type_opcode |=>
		Processor.controller.reg_wr == reg_wr_ref_next  && 
		Processor.controller.sel_A  == sel_A_ref_next   &&
		Processor.controller.sel_B  == sel_B_ref_next   &&
		Processor.controller.rd_en  == rd_en_ref_next   &&
		Processor.controller.alu_op == alu_op_ref_next  &&
		Processor.controller.wb_sel == wb_sel_ref_next;	
	endproperty

	property check_instruction_L_S_type_opcode;
		(Processor.instruction[6:0] == instruction_L_type_opcode ||
		Processor.instruction[6:0] == instruction_S_type_opcode) |=>
		Processor.controller.reg_wr == reg_wr_ref_next  && 
		Processor.controller.sel_A  == sel_A_ref_next   &&
		Processor.controller.sel_B  == sel_B_ref_next   &&
		Processor.controller.rd_en  == rd_en_ref_next   &&
		Processor.controller.alu_op == alu_op_ref_next  &&
		Processor.controller.wb_sel == wb_sel_ref_next;//  &&
		//Processor.controller.mask == mask_ref_next;	
	endproperty
	
	/*
	property check_instruction_U_type_opcode;
		Processor.instruction[6:0] == instruction_U_type_opcode |=>
		Processor.controller.reg_wr == reg_wr_ref_next  && 
		Processor.controller.sel_A  == sel_A_ref_next   &&
		Processor.controller.sel_B  == sel_B_ref_next   &&
		Processor.controller.rd_en  == rd_en_ref_next   &&
		Processor.controller.alu_op == alu_op_ref_next  &&
		Processor.controller.wb_sel == wb_sel_ref_next;
			
	endproperty
	*/

	property check_PC_for_R_I_L_S_U;
		Processor.instruction[6:0] == instruction_R_type_opcode || 
		Processor.instruction[6:0] == instruction_I_type_opcode ||
		Processor.instruction[6:0] == instruction_L_type_opcode ||
		Processor.instruction[6:0] == instruction_S_type_opcode ||
		Processor.instruction[6:0] == instruction_U_type_opcode |=>
		pc_index_next == pc_index + 4;
	endproperty


	assert_instruction_R_type_opcode : assert property( @(posedge clk) check_instruction_R_type_opcode);
	assert_instruction_I_type_opcode : assert property( @(posedge clk) check_instruction_I_type_opcode);
	assert_check_instruction_L_S_type_opcode : assert property (@(posedge clk) check_instruction_L_S_type_opcode);
	assert_check_PC_for_R_I_L_S_U    : assert property(@(posedge clk) check_PC_for_R_I_L_S_U);
	cover_mask : cover property(mask_ref_next[*3]);
endmodule

/*	
	input[31:0] plus4,
	input[31:0] next_index, //PC-in
	input[31:0] wdata,
	input[31:0] rdata,
	input[31:0] index,	//PC-out
	input[31:0] A,
	input[31:0] B,
	input[31:0] B_i,
	input[31:0] A_r,
	input[31:0] B_r,
	input[31:0] instruction,
	input[31:0] alu_out,
	input[3:0] alu_op,
	input[2:0] mask,
	input[2:0] br_type,
	input[1:0] wb_sel,
	logic reg_wr,
	logic rd_en,
	logic wr_en,
	logic sel_A,
	logic sel_B,
	logic br_taken 
	*/
