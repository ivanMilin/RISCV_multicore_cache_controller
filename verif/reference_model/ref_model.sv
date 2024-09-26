module ref_model
(
	input clk,
	input reset
);

	// Constant parametes - opcodes for each instruction type
	parameter[6:0] instruction_R_type_opcode = 7'b0110011;
	parameter[6:0] instruction_I_type_opcode = 7'b0010011;
	parameter[6:0] instruction_L_type_opcode = 7'b0000011;
	parameter[6:0] instruction_S_type_opcode = 7'b0100011;
	parameter[6:0] instruction_B_type_opcode = 7'b1100011;
	parameter[6:0] instruction_U_type_opcode = 7'b0110111;
	parameter[6:0] instruction_J_type_opcode = 7'b1101111;

	// Control singals (combinational) - for reference model 
	logic [3:0] alu_op_ref; 
	logic [2:0] mask_ref; 
	logic [2:0] br_type_ref;
	logic [1:0] wb_sel_ref; 
	logic reg_wr_ref; 
	logic sel_A_ref; 
	logic sel_B_ref; 
	logic rd_en_ref; 
	logic wr_en_ref; 
	
	// Control signal (clocked values) - for reference model 
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

	// Program counter signal(PC) - Combinational and clocked value
	logic[31:0] index_ref;   	// PC out
	logic[31:0] index_ref_next; // PC in 

	// Instruction signals from DUT - will be assigned
	logic[31:0] instruction_cpu,instruction_ref;
	logic[6:0] func7_ref;
	logic[2:0] func3_ref;	

	// CHANGE HERE // 
	logic[2:0] prev_func3;

	// Grey box signals from DUT - will be assigned
	logic [31:0] pc_index;	
	logic [31:0] pc_index_next;

	// Free variables - NDC 
	logic[31:0] specific_addr;

	// Data memory signals
	logic[31:0] wdata_ref;
	logic[31:0] rdata_ref;

	// Register file signals
	logic[31:0] operand1_ref;
	logic[31:0] operand2_ref;
	logic[31:0] result_ref;
	logic[11:0] small_immediate_ref;
	logic[19:0] big_immediate_ref;

	// Default setup for properties 
	default clocking @(posedge clk); endclocking
	default disable iff reset;

	// Assumptions for instuctions - which opcodes will tool feed
	R_I_type : assume property(Processor.instruction[6:0] inside  {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode});
	//R_type : assume property(Processor.instruction[6:0] == instruction_R_type_opcode);
	//I_type : assume property(Processor.instruction[6:0] == instruction_I_type_opcode);
	asm_addr_stable : assume property($stable(specific_addr));
	
	// Grey box signals assignment
	assign instruction_ref = Processor.instruction;	
	assign func7_ref = Processor.instruction[31:25];	
	assign func3_ref = Processor.instruction[14:12];	
	assign pc_index = Processor.index;
	assign pc_index_next = Processor.next_index;
	
	// AUX code for register file - here map each bits from instruction_ref to operand1, operand2, big_immediate_ref, small_immediate_ref and clock them
	// After that try to write asserts
	always_comb begin 
		case(instruction_ref[6:0])
			instruction_R_type_opcode : begin 
			end 
			
			instruction_I_type_opcode : begin 
			end 
			
	end 
	
	// AUX code for data memory CHANGE HERE // 
	// Write data on specific_addr
	always_ff @(posedge clk) begin
		if(Processor.memory.wr_en) begin 
			Processor.memory[specific_addr] <= wdata_ref;
		end else begin
			Processor.memory[specific_addr] <= 'b0;
		end
	end 
	
	// Read data on specific_addr
	always_ff @(posedge clk) begin
		if(Processor.memory.rd_en) begin 
			rdata_ref <= Processor.memory[specific_addr];
		end else begin 
			rdata_ref <= 'b0;
		end 
	end 
	
	//=================================================================// 
	
	// Flip flops to clock values from combinational network
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
			// CHANGE HERE // 
			prev_func3 <= 'b0;
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
			// CHANGE HERE // 
			prev_func3 <= func3_ref; 
		end
	end
		
	// Combinational logic
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
			instruction_R_type_opcode: begin
				
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
					// CHANGE HERE //
	    			//mask_ref_next   = Processor.instruction[14:12];			
					mask_ref_next   = prev_func3;
			end
			
			instruction_S_type_opcode: begin
					reg_wr_ref_next = 0;
	    			sel_A_ref_next  = 1;
	    			sel_B_ref_next  = 1;
	    			rd_en_ref_next  = 1;
	    			wr_en_ref_next  = 1;
	    			wb_sel_ref_next = 1;
	    			alu_op_ref_next = 0;
					// CHANGE HERE //
	    			//mask_ref_next   = Processor.instruction[14:12];	
					mask_ref_next = prev_func3;					
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
					// CHANGE HERE // 
	    			//br_type_ref_next = Processor.instruction[14:12];
					br_type_ref_next = prev_func3;
			end
			
			instruction_U_type_opcode: begin
	
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

	// Properties declaration 
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
		Processor.controller.mask == mask_ref_next;	
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

	// CHANGE HERE // 
	property check_data_memory;
		Processor.instruction[6:0] == instruction_S_type_opcode |-> ##[1:$] Processor.instruction[6:0] == instruction_L_type_opcode |-> wdata_ref == rdata_ref;
	endproperty
	
	
	// Assertions 
	assert_instruction_R_type_opcode : assert property( @(posedge clk) check_instruction_R_type_opcode);
	assert_instruction_I_type_opcode : assert property( @(posedge clk) check_instruction_I_type_opcode);
	assert_check_instruction_L_S_type_opcode : assert property (@(posedge clk) check_instruction_L_S_type_opcode);
	assert_check_PC_for_R_I_L_S_U    : assert property(@(posedge clk) check_PC_for_R_I_L_S_U);
	// CHANGE HERE // 
	assert_check_data_memory : assert property(check_data_memory);
	cover_mask : cover property(mask_ref_next[*3]);
	
	
endmodule

