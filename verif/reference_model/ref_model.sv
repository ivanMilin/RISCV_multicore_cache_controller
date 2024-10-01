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
	logic [31:0] index_ref;      // PC out
	logic [31:0] index_ref_next; // PC in 

	// Instruction signals from DUT - will be assigned
	logic [31:0] gb_instruction_ref;
	logic [6:0]  gb_func7_ref;
	logic [2:0]  gb_func3_ref;
	logic [31:0] gb_imm_jump_ref;
	logic [31:0] gb_imm_branch_ref;
	logic [31:0] gb_addr_to_be_stored;


	// Grey box signals from DUT - will be assigned
	logic [31:0] gb_pc_index;	
	logic [31:0] gb_pc_index_next;
	logic [31:0] gb_dmem_rdata;
	logic [31:0] gb_data_to_be_stored;
	logic [31:0] gb_rd;
	logic [31:0] gb_rs1;
	logic [31:0] gb_rs2;
	logic gb_br_taken;

	// Free variables - NDC 
	logic [31:0] fvar_specific_addr;

	// Data memory signals
	logic [31:0] wdata_ref;
	logic [31:0] rdata_ref;
	logic known;

	// Register file signals
	logic [31:0] operand1_ref;
	logic [31:0] operand2_ref;
	logic [31:0] result_ref;
	logic [31:0] destination_addr;
	logic [11:0] small_immediate_ref;
	logic [19:0] big_immediate_ref;

	//PC counter
	logic[31:0] pc_counter_ref;

	// Default setup for properties 
	default clocking @(posedge clk); endclocking
	default disable iff reset;

	// Assumptions for instructions - which opcodes will tool feed
	R_I_type : assume property(Processor.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode});
	//asm_addr_stable : assume property( $stable(fvar_specific_addr) && fvar_specific_addr <= 1024);
	asm_addr_stable : assume property( $stable(fvar_specific_addr) && fvar_specific_addr == 0);
	
	// Grey box signals assignment
	assign gb_instruction_ref = Processor.instruction;	
	assign gb_func7_ref 	  = Processor.instruction[31:25];	
	assign gb_func3_ref 	  = Processor.instruction[14:12];	
	assign gb_pc_index 	  = Processor.index;
	assign gb_pc_index_next   = Processor.next_index;


	assign gb_addr_to_be_stored = Processor.A_r + {Processor.instruction[31:25],Processor.instruction[11:7]};
	assign gb_data_to_be_stored = Processor.B_r;
	assign gb_dmem_rdata 	    = Processor.datamemory.memory[fvar_specific_addr]; 

	assign gb_rd  = Processor.instruction[11:7];
	assign gb_rs1 = Processor.rf.registerfile[Processor.instruction[19:15]];
	assign gb_rs2 = Processor.rf.registerfile[Processor.instruction[24:20]]; 
	assign small_immediate_ref = Processor.B_i; //output value from Immediate generator
	
	assign gb_imm_jump_ref = Processor.B_i;
	assign gb_br_taken = Processor.br_taken;
	assign gb_imm_branch_ref = Processor.B_i;


	
	// AUX code for data memory // 
	// Write data on fvar_specific_addr - STORE INSTRUCTION
	always_ff @(posedge clk) begin
		if(reset) begin
			wdata_ref <= 'b0;
			known     <= 'b0;		
		end else begin 
			if(Processor.datamemory.wr_en) begin 
				if(gb_addr_to_be_stored == fvar_specific_addr) begin
					 wdata_ref <= gb_data_to_be_stored;
					 known <= 1'b1;
				end else begin
					wdata_ref <= wdata_ref; 
					known <= 'b0; //Can we set "known" here on ZERO ??? 			
				end
			end else begin
					wdata_ref <= wdata_ref;
					known 	  <= 'b0;
			end
		end
	end 

	// AUX code for PC (program counter)
	//If opcode is anything but B or J, increment counter by 4, otherwise increment by immediate
	always_ff @(posedge clk) begin
		if(reset) begin
			pc_counter_ref <= 'b0;		
		end
		else begin
			if(Processor.instruction[6:0] == instruction_J_type_opcode && gb_br_taken == 1'b1) begin
				pc_counter_ref <= pc_counter_ref + gb_imm_jump_ref; //If this is not working as expected multiply "gb_imm_jump_ref" with TWO
			end
			else if(Processor.instruction[6:0] == instruction_B_type_opcode && gb_br_taken == 1'b1) begin
				pc_counter_ref <= pc_counter_ref + gb_imm_branch_ref; 	
			end
			else begin
				pc_counter_ref <= pc_counter_ref + 4;
			end
		end
	end

	//======================= REGISTER FILE AUX LOGIC ===================//
	always_comb begin 
	
		result_ref 	 = 'b0;
		operand1_ref 	 = 'b0;
		operand2_ref 	 = 'b0;
		destination_addr = 'b0;

		case(gb_instruction_ref[6:0])
			instruction_R_type_opcode : begin 
				
				operand1_ref = gb_rs1;
				operand2_ref = gb_rs2;
				destination_addr = gb_rd;

				case(gb_func3_ref) 
					3'b000 : begin		//SUB,ADD 
						if(gb_func7_ref == 7'b0100000) begin
							result_ref = operand1_ref - operand2_ref;
						end 
						else begin
							result_ref = operand1_ref + operand2_ref;
						end
					end
					3'b001: begin		//SLL
							result_ref = operand1_ref << operand2_ref;
					end
					3'b010: begin		//SLT
							result_ref = $signed(operand1_ref) < $signed(operand2_ref);
					end
					3'b011: begin		//SLTU
							result_ref = operand1_ref < operand2_ref;
					end
					3'b100: begin		//XOR
						result_ref = operand1_ref ^ operand2_ref;
					end
					3'b101: begin		//SRA, SRL
						if(gb_func7_ref == 7'b0100000) begin 
							result_ref = operand1_ref >>> operand2_ref;
						end 
						else begin
							result_ref = operand1_ref >> operand2_ref;
						end
					end
					3'b110: begin		//OR
						result_ref = operand1_ref | operand2_ref;
					end
					3'b111: begin		//AND
						result_ref = operand1_ref & operand2_ref;
					end
				endcase
			end
			instruction_I_type_opcode: begin
				operand1_ref = gb_rs1;
				destination_addr = gb_rd;

				case(gb_func3_ref) 
					3'b000 : begin		//ADDI 
						result_ref = operand1_ref + small_immediate_ref;
					end
					3'b001: begin		//SLLI
						if(small_immediate_ref[11:5] == 'b0) begin
							result_ref = operand1_ref << small_immediate_ref[4:0];
						end					
					end
					3'b010: begin		//SLTI
							result_ref = $signed(operand1_ref) < $signed(small_immediate_ref);
					end
					3'b011: begin		//SLTIU
							result_ref = operand1_ref < small_immediate_ref;
					end
					3'b100: begin		//XORI
						result_ref = operand1_ref ^ small_immediate_ref;
					end
					3'b101: begin		//SRAI, SRLI  
						if(small_immediate_ref == 7'b0100000) begin 
							result_ref = operand1_ref >>> small_immediate_ref[4:0];
						end 
						else if(small_immediate_ref == 'b0) begin
							result_ref = operand1_ref >> small_immediate_ref[4:0];
						end
					end
					3'b110: begin		//ORI
						result_ref = operand1_ref | small_immediate_ref;
					end
					3'b111: begin		//ANDI
						result_ref = operand1_ref & small_immediate_ref;
					end
				endcase
			end
		endcase
	end 
	
	
	//================== CONTROLLER AUX LOGIC ===================//
	// Clocked values - Sequential logic 
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
	
	// Combinational logic
	always_comb begin
		index_ref_next   = index_ref;	
		alu_op_ref_next  = 'b0;//alu_op_ref; 
		mask_ref_next    = 'b0; 
		br_type_ref_next = 'b0;
		wb_sel_ref_next  = wb_sel_ref; 
		reg_wr_ref_next  = reg_wr_ref; 
		sel_A_ref_next   = sel_A_ref; 
		sel_B_ref_next   = sel_B_ref; 
		rd_en_ref_next   = rd_en_ref; 
		wr_en_ref_next   = wr_en_ref;
		
		case(gb_instruction_ref[6:0])
			instruction_R_type_opcode: begin
				reg_wr_ref_next = 1;
	    			sel_A_ref_next  = 1;
	    			sel_B_ref_next  = 0;
	    			rd_en_ref_next  = 0;
	    			wb_sel_ref_next = 0;
				
				case(gb_func3_ref)										
					3'b000: begin if (gb_func7_ref == 7'b0100000) alu_op_ref_next = 9; else alu_op_ref_next = 0; end//sub, add
					3'b001:	alu_op_ref_next = 1;//sll
					3'b010:	alu_op_ref_next = 2;//slt
					3'b011:	alu_op_ref_next = 3;//sltu
					3'b100:	alu_op_ref_next = 4;//xor
					3'b101: begin if (gb_func7_ref == 7'b0100000) alu_op_ref_next = 6; else alu_op_ref_next = 5; end//sra, srl
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
					3'b101: begin if (Processor.instruction[31:25] == 7'b0000010) alu_op_ref_next  = 6; else alu_op_ref_next  = 5; end //srai, srli
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
				reg_wr_ref_next = 1;
	    			sel_A_ref_next  = 1;
	    			sel_B_ref_next  = 1;
	    			rd_en_ref_next  = 0;
	    			wr_en_ref_next  = 0;
	    			wb_sel_ref_next = 0;
	    			alu_op_ref_next = 0;
			end	
			
			instruction_J_type_opcode: begin				
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
		Processor.controller.wb_sel == wb_sel_ref_next  &&
		Processor.controller.mask == mask_ref_next;	
	endproperty
	
	
	property check_instruction_U_type_opcode;
		Processor.instruction[6:0] == instruction_U_type_opcode |=>
		Processor.controller.reg_wr == reg_wr_ref_next  && 
		Processor.controller.sel_A  == sel_A_ref_next   &&
		Processor.controller.sel_B  == sel_B_ref_next   &&
		Processor.controller.rd_en  == rd_en_ref_next   &&
		Processor.controller.alu_op == alu_op_ref_next  &&
		Processor.controller.wb_sel == wb_sel_ref_next;	
	endproperty

	property check_instruction_B_type_opcode;
		Processor.instruction[6:0] == instruction_B_type_opcode |=>
		Processor.controller.reg_wr == reg_wr_ref_next  && 
		Processor.controller.sel_A  == sel_A_ref_next   &&
		Processor.controller.sel_B  == sel_B_ref_next   &&
		Processor.controller.rd_en  == rd_en_ref_next   &&
		Processor.controller.alu_op == alu_op_ref_next  &&
		Processor.controller.wb_sel == wb_sel_ref_next;	
	endproperty
	
	property check_PC;
		Processor.index == pc_counter_ref;	
	endproperty

	// 
	property check_data_memory;
		//known && fvar_specific_addr == gb_addr_to_be_stored |=> wdata_ref == gb_dmem_rdata; // Add address check and flag
		known |=> wdata_ref == gb_dmem_rdata; // Add address check and flag
	endproperty
	
	// Temporary
	property check_rf_R_add;
		Processor.instruction[6:0] == instruction_R_type_opcode |=> Processor.rf.registerfile[destination_addr] == result_ref;
	endproperty

	
	// Assertions 
	// ============ CONTROLLER =========== //
	assert_instruction_R_type_opcode : assert property( @(posedge clk) check_instruction_R_type_opcode);
	assert_instruction_I_type_opcode : assert property( @(posedge clk) check_instruction_I_type_opcode);
	assert_instruction_U_type_opcode : assert property( @(posedge clk) check_instruction_U_type_opcode);
	assert_check_instruction_L_S_type_opcode : assert property (@(posedge clk) check_instruction_L_S_type_opcode);
	// ============= PROGRAM COUNTER ============ //
	assert_check_PC    : assert property(@(posedge clk) check_PC);
	// ============= DATA MEMORY ============= //
	assert_check_data_memory : assert property(@(posedge clk) check_data_memory);
	// ============= REGISTER FILE ============ //
	//assert_check_rf_R_add : assert property(check_rf_R_add);
		
endmodule

//Ask TIVADAR why new instruction appear on both edges
