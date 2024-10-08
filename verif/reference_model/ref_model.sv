`include "defines.sv"

module ref_model
(
	input clk,
	input reset
);
	`include "structs.sv"	
	
	// Constant parametes - opcodes for each instruction type
	// =========== TRY TO PLACE DEFINE MACROS HERE ============ //
	parameter[6:0] instruction_R_type_opcode = `TYPE_R;
	parameter[6:0] instruction_I_type_opcode = `TYPE_I;
	parameter[6:0] instruction_L_type_opcode = `TYPE_L;
	parameter[6:0] instruction_S_type_opcode = `TYPE_S;
	parameter[6:0] instruction_B_type_opcode = `TYPE_B;
	parameter[6:0] instruction_U_type_opcode = `TYPE_U;
	parameter[6:0] instruction_J_type_opcode = `TYPE_J;
	
	/*
	parameter[6:0] instruction_R_type_opcode = 7'b0110011;
	parameter[6:0] instruction_I_type_opcode = 7'b0010011;
	parameter[6:0] instruction_L_type_opcode = 7'b0000011;
	parameter[6:0] instruction_S_type_opcode = 7'b0100011;
	parameter[6:0] instruction_B_type_opcode = 7'b1100011;
	parameter[6:0] instruction_U_type_opcode = 7'b0110111;
	parameter[6:0] instruction_J_type_opcode = 7'b1101111;
	*/

	// Control singals (combinational) - for reference model 
	logic [31:0] rdata_ref;
	logic [3:0] alu_op_ref; 
	logic [2:0] mask_ref; 
	logic [2:0] br_type_ref;
	logic [1:0] wb_sel_ref; 
	logic reg_wr_ref; 
	logic sel_A_ref; 
	logic sel_B_ref; 
	logic rd_en_ref; 
	logic wr_en_ref;
	logic [31 : 0] data_from_rf_ref; //  Temporary signal for displaying data located in rf
	logic [4  : 0] address_from_rf;
	
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
	logic [31:0] address_to_check;

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
	
	//Signals for cheching jump and branch 
	logic jump_ref;
	logic branch_ref;
	logic br_taken_ref;


	// Grey box signals from DUT - will be assigned
	logic [31:0] gb_pc_index;	
	logic [31:0] gb_pc_index_next;
	logic [31:0] gb_dmem_rdata;
	logic [31:0] gb_data_to_be_stored_in_dmem;
	logic [31:0] gb_data_stored_in_rf;
	logic [31:0] gb_data_from_dmem_to_rf;
	logic [31:0] gb_rd;
	logic [31:0] gb_rs1;
	logic [31:0] gb_rs2;
	logic gb_br_taken;

	// Free variables - NDC 
	logic [31:0] fvar_specific_addr;
	logic [31:0] fvar_specific_addr_q;
	logic [31:0] fvar_specific_addr_q_neg;

	// Data memory signals
	logic [31:0] wdata_ref;
	logic known;
	logic valid, valid_loaded;
	logic [31:0] rdata_to_check;

	// Register file signals
	logic [31:0] operand1_ref;
	logic [31:0] operand2_ref;
	logic [31:0] result_ref;
	logic [31:0] result_ref_reg;
	logic [31:0] destination_addr;
	
	logic [11:0] small_immediate_ref;
	logic [31:0] signed_small_immediate_ref;
	
	logic [19:0] big_immediate_ref;
	logic [31:0] signed_big_immediate_ref;

	//PC counter
	logic[31:0] pc_counter_ref;
	
	struct_instruction_J struct_assignment;

	// Default setup for properties 
	// ================= ASSUMES SECTION ================// 

	// Assumptions for instructions - which opcodes will tool feed
	
	property assume_opcodes;
		@(posedge clk) disable iff(reset) 
		Processor.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode};
	endproperty 

	property assume_opcodes_neg;
		@(negedge clk) disable iff(reset) 
		Processor.instruction[6:0] inside {instruction_R_type_opcode,instruction_I_type_opcode,instruction_L_type_opcode,instruction_S_type_opcode,instruction_U_type_opcode,instruction_B_type_opcode,instruction_J_type_opcode};
	endproperty 
	
	property assume_load_rs2_not_NULL;
		@(posedge clk) disable iff(reset) 
		Processor.im.instruction[6:0] == instruction_L_type_opcode |-> 
		Processor.im.instruction[11:7] != 'b0 && Processor.im.instruction[31:20]+Processor.im.instruction[19:15] < 1024 && Processor.im.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
	endproperty
	
	property assume_load_rs2_not_NULL_neg;
		@(negedge clk) disable iff(reset) 
		Processor.im.instruction[6:0] == instruction_L_type_opcode |-> 
		Processor.im.instruction[11:7] != 'b0 && Processor.im.instruction[31:20]+Processor.im.instruction[19:15] < 1024 && Processor.im.instruction[14:12] inside {3'b000,3'b001,3'b010,3'b100,3'b101};
	endproperty
	
	property assume_store_less_than_1024;
		@(posedge clk) disable iff(reset)  
		Processor.im.instruction[6:0] == instruction_S_type_opcode |-> 
		{Processor.im.instruction[31:25],Processor.im.instruction[11:7]} + Processor.im.instruction[19:15] < 1024 &&
		({Processor.im.instruction[31:25],Processor.im.instruction[11:7]} + Processor.im.instruction[19:15]) % 4 == 0 && Processor.im.instruction[14:12] inside {3'b000,3'b001,3'b010};
	endproperty
	
	property assume_store_less_than_1024_neg;
		@(negedge clk) disable iff(reset)  
		Processor.im.instruction[6:0] == instruction_S_type_opcode |-> 
		{Processor.im.instruction[31:25],Processor.im.instruction[11:7]} + Processor.im.instruction[19:15] < 1024 && 
		({Processor.im.instruction[31:25],Processor.im.instruction[11:7]} + Processor.im.instruction[19:15]) % 4 == 0 && Processor.im.instruction[14:12] inside {3'b000,3'b001,3'b010};
	endproperty
	
	property assume_cant_write_to_x0;
		@(posedge clk) disable iff(reset) 
		Processor.im.instruction[6:0] == instruction_R_type_opcode || Processor.im.instruction[6:0] == instruction_I_type_opcode || Processor.im.instruction[6:0] == instruction_U_type_opcode |-> 
		Processor.im.instruction[11:7] != 0;
	endproperty
	
	property assume_cant_write_to_x0_neg;
		@(negedge clk) disable iff(reset) 
		Processor.im.instruction[6:0] == instruction_R_type_opcode || Processor.im.instruction[6:0] == instruction_I_type_opcode || Processor.im.instruction[6:0] == instruction_U_type_opcode |-> 
		Processor.im.instruction[11:7] != 0;
	endproperty

	property assume_asm_addr_stable;
		@(posedge clk) disable iff(reset) 
		fvar_specific_addr < 1024 && fvar_specific_addr % 4 == 0;
	endproperty
	
	property assume_asm_addr_stable_neg;
		@(negedge clk) disable iff(reset) 
		fvar_specific_addr < 1024 && fvar_specific_addr % 4 == 0;
	endproperty
	
	property assume_asm_addr_stableee;
		@(posedge clk) disable iff(reset) 
		!reset ##1 fvar_specific_addr_q == fvar_specific_addr;
	endproperty
	
	property assume_asm_addr_stableee_neg;
		@(negedge clk) disable iff(reset) 
		!reset ##1 fvar_specific_addr_q_neg == fvar_specific_addr;
	endproperty

	// Assumptions for instructions - which opcodes will tool feed
	all_types_active : assume property(assume_opcodes);
	all_types_active_neg : assume property(assume_opcodes_neg);
		
	// Cant load into x0 register
	load_rs2_not_NULL : assume property(assume_load_rs2_not_NULL);
	load_rs2_not_NULL_neg : assume property(assume_load_rs2_not_NULL_neg);
	
	// Memory size limit - set to 1024
	store_less_than_1024: assume property(assume_store_less_than_1024);
	store_less_than_1024_neg: assume property(assume_store_less_than_1024_neg);

	// When R or I type are active, you cant write in the x0 register
	cant_write_to_x0 : assume property (assume_cant_write_to_x0);
	cant_write_to_x0_neg : assume property (assume_cant_write_to_x0_neg);

	// Stabilize the free variable and set it accordingly to memory limitations
	asm_addr_stable : assume property(assume_asm_addr_stable);
	asm_addr_stable_neg : assume property(assume_asm_addr_stable_neg);
	
	asm_addr_stableee : assume property (assume_asm_addr_stableee);
	asm_addr_stableee_neg : assume property (assume_asm_addr_stableee_neg);

	// Grey box signals assignment
	assign gb_instruction_ref = Processor.instruction;	
	assign gb_func7_ref 	  = Processor.instruction[31:25];	
	assign gb_func3_ref 	  = Processor.instruction[14:12];	
	assign gb_pc_index 	  = Processor.index;
	assign gb_pc_index_next   = Processor.next_index;


	assign gb_addr_to_be_stored = Processor.A_r + {Processor.instruction[31:25],Processor.instruction[11:7]};
	assign gb_data_to_be_stored_in_dmem = Processor.B_r;
	assign gb_dmem_rdata 	    = Processor.datamemory.memory[fvar_specific_addr[31:2]]; 

	assign gb_data_stored_in_rf = Processor.rf.registerfile[Processor.instruction[11:7]];
	
	assign gb_rd  = Processor.instruction[11:7];
	assign gb_rs1 = Processor.rf.registerfile[Processor.instruction[19:15]];
	assign gb_rs2 = Processor.rf.registerfile[Processor.instruction[24:20]]; 
	
	assign small_immediate_ref = Processor.B_i; //output value from Immediate generator
	assign big_immediate_ref = Processor.im.instruction[31:12];
	
	assign signed_small_immediate_ref = $signed(small_immediate_ref);
	assign signed_big_immediate_ref   = $signed(big_immediate_ref);
	
	
	assign gb_imm_jump_ref = Processor.B_i;
	assign gb_br_taken = Processor.br_taken;
	assign gb_imm_branch_ref = Processor.B_i;

	
	assign struct_assignment = Processor.im.instruction;

	// AUX code for data memory // 
	// Write data on fvar_specific_addr - STORE INSTRUCTION
	// This one works - once we verify its all good, delete the upper code
	always_ff @(negedge clk) begin
		if(reset) begin
			wdata_ref <= 'b0;
			known <= 'b0;
			address_to_check <= 'b0; 
		end
		else begin 
			if(Processor.instruction[6:0] == instruction_S_type_opcode) begin
				if(gb_addr_to_be_stored == fvar_specific_addr) begin 
					known <= 1'b1;
					address_to_check <= Processor.alu_out; // Additional signal for property check
					case(Processor.instruction[14:12])
						3'b000 : begin // Store byte
							case(Processor.datamemory.addr[1:0])
								2'b00: begin
									wdata_ref <= {24'b0,gb_data_to_be_stored_in_dmem[7:0]}; // Byte 0
								end
								
								2'b01: begin
								 	wdata_ref <= {16'b0,gb_data_to_be_stored_in_dmem[7:0],8'b0}; // Byte 1
								end

								2'b10: begin
									wdata_ref <= {8'b0,gb_data_to_be_stored_in_dmem[7:0],16'b0}; // Byte 2
								end

								2'b11: begin 
									wdata_ref <= {gb_data_to_be_stored_in_dmem[7:0],24'b0}; // Byte 3								
								end
							endcase
						end

						3'b001: begin // Store halfword
							case(Processor.datamemory.addr[1])
								1'b0: begin
									wdata_ref <= {16'b0,gb_data_to_be_stored_in_dmem[15:0]};
								end
			
								1'b1: begin
									wdata_ref <= {gb_data_to_be_stored_in_dmem[31:16],16'b0};
								end 
							endcase
						end 
	
						3'b010: begin // Store word
							wdata_ref <= gb_data_to_be_stored_in_dmem;
						end

						default : wdata_ref <= 'b0;
					endcase
				end 
			end
		end  
	end 

	always_comb begin
		rdata_to_check = 'b0;
		
		if(Processor.instruction[6:0] == instruction_S_type_opcode) begin
			case(Processor.instruction[14:12])
				3'b000 : begin // Store byte				
					rdata_to_check = Processor.datamemory.rdata[7:0]; 
				end

				3'b001: begin // Store halfword
					rdata_to_check = Processor.datamemory.rdata[15:0];
				end 

				3'b010: begin // Store word
					rdata_to_check = Processor.datamemory.rdata;
				end

				default : rdata_to_check = 'b0;		 
			endcase
		end
	end
	

	// AUX code for checking LOAD instruction 
	always_comb begin
		valid = 0;
		
		if(Processor.instruction[6:0] == instruction_L_type_opcode) begin
			case(Processor.instruction[14:12])
				// Load byte, halfword, word
				3'b000, 3'b001, 3'b010: begin
					valid = 1;	
				end
				default : valid = 0; 
			endcase
		end
	end
	
	always_ff @(negedge clk) begin
		if(reset) begin
			rdata_ref <= 'b0;
			fvar_specific_addr_q_neg <= 'b0;
		end 
		else begin
			rdata_ref <= Processor.wdata;
			fvar_specific_addr_q_neg <= fvar_specific_addr;
		end
	end
	
	
	always_ff @(negedge clk) begin
		if(reset) begin
			data_from_rf_ref <= 'b0;
			valid_loaded <= 1'b0;
		end 
		else begin
			if(valid) begin
				valid_loaded <= 1'b1;
				address_from_rf <= Processor.instruction[11:7];
				data_from_rf_ref <= gb_data_stored_in_rf;
			end
		end
	end
	
	
	//======================= PROGRAM COUNTER AUX LOGIC ===================//
	// AUX code for PC (program counter) - Branch and jump can not be checked like this, dont steal branch taken from DUT, but calculate it here
	always_comb begin
		jump_ref = 0;
		branch_ref = 0;
	
		if(Processor.instruction[6:0] == instruction_J_type_opcode) begin
			jump_ref = 1;
		end
		else if(Processor.instruction[6:0] == instruction_B_type_opcode) begin
			case(Processor.instruction[14:12]) 
				3'b000: begin
					if(gb_rs1 == gb_rs2) begin
						branch_ref = 1;
					end
					else begin 
						branch_ref = 0;
					end
				end
				3'b001: begin
					if(gb_rs1 != gb_rs2) begin
						branch_ref = 1;
					end
					else begin
						branch_ref = 0;
					end
				end
				3'b100: begin
					if(gb_rs1 < gb_rs2) begin
						branch_ref = 1;
					end
					else begin
						branch_ref = 0;
					end
				end
				3'b101: begin
					if(gb_rs1 >= gb_rs2) begin
						branch_ref = 1;
					end
					else begin
						branch_ref = 0;
					end
				end
				3'b110: begin
					if($signed(gb_rs1) < $signed(gb_rs2)) begin
						branch_ref = 1;
					end
					else begin
						branch_ref = 0;
					end
				end
				3'b111: begin
					if($signed(gb_rs1) >= $signed(gb_rs2)) begin
						branch_ref = 1;
					end
					else begin
						branch_ref = 0;
					end
				end
				default: branch_ref = 0;
			endcase
		end
		else begin
			branch_ref = 0;
			jump_ref   = 0;
		end
		
		br_taken_ref = (branch_ref | jump_ref);
	end
	
	always_ff @(posedge clk) begin
		if(reset) begin
			pc_counter_ref <= 'b0;		
		end
		else begin
			if(Processor.instruction[6:0] == instruction_J_type_opcode && br_taken_ref == 1'b1) begin
				pc_counter_ref <= pc_counter_ref + gb_imm_jump_ref; //If this is not working as expected multiply "gb_imm_jump_ref" with TWO
			end
			else if(Processor.instruction[6:0] == instruction_B_type_opcode && br_taken_ref == 1'b1) begin
				pc_counter_ref <= pc_counter_ref + gb_imm_branch_ref; 	
			end
			else begin
				pc_counter_ref <= pc_counter_ref + 4;
			end
		end
	end
	
	//======================= REGISTER FILE AUX LOGIC ===================//
	// Error in following : rs1 and rs2 in our code CANT match rd, since we use combinational logic, sequentilize this or find other way
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
							result_ref = (operand1_ref < operand2_ref)?1:0;
					end
					3'b011: begin		//SLTU
							result_ref = (operand1_ref < operand2_ref)?1:0;
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
						result_ref = operand1_ref + signed_small_immediate_ref;
					end
					3'b001: begin		//SLLI
						if(small_immediate_ref[11:5] == 'b0) begin
							result_ref = operand1_ref << signed_small_immediate_ref;
						end					
					end
					3'b010: begin		//SLTI
						result_ref = (operand1_ref < signed_small_immediate_ref) ? 1 : 0;
					end
					3'b011: begin		//SLTIU
						result_ref = (operand1_ref < signed_small_immediate_ref) ? 1 : 0;
					end
					3'b100: begin		//XORI
						result_ref = operand1_ref ^ signed_small_immediate_ref;
					end
					3'b101: begin		//SRAI, SRLI  
						if(small_immediate_ref == 7'b0100000) begin 
							result_ref = operand1_ref >>> signed_small_immediate_ref;
						end 
						else begin
							result_ref = operand1_ref >> signed_small_immediate_ref;
						end
					end
					3'b110: begin		//ORI
						result_ref = operand1_ref | signed_small_immediate_ref;
					end
					3'b111: begin		//ANDI
						result_ref = operand1_ref & signed_small_immediate_ref;
					end
				endcase
			end
			instruction_U_type_opcode: begin
				destination_addr = gb_rd;
				result_ref = signed_big_immediate_ref << 12;
			end
		endcase
	end 
	
	always_ff @(negedge clk) begin
		if(reset) begin
			result_ref_reg <= 'b0;	
		end 
		else begin
			result_ref_reg <= result_ref;
		end
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
			fvar_specific_addr_q <= 'b0;
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
			fvar_specific_addr_q <= fvar_specific_addr;
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

	// =============== PROPERTIES SECTION ================ //

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

	// Property that checks if STORE is correct
	property check_data_memory;
		$rose(known) |-> fvar_specific_addr == address_to_check && wdata_ref == rdata_to_check; // Add address check and flag
	endproperty
	
	// Property that checks if LOAD is correct
	property check_load_in_rf;
		$rose(valid_loaded) |-> rdata_ref == Processor.rf.registerfile[address_from_rf] ;
	endproperty

	// Property that checks if values in register file are correct after R and I instruction, should U type be here aswell?
	property check_rf_R_I;
		Processor.instruction[6:0] == instruction_R_type_opcode || Processor.instruction[6:0] == instruction_I_type_opcode || Processor.instruction[6:0] == instruction_U_type_opcode |->
		Processor.rf.registerfile[destination_addr] == result_ref_reg;
	endproperty
	
	
	// ===================== ASSERTIONS SECTION ==================== //
 
	// ============ CONTROLLER ASSERTS =========== //
	//assert_instruction_R_type_opcode : assert property( @(posedge clk) check_instruction_R_type_opcode);
	//assert_instruction_I_type_opcode : assert property( @(posedge clk) check_instruction_I_type_opcode);
	//assert_instruction_U_type_opcode : assert property( @(posedge clk) check_instruction_U_type_opcode);
	//assert_check_instruction_L_S_type_opcode : assert property (@(posedge clk) check_instruction_L_S_type_opcode);
	
	// ============= PROGRAM COUNTER ASSERTS ============ //
	//assert_check_PC    : assert property(@(posedge clk) check_PC);
	
	// ============= DATA MEMORY ASSERTS ============= //
	//assert_check_data_memory : assert property(@(posedge clk) check_data_memory);
	//cover_check_data_memory  : cover property(@(posedge clk) Processor.datamemory.memory[0] == 5); // Additional cover that helped us work out issues with datamemory
	
	// ============= REGISTER FILE ASSERTS ============ //
	//assert_check_load_in_rf : assert property (@(negedge clk) check_load_in_rf);
	//cover_check_data_memory  : cover property(@(posedge clk) Processor.datamemory.memory[0] == 5); 

	// ============= REGISTER FILE RESULT CHECK  ASSERTS ================ //
	assert_check_rf_R_I : assert property(@(posedge clk) check_rf_R_I);
		
endmodule


