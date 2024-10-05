typedef struct packed 
{
    logic [6:0] funct7;
    logic [4:0] rs2;
    logic [4:0] rs1;
    logic [2:0] funct3;
    logic [4:0] rd;
    logic [6:0] opcode;
} struct_instruction_R;

typedef struct packed 
{
    logic [11:0] imm;
    logic [4:0]  rs1;
    logic [2:0]  funct3;
    logic [4:0]  rd;
    logic [6:0]  opcode;
} struct_instruction_I; 	// Za I i za L je isti format

typedef struct packed 
{
    logic [6:0] imm_31_25;
    logic [4:0] rs2;
    logic [4:0] rs1;
    logic [2:0] funct3;
    logic [4:0] imm_11_7;
    logic [6:0] opcode;
} struct_instruction_S;

typedef struct packed 
{
    logic [19:0] imm;
    logic [4:0]  rd;
    logic [6:0]  opcode;
} struct_instruction_J;		// Za U i za J je isti format

 
