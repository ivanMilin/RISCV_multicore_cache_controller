typedef struct packed 
{
    logic [6:0] funct7;
    logic [4:0] rs2;
    logic [4:0] rs1;
    logic [2:0] funct3;
    logic [4:0] rd;
    logic [6:0] opcode;
} struct_instruction_R;

// Bit width is same for I and L 
typedef struct packed 
{
    logic [11:0] imm;
    logic [4:0]  rs1;
    logic [2:0]  funct3;
    logic [4:0]  rd;
    logic [6:0]  opcode;
} struct_instruction_I_L; 

// Bit width is same for S and B 
typedef struct packed 
{
    logic [11:0] imm;
    logic [4:0]  rs2;
    logic [4:0]  rs1;
    logic [2:0]  funct3;
    logic [6:0]  opcode;
} struct_instruction_S_B;

// Bit width is same for U and J 
typedef struct packed 
{
    logic [19:0] imm;
    logic [4:0]  rd;
    logic [6:0]  opcode;
} struct_instruction_U_J;		

 
