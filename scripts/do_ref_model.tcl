clear -all

analyze -sv09  -f design.f -bbox_m InstructionMemory

elaborate -top Processor

clock clk -both_edges -factor 1 -phase 1
reset -expression {reset}

prove -all
