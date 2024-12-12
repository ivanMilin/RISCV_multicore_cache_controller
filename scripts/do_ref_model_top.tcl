clear -all

analyze -sv09 -f design_top.f -bbox_m InstructionMemory

check_cov -init
elaborate -top top -bbox_a 58368

clock clk -both_edges -factor 1 -phase 1
reset -expression {reset}

prove -all
