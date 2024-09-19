clear -all

analyze -sv09  -f design.f

elaborate -top Processor

clock clk -factor 1 -phase 1
reset -expression {reset}

prove -all
