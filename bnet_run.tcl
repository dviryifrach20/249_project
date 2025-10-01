clear -all

analyze -sv17 mod12_auto_generated.sv
elaborate -top BooleanNet

# set_property analysis_mode prove

# define clock & reset
clock clk
reset !rst_n

prove -all
