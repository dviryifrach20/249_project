import re
import sys

def write_prp(f,property_logic):
    f.write("      @(posedge clk) disable iff (!rst_n)\n")
    f.write("       " + property_logic + "\n")
    f.write("    endproperty\n\n")

def bnet_to_sv(bnet_file, sv_file, module_name="BooleanNet"):
    # Read .bnet
    with open(bnet_file) as f:
        lines = f.readlines()

    rules = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith('#') or line == "targets,factors":
            continue
        # for every line take 2 parts of the line in to parts
        parts = [p.strip() for p in line.split(',')]
        if len(parts) < 2:
            continue
        # unpack parts to target and expration
        target, expr = parts[0], parts[1]
        rules.append((target, expr))
    
    # Identify primary inputs: names in expressions not defined as targets
    targets = set(t for t, _ in rules)
    tokens = set()
    for _, expr in rules:
        tokens.update(re.findall(r'\b[vV]_[A-Za-z0-9_]+\b', expr))
    inputs = sorted(tokens - targets)
    outputs = sorted(t for t, _ in rules)

    with open(sv_file, 'w') as f:
        # Module header & port list
        f.write("`timescale 1ns/1ps\n\n")
        f.write(f"module {module_name} (\n")
        f.write("    input  logic clk,\n")
        f.write("    input  logic rst_n,\n")
        for inp in inputs:
            f.write(f"    input  logic {inp},\n")
        for i, out in enumerate(outputs):
            comma = ',' if i < len(outputs)-1 else ''
            f.write(f"    output logic {out}{comma}\n")
        f.write(");\n\n")

        # Next-state signals and continous assignments
        f.write("  // next-state signals\n")
        f.write("  logic " + ", ".join("next_"+o for o in outputs) + ";\n\n")
        f.write("  logic[" + str(len(outputs)-1) + ":0] network_state" + ";\n")
        f.write("  logic[" + str(len(inputs)-1) + ":0] inputs" + ";\n\n")
        f.write("  assign network_state = {" + ", ".join(o for o in outputs) + "};\n")
        f.write("  assign inputs = {" + ", ".join(i for i in inputs) + "};\n\n")
        
        # Combinational next-state logic
        f.write("  always_comb begin\n")
        for target, expr in rules:
            sv_expr = expr.replace('!', '~').replace('&', '&').replace('|', '|')
            f.write(f"    next_{target} = {sv_expr};\n")
        f.write("  end\n\n")

        # Sequential update
        f.write("  always_ff @(posedge clk) begin\n")
        for t in outputs:
            f.write(f"      {t} <= next_{t};\n")
        f.write("  end\n\n")
        
        # auto generated properties.
        f.write("    // properties:\n\n")
        # property to cover that the network isn't always toggling network.
        f.write("    property p_was_stable_for_once;\n")
        write_prp(f,"##1 $stable(network_state);")
        
        # property to assert - if fails, shows trace of the network entering steady state
        f.write("    property p_existencial_stable;\n")
        write_prp(f,"##[1:$] $stable(network_state) |=> not(always $stable(network_state));")
        
        # property to assert - proves that for any trace, the network enters steady state.
        f.write("    property p_universal_stable;\n")
        write_prp(f,"s_eventually (always $stable(network_state));")
        
        # auto generated assertions
        # asserting properties mentioned above.
        f.write("    // assertions:\n")
        f.write("    NOT_ALWAYS_TOGGLING: cover property (p_was_stable_for_once);\n")
        f.write("    SDY_STT_EXIST:       assert property (p_existencial_stable);\n")
        f.write("    SDY_STT_UNIVERSAL:   assert property (p_universal_stable);\n\n")
        
        f.write("endmodule\n")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python3.6 bnet_to_sv.py <input.bnet> <output.sv>")
        sys.exit(1)
    else:
        bnet_to_sv(sys.argv[1], sys.argv[2])
