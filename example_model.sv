`timescale 1ns/1ps

module BooleanNet (
    input  logic clk,
    input  logic rst_n,
    input  logic v_CycD,
    output logic v_Cdc20,
    output logic v_Cdh1,
    output logic v_CycA,
    output logic v_CycB,
    output logic v_CycE,
    output logic v_E2F,
    output logic v_Rb,
    output logic v_UbcH10,
    output logic v_p27
);

  // next-state signals
  logic next_v_Cdc20, next_v_Cdh1, next_v_CycA, next_v_CycB, next_v_CycE, next_v_E2F, next_v_Rb, next_v_UbcH10, next_v_p27;

  logic[8:0] network_state;
  logic[0:0] inputs;

  assign network_state = {v_Cdc20, v_Cdh1, v_CycA, v_CycB, v_CycE, v_E2F, v_Rb, v_UbcH10, v_p27};
  assign inputs = {v_CycD};

  always_comb begin
    next_v_Cdc20 = v_CycB;
    next_v_Cdh1 = ((v_Cdc20 | (v_p27 & ~v_CycB)) | ~(((v_p27 | v_CycB) | v_CycA) | v_Cdc20));
    next_v_CycA = ((v_CycA & ~(((v_Cdh1 & v_UbcH10) | v_Cdc20) | v_Rb)) | (v_E2F & ~(((v_Cdh1 & v_UbcH10) | v_Cdc20) | v_Rb)));
    next_v_CycB = ~(v_Cdc20 | v_Cdh1);
    next_v_CycE = (v_E2F & ~v_Rb);
    next_v_E2F = ((v_p27 & ~(v_CycB | v_Rb)) | ~(((v_p27 | v_Rb) | v_CycB) | v_CycA));
    next_v_Rb = ((v_p27 & ~(v_CycD | v_CycB)) | ~((((v_CycE | v_p27) | v_CycB) | v_CycD) | v_CycA));
    next_v_UbcH10 = (((((v_UbcH10 & ((v_Cdh1 & ((v_CycB | v_Cdc20) | v_CycA)) | ~v_Cdh1)) | (v_CycA & ~v_Cdh1)) | (v_Cdc20 & ~v_Cdh1)) | (v_CycB & ~v_Cdh1)) | ~((((v_UbcH10 | v_Cdh1) | v_CycB) | v_Cdc20) | v_CycA));
    next_v_p27 = ((v_p27 & ~((v_CycD | (v_CycA & v_CycE)) | v_CycB)) | ~((((v_CycE | v_p27) | v_CycB) | v_CycD) | v_CycA));
  end

  always_ff @(posedge clk) begin
      v_Cdc20 <= next_v_Cdc20;
      v_Cdh1 <= next_v_Cdh1;
      v_CycA <= next_v_CycA;
      v_CycB <= next_v_CycB;
      v_CycE <= next_v_CycE;
      v_E2F <= next_v_E2F;
      v_Rb <= next_v_Rb;
      v_UbcH10 <= next_v_UbcH10;
      v_p27 <= next_v_p27;
  end

    // properties:

    property p_was_stable_for_once;
      @(posedge clk) disable iff (!rst_n)
       ##1 $stable(network_state);
    endproperty

    property p_existencial_stable;
      @(posedge clk) disable iff (!rst_n)
       ##[1:$] $stable(network_state) |=> not(always $stable(network_state));
    endproperty

    property p_universal_stable;
      @(posedge clk) disable iff (!rst_n)
       s_eventually (always $stable(network_state));
    endproperty

    // assertions:
    NOT_ALWAYS_TOGGLING: cover property (p_was_stable_for_once);
    SDY_STT_EXIST:       assert property (p_existencial_stable);
    SDY_STT_UNIVERSAL:   assert property (p_universal_stable);

endmodule
