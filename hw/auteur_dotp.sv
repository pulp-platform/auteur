// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/*
 * A multiprecision dot product unit with support for MX formats.
 *
 * IMPORTANT:
 *  - The unit does NOT support denormals: it will flush any denormal, be it input or output, regardless of the chosen format
 *  - The accumulation is LOSSY
 *  - NaNs are treated as infinities
 *  - Infinity times zero is zero
 */

`include "auteur/timing.svh"

module auteur_dotp
  import auteur_pkg::*;
#(
  parameter int unsigned    NrIn = 1,
  parameter int unsigned    NrMaxJoins = 1,
  parameter int unsigned    InSuperFmtManBits = 1,
  parameter int unsigned    InSuperFmtExpBits = 1,
  parameter int unsigned    OutSuperFmtManBits = 1,
  parameter int unsigned    OutSuperFmtExpBits = 1,
  parameter int unsigned    MxScaleSuperFmtManBits = 1,
  parameter int unsigned    MxScaleSuperFmtExpBits = 1,
  // Indicates that the input mantissae include the explicit leading 1 (i.e., they are unnormalized).
  // This is useful when combining two narrow formats whose combined explicit mantissa bits are insufficient to fill the mantissa of a wider target format.
  // As an example, expanding two E2M1 inputs into one E4M3 format requires these explicit leading 1s to fill the target mantissa.
  parameter bit             InManUnnorm = 0,
  parameter int unsigned    AccRoundBits = 1,
  parameter int unsigned    YDelay = 0,
  parameter int unsigned    ScalesDelay = 0,
  parameter dotp_pipe_cfg_t PipeCfg = '{default: '0},

  localparam type in_super_fmt_t = struct packed {
    logic                                     sign;
    logic [InSuperFmtExpBits-1:0]             exponent;
    logic [InSuperFmtManBits+InManUnnorm-1:0] mantissa;
  },
  localparam type out_super_fmt_t = struct packed {
    logic                          sign;
    logic [OutSuperFmtExpBits-1:0] exponent;
    logic [OutSuperFmtManBits-1:0] mantissa;
  },
  localparam type mx_scale_super_fmt_t = struct packed {
    logic                              sign;
    logic [MxScaleSuperFmtExpBits-1:0] exponent;
    logic [MxScaleSuperFmtManBits-1:0] mantissa;
  },
  localparam type dotp_cfg_t = struct packed {
    logic[$clog2(NrMaxJoins):0] num_joins;
  }
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  dotp_cfg_t                cfg_i,

  input  logic                     in_valid_i,
  input  in_super_fmt_t [NrIn-1:0] x_i,
  input  in_super_fmt_t [NrIn-1:0] w_i,

  input  logic                     y_valid_i,
  input  out_super_fmt_t           y_i,

  input  logic                     scale_valid_i,
  input  mx_scale_super_fmt_t      x_scale_i,
  input  mx_scale_super_fmt_t      w_scale_i,

  output logic                     out_valid_o,
  output out_super_fmt_t           z_o
);
  localparam int unsigned MantAccFracWidth = OutSuperFmtManBits + AccRoundBits;
  localparam int unsigned MantAccIntWidth  = $clog2(NrIn+1) + 3 + 1; // Maximum possible number of carry bits + largest mantissa overflow + implicit 1
  localparam int unsigned MantAccWidth     = 1 + MantAccIntWidth + MantAccFracWidth; // We add the sign bit
  localparam int unsigned ShiftAmountWidth = $clog2(3+1+MantAccFracWidth);
  localparam int unsigned MaxInWidth       = 1<<NrMaxJoins;
  localparam int unsigned NrInMaxWidth     = NrIn>>NrMaxJoins;

  localparam int unsigned OutSuperFmtBias = (1<<(OutSuperFmtExpBits-1)) - 1;


  logic [NrIn-1:0]                                    x_sign_d, x_sign_q,
                                                      w_sign_d, w_sign_q;

  logic [NrIn-1:0][InSuperFmtExpBits-1:0]             x_exp_d, x_exp_q,
                                                      w_exp_d, w_exp_q;

  logic [NrIn-1:0][InSuperFmtManBits+InManUnnorm-1:0] x_mant_d, x_mant_q,
                                                      w_mant_d, w_mant_q;

  logic in_valid_mant_d, in_valid_mant_q,
        in_valid_exp_d, in_valid_exp_q;

  for (genvar i = 0; i < NrIn; i++) begin : assign_pipe_inputs
    assign x_sign_d[i] = x_i[i].sign;
    assign x_exp_d[i]  = x_i[i].exponent;
    assign x_mant_d[i] = x_i[i].mantissa;

    assign w_sign_d[i] = w_i[i].sign;
    assign w_exp_d[i]  = w_i[i].exponent;
    assign w_mant_d[i] = w_i[i].mantissa;
  end

  assign in_valid_mant_d = in_valid_i;
  assign in_valid_exp_d  = in_valid_i;

  `AUTEUR_PIPE(x_sign_pipe, PipeCfg.input_path.mantissa_path.inputs, logic [NrIn-1:0]                                   , x_sign_d, x_sign_q, in_valid_mant_d)
  `AUTEUR_PIPE(x_exp_pipe , PipeCfg.input_path.exponent_path.inputs, logic [NrIn-1:0][InSuperFmtExpBits-1:0]            , x_exp_d , x_exp_q , in_valid_exp_d )
  `AUTEUR_PIPE(x_mant_pipe, PipeCfg.input_path.mantissa_path.inputs, logic [NrIn-1:0][InSuperFmtManBits+InManUnnorm-1:0], x_mant_d, x_mant_q, in_valid_mant_d)

  `AUTEUR_PIPE(w_sign_pipe, PipeCfg.input_path.mantissa_path.inputs, logic [NrIn-1:0]                                   , w_sign_d, w_sign_q, in_valid_mant_d)
  `AUTEUR_PIPE(w_exp_pipe , PipeCfg.input_path.exponent_path.inputs, logic [NrIn-1:0][InSuperFmtExpBits-1:0]            , w_exp_d , w_exp_q , in_valid_exp_d )
  `AUTEUR_PIPE(w_mant_pipe, PipeCfg.input_path.mantissa_path.inputs, logic [NrIn-1:0][InSuperFmtManBits+InManUnnorm-1:0], w_mant_d, w_mant_q, in_valid_mant_d)

  `AUTEUR_PIPE_VALID(in_valid_mant_pipe, PipeCfg.input_path.mantissa_path.inputs, in_valid_mant_d, in_valid_mant_q)
  `AUTEUR_PIPE_VALID(in_valid_exp_pipe , PipeCfg.input_path.exponent_path.inputs, in_valid_exp_d , in_valid_exp_q )


  logic [NrMaxJoins:0][NrIn-1:0][2*InSuperFmtManBits-1:0] prod_mant_no_carry;
  logic [NrMaxJoins:0][NrIn-1:0][1:0]                     prod_mant_carry;

  logic [NrMaxJoins:0][NrIn-1:0][InSuperFmtExpBits-1:0] prod_exp_no_carry;
  logic [NrMaxJoins:0][NrIn-1:0]                        prod_exp_carry;

  logic [NrMaxJoins:0][NrIn-1:0] prod_sign;

  for (genvar i = 0; i < NrIn; i++) begin : gen_initial_products
    logic x_lead, w_lead;

    // If the input mantissa is normalized, we statically set the leading bit
    if (InManUnnorm == 0) begin
      assign x_lead = (i+1)%(1<<cfg_i.num_joins) == 0 ? 1'b1 : 1'b0;
      assign w_lead = (i+1)%(1<<cfg_i.num_joins) == 0 ? 1'b1 : 1'b0;
    end else begin
      assign x_lead = x_mant_q[i][InSuperFmtManBits];
      assign w_lead = w_mant_q[i][InSuperFmtManBits];
    end

    assign {prod_mant_carry[0][i],prod_mant_no_carry[0][i]} = {x_lead,x_mant_q[i][InSuperFmtManBits-1:0]}*{w_lead,w_mant_q[i][InSuperFmtManBits-1:0]};
    assign {prod_exp_carry[0][i],prod_exp_no_carry[0][i]} = x_exp_q[i] + w_exp_q[i];
    assign prod_sign[0][i] = x_sign_q[i] ^ w_sign_q[i];
  end

  for (genvar s = 0; s < NrMaxJoins; s++) begin : gen_join_stages
    localparam int unsigned JoinWidth = 1<<s;

    for (genvar c = 0; c < NrIn/JoinWidth; c+=2) begin : gen_per_element_join
      localparam int unsigned InCatWidth  = InManUnnorm == 0 ? InSuperFmtManBits*JoinWidth + 1 : (InSuperFmtManBits+InManUnnorm)*JoinWidth;
      localparam int unsigned InProdWidth = InManUnnorm == 0 ? 2*InCatWidth - 1 : 2*InCatWidth;

      logic [InCatWidth-1:0]  x_cat_l, x_cat_h, w_cat_l, w_cat_h;
      logic [InProdWidth-1:0] prod_mant_lh, prod_mant_hl;
      logic                   mant_carry;
      logic                   exp_carry;

      always_comb begin : concat_mantissae
        if (InManUnnorm == 0) begin
          for (int unsigned i = 0; i < JoinWidth; i++) begin
            x_cat_l[i*InSuperFmtManBits+:InSuperFmtManBits] = x_mant_q[c*JoinWidth+i];
            w_cat_l[i*InSuperFmtManBits+:InSuperFmtManBits] = w_mant_q[c*JoinWidth+i];
            x_cat_h[i*InSuperFmtManBits+:InSuperFmtManBits] = x_mant_q[(c+1)*JoinWidth+i];
            w_cat_h[i*InSuperFmtManBits+:InSuperFmtManBits] = w_mant_q[(c+1)*JoinWidth+i];
          end

          x_cat_l[InSuperFmtManBits*JoinWidth] = 1'b0;
          w_cat_l[InSuperFmtManBits*JoinWidth] = 1'b0;
          x_cat_h[InSuperFmtManBits*JoinWidth] = ((c+2)*JoinWidth)%(1<<cfg_i.num_joins) == 0 ? 1'b1 : 1'b0;
          w_cat_h[InSuperFmtManBits*JoinWidth] = ((c+2)*JoinWidth)%(1<<cfg_i.num_joins) == 0 ? 1'b1 : 1'b0;
        end else begin
          x_cat_l = x_mant_q[c*JoinWidth];
          w_cat_l = w_mant_q[c*JoinWidth];
          x_cat_h = x_mant_q[(c+1)*JoinWidth];
          w_cat_h = w_mant_q[(c+1)*JoinWidth];
        end
      end

      for (genvar i = c*JoinWidth; i < (c+2)*JoinWidth-1; i++) begin : assign_unchanged_carries
        if (InManUnnorm == 0) begin
          assign prod_mant_carry[s+1][i] = prod_mant_carry[s][i];
        end

        assign prod_exp_carry[s+1][i]  = i == (c+1)*JoinWidth-1 ? (cfg_i.num_joins <= s ? prod_exp_carry[s][i] : 1'b0) : prod_exp_carry[s][i];
      end

      assign prod_mant_lh = cfg_i.num_joins > s ? x_cat_l*w_cat_h : '0;
      assign prod_mant_hl = cfg_i.num_joins > s ? x_cat_h*w_cat_l : '0;

      if (InManUnnorm == 0) begin : gen_norm_products
        assign {mant_carry,prod_mant_no_carry[s+1][(c+2)*JoinWidth-1:c*JoinWidth]} = prod_mant_no_carry[s][(c+2)*JoinWidth-1:c*JoinWidth] + {prod_mant_lh,{(InSuperFmtManBits*JoinWidth){1'b0}}} + {prod_mant_hl,{(InSuperFmtManBits*JoinWidth){1'b0}}};
        assign prod_mant_carry[s+1][(c+2)*JoinWidth-1]                             = prod_mant_carry[s][(c+2)*JoinWidth-1] + mant_carry;
      end else begin : gen_denorm_products
        logic [2*JoinWidth-1:0][2*InSuperFmtManBits+1:0] prod_mant_packed;
        logic [2*JoinWidth-1:0][2*InSuperFmtManBits+1:0] res_packed;

        for (genvar e = 0; e < 2*JoinWidth; e++) begin : pack_prod_mant
          assign prod_mant_packed[e] = {prod_mant_carry[s][c*JoinWidth+e],prod_mant_no_carry[s][c*JoinWidth+e]};
        end

        assign res_packed = prod_mant_packed + {prod_mant_lh,{(InCatWidth){1'b0}}} + {prod_mant_hl,{(InCatWidth){1'b0}}};

        for (genvar e = 0; e < 2*JoinWidth; e++) begin : unpack_prod_mant
          assign {prod_mant_carry[s+1][c*JoinWidth+e], prod_mant_no_carry[s+1][c*JoinWidth+e]} = res_packed[e];
        end
      end

      assign {exp_carry,prod_exp_no_carry[s+1][(c+2)*JoinWidth-1:c*JoinWidth]} = prod_exp_no_carry[s][(c+2)*JoinWidth-1:c*JoinWidth] + (cfg_i.num_joins > s ? {prod_exp_carry[s][(c+2)*JoinWidth-JoinWidth-1],{(InSuperFmtExpBits*JoinWidth){1'b0}}} : '0);
      assign prod_exp_carry[s+1][(c+2)*JoinWidth-1]                            = prod_exp_carry[s][(c+2)*JoinWidth-1] + exp_carry;

      for (genvar i = c*JoinWidth; i < (c+2)*JoinWidth-1; i++) begin : assign_changed_signs
        assign prod_sign[s+1][i] = cfg_i.num_joins > s ? prod_sign[s][(c+2)*JoinWidth-1] : prod_sign[s][i];
      end

      assign prod_sign[s+1][(c+2)*JoinWidth-1] = prod_sign[s][(c+2)*JoinWidth-1];
    end
  end

  logic [NrIn-1:0][2*InSuperFmtManBits-1:0] prod_mant_no_carry_d, prod_mant_no_carry_q;
  logic [NrIn-1:0][1:0]                     prod_mant_carry_d, prod_mant_carry_q;

  logic [NrIn-1:0][InSuperFmtExpBits-1:0]   prod_exp_no_carry_d, prod_exp_no_carry_q;
  logic [NrIn-1:0]                          prod_exp_carry_d, prod_exp_carry_q;

  logic [NrIn-1:0]                          prod_sign_d, prod_sign_q;

  logic                                     prod_mant_valid_d, prod_mant_valid_q;
  logic                                     prod_exp_valid_d, prod_exp_valid_q;

  assign prod_mant_valid_d    = in_valid_mant_q;
  assign prod_exp_valid_d     = in_valid_exp_q;

  assign prod_mant_no_carry_d = prod_mant_no_carry[NrMaxJoins];
  assign prod_mant_carry_d    = prod_mant_carry[NrMaxJoins];

  assign prod_exp_no_carry_d  = prod_exp_no_carry[NrMaxJoins];
  assign prod_exp_carry_d     = prod_exp_carry[NrMaxJoins];

  assign prod_sign_d          = prod_sign[NrMaxJoins];

  `AUTEUR_PIPE(prod_mant_no_carry_pipe, PipeCfg.input_path.mantissa_path.input_products, logic [NrIn-1:0][2*InSuperFmtManBits-1:0], prod_mant_no_carry_d, prod_mant_no_carry_q, prod_mant_valid_d)
  `AUTEUR_PIPE(prod_mant_carry_pipe   , PipeCfg.input_path.mantissa_path.input_products, logic [NrIn-1:0][1:0]                    , prod_mant_carry_d   , prod_mant_carry_q   , prod_mant_valid_d)
  `AUTEUR_PIPE(prod_exp_no_carry_pipe , PipeCfg.input_path.exponent_path.input_products, logic [NrIn-1:0][InSuperFmtExpBits-1:0]  , prod_exp_no_carry_d , prod_exp_no_carry_q , prod_exp_valid_d )
  `AUTEUR_PIPE(prod_exp_carry_pipe    , PipeCfg.input_path.exponent_path.input_products, logic [NrIn-1:0]                         , prod_exp_carry_d    , prod_exp_carry_q    , prod_exp_valid_d )
  `AUTEUR_PIPE(prod_sign_pipe         , PipeCfg.input_path.mantissa_path.input_products, logic [NrIn-1:0]                         , prod_sign_d         , prod_sign_q         , prod_mant_valid_d)

  `AUTEUR_PIPE_VALID(prod_mant_valid_pipe, PipeCfg.input_path.mantissa_path.input_products, prod_mant_valid_d, prod_mant_valid_q)
  `AUTEUR_PIPE_VALID(prod_exp_valid_pipe , PipeCfg.input_path.exponent_path.input_products, prod_exp_valid_d , prod_exp_valid_q )


  // We wait here for the mantissae

  logic [NrIn-1:0][InSuperFmtExpBits-1:0] prod_exp_no_carry_fifo_d, prod_exp_no_carry_fifo_q;
  logic [NrIn-1:0]                        prod_exp_carry_fifo_d, prod_exp_carry_fifo_q;

  logic prod_exp_valid_fifo_d, prod_exp_valid_fifo_q;

  assign prod_exp_valid_fifo_d = prod_exp_valid_q;

  assign prod_exp_no_carry_fifo_d = prod_exp_no_carry_q;
  assign prod_exp_carry_fifo_d    = prod_exp_carry_q;

  `AUTEUR_PIPE_VALID(in_valid_exps_pipe, get_exp_mant_input_margin(PipeCfg), prod_exp_valid_fifo_d, prod_exp_valid_fifo_q)

  `AUTEUR_FIFO(prod_exp_no_carry_fifo, get_exp_mant_input_margin(PipeCfg), logic [NrIn-1:0][InSuperFmtExpBits-1:0], prod_exp_no_carry_fifo_d, prod_exp_no_carry_fifo_q, prod_exp_valid_fifo_d, prod_exp_valid_fifo_q)
  `AUTEUR_FIFO(prod_exp_carry_fifo   , get_exp_mant_input_margin(PipeCfg), logic [NrIn-1:0]                       , prod_exp_carry_fifo_d   , prod_exp_carry_fifo_q   , prod_exp_valid_fifo_d, prod_exp_valid_fifo_q)


  logic                              x_scale_sign_fifo_q, w_scale_sign_fifo_q;
  logic [MxScaleSuperFmtExpBits-1:0] x_scale_exp_fifo_q, w_scale_exp_fifo_q;
  logic [MxScaleSuperFmtManBits-1:0] x_scale_mant_fifo_q, w_scale_mant_fifo_q;

  logic in_valid_mant_scales_fifo;
  logic in_valid_exp_scales_fifo;

  // These pipes are here only to simplify the code, hopefully the synthesis tool will merge these with the one in the join stages
  `AUTEUR_PIPE_VALID(in_valid_mant_scales_fifo_pipe, get_mant_scales_inputs_margin(PipeCfg), in_valid_i, in_valid_mant_scales_fifo)
  `AUTEUR_PIPE_VALID(in_valid_exp_scales_fifo_pipe , get_exp_scales_inputs_margin(PipeCfg) , in_valid_i, in_valid_exp_scales_fifo )

  `AUTEUR_FIFO(x_scale_sign_fifo, get_mant_scales_inputs_margin(PipeCfg) - ScalesDelay, logic                             , x_scale_i.sign    , x_scale_sign_fifo_q, scale_valid_i, in_valid_mant_scales_fifo)
  `AUTEUR_FIFO(x_scale_exp_fifo , get_exp_scales_inputs_margin(PipeCfg)  - ScalesDelay, logic [MxScaleSuperFmtExpBits-1:0], x_scale_i.exponent, x_scale_exp_fifo_q , scale_valid_i, in_valid_exp_scales_fifo )
  `AUTEUR_FIFO(x_scale_mant_fifo, get_mant_scales_inputs_margin(PipeCfg) - ScalesDelay, logic [MxScaleSuperFmtManBits-1:0], x_scale_i.mantissa, x_scale_mant_fifo_q, scale_valid_i, in_valid_mant_scales_fifo)

  `AUTEUR_FIFO(w_scale_sign_fifo, get_mant_scales_inputs_margin(PipeCfg) - ScalesDelay, logic                             , w_scale_i.sign    , w_scale_sign_fifo_q, scale_valid_i, in_valid_mant_scales_fifo)
  `AUTEUR_FIFO(w_scale_exp_fifo , get_exp_scales_inputs_margin(PipeCfg)  - ScalesDelay, logic [MxScaleSuperFmtExpBits-1:0], w_scale_i.exponent, w_scale_exp_fifo_q , scale_valid_i, in_valid_exp_scales_fifo )
  `AUTEUR_FIFO(w_scale_mant_fifo, get_mant_scales_inputs_margin(PipeCfg) - ScalesDelay, logic [MxScaleSuperFmtManBits-1:0], w_scale_i.mantissa, w_scale_mant_fifo_q, scale_valid_i, in_valid_mant_scales_fifo)


  //Movable registers for the scales
  logic                              x_scale_sign_q, w_scale_sign_q;
  logic [MxScaleSuperFmtExpBits-1:0] x_scale_exp_q, w_scale_exp_q;
  logic [MxScaleSuperFmtManBits-1:0] x_scale_mant_q, w_scale_mant_q;

  logic in_valid_mant_scales;
  logic in_valid_exp_scales;

  `AUTEUR_PIPE_VALID(in_valid_mant_scales_pipe, PipeCfg.scale_path.mantissa_path.inputs, in_valid_mant_scales_fifo, in_valid_mant_scales)
  `AUTEUR_PIPE_VALID(in_valid_exp_scales_pipe , PipeCfg.scale_path.exponent_path.inputs, in_valid_exp_scales_fifo , in_valid_exp_scales )

  `AUTEUR_PIPE(x_scale_sign_pipe, PipeCfg.scale_path.mantissa_path.inputs, logic                             , x_scale_sign_fifo_q, x_scale_sign_q, in_valid_mant_scales_fifo)
  `AUTEUR_PIPE(x_scale_exp_pipe , PipeCfg.scale_path.exponent_path.inputs, logic [MxScaleSuperFmtExpBits-1:0], x_scale_exp_fifo_q , x_scale_exp_q , in_valid_exp_scales_fifo )
  `AUTEUR_PIPE(x_scale_mant_pipe, PipeCfg.scale_path.mantissa_path.inputs, logic [MxScaleSuperFmtManBits-1:0], x_scale_mant_fifo_q, x_scale_mant_q, in_valid_mant_scales_fifo)

  `AUTEUR_PIPE(w_scale_sign_pipe, PipeCfg.scale_path.mantissa_path.inputs, logic                             , w_scale_sign_fifo_q, w_scale_sign_q, in_valid_mant_scales_fifo)
  `AUTEUR_PIPE(w_scale_exp_pipe , PipeCfg.scale_path.exponent_path.inputs, logic [MxScaleSuperFmtExpBits-1:0], w_scale_exp_fifo_q , w_scale_exp_q , in_valid_exp_scales_fifo )
  `AUTEUR_PIPE(w_scale_mant_pipe, PipeCfg.scale_path.mantissa_path.inputs, logic [MxScaleSuperFmtManBits-1:0], w_scale_mant_fifo_q, w_scale_mant_q, in_valid_mant_scales_fifo)


  // Zero Detectors

  logic [NrIn-1:0] either_in_is_zero_d, either_in_is_zero_q;

  for (genvar i = 0; i < NrIn; i++) begin : gen_input_zero_detector
    logic [$clog2(NrIn)-1:0] fmt_start;
    logic [NrMaxJoins-1:0]   fmt_width;

    logic                    x_is_zero,
                             w_is_zero;

    assign fmt_width = 1<<cfg_i.num_joins;
    assign fmt_start = i & ~(fmt_width-1);

    always_comb begin
      x_is_zero = 1'b1;
      w_is_zero = 1'b1;

      for (int unsigned e = 0; e < fmt_width; e++) begin
        x_is_zero &= ~|x_exp_q[fmt_start+e];
        w_is_zero &= ~|w_exp_q[fmt_start+e];
      end
    end

    assign either_in_is_zero_d[i] = x_is_zero || w_is_zero;
  end

  `AUTEUR_PIPE(either_in_is_zero_pipe, PipeCfg.input_path.mantissa_path.input_products, logic [NrIn-1:0], either_in_is_zero_d, either_in_is_zero_q, in_valid_mant_q)

  logic either_scale_is_zero;

  assign either_scale_is_zero = ~|x_scale_exp_q || ~|w_scale_exp_q;


  logic [NrIn-1:0][2*InSuperFmtManBits-1:0] in_prod_mant_no_carry;
  logic [NrIn-1:0][1:0]                     in_prod_mant_carry;
  logic [NrIn-1:0][InSuperFmtExpBits-1:0]   in_prod_exp_no_carry;
  logic [NrIn-1:0]                          in_prod_exp_carry;
  logic [NrIn-1:0]                          in_prod_sign;

  for (genvar i = 0; i < NrIn; i++) begin : filter_mantissae
    assign in_prod_mant_no_carry[i] = either_in_is_zero_q[i] ? '0 : prod_mant_no_carry_q[i];
    assign in_prod_mant_carry[i]    = either_in_is_zero_q[i] ? '0 : prod_mant_carry_q[i];
  end

  assign in_prod_exp_no_carry  = prod_exp_no_carry_fifo_q;
  assign in_prod_exp_carry     = prod_exp_carry_fifo_q;
  assign in_prod_sign          = prod_sign_q;


  logic [2*MxScaleSuperFmtManBits+1:0] scale_prod_mant_d, scale_prod_mant_q;
  logic [MxScaleSuperFmtExpBits:0]     scale_prod_exp_d, scale_prod_exp_q;
  logic                                scale_prod_sign_d, scale_prod_sign_q;

  logic                                scale_prod_mant_valid_d, scale_prod_mant_valid_q;
  logic                                scale_prod_exp_valid_d, scale_prod_exp_valid_q;

  assign scale_prod_mant_d = either_scale_is_zero ? '0 : {1'b1,x_scale_mant_q}*{1'b1,w_scale_mant_q};
  assign scale_prod_exp_d  = x_scale_exp_q + w_scale_exp_q;
  assign scale_prod_sign_d = x_scale_sign_q ^ w_scale_sign_q;

  assign scale_prod_mant_valid_d = in_valid_mant_scales;
  assign scale_prod_exp_valid_d  = in_valid_exp_scales;

  `AUTEUR_PIPE(scale_prod_mant_pipe, PipeCfg.scale_path.mantissa_path.scale_product, logic [2*MxScaleSuperFmtManBits+1:0], scale_prod_mant_d, scale_prod_mant_q, scale_prod_mant_valid_d)
  `AUTEUR_PIPE(scale_prod_exp_pipe , PipeCfg.scale_path.exponent_path.scale_product, logic [MxScaleSuperFmtExpBits:0]    , scale_prod_exp_d , scale_prod_exp_q , scale_prod_exp_valid_d )
  `AUTEUR_PIPE(scale_prod_sign_pipe, PipeCfg.scale_path.mantissa_path.scale_product, logic                               , scale_prod_sign_d, scale_prod_sign_q, scale_prod_mant_valid_d)

  `AUTEUR_PIPE_VALID(scale_prod_mant_valid_pipe, PipeCfg.scale_path.mantissa_path.scale_product, scale_prod_mant_valid_d, scale_prod_mant_valid_q)
  `AUTEUR_PIPE_VALID(scale_prod_exp_valid_pipe , PipeCfg.scale_path.exponent_path.scale_product, scale_prod_exp_valid_d , scale_prod_exp_valid_q )


  // ASSUMPTION: no supported input format can have more exponent bits than the output super format
  // NOTE: there is one more bit since the surplus bias has not been subtracted yet
  logic [$clog2(NrInMaxWidth):0][NrInMaxWidth-1:0][MaxInWidth-1:0][InSuperFmtExpBits:0] max_in_prod_exps_tree_stages;
  logic [NrMaxJoins:0][MaxInWidth-1:0][InSuperFmtExpBits:0] max_in_prod_exps_narrow_tree_stages;

  logic [MaxInWidth-1:0][InSuperFmtExpBits:0] max_in_prod_exps;

  for (genvar n = 0; n < NrIn; n += MaxInWidth) begin : gen_max_tree_initial_nodes
    for (genvar e = 0; e < MaxInWidth; e++) begin : assign_elements
      assign max_in_prod_exps_tree_stages[0][n>>NrMaxJoins][e] = {in_prod_exp_carry[n+e],in_prod_exp_no_carry[n+e]};
    end
  end

  // The max tree is generated wrt the largest supported input format
  for (genvar s = 0; s < $clog2(NrInMaxWidth); s++) begin : gen_max_tree
    for (genvar n = 0; n < NrIn>>(NrMaxJoins+s); n+=2) begin : gen_nodes
      logic [MaxInWidth-1:0][1:0] comp_carry_out;

      for (genvar c = 0; c < MaxInWidth; c++) begin : gen_comparators
        logic [1:0] comp_carry_in;

        assign comp_carry_in[0] = (c+1) % (1<<cfg_i.num_joins) == 0 ? 1'b0 : comp_carry_out[c+1][0];
        assign comp_carry_in[1] = (c+1) % (1<<cfg_i.num_joins) == 0 ? 1'b0 : comp_carry_out[c+1][1];

        assign comp_carry_out[c][0] = {comp_carry_in[0],max_in_prod_exps_tree_stages[s][n][c]} >= {comp_carry_in[1],max_in_prod_exps_tree_stages[s][n+1][c]};
        assign comp_carry_out[c][1] = {comp_carry_in[0],max_in_prod_exps_tree_stages[s][n][c]} <  {comp_carry_in[1],max_in_prod_exps_tree_stages[s][n+1][c]};

        assign max_in_prod_exps_tree_stages[s+1][n>>1][c] = {comp_carry_in[0],max_in_prod_exps_tree_stages[s][n][c]} >= {comp_carry_in[1],max_in_prod_exps_tree_stages[s][n+1][c]} ? max_in_prod_exps_tree_stages[s][n][c] : max_in_prod_exps_tree_stages[s][n+1][c];
      end
    end
  end

  assign max_in_prod_exps_narrow_tree_stages[0] = max_in_prod_exps_tree_stages[$clog2(NrInMaxWidth)][0];

  // For the narrower formats, a smaller tree is generated
  for (genvar s = 0; s < NrMaxJoins; s++) begin : gen_narrow_max_tree
    localparam int unsigned NodeWidth = 1<<(NrMaxJoins-s-1);

    for (genvar n = 0; n < MaxInWidth; n+=2*NodeWidth) begin : gen_nodes
      logic [NodeWidth-1:0][1:0] comp_carry_out;

      for (genvar c = 0; c < NodeWidth; c++) begin : gen_comparators
        logic [1:0] comp_carry_in;

        assign comp_carry_in[0] = c == NodeWidth-1 ? s>=(NrMaxJoins-cfg_i.num_joins) : (c+1) % (1<<cfg_i.num_joins) == 0 ? 1'b0 : comp_carry_out[c+1][0];
        assign comp_carry_in[1] = c == NodeWidth-1 ? 1'b0                            : (c+1) % (1<<cfg_i.num_joins) == 0 ? 1'b0 : comp_carry_out[c+1][1];

        assign comp_carry_out[c][0] = {comp_carry_in[0],max_in_prod_exps_narrow_tree_stages[s][n+c]} >= {comp_carry_in[1],max_in_prod_exps_narrow_tree_stages[s][n+NodeWidth+c]};
        assign comp_carry_out[c][1] = {comp_carry_in[0],max_in_prod_exps_narrow_tree_stages[s][n+c]} <  {comp_carry_in[1],max_in_prod_exps_narrow_tree_stages[s][n+NodeWidth+c]};

        assign max_in_prod_exps_narrow_tree_stages[s+1][n+c]           = {comp_carry_in[0],max_in_prod_exps_narrow_tree_stages[s][n+c]} >= {comp_carry_in[1],max_in_prod_exps_narrow_tree_stages[s][n+NodeWidth+c]} ? max_in_prod_exps_narrow_tree_stages[s][n+c] : max_in_prod_exps_narrow_tree_stages[s][n+NodeWidth+c];
        assign max_in_prod_exps_narrow_tree_stages[s+1][n+NodeWidth+c] = s>=(NrMaxJoins-cfg_i.num_joins) ? max_in_prod_exps_narrow_tree_stages[s][n+NodeWidth+c] : max_in_prod_exps_narrow_tree_stages[s+1][n+c];
      end
    end
  end

  assign max_in_prod_exps = max_in_prod_exps_narrow_tree_stages[NrMaxJoins];

  // Now that we have the maximum exponent:
  //  - we use it to calculate the shifts for each of the elements
  //  - we calculate the actual exponent value (using OutSuperFmtExpBits) and use it to compute the shift wrt y_i

  logic [NrInMaxWidth-1:0][MaxInWidth-1:0][InSuperFmtExpBits:0] in_shifts_wrt_in_d, in_shifts_wrt_in_q;

  for (genvar i = 0; i < NrInMaxWidth; i++) begin : assign_shifts
    logic [MaxInWidth-1:0][InSuperFmtExpBits:0] exp_packed;

    for (genvar e = 0; e < MaxInWidth; e++) begin
      assign exp_packed[e] = {in_prod_exp_carry[i*MaxInWidth+e],in_prod_exp_no_carry[i*MaxInWidth+e]};
    end

    assign in_shifts_wrt_in_d[i] = max_in_prod_exps - exp_packed;
  end


  logic [MaxInWidth*InSuperFmtExpBits:0] max_in_prod_exps_norm_wide;

  logic [OutSuperFmtExpBits:0]           max_in_prod_exps_norm_wide_pad,
                                         scale_prod_exp_pad;

  logic [OutSuperFmtExpBits-1:0]         inputs_max_exp_norm;
  logic                                  inputs_max_exp_overflow;
  logic [OutSuperFmtExpBits:0]           scale_exp_norm;

  logic [OutSuperFmtExpBits-1:0]         in_scale_prod_exp_norm_d, in_scale_prod_exp_norm_q;
  logic                                  in_scale_prod_exp_norm_overflow;

  logic                                  maximum_exponent_overflow_d, maximum_exponent_overflow_q;

  logic                                  maximum_exponent_valid_d, maximum_exponent_valid_q;

  always_comb begin : assign_max_in_prod_exps_norm_wide
    max_in_prod_exps_norm_wide = '0;

    for (int unsigned e = 0; e < 1<<cfg_i.num_joins; e++) begin
      max_in_prod_exps_norm_wide[e*InSuperFmtExpBits+:InSuperFmtExpBits] = max_in_prod_exps[e][InSuperFmtExpBits-1:0];
      max_in_prod_exps_norm_wide[MaxInWidth*InSuperFmtExpBits-:1]        = max_in_prod_exps[e][InSuperFmtExpBits-:1];
    end

    for (int unsigned i = (1<<cfg_i.num_joins)*InSuperFmtExpBits; i < MaxInWidth*InSuperFmtExpBits; i++) begin
      max_in_prod_exps_norm_wide[i] = ~max_in_prod_exps_norm_wide[MaxInWidth*InSuperFmtExpBits];
    end
  end

  // Pad max_in_prod_exps_norm_wide and scale_prod_exp if they are shorter than OutSuperFmtExpBits
  if (MaxInWidth*InSuperFmtExpBits < OutSuperFmtExpBits) begin
    assign max_in_prod_exps_norm_wide_pad = {max_in_prod_exps_norm_wide[MaxInWidth*InSuperFmtExpBits-:2],{(OutSuperFmtExpBits-MaxInWidth*InSuperFmtExpBits){1'b0}},max_in_prod_exps_norm_wide[MaxInWidth*InSuperFmtExpBits-2:0]};
  end else begin
    assign max_in_prod_exps_norm_wide_pad = {max_in_prod_exps_norm_wide[MaxInWidth*InSuperFmtExpBits-:2],max_in_prod_exps_norm_wide[OutSuperFmtExpBits-2:0]};
  end

  if (MxScaleSuperFmtExpBits < OutSuperFmtExpBits) begin
    assign scale_prod_exp_pad = {scale_prod_exp_q[MxScaleSuperFmtExpBits-:2],{(OutSuperFmtManBits-MxScaleSuperFmtExpBits){1'b0}},scale_prod_exp_q[MxScaleSuperFmtExpBits-2:0]};
  end else begin
    assign scale_prod_exp_pad = scale_prod_exp_q[MxScaleSuperFmtExpBits-:OutSuperFmtExpBits+1];
  end

  // Again, here we assume no valid input format can have more exponent bits than the output super format
  assign {inputs_max_exp_overflow,inputs_max_exp_norm} = max_in_prod_exps_norm_wide_pad - OutSuperFmtBias;

  assign scale_exp_norm                                             = scale_prod_exp_pad - OutSuperFmtBias;
  assign {in_scale_prod_exp_norm_overflow,in_scale_prod_exp_norm_d} = inputs_max_exp_norm + scale_exp_norm - OutSuperFmtBias;

  assign maximum_exponent_overflow_d = in_scale_prod_exp_norm_overflow || inputs_max_exp_overflow;

  assign maximum_exponent_valid_d = prod_exp_valid_fifo_q;

  `AUTEUR_PIPE(in_shifts_wrt_in_pipe      , PipeCfg.input_path.exponent_path.maximum_exponent, logic [NrInMaxWidth-1:0][MaxInWidth-1:0][InSuperFmtExpBits:0], in_shifts_wrt_in_d, in_shifts_wrt_in_q, maximum_exponent_valid_d)
  `AUTEUR_PIPE(in_scale_prod_exp_norm_pipe, PipeCfg.input_path.exponent_path.maximum_exponent, logic [OutSuperFmtExpBits-1:0]                               , in_scale_prod_exp_norm_d, in_scale_prod_exp_norm_q, maximum_exponent_valid_d)
  `AUTEUR_PIPE_VALID(in_scale_prod_exp_norm_valid, PipeCfg.input_path.exponent_path.maximum_exponent, maximum_exponent_valid_d, maximum_exponent_valid_q)

  `AUTEUR_PIPE(maximum_exponent_overflow_pipe, get_exp_overflow_delay(PipeCfg), logic, maximum_exponent_overflow_d, maximum_exponent_overflow_q, maximum_exponent_valid_d)


  logic [OutSuperFmtExpBits-1:0] y_exp_q;
  `AUTEUR_FIFO(y_fifo_max_exp, get_max_exp_delay(PipeCfg)-YDelay, logic [OutSuperFmtExpBits-1:0], y_i.exponent, y_exp_q, y_valid_i, maximum_exponent_valid_q)


  logic [OutSuperFmtExpBits-1:0] in_scale_prod_exp_norm_shift_d, in_scale_prod_exp_norm_shift_q;

  logic [OutSuperFmtExpBits-1:0] y_shift_wide;
  logic [OutSuperFmtExpBits-1:0] in_shift_wide;

  logic [ShiftAmountWidth-1:0]   y_shift_d, y_shift_q;
  logic [ShiftAmountWidth-1:0]   in_shift;

  assign in_scale_prod_exp_norm_shift_d = in_scale_prod_exp_norm_q;

  assign y_shift_wide  = in_scale_prod_exp_norm_shift_d >  y_exp_q ? in_scale_prod_exp_norm_shift_d - y_exp_q : 0;
  assign in_shift_wide = in_scale_prod_exp_norm_shift_d <= y_exp_q ? y_exp_q - in_scale_prod_exp_norm_shift_d : 0;

  assign y_shift_d  = (y_shift_wide  >> ShiftAmountWidth) != 0 ? '1 : y_shift_wide[ShiftAmountWidth-1:0];
  assign in_shift = (in_shift_wide >> ShiftAmountWidth) != 0 ? '1 : in_shift_wide[ShiftAmountWidth-1:0];


  logic [NrIn-1:0][ShiftAmountWidth-1:0] in_shifts_norm;

  for (genvar i = 0; i < NrIn; i++) begin : normalize_input_shifts
    logic [$clog2(NrIn)-1:0]               fmt_start;
    logic [NrMaxJoins-1:0]                 fmt_width;

    logic [MaxInWidth*InSuperFmtExpBits:0] shift_wide;
    logic                                  overflow;

    assign fmt_width = 1<<cfg_i.num_joins;
    assign fmt_start = i[NrMaxJoins-1:0] & ~(fmt_width-1);

    always_comb begin : assign_wide_shifts
      shift_wide = '0;

      // Here we get rid of all the surplus carry bits if joining inputs
      for (int unsigned e = 0; e < fmt_width; e++) begin
        shift_wide[e*InSuperFmtExpBits+:InSuperFmtExpBits+1] = in_shifts_wrt_in_q[i>>NrMaxJoins][e+fmt_start];
      end
    end

    assign overflow          = (shift_wide>>ShiftAmountWidth) != 0;
    assign in_shifts_norm[i] = overflow ? '1 : shift_wide[ShiftAmountWidth-1:0];
  end


  logic [NrIn-1:0][ShiftAmountWidth-1:0] in_shifts_final_d, in_shifts_final_q;
  logic                                  in_shifts_final_valid_d, in_shifts_final_valid_q;

  for (genvar i = 0; i < NrIn; i++) begin : assign_final_input_shifts
    logic                        overflow;
    logic                        overflow_adj;
    logic [ShiftAmountWidth-1:0] local_shift;
    logic [ShiftAmountWidth-1:0] local_shift_adj;

    assign {overflow,local_shift}          = in_shift + in_shifts_norm[i];
    assign {overflow_adj, local_shift_adj} = local_shift + ((MaxInWidth - i - 1) % (1<<cfg_i.num_joins)) * ((InSuperFmtManBits+InManUnnorm) * 2); // Adjust the local shift if it is part of a larger mantissa
    assign in_shifts_final_d[i]            = overflow || overflow_adj ? '1 : local_shift_adj;
  end

  assign in_shifts_final_valid_d = maximum_exponent_valid_q;

  `AUTEUR_PIPE(y_shift_pipe                     , PipeCfg.input_path.exponent_path.final_shifts, logic [ShiftAmountWidth-1:0]          , y_shift_d                     , y_shift_q                     , in_shifts_final_valid_d)
  `AUTEUR_PIPE(in_scale_prod_exp_norm_shift_pipe, PipeCfg.input_path.exponent_path.final_shifts, logic [OutSuperFmtExpBits-1:0]        , in_scale_prod_exp_norm_shift_d, in_scale_prod_exp_norm_shift_q, in_shifts_final_valid_d)
  `AUTEUR_PIPE(in_shifts_final_pipe             , PipeCfg.input_path.exponent_path.final_shifts, logic [NrIn-1:0][ShiftAmountWidth-1:0], in_shifts_final_d             , in_shifts_final_q             , in_shifts_final_valid_d)
  `AUTEUR_PIPE_VALID(final_shift_pipe_valid, PipeCfg.input_path.exponent_path.final_shifts, in_shifts_final_valid_d, in_shifts_final_valid_q)  // Do we need this? We should be synchronized with the mantissa path at this point...


  logic [NrIn-1:0][2*InSuperFmtManBits+2*MxScaleSuperFmtManBits+3:0] scale_in_prod_mant_d, scale_in_prod_mant_q;
  logic [NrIn-1:0]                                                   scale_in_prod_sign_d, scale_in_prod_sign_q;

  logic                                                              scale_in_prod_valid_d, scale_in_prod_valid_q;

  for (genvar i = 0; i < NrIn; i++) begin : gen_scale_input_products
    assign scale_in_prod_mant_d[i] = {in_prod_mant_carry[i],in_prod_mant_no_carry[i]}*scale_prod_mant_q;
    assign scale_in_prod_sign_d[i] = in_prod_sign[i] ^ scale_prod_sign_q;
  end

  assign scale_in_prod_valid_d = prod_mant_valid_q;

  `AUTEUR_PIPE(scale_in_prod_mant_pipe, PipeCfg.input_path.mantissa_path.scale_input_products, logic [NrIn-1:0][2*InSuperFmtManBits+2*MxScaleSuperFmtManBits+3:0], scale_in_prod_mant_d, scale_in_prod_mant_q, scale_in_prod_valid_d)
  `AUTEUR_PIPE(scale_in_prod_sign_pipe, PipeCfg.input_path.mantissa_path.scale_input_products, logic [NrIn-1:0]                                                  , scale_in_prod_sign_d, scale_in_prod_sign_q, scale_in_prod_valid_d)
  `AUTEUR_PIPE_VALID(scale_in_prod_valid_pipe, PipeCfg.input_path.mantissa_path.scale_input_products, scale_in_prod_valid_d, scale_in_prod_valid_q)


  // Y Input FIFO (Accumulation)

  logic                          y_sign_acc_q;
  logic [OutSuperFmtExpBits-1:0] y_exp_acc_q;
  logic [OutSuperFmtManBits-1:0] y_mant_acc_q;

  `AUTEUR_FIFO(y_sign_fifo_acc, get_input_mant_delay(PipeCfg)-YDelay                    , logic                         , y_i.sign    , y_sign_acc_q, y_valid_i               , scale_in_prod_valid_q)
  `AUTEUR_FIFO(y_exp_fifo_acc , get_input_mant_delay(PipeCfg)-get_max_exp_delay(PipeCfg), logic [OutSuperFmtExpBits-1:0], y_i.exponent, y_exp_acc_q , maximum_exponent_valid_q, scale_in_prod_valid_q)
  `AUTEUR_FIFO(y_mant_fifo_acc, get_input_mant_delay(PipeCfg)-YDelay                    , logic [OutSuperFmtManBits-1:0], y_i.mantissa, y_mant_acc_q, y_valid_i               , scale_in_prod_valid_q)


  // FINAL ACCUMULATION

  logic signed [MantAccWidth-1:0]               mant_acc_d, mant_acc_q;
  logic [OutSuperFmtExpBits-1:0]                exp_acc_d, exp_acc_q;
  logic                                         acc_valid_d, acc_valid_q;

  logic signed [NrIn-1:0][MantAccFracWidth+4:0] scale_in_prod_mant_signed;

  always_comb begin : sum_mantissae
    mant_acc_d = signed'({y_sign_acc_q,|y_exp_acc_q,y_mant_acc_q,{(AccRoundBits){1'b0}}}) >>> y_shift_q;

    for (int unsigned i = 0; i < NrIn; i++) begin
      scale_in_prod_mant_signed[i] =  signed'({scale_in_prod_sign_q[i],scale_in_prod_sign_q[i] ? ~scale_in_prod_mant_q[i]+1 : scale_in_prod_mant_q[i],{(MantAccFracWidth-2*InSuperFmtManBits-2*MxScaleSuperFmtManBits){1'b0}}});
      mant_acc_d                   += signed'(scale_in_prod_mant_signed[i]) >>> in_shifts_final_q[i];
    end
  end

  assign exp_acc_d = in_scale_prod_exp_norm_shift_q >= y_exp_acc_q ? in_scale_prod_exp_norm_shift_q : y_exp_acc_q;

  assign acc_valid_d = scale_in_prod_valid_q;

  `AUTEUR_PIPE(mant_acc_pipe, PipeCfg.accumulation, logic [MantAccWidth-1:0]      , mant_acc_d, mant_acc_q, acc_valid_d)
  `AUTEUR_PIPE(exp_acc_pipe , PipeCfg.accumulation, logic [OutSuperFmtManBits-1:0], exp_acc_d , exp_acc_q , acc_valid_d)
  `AUTEUR_PIPE_VALID(acc_valid_pipe, PipeCfg.accumulation, acc_valid_d, acc_valid_q)

  // Normalization and Rounding

  logic                              final_sign_d, final_sign_q;
  logic [OutSuperFmtExpBits-1:0]     final_exp_d, final_exp_q;
  logic [OutSuperFmtManBits-1:0]     final_mant_d, final_mant_q;
  logic                              norm_valid_d, norm_valid_q;

  logic [MantAccWidth-2:0]           mant_acc_unsigned;
  logic [$clog2(MantAccWidth-1)-1:0] mant_acc_lz;
  logic                              mant_acc_is_zero;

  logic [MantAccWidth:0]             final_mant_pre_round;

  logic [OutSuperFmtExpBits-1:0]     final_exp_pre_overflow;
  logic                              final_exp_overflow;

  assign mant_acc_unsigned = mant_acc_q[MantAccWidth-1] ? ~mant_acc_q + 1 : mant_acc_q;

  lzc #(
    .WIDTH (MantAccWidth-1),
    .MODE  (1)
  ) acc_leading_zeros_counter (
    .in_i    (mant_acc_unsigned),
    .cnt_o   (mant_acc_lz),
    .empty_o (mant_acc_is_zero)
  );

  assign {final_exp_overflow,final_exp_pre_overflow} = mant_acc_lz < MantAccIntWidth ? exp_acc_q + (MantAccIntWidth - 1 - mant_acc_lz) : exp_acc_q - (mant_acc_lz - MantAccIntWidth + 1);
  assign final_exp_d                                 = mant_acc_is_zero ? '0 : maximum_exponent_overflow_q ? '1 : (final_exp_overflow ? (mant_acc_lz < MantAccIntWidth ? '1 : '0) : final_exp_pre_overflow);

  assign final_mant_pre_round = mant_acc_lz < MantAccIntWidth ? mant_acc_unsigned >> (MantAccIntWidth - 1 - mant_acc_lz) : mant_acc_unsigned << (mant_acc_lz - MantAccIntWidth + 1);
  assign final_mant_d         = (maximum_exponent_overflow_q || final_exp_overflow) ? '0 : final_mant_pre_round[OutSuperFmtManBits:AccRoundBits] + final_mant_pre_round[AccRoundBits-1];

  assign final_sign_d         = mant_acc_q[MantAccWidth-1];

  assign norm_valid_d         = acc_valid_q;

  `AUTEUR_PIPE(final_sign_pipe, PipeCfg.normalization, logic                         , final_sign_d, final_sign_q, norm_valid_d)
  `AUTEUR_PIPE(final_exp_pipe , PipeCfg.normalization, logic [OutSuperFmtExpBits-1:0], final_exp_d , final_exp_q , norm_valid_d)
  `AUTEUR_PIPE(final_mant_pipe, PipeCfg.normalization, logic [OutSuperFmtManBits-1:0], final_mant_d, final_mant_q, norm_valid_d)
  `AUTEUR_PIPE_VALID(norm_valid_pipe, PipeCfg.normalization, norm_valid_d, norm_valid_q)

  assign z_o.sign     = final_sign_q;
  assign z_o.exponent = final_exp_q;
  assign z_o.mantissa = final_mant_q;

  assign out_valid_o  = norm_valid_q;

endmodule