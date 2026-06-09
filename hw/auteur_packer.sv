// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_packer
  import auteur_pkg::*;
#(
  parameter int unsigned  NrIn = 1,
  parameter int unsigned  NrMaxJoins = 1,
  parameter int unsigned  BaseInFmtWidth = 1,
  parameter int unsigned  NrFormats = 1,
  parameter fp_encoding_t InFpEncoding [NrFormats-1:0] = '{default:'0},
  parameter int unsigned  OutFmtManBits = 1,
  parameter int unsigned  OutFmtExpBits = 1,
  parameter bit           OutManUnnorm = 0,

  localparam int unsigned OutPackWidth = 2**NrMaxJoins * (1 + OutFmtExpBits + OutFmtManBits + OutManUnnorm),

  parameter logic [OutPackWidth-1:0][NrFormats-1:0][31:0] FormatMapTable = '{default:'0},

  localparam int unsigned MaxInWidth = 1<<NrMaxJoins,
  localparam int unsigned NrInMaxWidth = NrIn>>NrMaxJoins,
  localparam int unsigned SelWidth = NrFormats > 1 ? $clog2(NrFormats) : 1,

  localparam type out_fmt_t = struct packed {
    logic                                  sign;
    logic [OutFmtExpBits-1:0]              exponent;
    logic [OutFmtManBits+OutManUnnorm-1:0] mantissa;
  }
) (
  input  logic [NrInMaxWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] in_i,
  input  logic [SelWidth-1:0]                                    in_fmt_i,
  output out_fmt_t [NrInMaxWidth-1:0][MaxInWidth-1:0]            out_o,
  output fp_flags_t [NrInMaxWidth-1:0][MaxInWidth-1:0]           flags_o
);

  function automatic logic [NrFormats-1:0][MaxInWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] gen_exp_mask();
    logic [NrFormats-1:0][MaxInWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] res = '0;

    for (int unsigned f = 0; f < NrFormats; f++) begin
      for (int unsigned i = 0; i < MaxInWidth; i++) begin
        logic [OutPackWidth-1:0] msk = ((2**(OutFmtExpBits*2**InFpEncoding[f].required_joins-1) + 2**(InFpEncoding[f].exponent_bits-1)-1) << (i/2**InFpEncoding[f].required_joins*OutFmtExpBits*2**InFpEncoding[f].required_joins)) << (MaxInWidth*(OutFmtManBits+OutManUnnorm));

        // We permute the mask so that it can be applied to the inputs
        logic [BaseInFmtWidth*MaxInWidth-1:0] msk_perm;

        for (int unsigned b = 0; b < OutPackWidth; b++) begin
          if (FormatMapTable[b][f] < BaseInFmtWidth*MaxInWidth) begin
            msk_perm[FormatMapTable[b][f]] = msk[b];
          end
        end

        res[f][i] = msk_perm;
      end
    end

    return res;
  endfunction

  function automatic logic [NrFormats-1:0][MaxInWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] gen_mant_mask();
    logic [NrFormats-1:0][MaxInWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] res = '0;

    for (int unsigned f = 0; f < NrFormats; f++) begin
      for (int unsigned i = 0; i < MaxInWidth; i++) begin
        logic [OutPackWidth-1:0] msk = (2**(InFpEncoding[f].mantissa_bits)-1) << (i/2**InFpEncoding[f].required_joins*(OutFmtManBits+OutManUnnorm)*2**InFpEncoding[f].required_joins + ((2**InFpEncoding[f].required_joins*(OutFmtManBits+OutManUnnorm)-OutManUnnorm)-InFpEncoding[f].mantissa_bits));

        // We permute the mask so that it can be applied to the inputs
        logic [BaseInFmtWidth*MaxInWidth-1:0] msk_perm;

        for (int unsigned b = 0; b < OutPackWidth; b++) begin
          if (FormatMapTable[b][f] < BaseInFmtWidth*MaxInWidth) begin
            msk_perm[FormatMapTable[b][f]] = msk[b];
          end
        end

        res[f][i] = msk_perm;
      end
    end

    return res;
  endfunction

  localparam logic [NrFormats-1:0][MaxInWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] ExpMask  = gen_exp_mask();
  localparam logic [NrFormats-1:0][MaxInWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] MantMask = gen_mant_mask();

  logic [NrInMaxWidth-1:0][OutPackWidth-1:0] packed_out;

  logic [NrInMaxWidth-1:0][MaxInWidth-1:0] in_is_denormal,
                                           in_is_zero,
                                           in_is_infinity,
                                           in_is_nan;

  for (genvar p = 0; p < NrInMaxWidth; p++) begin : detect_exceptions
    for (genvar i = 0; i < MaxInWidth; i++) begin : assign_exceptions
      // A number is denormal if its exponent is zero
      assign in_is_denormal[p][i] = ~|(in_i[p] & ExpMask[in_fmt_i][i]);

      // A zero has both its mantissa end exponent equal to zero
      assign in_is_zero[p][i]     = ~|(in_i[p] & ExpMask[in_fmt_i][i]) && ~|(in_i[p] & MantMask[in_fmt_i][i]);

      // In a format with infinities we check if its exponent is all ones. In addition, if it also supports NaNs, we also check if its mantissa is zero
      assign in_is_infinity[p][i] = &(in_i[p] & ExpMask[in_fmt_i][i]) && (~|(in_i[p] & MantMask[in_fmt_i][i]) || ~InFpEncoding[in_fmt_i].has_nan) && (InFpEncoding[in_fmt_i].has_infinity);

      // In a format with NaNs we check if the exponent is all ones and if at least one mantissa bit is one. Additionally, in a format without infinities, the only valid NaN is the one with a mantissa of only ones
      assign in_is_nan[p][i]      = &(in_i[p] & ExpMask[in_fmt_i][i]) && (InFpEncoding[in_fmt_i].has_infinity ? |(in_i[p] & MantMask[in_fmt_i][i]) : &(in_i[p] & MantMask[in_fmt_i][i])) && InFpEncoding[in_fmt_i].has_nan;
    end
  end

  for (genvar p = 0; p < NrInMaxWidth; p++) begin : gen_packers
    logic [MaxInWidth-1:0]                           exp_options;
    logic [BaseInFmtWidth*MaxInWidth+MaxInWidth*2:0] map_options;

    for (genvar e = 0; e < MaxInWidth; e++) begin : assign_exp_options
      assign exp_options[e] = ~in_i[p][FormatMapTable[MaxInWidth*(OutFmtManBits+OutManUnnorm)+(e+1)*OutFmtExpBits-1][0]];
    end

    // {Zero bit, Exponent extension, Unnormalized mantissa assignment, Simple maps}
    assign map_options = {1'b0, exp_options,~in_is_denormal[p],in_i[p]};

    for (genvar i = 0; i < OutPackWidth; i++) begin : assign_packed_output
      assign packed_out[p][i] = map_options[FormatMapTable[i][in_fmt_i]];
    end

    for (genvar i = 0; i < MaxInWidth; i++) begin : assign_outputs
      assign out_o[p][i].sign     = packed_out[p][(OutFmtManBits+OutManUnnorm+OutFmtExpBits)*MaxInWidth+i];
      assign out_o[p][i].exponent = packed_out[p][(OutFmtManBits+OutManUnnorm)*MaxInWidth+i*OutFmtExpBits+:OutFmtExpBits];
      assign out_o[p][i].mantissa = packed_out[p][i*(OutFmtManBits+OutManUnnorm)+:OutFmtManBits+OutManUnnorm];

      assign flags_o[p][i].is_denormal = in_is_denormal[p][i];
      assign flags_o[p][i].is_zero     = in_is_zero[p][i];
      assign flags_o[p][i].is_infinity = in_is_infinity[p][i];
      assign flags_o[p][i].is_nan      = in_is_nan[p][i];
    end
  end

endmodule