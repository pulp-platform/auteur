// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_unpacker
  import auteur_pkg::*;
#(
  parameter int unsigned   InFmtManBits = 1,
  parameter int unsigned   InFmtExpBits = 1,
  parameter int unsigned   OutFmtWidth = 1,
  parameter int unsigned   NrFormats = 1,
  parameter fp_encoding_t  OutFpEncoding [NrFormats-1:0] = '{default:'0},

  localparam int unsigned SelWidth = NrFormats > 1 ? $clog2(NrFormats) : 1,

  localparam type in_fmt_t = struct packed {
    logic                    sign;
    logic [InFmtExpBits-1:0] exponent;
    logic [InFmtManBits-1:0] mantissa;
  }
) (
  input  in_fmt_t                in_i,
  input  fp_flags_t              flags_i,
  input  logic [SelWidth-1:0]    out_fmt_i,
  output logic [OutFmtWidth-1:0] out_o
);
  int unsigned fmt_mant_width, fmt_exp_width, fmt_tot_width;
  bit          fmt_is_signed;

  bit fmt_has_infinity, fmt_has_nan, fmt_has_denormals;

  assign fmt_mant_width = OutFpEncoding[out_fmt_i].mantissa_bits;
  assign fmt_exp_width  = OutFpEncoding[out_fmt_i].exponent_bits;
  assign fmt_is_signed  = OutFpEncoding[out_fmt_i].is_signed;
  assign fmt_tot_width  = fmt_mant_width + fmt_exp_width + fmt_is_signed;

  assign fmt_has_infinity  = OutFpEncoding[out_fmt_i].has_infinity;
  assign fmt_has_nan       = OutFpEncoding[out_fmt_i].has_nan;
  assign fmt_has_denormals = OutFpEncoding[out_fmt_i].has_denormals;

  logic is_nan, is_infinity, is_zero;

  logic [InFmtExpBits-1:0] out_exp;
  logic                    invalid_exp;

  always_comb begin : check_exponent
    out_exp     = '0;
    invalid_exp = 1'b0;

    if (out_fmt_i < NrFormats) begin
      for (int unsigned e = 0; e < InFmtExpBits; e++) begin
        if (e < fmt_exp_width-1) begin
          out_exp[e] = in_i.exponent[e];
        end else if (e == InFmtExpBits-1) begin
          out_exp[fmt_exp_width-1] = in_i.exponent[e];
        end else begin
          invalid_exp |= in_i.exponent[e] != ~in_i.exponent[InFmtExpBits-1];
        end
      end
    end
  end

  logic [InFmtManBits-1:0] out_mant;

  always_comb begin : check_mantissa
    out_mant = '0;

    if (out_fmt_i < NrFormats) begin
      for (int unsigned m = 0; m < InFmtManBits; m++) begin
        // TODO: implement more rounding modes other than truncation
        if (m >= InFmtManBits-fmt_mant_width) begin
          out_mant[m-(InFmtManBits-fmt_mant_width)] = in_i.mantissa[m];
        end
      end
    end
  end

  logic out_sign;
  logic invalid_sign;

  always_comb begin : check_sign
    out_sign     = in_i.sign;
    invalid_sign = 1'b0;

    if (out_fmt_i < NrFormats) begin
      if (~fmt_is_signed) begin
        if (in_i.sign == 1'b1) begin
          invalid_sign = 1'b1;
        end
      end
    end
  end

  assign is_nan      = flags_i.is_nan || invalid_sign;
  assign is_infinity = flags_i.is_infinity || (invalid_exp && in_i.exponent[InFmtExpBits-1]);
  // TODO: Handle denormals, if supported
  assign is_zero     = flags_i.is_zero || (invalid_exp && ~in_i.exponent[InFmtExpBits-1]);

  always_comb begin : unpack_input
    out_o = '0;

    if (out_fmt_i < NrFormats) begin
      for (int b = OutFmtWidth-1; b >= 0; b--) begin
        if (b < fmt_tot_width-1) begin
          if (is_nan) begin
            if (fmt_has_nan) begin
              // If the format has NaNs we set all bits to 1
              out_o[b] = 1'b1;
            end else begin
              // If the format does not support NaNs we just output a zero
              out_o[b] = 1'b0;
            end
          end else if (is_infinity) begin
            if (~fmt_has_infinity) begin
              // If the format has no representations for infinities, we output a NaN (if supported) or the maximum possible number
              out_o[b] = 1'b1;
            end else begin
              if (b >= fmt_mant_width) begin
                out_o[b] = 1'b1;
              end else begin
                out_o[b] = 1'b0;
              end
            end
          end else if (is_zero) begin
            out_o[b] = 1'b0;
          end else begin
            if (b >= fmt_mant_width) begin
              out_o[b] = out_exp[b-fmt_mant_width];
            end else begin
              out_o[b] = out_mant[b];
            end
          end
        end

        // Output sign
        if (b == fmt_tot_width-1) begin
          out_o[b] = out_sign;
        end
      end
    end
  end

endmodule