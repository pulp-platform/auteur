// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_packer
  import auteur_pkg::*;
#(
  parameter int unsigned   NrIn = 1,
  parameter int unsigned   NrMaxJoins = 1,
  parameter int unsigned   BaseInFmtWidth = 1,
  parameter int unsigned   NrFormats = 1,
  parameter fp_encoding_t  InFpEncoding [NrFormats-1:0] = '{default:'0},
  parameter int unsigned   OutFmtManBits = 1,
  parameter int unsigned   OutFmtExpBits = 1,
  parameter bit            OutManUnnorm = 0,

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
  logic [NrInMaxWidth-1:0][MaxInWidth-1:0] in_is_denormal,
                                           in_is_zero,
                                           in_is_infinity,
                                           in_is_nan;

  for (genvar i = 0; i < NrInMaxWidth; i++) begin : gen_packers
    let fmt_joins      = InFpEncoding[in_fmt_i].required_joins;
    let fmt_width      = 1<<fmt_joins;
    let fmt_mant_width = InFpEncoding[in_fmt_i].mantissa_bits;
    let fmt_exp_width  = InFpEncoding[in_fmt_i].exponent_bits;
    let fmt_is_signed  = InFpEncoding[in_fmt_i].is_signed;
    let fmt_tot_width  = fmt_mant_width + fmt_exp_width + fmt_is_signed;

    let fmt_has_infinity  = InFpEncoding[in_fmt_i].has_infinity;
    let fmt_has_nan       = InFpEncoding[in_fmt_i].has_nan;
    let fmt_has_denormals = InFpEncoding[in_fmt_i].has_denormals;

    logic [MaxInWidth-1:0]                                 out_signs;
    logic [MaxInWidth-1:0][OutFmtExpBits-1:0]              out_exponents;
    logic [MaxInWidth-1:0][OutFmtManBits+OutManUnnorm-1:0] out_mantissae;

    logic [MaxInWidth-1:0] in_mant_is_zero,
                           in_mant_is_one,
                           in_exp_is_zero,
                           in_exp_is_one;

    for (genvar j = 0; j < MaxInWidth; j++) begin : gen_group_pack
      let element = j >> fmt_joins;

      always_comb begin : check_fmt
        in_mant_is_zero[j] = 1'b1;
        in_mant_is_one[j]  = 1'b1;
        in_exp_is_zero[j]  = 1'b1;
        in_exp_is_one[j]   = 1'b1;

        if (in_fmt_i < NrFormats) begin
          for (int unsigned b = 0; b < BaseInFmtWidth; b++) begin
            let position = b + (j % fmt_width)*BaseInFmtWidth;

            // Is the bit an exponent bit?
            if (position >= fmt_mant_width && position < fmt_tot_width - fmt_is_signed) begin
              in_exp_is_zero[j] &= ~in_i[i][j*BaseInFmtWidth + b];
              in_exp_is_one[j]  &= in_i[i][j*BaseInFmtWidth + b];
            end

            // Is the bit a mantissa bit?
            if (position < fmt_mant_width) begin
              in_mant_is_zero[j] &= ~in_i[i][j*BaseInFmtWidth + b];
              in_mant_is_one[j]  &= in_i[i][j*BaseInFmtWidth + b];
            end
          end
        end
      end

      always_comb begin : classify_inputs
        in_is_denormal[i][j] = 1'b1;
        in_is_zero[i][j]     = 1'b1;
        in_is_infinity[i][j] = 1'b1;
        in_is_nan[i][j]      = 1'b1;

        if (in_fmt_i < NrFormats) begin
          in_is_infinity[i][j] = fmt_has_infinity;
          in_is_nan[i][j]      = fmt_has_nan;

          for (int unsigned p = 0; p < MaxInWidth; p++) begin
            if (p >> fmt_joins == element) begin
              // To determine whether an input is denormal or not, we check if the exponent bits of every partition are zero
              in_is_denormal[i][j] &= in_exp_is_zero[p];

              // For zeros is the same, except we have to also check the mantissa
              in_is_zero[i][j] &= in_exp_is_zero[p] & in_mant_is_zero[p];

              // If the selected format has infinities we check whether the exponents of the corresponding partitions are all one
              if (fmt_has_infinity) begin
                in_is_infinity[i][j] &= in_exp_is_one[p];

                // Additionally, if we can have NaNs, we also check that the mantissa is zero
                if (fmt_has_nan) begin
                  in_is_infinity[i][j] &= in_mant_is_zero[p];
                end
              end

              if (fmt_has_nan) begin
                in_is_nan[i][j] &= in_exp_is_one[p];

                // In a format without infinity, the only valid NaN is the one with a mantissa of only ones
                if (~fmt_has_infinity) begin
                  in_is_nan[i][j] &= in_mant_is_one[p];
                end
              end
            end
          end

          // Finally, if we have infinities and NaNs, we have to make sure a number with a '1 exponent is not an infinity
          if (fmt_has_nan && fmt_has_infinity) begin
            in_is_nan[i][j] &= ~in_is_infinity[i][j];
          end
        end
      end

      assign flags_o[i][j].is_denormal = in_is_denormal[i][j];
      assign flags_o[i][j].is_zero     = in_is_zero[i][j];
      assign flags_o[i][j].is_infinity = in_is_infinity[i][j];
      assign flags_o[i][j].is_nan      = in_is_nan[i][j];

      assign out_signs[j] = fmt_is_signed ? in_i[i][(j+1)*BaseInFmtWidth-1] : 1'b0;

      for (genvar e = 0; e < OutFmtExpBits; e++) begin : assign_exponent_bits
        let super_fmt_exp_width = fmt_width*OutFmtExpBits;
        let position            = (j % fmt_width)*(OutFmtExpBits) + e;

        always_comb begin : assign_bit
          out_exponents[j][e] = 1'b0;

          if (in_fmt_i < NrFormats) begin
            if (position < fmt_exp_width-1) begin
              // If the input is denormal we increase the exponent by one to compensate for the mantissa shift
              if (in_is_denormal[i][j] && position == 0) begin
                out_exponents[j][e] = 1'b1;
              end else begin
                out_exponents[j][e] = in_i[i][fmt_mant_width+(element*fmt_tot_width)+position];
              end
            end else if (position == super_fmt_exp_width-1) begin
              // The final bit corresponds to the final bit of the original exponent
              out_exponents[j][e] = in_i[i][fmt_mant_width+(element*fmt_tot_width)+fmt_exp_width-1];
            end else begin
              // We set every other bit to the inverted value of the last exponent bit in the original format
              out_exponents[j][e] = ~in_i[i][fmt_mant_width+(element*fmt_tot_width)+fmt_exp_width-1];
            end
          end
        end
      end

      for (genvar m = 0; m < OutFmtManBits+OutManUnnorm; m++) begin : assign_mantissa_bits
        let distance = (fmt_width*(OutFmtManBits+OutManUnnorm)) - ((j % fmt_width)*(OutFmtManBits+OutManUnnorm) + m) - 1;

        always_comb begin : assign_bit
          out_mantissae[j][m] = 1'b0;

          if (in_fmt_i < NrFormats) begin
            if (distance >= fmt_mant_width + OutManUnnorm) begin
              //  If no format's mantissa can reach this bit, we tie it to zero
              out_mantissae[j][m] = 1'b0;
            end else if (distance == 0 && OutManUnnorm) begin
              // If this is the final bit and the mantissa has to be unnormalized, we tie it to one unless the number is denormal
              out_mantissae[j][m] = ~in_is_denormal[i][j];
            end else begin
              // Bit selection logic
              if (OutManUnnorm) begin
                out_mantissae[j][m] = in_i[i][fmt_mant_width+(element*fmt_tot_width)-distance];
              end else begin
                out_mantissae[j][m] = in_i[i][fmt_mant_width+(element*fmt_tot_width)-distance-1];
              end
            end
          end
        end
      end

      assign out_o[i][j].sign     = out_signs[j];
      assign out_o[i][j].exponent = out_exponents[j];
      assign out_o[i][j].mantissa = out_mantissae[j];
    end
  end
endmodule