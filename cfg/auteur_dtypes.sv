// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51


package auteur_dtypes;
  import auteur_pkg::*;

  // Element data types
  localparam int unsigned NrElementTypes = 5;
  localparam int unsigned NrJoinStages = 2;
  localparam int unsigned BaseElementWidth = 4;

  localparam fp_encoding_t FP4_E2M1   = '{is_signed: 1, mantissa_bits:  1, exponent_bits: 2, has_infinity: 0, has_nan: 0, required_joins: 0};
  localparam fp_encoding_t FP8_E4M3   = '{is_signed: 1, mantissa_bits:  3, exponent_bits: 4, has_infinity: 0, has_nan: 1, required_joins: 1};
  localparam fp_encoding_t FP8_E5M2   = '{is_signed: 1, mantissa_bits:  2, exponent_bits: 5, has_infinity: 1, has_nan: 1, required_joins: 1};
  localparam fp_encoding_t FP16_E5M10 = '{is_signed: 1, mantissa_bits: 10, exponent_bits: 5, has_infinity: 1, has_nan: 1, required_joins: 2};
  localparam fp_encoding_t FP16_E8M7  = '{is_signed: 1, mantissa_bits:  7, exponent_bits: 8, has_infinity: 1, has_nan: 1, required_joins: 2};

  localparam fp_encoding_t ElementTypes [NrElementTypes-1:0] = '{FP16_E8M7, FP16_E5M10, FP8_E5M2, FP8_E4M3, FP4_E2M1};

  // Scale data types
  localparam int unsigned NrScaleTypes = 2;
  localparam int unsigned ScaleWidth = 8;

  localparam fp_encoding_t SFP8_E8M0 = '{is_signed: 0, mantissa_bits: 0, exponent_bits: 8, has_infinity: 0, has_nan: 1, required_joins: 0};
  localparam fp_encoding_t SFP8_E4M3 = '{is_signed: 1, mantissa_bits: 3, exponent_bits: 4, has_infinity: 0, has_nan: 1, required_joins: 0};

  localparam fp_encoding_t ScaleTypes [NrScaleTypes-1:0] = '{SFP8_E4M3, SFP8_E8M0};

  localparam int unsigned BlockSize = 16;

  // Output data types
  localparam int unsigned NrOutTypes = 1;
  localparam int unsigned OutWidth = 32;

  localparam fp_encoding_t FP32_E8M23 = '{is_signed: 1, mantissa_bits: 23, exponent_bits: 8, has_infinity: 1, has_nan: 1, required_joins: 0};

  localparam fp_encoding_t OutTypes [NrOutTypes-1:0] = '{FP32_E8M23};
endpackage
