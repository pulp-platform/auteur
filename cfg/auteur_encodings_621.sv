// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

package auteur_encodings;
  enum int unsigned {
    M0  = 0,
    M1  = 1,
    M2  = 2,
    M3  = 3,
    M4  = 4,
    M5  = 5,
    M6  = 6,
    M7  = 7,
    M8  = 8,
    M9  = 9,
    M10 = 10,
    M11 = 11,
    E0  = 12,
    E1  = 13,
    E2  = 14,
    E3  = 15,
    E4  = 16,
    E5  = 17,
    E6  = 18,
    E7  = 19,
    E8  = 20,
    E9  = 21,
    E10 = 22,
    E11 = 23,
    S0  = 24,
    S1  = 25,
    S2  = 26,
    S3  = 27,
    S4  = 28,
    S5  = 29
  } element_super_fmt_indexes_e;

  enum int unsigned {
    SM0 = 0,
    SM1 = 1,
    SM2 = 2,
    SE0 = 3,
    SE1 = 4,
    SE2 = 5,
    SE3 = 6,
    SE4 = 7,
    SE5 = 8,
    SE6 = 9,
    SE7 = 10,
    SS0 = 11
  } scale_super_fmt_indexes_e;

  // NOTE: we need MLD* even if mantissae are normalized
  enum int unsigned {
    MLD0 = 24, // Unnormalized mantissa leading zero 0
    MLD1 = 25, // Unnormalized mantissa leading zero 1
    MLD2 = 26, // Unnormalized mantissa leading zero 2
    MLD3 = 27, // Unnormalized mantissa leading zero 3
    MLD4 = 28, // Unnormalized mantissa leading zero 4
    MLD5 = 29, // Unnormalized mantissa leading zero 5
    EXT0 = 30, // Exponent extension 0
    EXT1 = 31, // Exponent extension 1
    EXT2 = 32, // Exponent extension 2
    EXT3 = 33, // Exponent extension 3
    EXT4 = 34, // Exponent extension 4
    EXT5 = 35, // Exponent extension 5
    ZERO = 36  // Tie to zero
  } element_special_maps_e;

  enum int unsigned {
    SMLD0 = 8,
    SEXT0 = 9,
    SZERO = 10
  } scales_special_maps_e;

  localparam int unsigned ElementSuperFmtWidth = 30;
  localparam int unsigned ElementSuperFmtExpBits = 2;
  localparam int unsigned ElementSuperFmtManBits = 2;
  localparam bit          ElementManUnnorm = 0;

  localparam int unsigned NrJoinsPerStage [auteur_dtypes::NrJoinStages-1:0] = '{2,3};

  localparam logic [ElementSuperFmtWidth-1:0][auteur_dtypes::NrElementTypes-1:0][31:0] ElementEncodingMap = '{
  //FP16  BF16  FP8E5 FP8E4 FP4
  '{   2,    2,    2,    2,    2},
  '{ZERO, ZERO, ZERO, ZERO,   11},
  '{ZERO, ZERO, ZERO, ZERO,   22},
  '{ZERO, ZERO,   17,   17,   17},
  '{ZERO, ZERO, ZERO, ZERO,    5},
  '{ZERO, ZERO, ZERO, ZERO,   18},
  '{  21,   21,   21,   21,   21},
  '{EXT5, EXT5, EXT5, EXT5,   16},
  '{EXT5, EXT5,    0, EXT5,    0},
  '{EXT5, EXT5,    3,    3,    3},
  '{EXT5, EXT5,   19,   19,   19},
  '{EXT5,   23,   23,   23,   23},
  '{EXT5,   20,   20,   20,   20},
  '{EXT5,   13, EXT2, EXT2,   13},
  '{   1,    1,    1, EXT2,    1},
  '{   9,    9,    9,    9,    9},
  '{   4,    4,    4,    4,    4},
  '{  14,   14,   14,   14,   14},
  '{  15,   15,   15,   15,   15},
  '{   5,    5,    5,    5, ZERO},
  '{   8,    8, ZERO,    8,    8},
  '{   0,    0, ZERO, ZERO, ZERO},
  '{  12,   12, ZERO, ZERO,   12},
  '{   3,    3, ZERO, ZERO, ZERO},
  '{   6,    6,    6,    6,    6},
  '{  10, ZERO,   10,   10, ZERO},
  '{   7, ZERO, ZERO,    7,    7},
  '{  11, ZERO, ZERO, ZERO, ZERO},
  '{ZERO, ZERO, ZERO, ZERO,   10},
  '{ZERO, ZERO, ZERO, ZERO, ZERO}
};

  localparam int unsigned ScaleSuperFmtWidth = 12;
  localparam int unsigned ScaleSuperFmtExpBits = 8;
  localparam int unsigned ScaleSuperFmtManBits = 3;

  localparam logic [ScaleSuperFmtWidth-1:0][auteur_dtypes::NrScaleTypes-1:0][31:0] ScaleEncodingMap = '{
  //E4M3    E8M0
  '{6    , SZERO}, // SS0
  '{7    , 7    }, // SE7
  '{SEXT0, 6    }, // SE6
  '{SEXT0, 5    }, // SE5
  '{SEXT0, 4    }, // SE4
  '{SEXT0, 3    }, // SE3
  '{2    , 2    }, // SE2
  '{1    , 1    }, // SE1
  '{0    , 0    }, // SE0
  '{5    , SZERO}, // SM2
  '{4    , SZERO}, // SM1
  '{3    , SZERO}  // SM0
  };

  localparam int unsigned OutSuperFmtWidth = 32;
  localparam int unsigned OutSuperFmtExpBits = 8;
  localparam int unsigned OutSuperFmtManBits = 23;

  localparam logic [OutSuperFmtWidth-1:0][auteur_dtypes::NrOutTypes-1:0][31:0] OutEncodingMap = '{
    '{31},
    '{30},
    '{29},
    '{28},
    '{27},
    '{26},
    '{25},
    '{24},
    '{23},
    '{22},
    '{21},
    '{20},
    '{19},
    '{18},
    '{17},
    '{16},
    '{15},
    '{14},
    '{13},
    '{12},
    '{11},
    '{10},
    '{9 },
    '{8 },
    '{7 },
    '{6 },
    '{5 },
    '{4 },
    '{3 },
    '{2 },
    '{1 },
    '{0 }
  };

  localparam int unsigned XXX = 0;

  localparam logic [auteur_dtypes::NrElementTypes-1:0][23:0][31:0] ElementDecodingMap = '{
  '{  S5, E11,  E3,  E2,  E1,  E0, M11, M10,  M9,  M8,  M7,  M6,  M5,  M4,  M3,  M2, XXX, XXX, XXX, XXX, XXX, XXX, XXX, XXX}, // FP16_E5M10
  '{  S5, E11,  E6,  E5,  E4,  E3,  E2,  E1,  E0, M11, M10,  M9,  M8,  M7,  M6,  M5, XXX, XXX, XXX, XXX, XXX, XXX, XXX, XXX}, // FP16_E8M7
  '{  S5, E11,  E9,  E8,  E7,  E6, M11, M10,  S2,  E5,  E3,  E2,  E1,  E0,  M5,  M4, XXX, XXX, XXX, XXX, XXX, XXX, XXX, XXX}, // FP8_E5M2
  '{  S5, E11,  E8,  E7,  E6, M11, M10,  M9,  S2,  E5,  E2,  E1,  E0,  M5,  M4,  M3, XXX, XXX, XXX, XXX, XXX, XXX, XXX, XXX}, // FP8_E4M3
  '{  S5, E11, E10, M11,  S4,  E9,  E8,  M9,  S3,  E7,  E6,  M7,  S2,  E5,  E4,  M5,  S1,  E3,  E2,  M3,  S0,  E1,  E0,  M1}  // FP4_E2M1
};

  localparam logic [auteur_dtypes::NrScaleTypes-1:0][7:0][31:0] ScaleDecodingMap = '{
    '{SS0, SE7, SE2, SE1, SE0, SM2, SM1, SM0}, // FP8_E4M3
    '{SE7, SE6, SE5, SE4, SE3, SE2, SE1, SE0}  // FP8_E8M0
  };
endpackage