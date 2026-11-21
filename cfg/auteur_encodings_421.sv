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
    S3  = 27
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

  enum int unsigned {
    MLD0 = 16, // Unnormalized mantissa leading zero 0
    MLD1 = 17, // Unnormalized mantissa leading zero 1
    MLD2 = 18, // Unnormalized mantissa leading zero 2
    MLD3 = 19, // Unnormalized mantissa leading zero 3
    EXT0 = 20, // Exponent extension 0
    EXT1 = 21, // Exponent extension 1
    EXT2 = 22, // Exponent extension 2
    EXT3 = 23, // Exponent extension 3
    ZERO = 24  // Tie to zero
  } element_special_maps_e;

  enum int unsigned {
    SMLD0 = 8,
    SEXT0 = 9,
    SZERO = 10
  } scales_special_maps_e;

  localparam int unsigned ElementSuperFmtWidth = 28;
  localparam int unsigned ElementSuperFmtExpBits = 3;
  localparam int unsigned ElementSuperFmtManBits = 2;
  localparam bit          ElementManUnnorm = 1;

  localparam int unsigned NrJoinsPerStage [auteur_dtypes::NrJoinStages-1:0] = '{2,2};

  localparam logic [ElementSuperFmtWidth-1:0][auteur_dtypes::NrElementTypes-1:0][31:0] ElementEncodingMap = '{
  //FP16  BF16  FP8E5 FP8E4 FP4
  '{3   , 3   , 3   , 3   , 3   }, // S3
  '{ZERO, ZERO, ZERO, ZERO, 10  }, // S2
  '{ZERO, ZERO, 8   , 8   , 8   }, // S1
  '{ZERO, ZERO, ZERO, ZERO, 11  }, // S0
  '{9   , 9   , 9   , 9   , 9   }, // E11
  '{EXT3, EXT3, EXT3, EXT3, EXT3}, // E10
  '{EXT3, EXT3, 1   , EXT3, 1   }, // E9
  '{EXT3, EXT3, 5   , 5   , 5   }, // E8
  '{EXT3, EXT3, 6   , 6   , EXT2}, // E7
  '{EXT3, 12  , 12  , 0   , 12  }, // E6
  '{EXT3, 4   , 4   , 4   , 4   }, // E5
  '{EXT3, 6   , EXT1, EXT1, EXT1}, // E4
  '{0   , 0   , 0   , EXT1, 0   }, // E3
  '{2   , 2   , 2   , 2   , 2   }, // E2
  '{11  , 11  , 11  , 11  , EXT0}, // E1
  '{14  , 14  , 14  , 14  , 14  }, // E0
  '{MLD3, MLD3, MLD3, MLD3, MLD3}, // M11
  '{7   , 7   , 7   , 7   , 7   }, // M10
  '{10  , 10  , 10  , 10  , ZERO}, // M9
  '{1   , 1   , ZERO, 1   , MLD2}, // M8
  '{4   , 13  , ZERO, ZERO, 13  }, // M7
  '{8   , 8   , ZERO, ZERO, ZERO}, // M6
  '{5   , 5   , MLD1, MLD1, MLD1}, // M5
  '{15  , 15  , 15  , 15  , 15  }, // M4
  '{13  , ZERO, 13  , 13  , ZERO}, // M3
  '{12  , ZERO, ZERO, 12  , MLD0}, // M2
  '{6   , ZERO, ZERO, ZERO, 6   }, // M1
  '{ZERO, ZERO, ZERO, ZERO, ZERO}  // M0
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

  localparam logic [auteur_dtypes::NrElementTypes-1:0][15:0][31:0] ElementDecodingMap = '{
    '{S3  , E11 , E3  , E2  , E1  , E0  , M10 , M9  , M8  , M7  , M6  , M5  , M4  , M3  , M2  , M1 }, // FP16_E5M10
    '{S3  , E11 , E6  , E5  , E4  , E3  , E2  , E1  , E0  , M10 , M9  , M8  , M7  , M6  , M5  , M4 }, // FP16_E8M7
    '{S3  , E11 , E9  , E8  , E7  , E6  , M10 , M9  , S1  , E5  , E3  , E2  , E1  , E0  , M4  , M3 }, // FP8_E5M2
    '{S3  , E11 , E8  , E7  , E6  , M10 , M9  , M8  , S1  , E5  , E2  , E1  , E0  , M4  , M3  , M2 }, // FP8_E4M3
    '{S3  , E11 , E9  , M10 , S2  , E8  , E6  , M7  , S1  , E5  , E3  , M4  , S0  , E2  , E0  , M1 }  // FP4_E2M1
  };

  localparam logic [auteur_dtypes::NrScaleTypes-1:0][7:0][31:0] ScaleDecodingMap = '{
    '{SS0, SE7, SE2, SE1, SE0, SM2, SM1, SM0}, // FP8_E4M3
    '{SE7, SE6, SE5, SE4, SE3, SE2, SE1, SE0}  // FP8_E8M0
  };
endpackage