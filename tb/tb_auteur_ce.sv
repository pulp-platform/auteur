`timescale 1ns/1ps

import auteur_pkg::*;

module tb_auteur_dotp;
  parameter int unsigned    BaseInFmtWidth = auteur_dtypes::BaseElementWidth;
  parameter int unsigned    ScaleFmtWidth = auteur_dtypes::ScaleWidth;
  parameter int unsigned    OutFmtWidth = auteur_dtypes::OutWidth;
  parameter int unsigned    NrIn = `WIDTH;
  parameter int unsigned    NrJoinStages = auteur_dtypes::NrJoinStages;
  parameter int unsigned    NrJoinsPerStage [NrJoinStages-1:0] = auteur_encodings::NrJoinsPerStage;
  parameter int unsigned    BlockSize = auteur_dtypes::BlockSize;
  parameter int unsigned    InSuperFmtManBits = auteur_encodings::ElementSuperFmtManBits;
  parameter int unsigned    InSuperFmtExpBits = auteur_encodings::ElementSuperFmtExpBits;
  parameter int unsigned    OutSuperFmtManBits = auteur_encodings::OutSuperFmtManBits;
  parameter int unsigned    OutSuperFmtExpBits = auteur_encodings::OutSuperFmtExpBits;
  parameter int unsigned    ScaleSuperFmtManBits = auteur_encodings::ScaleSuperFmtManBits;
  parameter int unsigned    ScaleSuperFmtExpBits = auteur_encodings::ScaleSuperFmtExpBits;
  parameter bit             InManUnnorm = auteur_encodings::ElementManUnnorm;
  parameter int unsigned    AccRoundBits = 1;
  parameter dotp_pipe_cfg_t PipeCfg = '{default: '0};
  parameter int unsigned    NrInFormats = auteur_dtypes::NrElementTypes;
  parameter fp_encoding_t   InFpEncoding [NrInFormats-1:0] = auteur_dtypes::ElementTypes;
  parameter int unsigned    NrScaleFormats = auteur_dtypes::NrScaleTypes;
  parameter fp_encoding_t   ScaleFpEncoding [NrScaleFormats-1:0] = auteur_dtypes::ScaleTypes;
  parameter int unsigned    NrOutFormats = auteur_dtypes::NrOutTypes;
  parameter fp_encoding_t   OutFpEncoding [NrOutFormats-1:0] = auteur_dtypes::OutTypes;

  localparam int unsigned MaxInWidth     = get_max_width(NrJoinsPerStage, NrJoinStages);
  localparam int unsigned InPackWidth    = MaxInWidth * (1 + InSuperFmtExpBits + InSuperFmtManBits + InManUnnorm);
  localparam int unsigned ScalePackWidth = (1 + ScaleSuperFmtExpBits + ScaleSuperFmtManBits);
  localparam int unsigned OutPackWidth   = (1 + OutSuperFmtExpBits + OutSuperFmtManBits);

  parameter logic [InPackWidth-1:0][NrInFormats-1:0][31:0]       InFormatMapTable    = auteur_encodings::ElementEncodingMap;
  parameter logic [ScalePackWidth-1:0][NrScaleFormats-1:0][31:0] ScaleFormatMapTable = auteur_encodings::ScaleEncodingMap;
  parameter logic [OutPackWidth-1:0][NrOutFormats-1:0][31:0]     OutFormatMapTable   = auteur_encodings::OutEncodingMap;

  localparam int unsigned NrBlocks     = NrIn/BlockSize;
  localparam int unsigned NrInMaxWidth = NrIn/MaxInWidth;

  localparam type fmt_cfg_t = struct packed {
    logic [cf_math_pkg::idx_width(NrInFormats)-1:0]    in_fmt;
    logic [cf_math_pkg::idx_width(NrScaleFormats)-1:0] scale_fmt;
    logic [cf_math_pkg::idx_width(NrOutFormats)-1:0]   out_fmt;
  };


  function automatic logic [NrInMaxWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] element_permute(logic [NrInMaxWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] x, int unsigned f);
    logic [NrInMaxWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] res = '0;

    for (int unsigned i = 0; i < NrInMaxWidth; i++) begin
      for (int unsigned b = 0; b < BaseInFmtWidth*MaxInWidth; b++) begin
        res[i][auteur_encodings::ElementEncodingMap[auteur_encodings::ElementDecodingMap[f][b]][f]] = x[i][b];
      end
    end

    return res;
  endfunction

  function automatic logic [NrBlocks-1:0][7:0] scale_permute(logic [NrBlocks-1:0][7:0] x, int unsigned f);
    logic [NrBlocks-1:0][7:0] res = '0;

    for (int unsigned i = 0; i < NrBlocks; i++) begin
      for (int unsigned b = 0; b < ScaleFmtWidth; b++) begin
        res[i][auteur_encodings::ScaleEncodingMap[auteur_encodings::ScaleDecodingMap[f][b]][f]] = x[i][b];
      end
    end

    return res;
  endfunction


  logic                                                   clk_i;
  logic                                                   rst_ni;
  fmt_cfg_t                                               cfg_i;
  logic                                                   in_valid_i;
  logic [NrInMaxWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] x_i, x;
  logic [NrInMaxWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] w_i, w;
  logic                                                   scale_valid_i;
  logic [NrBlocks-1:0][ScaleFmtWidth-1:0]                 x_scale_i, x_scale;
  logic [NrBlocks-1:0][ScaleFmtWidth-1:0]                 w_scale_i, w_scale;
  logic                                                   y_valid_i;
  logic [OutFmtWidth-1:0]                                 y_i;
  logic                                                   z_valid_o;
  logic [OutFmtWidth-1:0]                                 z_o;


  auteur_ce #(
    .BaseInFmtWidth (BaseInFmtWidth),
    .ScaleFmtWidth (ScaleFmtWidth),
    .OutFmtWidth (OutFmtWidth),
    .NrIn (NrIn),
    .NrJoinStages (NrJoinStages),
    .NrJoinsPerStage (NrJoinsPerStage),
    .BlockSize (BlockSize),
    .InSuperFmtManBits (InSuperFmtManBits),
    .InSuperFmtExpBits (InSuperFmtExpBits),
    .OutSuperFmtManBits (OutSuperFmtManBits),
    .OutSuperFmtExpBits (OutSuperFmtExpBits),
    .ScaleSuperFmtManBits (ScaleSuperFmtManBits),
    .ScaleSuperFmtExpBits (ScaleSuperFmtExpBits),
    .InManUnnorm (InManUnnorm),
    .AccRoundBits (AccRoundBits),
    .YDelay (0),
    .ScalesDelay (0),
    .PipeCfg (PipeCfg),
    .NrInFormats (NrInFormats),
    .InFpEncoding (InFpEncoding),
    .NrScaleFormats (NrScaleFormats),
    .ScaleFpEncoding (ScaleFpEncoding),
    .NrOutFormats (NrOutFormats),
    .OutFpEncoding (OutFpEncoding),
    .InFormatMapTable (InFormatMapTable),
    .ScaleFormatMapTable (ScaleFormatMapTable),
    .OutFormatMapTable (OutFormatMapTable)
  ) i_ce (.*);


  initial begin
    clk_i = 0;
    forever #5 clk_i = ~clk_i;
  end

  initial begin
    int stimuli_file;

    rst_ni = '1;
    cfg_i = '0;
    in_valid_i = '0;
    x = '0;    x_i = '0;
    w = '0;    w_i = '0;
    scale_valid_i = '0;
    x_scale = '0;    x_scale_i = '0;
    w_scale = '0;    w_scale_i = '0;
    y_valid_i = '0;
    y_i = '0;

    @(negedge clk_i);

    rst_ni = '0;

    @(negedge clk_i);

    rst_ni = '1;

    stimuli_file = $fopen("./dotp_stimuli.txt", "r");

    if (stimuli_file == 0) begin
      $display("Could not open stimuli file");
      $finish();
    end

    in_valid_i = '1;
    y_valid_i = '1;
    scale_valid_i = '1;

    while (!$feof(stimuli_file)) begin
      $fscanf(stimuli_file, "%h %h %h %h %h %h", x, w, x_scale, w_scale, y_i, cfg_i);

      x_i = element_permute(x, cfg_i.in_fmt);
      w_i = element_permute(w, cfg_i.in_fmt);
      x_scale_i = scale_permute(x_scale, cfg_i.scale_fmt);
      w_scale_i = scale_permute(w_scale, cfg_i.scale_fmt);
      @(negedge clk_i);
    end

    in_valid_i = '0;
    y_valid_i = '0;
    scale_valid_i = '0;

    $fclose(stimuli_file);
  end

  initial begin
    int results_file;
    int errors;
    int index;
    int res;

    errors = 0;
    index = 0;

    results_file = $fopen("./result.txt", "r");
    if (results_file == 0) begin
          $display("Could not open results file");
          $finish();
    end

    forever begin
      @(negedge clk_i)
      if (z_valid_o === 1'b1) begin
        $fscanf(results_file, "%h\n", res);

        if ((z_o !== res) || $isunknown(z_o)) begin
          errors += 1;
          $display("MISMATCH @ %d: expexted\t%h; got\t%h", index, res, z_o);
        end

        if ($feof(results_file)) begin
          $fclose(results_file);
          $display("SUMMARY: checked %0d, errors %0d", index, errors);
          $finish();
        end

        index += 1;
      end
    end
  end

endmodule