// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "auteur/timing.svh"

module auteur_ce
  import auteur_pkg::*;
#(
  parameter int unsigned    BaseInFmtWidth = 1,
  parameter int unsigned    ScaleFmtWidth = 1,
  parameter int unsigned    OutFmtWidth = 1,
  parameter int unsigned    NrIn = 1,
  parameter int unsigned    NrMaxJoins = 1,
  parameter int unsigned    MxGroupSize = NrIn,
  parameter int unsigned    InSuperFmtManBits = 1,
  parameter int unsigned    InSuperFmtExpBits = 1,
  parameter int unsigned    OutSuperFmtManBits = 1,
  parameter int unsigned    OutSuperFmtExpBits = 1,
  parameter int unsigned    MxScaleSuperFmtManBits = 1,
  parameter int unsigned    MxScaleSuperFmtExpBits = 1,
  parameter bit             InManUnnorm = 0,
  parameter int unsigned    AccRoundBits = 1,
  parameter int unsigned    YDelay = 0,
  parameter int unsigned    ScalesDelay = 0,
  parameter dotp_pipe_cfg_t PipeCfg = '{default: '0},
  parameter int unsigned    NrInFormats = 1,
  parameter fp_encoding_t   InFpEncoding [NrInFormats-1:0] = '{default: '0},
  parameter int unsigned    NrScaleFormats = 1,
  parameter fp_encoding_t   ScaleFpEncoding [NrScaleFormats-1:0] = '{default: '0},
  parameter int unsigned    NrOutFormats = 1,
  parameter fp_encoding_t   OutFpEncoding [NrOutFormats-1:0] = '{default: '0},

  localparam int unsigned MaxInWidth   = 1<<NrMaxJoins,
  localparam int unsigned NrMxGroups   = NrIn/MxGroupSize,
  localparam int unsigned NrInMaxWidth = NrIn>>NrMaxJoins,

  localparam type fmt_cfg_t = struct packed {
    logic [$clog2(NrInFormats)-1:0]    in_fmt;
    logic [$clog2(NrScaleFormats)-1:0] scale_fmt;
    logic [$clog2(NrOutFormats)-1:0]   out_fmt;
  }
) (
  input  logic                                                   clk_i,
  input  logic                                                   rst_ni,

  input  logic                                                   cfg_valid_i,
  input  fmt_cfg_t                                               cfg_i,

  input  logic                                                   in_valid_i,
  input  logic [NrInMaxWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] x_i,
  input  logic [NrInMaxWidth-1:0][BaseInFmtWidth*MaxInWidth-1:0] w_i,

  input  logic                                                   scale_valid_i,
  input  logic [NrMxGroups-1:0][ScaleFmtWidth-1:0]               x_scale_i,
  input  logic [NrMxGroups-1:0][ScaleFmtWidth-1:0]               w_scale_i,

  input  logic                                                   y_valid_i,
  input  logic [OutFmtWidth-1:0]                                 y_i,

  output logic                                                   z_valid_o,
  output logic [OutFmtWidth-1:0]                                 z_o
);
  localparam type in_super_fmt_t = struct packed {
    logic                                     sign;
    logic [InSuperFmtExpBits-1:0]             exponent;
    logic [InSuperFmtManBits+InManUnnorm-1:0] mantissa;
  };

  localparam type mx_scale_super_fmt_t = struct packed {
    logic                              sign;
    logic [MxScaleSuperFmtExpBits-1:0] exponent;
    logic [MxScaleSuperFmtManBits-1:0] mantissa;
  };

  localparam type out_super_fmt_t = struct packed {
    logic                          sign;
    logic [OutSuperFmtExpBits-1:0] exponent;
    logic [OutSuperFmtManBits-1:0] mantissa;
  };

  localparam type dotp_cfg_t = struct packed {
    logic [$clog2(NrMaxJoins):0] num_joins;
  };

  dotp_cfg_t dotp_cfg;

  in_super_fmt_t [NrInMaxWidth-1:0][MaxInWidth-1:0] x_dotp, w_dotp;
  mx_scale_super_fmt_t [NrMxGroups-1:0]             x_scale_dotp, w_scale_dotp;
  out_super_fmt_t                                   y_dotp, z_dotp;

  fp_flags_t [NrInMaxWidth-1:0][MaxInWidth-1:0] x_flags, w_flags;
  fp_flags_t [NrMxGroups-1:0]                   x_scale_flags, w_scale_flags;
  fp_flags_t                                    y_flags, z_flags;

  auteur_packer #(
    .NrIn (NrIn),
    .NrMaxJoins (NrMaxJoins),
    .BaseInFmtWidth (BaseInFmtWidth),
    .NrFormats (NrInFormats),
    .InFpEncoding (InFpEncoding),
    .OutFmtManBits (InSuperFmtManBits),
    .OutFmtExpBits (InSuperFmtExpBits),
    .OutManUnnorm (InManUnnorm)
  ) i_x_packer (
    .in_i (x_i),
    .in_fmt_i (cfg_i.in_fmt),
    .out_o (x_dotp),
    .flags_o (x_flags)
  );

  auteur_packer #(
    .NrIn (NrIn),
    .NrMaxJoins (NrMaxJoins),
    .BaseInFmtWidth (BaseInFmtWidth),
    .NrFormats (NrInFormats),
    .InFpEncoding (InFpEncoding),
    .OutFmtManBits (InSuperFmtManBits),
    .OutFmtExpBits (InSuperFmtExpBits),
    .OutManUnnorm (InManUnnorm)
  ) i_w_packer (
    .in_i (w_i),
    .in_fmt_i (cfg_i.in_fmt),
    .out_o (w_dotp),
    .flags_o (w_flags)
  );

  auteur_packer #(
    .NrIn (NrMxGroups),
    .NrMaxJoins (0),
    .BaseInFmtWidth (ScaleFmtWidth),
    .NrFormats (NrScaleFormats),
    .InFpEncoding (ScaleFpEncoding),
    .OutFmtManBits (MxScaleSuperFmtManBits),
    .OutFmtExpBits (MxScaleSuperFmtExpBits),
    .OutManUnnorm (0)
  ) i_x_scale_packer (
    .in_i (x_scale_i),
    .in_fmt_i (cfg_i.scale_fmt),
    .out_o (x_scale_dotp),
    .flags_o (x_scale_flags)
  );

  auteur_packer #(
    .NrIn (NrMxGroups),
    .NrMaxJoins (0),
    .BaseInFmtWidth (ScaleFmtWidth),
    .NrFormats (NrScaleFormats),
    .InFpEncoding (ScaleFpEncoding),
    .OutFmtManBits (MxScaleSuperFmtManBits),
    .OutFmtExpBits (MxScaleSuperFmtExpBits),
    .OutManUnnorm (0)
  ) i_w_scale_packer (
    .in_i (w_scale_i),
    .in_fmt_i (cfg_i.scale_fmt),
    .out_o (w_scale_dotp),
    .flags_o (w_scale_flags)
  );

  auteur_packer #(
    .NrIn (1),
    .NrMaxJoins (0),
    .BaseInFmtWidth (OutFmtWidth),
    .NrFormats (NrOutFormats),
    .InFpEncoding (OutFpEncoding),
    .OutFmtManBits (OutSuperFmtManBits),
    .OutFmtExpBits (OutSuperFmtExpBits),
    .OutManUnnorm (0)
  ) i_y_packer (
    .in_i (y_i),
    .in_fmt_i (cfg_i.out_fmt),
    .out_o (y_dotp),
    .flags_o (y_flags)
  );

  assign dotp_cfg = '{num_joins: InFpEncoding[cfg_i.in_fmt].required_joins};

  auteur_dotp #(
    .NrIn (NrIn),
    .NrMaxJoins (NrMaxJoins),
    .MxGroupSize (MxGroupSize),
    .InSuperFmtManBits (InSuperFmtManBits),
    .InSuperFmtExpBits (InSuperFmtExpBits),
    .OutSuperFmtManBits (OutSuperFmtManBits),
    .OutSuperFmtExpBits (OutSuperFmtExpBits),
    .MxScaleSuperFmtManBits (MxScaleSuperFmtManBits),
    .MxScaleSuperFmtExpBits (MxScaleSuperFmtExpBits),
    .InManUnnorm (InManUnnorm),
    .AccRoundBits (AccRoundBits),
    .YDelay (YDelay),
    .ScalesDelay (ScalesDelay),
    .PipeCfg (PipeCfg)
  ) i_dotp (
    .clk_i (clk_i),
    .rst_ni (rst_ni),
    .cfg_i (dotp_cfg),
    .in_valid_i (in_valid_i),
    .x_i (x_dotp),
    .w_i (w_dotp),
    .x_flags_i (x_flags),
    .w_flags_i (w_flags),
    .y_valid_i (y_valid_i),
    .y_i (y_dotp),
    .y_flags_i (y_flags),
    .scale_valid_i (scale_valid_i),
    .x_scale_i (x_scale_dotp),
    .w_scale_i (w_scale_dotp),
    .x_scale_flags_i (x_scale_flags),
    .w_scale_flags_i (w_scale_flags),
    .out_valid_o (z_valid_o),
    .z_o (z_dotp),
    .z_flags_o (z_flags)
  );

  auteur_unpacker #(
    .InFmtManBits (OutSuperFmtManBits),
    .InFmtExpBits (OutSuperFmtExpBits),
    .OutFmtWidth (OutFmtWidth),
    .NrFormats (NrOutFormats),
    .OutFpEncoding (OutFpEncoding)
  ) i_out_unpacker (
    .in_i (z_dotp),
    .flags_i (z_flags),
    .out_fmt_i (cfg_i.out_fmt),
    .out_o (z_o)
  );

endmodule