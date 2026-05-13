// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_datapath
  import auteur_pkg::*;
#(
  parameter int unsigned    NrGroupsX = 1,
  parameter int unsigned    NrGroupsW = 1,
  parameter int unsigned    CtrlTreeDepth = 1,
  parameter int unsigned    CtrlTreeWidth = 1,
  parameter int unsigned    CtrlGroupX = 1,
  parameter int unsigned    CtrlGroupW = 1,

  parameter int unsigned    ReadDataWidth = 1,
  parameter int unsigned    WriteDataWidth = 1,
  parameter int unsigned    GroupSizeX = 1,
  parameter int unsigned    GroupSizeW = 1,
  parameter int unsigned    IntercoWidth = 1,

  parameter int unsigned    BaseInFmtWidth = 1,
  parameter int unsigned    ScaleFmtWidth = 1,
  parameter int unsigned    OutFmtWidth = 1,
  parameter int unsigned    NrIn = 1,
  parameter int unsigned    NrMaxJoins = 0,
  parameter int unsigned    MxGroupSize = NrIn,
  parameter int unsigned    InSuperFmtManBits = 1,
  parameter int unsigned    InSuperFmtExpBits = 1,
  parameter int unsigned    OutSuperFmtManBits = 1,
  parameter int unsigned    OutSuperFmtExpBits = 1,
  parameter int unsigned    MxScaleSuperFmtManBits = 1,
  parameter int unsigned    MxScaleSuperFmtExpBits = 1,
  parameter bit             InManUnnorm = 0,
  parameter int unsigned    AccRoundBits = 1,
  parameter dotp_pipe_cfg_t PipeCfg = '{default: '0},
  parameter int unsigned    NrInFormats = 1,
  parameter fp_encoding_t   InFpEncoding [NrInFormats-1:0] = '{default: '0},
  parameter int unsigned    NrScaleFormats = 1,
  parameter fp_encoding_t   ScaleFpEncoding [NrScaleFormats-1:0] = '{default: '0},
  parameter int unsigned    NrOutFormats = 1,
  parameter fp_encoding_t   OutFpEncoding [NrOutFormats-1:0] = '{default: '0},

  parameter int unsigned    OutputBufferDepth = 1,
  parameter int unsigned    OutputBufferBanks = 2,
  parameter bit             OutputBufferSplitReadWrite = 0,

  parameter int unsigned    InputBufferTotDepth = 1,
  parameter int unsigned    InputBufferBanks = 2,
  parameter bit             InputBufferLatches = 0,

  localparam int unsigned InputBufferDepth = InputBufferTotDepth / NrGroupsX,  // FIXME: Support NrGroupsX =/= NrGroupsW

  // FIXME: All the parameters in this section are only needed to calculate the final address widths
  localparam int unsigned NrMxGroups = NrIn / MxGroupSize,

  localparam int unsigned NrOutputBuffersW = GroupSizeW / IntercoWidth,

  localparam int unsigned InputBufferWideWordWidth = NrIn * BaseInFmtWidth + NrMxGroups * ScaleFmtWidth,
  localparam int unsigned InputBufferNarrowWordWidth = WriteDataWidth > InputBufferWideWordWidth ? InputBufferWideWordWidth : WriteDataWidth,

  localparam int unsigned OutputBufferDataWidth = OutFmtWidth*IntercoWidth,

  localparam int unsigned NrInputBufferReqs = WriteDataWidth / InputBufferNarrowWordWidth,

  localparam int unsigned NrOutputBufferWriteReqs = WriteDataWidth / OutputBufferDataWidth,
  localparam int unsigned NrOutputBufferReadReqs = ReadDataWidth / OutputBufferDataWidth,

  localparam int unsigned NrInputBufferBundles = (GroupSizeX + GroupSizeW) / NrInputBufferReqs,
  localparam int unsigned NrOutputBufferWriteBundles = GroupSizeX * NrOutputBuffersW / NrOutputBufferWriteReqs,
  localparam int unsigned NrOutputBufferReadBundles = GroupSizeX * NrOutputBuffersW / NrOutputBufferReadReqs,

  localparam int unsigned OutputBufferAddrWidth = OutputBufferDepth > 1 ? $clog2(OutputBufferDepth) : 1,
  localparam int unsigned InputBufferWideAddrWidth = InputBufferDepth > 1 ? $clog2(InputBufferDepth) : 1,

  localparam int unsigned InputBufferNarrowAddrWidth = InputBufferWideWordWidth/InputBufferNarrowWordWidth * InputBufferDepth > 1 ? $clog2(InputBufferWideWordWidth/InputBufferNarrowWordWidth * InputBufferDepth) : 1,

  localparam int unsigned InputBundleAddrWidth = $clog2(NrInputBufferBundles),
  localparam int unsigned OutputBundleWriteAddrWidth = $clog2(NrOutputBufferWriteBundles),
  localparam int unsigned OutputBundleReadAddrWidth = $clog2(NrOutputBufferReadBundles),

  localparam int unsigned GroupIdWidth = NrGroupsX > 1 ? $clog2(NrGroupsX) : 1,

  // GroupIdWidth + Buffer selection bit + Longest Bundle selection & Buffer address pair
  localparam int unsigned WriteAddrWidth = GroupIdWidth + 1 + (InputBundleAddrWidth + InputBufferNarrowAddrWidth > OutputBundleWriteAddrWidth + OutputBufferAddrWidth ? InputBundleAddrWidth + InputBufferNarrowAddrWidth : OutputBundleWriteAddrWidth + OutputBufferAddrWidth),
  localparam int unsigned ReadAddrWidth = GroupIdWidth + 1 + OutputBundleReadAddrWidth + OutputBufferAddrWidth,

  localparam int unsigned InFmtSelWidth = NrInFormats > 1 ? $clog2(NrInFormats) : 1,
  localparam int unsigned ScaleFmtSelWidth = NrScaleFormats > 1 ? $clog2(NrScaleFormats) : 1,
  localparam int unsigned OutFmtSelWidth = NrOutFormats > 1 ? $clog2(NrOutFormats) : 1,

  localparam int unsigned InIterWidth = InputBufferTotDepth > 1 ? $clog2(InputBufferTotDepth) : 1,

  localparam type fmt_cfg_t = struct packed {
    logic [InFmtSelWidth-1:0]    in_fmt;
    logic [ScaleFmtSelWidth-1:0] scale_fmt;
    logic [OutFmtSelWidth-1:0]   out_fmt;
  },

  localparam type ctrl_t = struct packed {
    fmt_cfg_t                            fmt_cfg;
    logic                                is_biased;
    logic [OutputBufferAddrWidth-1:0]    out_start_addr;
    logic [InputBufferWideAddrWidth-1:0] in_x_start_addr;
    logic [InputBufferWideAddrWidth-1:0] in_w_start_addr;
    logic [InIterWidth-1:0]              x_iters;
    logic [InIterWidth-1:0]              w_iters;
  },

  localparam type write_req_t = struct packed {
    logic                      valid;
    logic [WriteAddrWidth-1:0] addr;
    logic [WriteDataWidth-1:0] wdata;
  },

  localparam type read_req_t = struct packed {
    logic                     valid;
    logic [ReadAddrWidth-1:0] addr;
  },

  localparam type read_rsp_t = struct packed {
    logic                     valid;
    logic [ReadDataWidth-1:0] rdata;
  }
) (
  input  logic                       clk_i,
  input  logic                       rst_ni,

  input  ctrl_t                      ctrl_i,
  input  logic                       ctrl_valid_i,
  output logic                       ctrl_ready_o,

  input  write_req_t [NrGroupsW-1:0] write_req_i,

  input  read_req_t  [NrGroupsW-1:0] read_req_i,
  output read_rsp_t  [NrGroupsW-1:0] read_rsp_o
);

  localparam int unsigned InputBufferWideWord = NrIn * BaseInFmtWidth + NrMxGroups * ScaleFmtWidth;
  localparam int unsigned CtrlTreeMaxWidth    = CtrlTreeWidth ** CtrlTreeDepth;

  ctrl_t [CtrlTreeDepth:0][CtrlTreeMaxWidth-1:0] ctrl_tree;
  logic  [CtrlTreeDepth:0][CtrlTreeMaxWidth-1:0] ctrl_tree_valid;
  logic  [CtrlTreeDepth:0][CtrlTreeMaxWidth-1:0] ctrl_tree_ready;

  assign ctrl_tree[0][0]       = ctrl_i;
  assign ctrl_tree_valid[0][0] = ctrl_valid_i;
  assign ctrl_ready_o          = ctrl_tree_ready[0][0];

  for (genvar d = 0; d < CtrlTreeDepth; d++) begin : gen_ctrl_tree
    localparam int unsigned NrCurNodes  = CtrlTreeWidth ** (d+1);
    localparam int unsigned NrPrecNodes = CtrlTreeWidth ** d;

    for (genvar n = 0; n < NrCurNodes; n++) begin : gen_nodes
      logic local_ready;

      spill_register #(
        .T (ctrl_t)
      ) i_ctrl_tree_node (
        .clk_i (clk_i),
        .rst_ni (rst_ni),
        .valid_i (ctrl_tree_valid[d][n/CtrlTreeWidth]),
        .ready_o (local_ready),
        .data_i (ctrl_tree[d][n/CtrlTreeWidth]),
        .valid_o (ctrl_tree_valid[d+1][n]),
        .ready_i (ctrl_tree_ready[d+1][n]),
        .data_o (ctrl_tree[d+1][n])
      );

      if (n % CtrlTreeWidth == 0) begin
        assign ctrl_tree_ready[d][n/CtrlTreeWidth] = local_ready;
      end
    end
  end

  logic [NrGroupsX-1:0][NrGroupsW-1:0][GroupSizeX*InputBufferWideWord-1:0] x_ext;
  logic [NrGroupsW-1:0][NrGroupsX-1:0][GroupSizeW*InputBufferWideWord-1:0] w_ext;

  write_req_t [NrGroupsW-1:0][NrGroupsX-1:0] write_reqs;
  read_req_t  [NrGroupsW-1:0][NrGroupsX-1:0] read_reqs;
  read_rsp_t  [NrGroupsW-1:0][NrGroupsX-1:0] read_rsps;

  for (genvar w = 0; w < NrGroupsW; w++) begin : assign_req_rsp
    assign write_reqs[w][0] = write_req_i[w];
    assign read_reqs[w][0]  = read_req_i[w];
    assign read_rsp_o[w]    = read_rsps[w][0];
  end

  for (genvar x = 0; x < NrGroupsX; x++) begin : gen_rows
    for (genvar w = 0; w < NrGroupsW; w++) begin : gen_columns
      logic [GroupIdWidth-1:0] group_id;

      logic [GroupSizeX*InputBufferWideWord-1:0] x_ext_in;
      logic [GroupSizeW*InputBufferWideWord-1:0] w_ext_in;

      write_req_t local_write_req;
      read_req_t  local_read_req;
      read_rsp_t  local_read_rsp;

      logic local_ctrl_ready;

      int unsigned x_sel, w_sel;

      if (x % 2 == 0) begin
        if (x == 0) begin
          assign x_sel = 1;
        end else begin
          assign x_sel = x-2;
        end
      end else begin
        if (x == NrGroupsX-1) begin
          assign x_sel = NrGroupsX-2;
        end else if (x == NrGroupsX-2) begin
          assign x_sel = NrGroupsX-1;
        end else begin
          assign x_sel = x+2;
        end
      end

      if (w % 2 == 0) begin
        if (w == 0) begin
          assign w_sel = 1;
        end else begin
          assign w_sel = w-2;
        end
      end else begin
        if (w == NrGroupsW-1) begin
          assign w_sel = NrGroupsW-2;
        end else if (w == NrGroupsW-2) begin
          assign w_sel = NrGroupsW-1;
        end else begin
          assign w_sel = w+2;
        end
      end

      assign group_id = w;

      auteur_group #(
        .ReadAddrWidth (ReadAddrWidth),
        .WriteAddrWidth (WriteAddrWidth),
        .ReadDataWidth (ReadDataWidth),
        .WriteDataWidth (WriteDataWidth),
        .GroupIdWidth (GroupIdWidth),
        .GroupSizeX (GroupSizeX),
        .GroupSizeW (GroupSizeW),
        .IntercoWidth (IntercoWidth),
        .BaseInFmtWidth (BaseInFmtWidth),
        .ScaleFmtWidth (ScaleFmtWidth),
        .OutFmtWidth (OutFmtWidth),
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
        .PipeCfg (PipeCfg),
        .NrInFormats (NrInFormats),
        .InFpEncoding (InFpEncoding),
        .NrScaleFormats (NrScaleFormats),
        .ScaleFpEncoding (ScaleFpEncoding),
        .NrOutFormats (NrOutFormats),
        .OutFpEncoding (OutFpEncoding),
        .OutputBufferDepth (OutputBufferDepth),
        .OutputBufferBanks (OutputBufferBanks),
        .OutputBufferSplitReadWrite (OutputBufferSplitReadWrite),
        .InputBufferTotDepth (InputBufferTotDepth),
        .InputBufferDepth (InputBufferDepth),
        .InputBufferBanks (InputBufferBanks),
        .InputBufferLatches (InputBufferLatches)
      ) i_group (
        .clk_i (clk_i),
        .rst_ni (rst_ni),
        .group_id_i (group_id),
        .ctrl_valid_i (ctrl_tree_valid[CtrlTreeDepth][x/CtrlGroupX*CtrlGroupW + w/CtrlGroupW]),
        .ctrl_ready_o (local_ctrl_ready),
        .ctrl_i (ctrl_tree[CtrlTreeDepth][x/CtrlGroupX*CtrlGroupW + w/CtrlGroupW]),
        .x_ext_i (x_ext[x][w_sel]),
        .w_ext_i (w_ext[w][x_sel]),
        .x_ext_o (x_ext[x][w]),
        .w_ext_o (w_ext[w][x]),
        .write_req_i (write_reqs[w][x]),
        .write_req_o (local_write_req),
        .read_req_i (read_reqs[w][x]),
        .read_req_o (local_read_req),
        .read_rsp_o (read_rsps[w][x]),
        .read_rsp_i (local_read_rsp)
      );

      if (x != NrGroupsX-1) begin
        assign write_reqs[w][x+1] = local_write_req;
        assign read_reqs[w][x+1]  = local_read_req;
        assign local_read_rsp     = read_rsps[w][x+1];
      end

      if (x == NrGroupsX-1) begin
        assign local_read_rsp = '0;
      end

      if ((w % CtrlGroupW == 0) && (x % CtrlGroupX == 0)) begin
        assign ctrl_tree_ready[CtrlTreeDepth][x/CtrlGroupX*CtrlGroupW + w/CtrlGroupW] = local_ctrl_ready;
      end
    end
  end

endmodule