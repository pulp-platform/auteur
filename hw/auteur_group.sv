// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_group
  import auteur_pkg::*;
#(
  parameter int unsigned    GroupSizeX = 1,
  parameter int unsigned    GroupSizeW = 1,
  parameter int unsigned    IntercoWidth = 1,
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
  parameter dotp_pipe_cfg_t PipeCfg = '{default: '0},
  parameter int unsigned    NrInFormats = 1,
  parameter fp_encoding_t   InFpEncoding [NrInFormats-1:0] = '{default: '0},
  parameter int unsigned    NrScaleFormats = 1,
  parameter fp_encoding_t   ScaleFpEncoding [NrScaleFormats-1:0] = '{default: '0},
  parameter int unsigned    NrOutFormats = 1,
  parameter fp_encoding_t   OutFpEncoding [NrOutFormats-1:0] = '{default: '0},
  parameter int unsigned    OutputBufferDepth = 1,
  parameter int unsigned    OutputBufferBanks = 2,

  localparam int unsigned NrMxGroups = NrIn/MxGroupSize,

  localparam int unsigned AddrWidth = OutputBufferDepth*GroupSizeX/IntercoWidth > 1 ? $clog2(OutputBufferDepth*GroupSizeX/IntercoWidth) : 0,
  localparam int unsigned DataWidth = OutFmtWidth*IntercoWidth,
  localparam int unsigned BeWidth   = DataWidth/8,

  localparam int unsigned OutputBufferAddrWidth = OutputBufferDepth > 1 ? $clog2(OutputBufferDepth) : 1,

  localparam type fmt_cfg_t = struct packed {
    logic [$clog2(NrInFormats)-1:0]    in_fmt;
    logic [$clog2(NrScaleFormats)-1:0] scale_fmt;
    logic [$clog2(NrOutFormats)-1:0]   out_fmt;
  },

  localparam type group_cfg_t = struct packed {
    logic [OutputBufferAddrWidth-1:0] ce_read_addr;
    logic [OutputBufferAddrWidth-1:0] ce_write_addr;
    fmt_cfg_t                         fmt_cfg;
  },

  localparam type group_req_t = struct packed {
    logic                 valid;
    logic [AddrWidth-1:0] addr;
    logic                 we;
    logic [DataWidth-1:0] wdata;
    logic [BeWidth-1:0]   be;
  },

  localparam type group_rsp_t = struct packed {
    logic                 valid;
    logic                 ready;
    logic [DataWidth-1:0] rdata;
  }
) (
  input  logic                                                     clk_i,
  input  logic                                                     rst_ni,

  input  group_cfg_t                                               group_cfg_i,

  input  logic                                                     data_valid_i,

  input  logic [GroupSizeX-1:0][NrIn-1:0][BaseInFmtWidth-1:0]      x_i,
  input  logic [GroupSizeW-1:0][NrIn-1:0][BaseInFmtWidth-1:0]      w_i,

  input  logic [GroupSizeX-1:0][NrMxGroups-1:0][ScaleFmtWidth-1:0] x_scale_i,
  input  logic [GroupSizeW-1:0][NrMxGroups-1:0][ScaleFmtWidth-1:0] w_scale_i,

  input  group_req_t [GroupSizeW-1:0]                              group_req_i,
  output group_rsp_t [GroupSizeW-1:0]                              group_rsp_o
);

  localparam type buf_req_t = struct packed {
    logic                             valid;
    logic [OutputBufferAddrWidth-1:0] addr;
    logic                             we;
    logic [OutFmtWidth-1:0]           wdata;
    logic [OutFmtWidth/8-1:0]         be;
  };

  localparam type buf_rsp_t = struct packed {
    logic                   valid;
    logic                   ready;
    logic [OutFmtWidth-1:0] rdata;
  };

  for (genvar w = 0; w < GroupSizeW; w++) begin : gen_rows
    buf_rsp_t [GroupSizeX-1:0] buf_rsp_ext;

    for (genvar x = 0; x < GroupSizeX; x++) begin : gen_columns
      localparam int unsigned Segment = x/IntercoWidth;
      localparam int unsigned Offset  = x%IntercoWidth;

      logic [OutFmtWidth-1:0] y_ce, z_ce;
      logic                   y_ce_valid, z_ce_valid;

      logic buf_select;

      buf_req_t buf_req_ce_read, buf_req_ce_write, buf_req_ext;
      buf_rsp_t buf_rsp_ce_read, buf_rsp_ce_write;

      assign buf_req_ce_read = '{
        valid: data_valid_i,
        addr: group_cfg_i.ce_read_addr,
        we: 1'b0,
        wdata: '0,
        be: '1
      };

      assign buf_req_ce_write = '{
        valid: z_ce_valid,
        addr: group_cfg_i.ce_write_addr,
        we: 1'b1,
        wdata: z_ce,
        be: '1
      };

      assign buf_select = group_req_i[w].valid && (group_req_i[w].addr%(GroupSizeX/IntercoWidth)) == Segment;

      assign buf_req_ext = '{
        valid: buf_select,
        addr: group_req_i[w].addr[OutputBufferAddrWidth-1+$clog2(GroupSizeX/IntercoWidth):$clog2(GroupSizeX/IntercoWidth)],
        we: group_req_i[w].we,
        wdata: group_req_i[w].wdata[Offset*OutFmtWidth+:OutFmtWidth],
        be: group_req_i[w].be[Offset*OutFmtWidth/8+:OutFmtWidth/8]
      };

      assign y_ce       = buf_rsp_ce_read.rdata;
      assign y_ce_valid = buf_rsp_ce_read.valid;

      auteur_ce #(
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
        .YDelay (1),
        .ScalesDelay (0),
        .PipeCfg (PipeCfg),
        .NrInFormats (NrInFormats),
        .InFpEncoding (InFpEncoding),
        .NrScaleFormats (NrScaleFormats),
        .ScaleFpEncoding (ScaleFpEncoding),
        .NrOutFormats (NrOutFormats),
        .OutFpEncoding (OutFpEncoding)
      ) i_ce (
        .clk_i (clk_i),
        .rst_ni (rst_ni),
        .cfg_valid_i (data_valid_i),
        .cfg_i (group_cfg_i.fmt_cfg),
        .in_valid_i (data_valid_i),
        .x_i (x_i[x]),
        .w_i (w_i[w]),
        .scale_valid_i (data_valid_i),
        .x_scale_i (x_scale_i[x]),
        .w_scale_i (w_scale_i[w]),
        .y_valid_i (y_ce_valid),
        .y_i (y_ce),
        .z_valid_o (z_ce_valid),
        .z_o (z_ce)
      );

      auteur_output_buffer #(
        .DataWidth (OutFmtWidth),
        .ByteWidth (8),
        .Depth (OutputBufferDepth),
        .NrBanks (OutputBufferBanks),
        .BankAddrStart (1)
      ) i_output_buffer (
        .clk_i (clk_i),
        .rst_ni (rst_ni),
        .req_i ({buf_req_ext   , buf_req_ce_write, buf_req_ce_read}),
        .rsp_o ({buf_rsp_ext[x], buf_rsp_ce_write, buf_rsp_ce_read})
      );
    end

    logic                 rsp_valid, rsp_ready;
    logic [DataWidth-1:0] rsp_rdata;

    always_comb begin : assign_rsp
      rsp_valid = 1'b0;
      rsp_ready = 1'b0;
      rsp_rdata = '0;

      for (int unsigned x = 0; x < GroupSizeX; x+=IntercoWidth) begin
        rsp_ready |= buf_rsp_ext[x].ready;
      end

      for (int unsigned x = 0; x < GroupSizeX; x+=IntercoWidth) begin
        if (~rsp_valid) begin
          rsp_valid |= buf_rsp_ext[x].valid;

          for (int unsigned i = 0; i < IntercoWidth; i++) begin
            rsp_rdata[OutFmtWidth*i+:OutFmtWidth] = buf_rsp_ext[x+i].rdata;
          end
        end
      end
    end

    assign group_rsp_o[w].valid = rsp_valid;
    assign group_rsp_o[w].ready = rsp_ready;
    assign group_rsp_o[w].rdata = rsp_rdata;
  end

endmodule