// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_group
  import auteur_pkg::*;
#(
  parameter int unsigned    ReadAddrWidth = 1,
  parameter int unsigned    WriteAddrWidth = 1,
  parameter int unsigned    ReadDataWidth = 1,
  parameter int unsigned    WriteDataWidth = 1,
  parameter int unsigned    GroupIdWidth = 1,
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

  parameter int unsigned    InputBufferTotDepth = 1,
  parameter int unsigned    InputBufferDepth = 1,
  parameter int unsigned    InputBufferBanks = 2,
  parameter bit             InputBufferLatches = 0,

  localparam int unsigned NrMxGroups = NrIn/MxGroupSize,

  localparam int unsigned DataWidth = OutFmtWidth*IntercoWidth,

  localparam int unsigned InputBufferWideWord = NrIn * BaseInFmtWidth + NrMxGroups * ScaleFmtWidth,

  localparam int unsigned OutputBufferAddrWidth = OutputBufferDepth > 1 ? $clog2(OutputBufferDepth) : 1,
  localparam int unsigned InputBufferWideAddrWidth = InputBufferDepth > 1 ? $clog2(InputBufferDepth) : 1,
  localparam int unsigned InputBufferNarrowAddrWidth = InputBufferWideWord/DataWidth * InputBufferDepth > 1 ? $clog2(InputBufferWideWord/DataWidth * InputBufferDepth) : 1,

  localparam int unsigned NrOutputBuffersW = GroupSizeW/IntercoWidth,

  localparam int unsigned OutputBufferSize = GroupSizeX * GroupSizeW * OutputBufferDepth * OutputBufferBanks / IntercoWidth,
  localparam int unsigned InputBufferSize  = 2 * (GroupSizeX + GroupSizeW) * InputBufferBanks * InputBufferDepth * InputBufferWideWord / DataWidth / IntercoWidth,

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
  input  logic                                           clk_i,
  input  logic                                           rst_ni,

  input  logic [GroupIdWidth-1:0]                        group_id_i,

  input  logic                                           ctrl_valid_i,
  output logic                                           ctrl_ready_o,
  input  ctrl_t                                          ctrl_i,

  input  logic [GroupSizeX-1:0][InputBufferWideWord-1:0] x_ext_i,
  input  logic [GroupSizeW-1:0][InputBufferWideWord-1:0] w_ext_i,

  output logic [GroupSizeX-1:0][InputBufferWideWord-1:0] x_ext_o,
  output logic [GroupSizeW-1:0][InputBufferWideWord-1:0] w_ext_o,

  input  write_req_t                                     write_req_i,
  output write_req_t                                     write_req_o,

  input  read_req_t                                      read_req_i,
  output read_req_t                                      read_req_o,
  output read_rsp_t                                      read_rsp_o,
  input  read_rsp_t                                      read_rsp_i
);

  typedef struct packed {
    logic                                  valid;
    logic [InputBufferNarrowAddrWidth-1:0] addr;
    logic [WriteDataWidth-1:0]             wdata;
  } input_buffer_req_t;

  typedef struct packed {
    logic                             valid;
    logic [OutputBufferAddrWidth-1:0] addr;
    logic                             we;
    logic [WriteDataWidth-1:0]        wdata;
  } output_buffer_req_t;

  typedef struct packed {
    logic                     valid;
    logic [ReadDataWidth-1:0] rdata;
  } output_buffer_rsp_t;

  typedef struct packed {
    logic                                valid;
    logic [InputBufferWideAddrWidth-1:0] addr;
  } input_buffer_wide_req_t;

  input_buffer_req_t  [GroupSizeX+GroupSizeW-1:0]            input_buffer_req;
  output_buffer_req_t [GroupSizeX-1:0][NrOutputBuffersW-1:0] output_buffer_req;
  output_buffer_rsp_t [GroupSizeX-1:0][NrOutputBuffersW-1:0] output_buffer_rsp;

  auteur_broker #(
    .ReadAddrWidth (ReadAddrWidth),
    .WriteAddrWidth (WriteAddrWidth),
    .ReadDataWidth (ReadDataWidth),
    .WriteDataWidth (WriteDataWidth),
    .GroupIdWidth (GroupIdWidth),
    .GroupSizeX (GroupSizeX),
    .GroupSizeW (GroupSizeW),
    .IntercoWidth (IntercoWidth),
    .InputBufferAddrWidth (InputBufferNarrowAddrWidth),
    .OutputBufferAddrWidth (OutputBufferAddrWidth)
  ) i_auteur_broker (
    .clk_i (clk_i),
    .rst_ni (rst_ni),
    .group_id_i (group_id_i),
    .write_req_i (write_req_i),
    .write_req_o (write_req_o),
    .read_req_i (read_req_i),
    .read_req_o (read_req_o),
    .read_rsp_o (read_rsp_o),
    .read_rsp_i (read_rsp_i),
    .input_buffer_req_o (input_buffer_req),
    .output_buffer_req_o (output_buffer_req),
    .output_buffer_rsp_i (output_buffer_rsp)
  );

  fmt_cfg_t                            fmt_cfg;
  logic                                bias_en;
  logic                                addr_valid, data_valid;
  logic [InputBufferWideAddrWidth-1:0] x_read_addr, x_write_addr, w_read_addr, w_write_addr;
  logic [OutputBufferAddrWidth-1:0]    out_read_addr, out_write_addr;
  logic                                x_iter, w_iter;
  logic                                out_valid;

  auteur_ctrl_local #(
    .DotpDelay (auteur_pkg::get_total_delay(PipeCfg)),
    .OutputBufferAddrWidth (OutputBufferAddrWidth),
    .InputBufferAddrWidth (InputBufferWideAddrWidth),
    .InFmtSelWidth (InFmtSelWidth),
    .ScaleFmtSelWidth (ScaleFmtSelWidth),
    .OutFmtSelWidth (OutFmtSelWidth),
    .InputBufferTotDepth(InputBufferTotDepth)
  ) i_local_ctrl (
    .clk_i (clk_i),
    .rst_ni (rst_ni),
    .valid_i (ctrl_valid_i),
    .ctrl_i (ctrl_i),
    .ready_o (ctrl_ready_o),
    .out_valid_i (out_valid),
    .addr_valid_o (addr_valid),
    .data_valid_o (data_valid),
    .fmt_cfg_o (fmt_cfg),
    .bias_en_o (bias_en),
    .x_read_addr_o (x_read_addr),
    .w_read_addr_o (w_read_addr),
    .x_write_addr_o (x_write_addr),
    .w_write_addr_o (w_write_addr),
    .x_iter_o (x_iter), // OK, FOR WRITES ONLY
    .w_iter_o (w_iter), // OK, FOR WRITES ONLY
    .out_read_addr_o (out_read_addr),
    .out_write_addr_o (out_write_addr)
  );

  logic [GroupSizeX-1:0][NrIn*BaseInFmtWidth-1:0] x_buf;
  logic [GroupSizeW-1:0][NrIn*BaseInFmtWidth-1:0] w_buf;

  logic [GroupSizeX-1:0][NrMxGroups-1:0][ScaleFmtWidth-1:0] x_scale_buf;
  logic [GroupSizeW-1:0][NrMxGroups-1:0][ScaleFmtWidth-1:0] w_scale_buf;

  input_buffer_wide_req_t x_write_req, x_read_req, w_write_req, w_read_req;

  assign x_write_req = '{
    valid: x_iter,
    addr:  x_write_addr
  };

  assign x_read_req = '{
    valid: addr_valid,
    addr:  x_read_addr
  };

  assign w_write_req = '{
    valid: w_iter,
    addr:  w_write_addr
  };

  assign w_read_req = '{
    valid: addr_valid,
    addr:  w_read_addr
  };

  for (genvar x = 0; x < GroupSizeX; x++) begin : gen_x_buffers
    auteur_input_buffer #(
      .NarrowWordWidth (DataWidth),
      .WideWordWidth (InputBufferWideWord),
      .Depth (InputBufferDepth),
      .NumBanks (InputBufferBanks),
      .UseLatches (InputBufferLatches)
    ) i_x_buffer (
      .clk_i (clk_i),
      .rst_ni (rst_ni),
      .narrow_req_i (input_buffer_req[x]),
      .wide_read_req_i (x_read_req),
      .wide_rdata_o ({x_scale_buf[x], x_buf[x]}),
      .wide_write_req_i (x_write_req),
      .wide_wdata_i (x_ext_i[x])
    );

    assign x_ext_o[x] = {x_scale_buf[x], x_buf[x]};
  end

  for (genvar w = 0; w < GroupSizeW; w++) begin : gen_w_buffers
    auteur_input_buffer #(
      .NarrowWordWidth (DataWidth),
      .WideWordWidth (InputBufferWideWord),
      .Depth (InputBufferDepth),
      .NumBanks (InputBufferBanks),
      .UseLatches (InputBufferLatches)
    ) i_w_buffer (
      .clk_i (clk_i),
      .rst_ni (rst_ni),
      .narrow_req_i (input_buffer_req[GroupSizeX+w]),
      .wide_read_req_i (w_read_req),
      .wide_rdata_o ({w_scale_buf[w], w_buf[w]}),
      .wide_write_req_i (w_write_req),
      .wide_wdata_i (w_ext_i[w])
    );

    assign w_ext_o[w] = {w_scale_buf[w], w_buf[w]};
  end

  for (genvar x = 0; x < GroupSizeX; x++) begin : gen_rows
    for (genvar w = 0; w < NrOutputBuffersW; w++) begin : gen_columns
      logic [IntercoWidth-1:0][OutFmtWidth-1:0] y_ce, z_ce;
      logic [IntercoWidth-1:0]                  z_ce_valid;

      output_buffer_req_t buf_req_ce_read, buf_req_ce_write;
      output_buffer_rsp_t buf_rsp_ce_read, buf_rsp_ce_write;

      assign buf_req_ce_read = '{
        valid: addr_valid && bias_en,
        addr: out_read_addr,
        we: 1'b0,
        wdata: '0
      };

      assign buf_req_ce_write = '{
        valid: z_ce_valid[0],
        addr: out_write_addr,
        we: 1'b1,
        wdata: z_ce
      };

      assign y_ce = bias_en ? buf_rsp_ce_read.rdata : '0;

      for (genvar i = 0; i < IntercoWidth; i++) begin : gen_local_ces
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
          .YDelay (0),
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
          .cfg_valid_i (data_valid),
          .cfg_i (fmt_cfg),
          .in_valid_i (data_valid),
          .x_i (x_buf[x]),
          .w_i (w_buf[w*IntercoWidth+i]),
          .scale_valid_i (data_valid),
          .x_scale_i (x_scale_buf[x]),
          .w_scale_i (w_scale_buf[w*IntercoWidth+i]),
          .y_valid_i (data_valid),
          .y_i (y_ce[i]),
          .z_valid_o (z_ce_valid[i]),
          .z_o (z_ce[i])
        );

        // This CE will for sure be active
        if (x == 0 && w == 0 && i == 0) begin
          assign out_valid = z_ce_valid[i];
        end
      end

      auteur_output_buffer #(
        .DataWidth (OutFmtWidth),
        .Depth (OutputBufferDepth),
        .NrBanks (OutputBufferBanks),
        .BankAddrStart (1)
      ) i_output_buffer (
        .clk_i (clk_i),
        .rst_ni (rst_ni),
        .req_i ({output_buffer_req[x][w], buf_req_ce_write, buf_req_ce_read}),
        .rsp_o ({output_buffer_rsp[x][w], buf_rsp_ce_write, buf_rsp_ce_read})
      );
    end
  end

endmodule