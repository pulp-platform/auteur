// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_ctrl_local #(
  parameter int unsigned DotpDelay = 0,
  parameter int unsigned OutputBufferAddrWidth = 1,
  parameter int unsigned InputBufferAddrWidth = 1,
  parameter int unsigned InFmtSelWidth = 1,
  parameter int unsigned ScaleFmtSelWidth = 1,
  parameter int unsigned OutFmtSelWidth = 1,
  // Not the local number of buffers!
  parameter int unsigned InputBufferTotDepth = 1,

  localparam int unsigned InIterWidth = InputBufferTotDepth > 1 ? $clog2(InputBufferTotDepth) : 1,

  localparam type fmt_cfg_t = struct packed {
    logic [InFmtSelWidth-1:0]    in_fmt;
    logic [ScaleFmtSelWidth-1:0] scale_fmt;
    logic [OutFmtSelWidth-1:0]   out_fmt;
  },

  localparam type ctrl_t = struct packed {
    fmt_cfg_t                         fmt_cfg;
    logic                             is_biased;
    logic [OutputBufferAddrWidth-1:0] out_start_addr;
    logic [InputBufferAddrWidth-1:0]  in_x_start_addr;
    logic [InputBufferAddrWidth-1:0]  in_w_start_addr;
    logic [InIterWidth-1:0]           x_iters;
    logic [InIterWidth-1:0]           w_iters;
  }
) (
  input  logic                             clk_i,
  input  logic                             rst_ni,

  input  logic                             valid_i,
  input  ctrl_t                            ctrl_i,

  input  logic                             out_valid_i,

  output logic                             ready_o,
  output logic                             addr_valid_o,
  output logic                             data_valid_o,
  output fmt_cfg_t                         fmt_cfg_o,
  output logic                             bias_en_o,
  output logic [InputBufferAddrWidth-1:0]  x_read_addr_o,
  output logic [InputBufferAddrWidth-1:0]  w_read_addr_o,
  output logic [InputBufferAddrWidth-1:0]  x_write_addr_o,
  output logic [InputBufferAddrWidth-1:0]  w_write_addr_o,
  output logic                             x_iter_o,
  output logic                             w_iter_o,
  output logic [OutputBufferAddrWidth-1:0] out_read_addr_o,
  output logic [OutputBufferAddrWidth-1:0] out_write_addr_o
);

  logic [InIterWidth-1:0] x_iters_cnt, w_iters_cnt;
  logic                   x_iter_d, x_iter_q, w_iter_d, w_iter_q;

  logic fifo_empty_d, fifo_empty_q, fifo_full;
  ctrl_t ctrl_q;

  fifo_v3 #(
    .DEPTH (2),
    .dtype (ctrl_t)
  ) i_inst_fifo (
    .clk_i (clk_i),
    .rst_ni (rst_ni),
    .flush_i (1'b0),
    .data_i (ctrl_i),
    .push_i (valid_i && ~fifo_full),
    .data_o (ctrl_q),
    .pop_i (~fifo_empty_d && x_iters_cnt == ctrl_q.x_iters && w_iters_cnt == ctrl_q.w_iters),
    .empty_o (fifo_empty_d),
    .full_o (fifo_full)
  );

  assign w_iter_d = ~fifo_empty_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : w_iters_counter
    if (~rst_ni) begin
      w_iters_cnt <= '0;
    end else begin
      if (w_iter_d) begin
        if (w_iters_cnt == ctrl_q.w_iters) begin
          w_iters_cnt <= '0;
        end else begin
          w_iters_cnt <= w_iters_cnt + 1;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : w_iter_register
    if (~rst_ni) begin
      w_iter_q <= 1'b0;
    end else begin
      w_iter_q <= w_iter_d;
    end
  end

  assign x_iter_d = w_iter_d && w_iters_cnt == ctrl_q.w_iters;

  always_ff @(posedge clk_i or negedge rst_ni) begin : x_iters_counter
    if (~rst_ni) begin
      x_iters_cnt <= '0;
    end else begin
      if (x_iter_d) begin
        if (x_iters_cnt == ctrl_q.x_iters) begin
          x_iters_cnt <= '0;
        end else begin
          x_iters_cnt <= x_iters_cnt + 1;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : x_iter_register
    if (~rst_ni) begin
      x_iter_q <= 1'b0;
    end else begin
      x_iter_q <= x_iter_d;
    end
  end

  logic [OutputBufferAddrWidth-1:0] tot_read_iters_cnt;

  always_ff @(posedge clk_i or negedge rst_ni) begin : tot_read_iters_counter
    if (~rst_ni) begin
      tot_read_iters_cnt <= '0;
    end else begin
      if (~fifo_empty_d) begin
        if (x_iters_cnt == ctrl_q.x_iters && w_iters_cnt == ctrl_q.w_iters) begin
          tot_read_iters_cnt <= '0;
        end else begin
          tot_read_iters_cnt <= tot_read_iters_cnt + 1;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : fifo_empty_register
    if (~rst_ni) begin
      fifo_empty_q <= 1'b1;
    end else begin
      fifo_empty_q <= fifo_empty_d;
    end
  end

  logic [InputBufferAddrWidth-1:0]  x_addr_d, x_addr_q, w_addr_d, w_addr_q;

  assign x_addr_d = ctrl_q.in_x_start_addr + x_iters_cnt / InputBufferTotDepth;
  assign w_addr_d = ctrl_q.in_w_start_addr + w_iters_cnt / InputBufferTotDepth;

  always_ff @(posedge clk_i or negedge rst_ni) begin : x_addr_register
    if (~rst_ni) begin
      x_addr_q <= '0;
    end else begin
      if (~fifo_empty_d) begin
        x_addr_q <= x_addr_d;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : w_addr_register
    if (~rst_ni) begin
      w_addr_q <= '0;
    end else begin
      if (~fifo_empty_d) begin
        w_addr_q <= w_addr_d;
      end
    end
  end

  logic [OutputBufferAddrWidth-1:0] out_write_addr_q;

  // We use this fifo since we also support the (extremely unlikely) case in which only 1-iteration operations are issued
  fifo_v3 #(
    .DEPTH (DotpDelay+1),
    .DATA_WIDTH (OutputBufferAddrWidth)
  ) i_out_write_addr_fifo (
    .clk_i (clk_i),
    .rst_ni (rst_ni),
    .flush_i (1'b0),
    .data_i (ctrl_q.out_start_addr),
    .push_i (~fifo_empty_d),
    .data_o (out_write_addr_q),
    .pop_i (out_valid_i),
    .empty_o (),
    .full_o ()
  );


  assign ready_o          = ~fifo_full;
  assign addr_valid_o     = ~fifo_empty_d;
  assign data_valid_o     = ~fifo_empty_q;
  assign fmt_cfg_o        = ctrl_q.fmt_cfg;
  assign bias_en_o        = ctrl_q.is_biased || ~(x_iters_cnt == 0 && ~fifo_empty_d);
  assign x_read_addr_o    = x_addr_d;
  assign w_read_addr_o    = w_addr_d;
  assign x_write_addr_o   = x_addr_q;
  assign w_write_addr_o   = w_addr_q;
  assign x_iter_o         = x_iter_q;
  assign w_iter_o         = w_iter_q;
  assign out_read_addr_o  = ctrl_q.out_start_addr + tot_read_iters_cnt;
  assign out_write_addr_o = out_write_addr_q;

endmodule