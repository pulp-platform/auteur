// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_input_buffer #(
  parameter int unsigned NarrowWordWidth = 1,
  parameter int unsigned WideWordWidth = 1,
  parameter int unsigned Depth = 1,
  parameter int unsigned NumBanks = 1,
  parameter bit          UseLatches = 0,

  localparam int unsigned NumNarrowWords = WideWordWidth/NarrowWordWidth,
  localparam int unsigned NarrowAddrWidth = $clog2(NumNarrowWords * Depth),
  localparam int unsigned WideAddrWidth = Depth > 1 ? $clog2(Depth) : 1,

  localparam type narrow_req_t = struct packed {
    logic                       valid;
    logic [NarrowAddrWidth-1:0] addr;
    logic [NarrowWordWidth-1:0] wdata;
  },

  localparam type wide_req_t = struct packed {
    logic                     valid;
    logic [WideAddrWidth-1:0] addr;
  }
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  narrow_req_t              narrow_req_i,

  input  wide_req_t                wide_read_req_i,
  output logic [WideWordWidth-1:0] wide_rdata_o,

  input  wide_req_t                wide_write_req_i,
  input  logic [WideWordWidth-1:0] wide_wdata_i
);

  localparam int unsigned BankDepth = Depth / NumBanks;

  logic [WideAddrWidth-1:0] wide_raddr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : wide_read_addr_register
    if (~rst_ni) begin
      wide_raddr_q <= '0;
    end else begin
      if (wide_read_req_i.valid) begin
        wide_raddr_q <= wide_read_req_i.addr;
      end
    end
  end

  logic [NumBanks-1:0][BankDepth-1:0][NumNarrowWords-1:0][NarrowWordWidth-1:0] mem_q;

  assign wide_rdata_o = mem_q[wide_raddr_q[WideAddrWidth-1-:$clog2(NumBanks)]][wide_raddr_q[0+:$clog2(BankDepth)]];

  logic [NumNarrowWords-1:0][NarrowWordWidth-1:0] wdata_q;

  for (genvar n = 0; n < NumNarrowWords; n++) begin : gen_latch_wdata_registers
    int unsigned narrow_word_sel;

    if (NumNarrowWords != 1) begin
      assign narrow_word_sel = narrow_req_i.addr[0+:$clog2(NumNarrowWords)];
    end else begin
      assign narrow_word_sel = 0;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : latch_wdata_register
      if (~rst_ni) begin
        wdata_q[n] <= '0;
      end else begin
        if (wide_write_req_i.valid) begin
          wdata_q[n] <= wide_wdata_i[NarrowWordWidth*n+:NarrowWordWidth];
        end else if (narrow_req_i.valid && narrow_word_sel == n) begin
          wdata_q[n] <= narrow_req_i.wdata;
        end
      end
    end
  end

  for (genvar b = 0; b < NumBanks; b++) begin : gen_buffers
    for (genvar w = 0; w < BankDepth; w++) begin : gen_wide_words
      int unsigned wide_req_bank_sel, wide_req_wide_word_sel;

      logic wide_word_wen_d;

      if (NumBanks != 1) begin
        assign wide_req_bank_sel = wide_write_req_i.addr[$clog2(BankDepth)+:$clog2(NumBanks)];
      end else begin
        assign wide_req_bank_sel = 0;
      end

      if (BankDepth != 1) begin
        assign wide_req_wide_word_sel = wide_write_req_i.addr[0+:$clog2(BankDepth)];
      end else begin
        assign wide_req_wide_word_sel = 0;
      end

      assign wide_word_wen_d = wide_write_req_i.valid && wide_req_bank_sel == b && wide_req_wide_word_sel == w;

      for (genvar n = 0; n < NumNarrowWords; n++) begin : gen_narrow_words
        int unsigned narrow_req_bank_sel, narrow_req_wide_word_sel, narrow_req_narrow_word_sel;

        logic narrow_word_wen_d;

        if (NumBanks != 1) begin
          assign narrow_req_bank_sel = narrow_req_i.addr[$clog2(NumNarrowWords)+$clog2(BankDepth)+:$clog2(NumBanks)];
        end else begin
          assign narrow_req_bank_sel = 0;
        end

        if (BankDepth != 1) begin
          assign narrow_req_wide_word_sel = narrow_req_i.addr[$clog2(NumNarrowWords)+:$clog2(BankDepth)];
        end else begin
          assign narrow_req_wide_word_sel = 0;
        end

        if (NumNarrowWords != 1) begin
          assign narrow_req_narrow_word_sel = narrow_req_i.addr[0+:$clog2(NumNarrowWords)];
        end else begin
          assign narrow_req_narrow_word_sel = 0;
        end

        assign narrow_word_wen_d = narrow_req_i.valid && narrow_req_bank_sel == b && narrow_req_wide_word_sel == w && narrow_req_narrow_word_sel == n;

        if (UseLatches) begin : gen_latches
          logic clk_w;

          tc_clk_gating i_clk_gate (
            .clk_i     ( clk_i                                ),
            .en_i      ( wide_word_wen_d || narrow_word_wen_d ),
            .test_en_i ( 1'b0                                 ),
            .clk_o     ( clk_w                                )
          );

          always_latch begin : word
            if (clk_w) begin
              mem_q[b][w][n] = wdata_q[n];
            end
          end

        end else begin : gen_flops
          always_ff @(posedge clk_i or negedge rst_ni) begin : word
            if (~rst_ni) begin
              mem_q[b][w][n] <= '0;
            end else begin
              if (wide_word_wen_d) begin
                mem_q[b][w][n] <= wide_wdata_i[NarrowWordWidth*n+:NarrowWordWidth];
              end else if (narrow_word_wen_d) begin
                mem_q[b][w][n] <= narrow_req_i.wdata;
              end
            end
          end
        end
      end
    end
  end

endmodule