// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_broker
  import auteur_pkg::*;
#(
  parameter int unsigned  WriteAddrWidth = 1,
  parameter int unsigned  ReadAddrWidth = 1,
  parameter int unsigned  GroupIdWidth = 1,
  parameter int unsigned  WriteDataWidth = 1,
  parameter int unsigned  ReadDataWidth = 1,
  parameter int unsigned  InputBufferDataWidth = 1,
  parameter int unsigned  OutputBufferDataWidth = 1,

  parameter int unsigned  GroupSizeX = 1,
  parameter int unsigned  GroupSizeW = 1,
  parameter int unsigned  IntercoWidth = 1,

  parameter int unsigned  InputBufferAddrWidth  = 1,
  parameter int unsigned  OutputBufferAddrWidth = 1,

  parameter bit           OutputBufferSplitReadWrite = 0,

  localparam int unsigned NrOutputBufferChannels = OutputBufferSplitReadWrite ? 2 : 1,

  localparam int unsigned NrOutputBuffersW = GroupSizeW / IntercoWidth,

  localparam int unsigned NrInputBufferReqs = WriteDataWidth / InputBufferDataWidth <= (GroupSizeX + GroupSizeW) ? WriteDataWidth / InputBufferDataWidth : (GroupSizeX + GroupSizeW),

  localparam int unsigned NrOutputBufferWriteReqs = WriteDataWidth / OutputBufferDataWidth <= GroupSizeX * NrOutputBuffersW ? WriteDataWidth / OutputBufferDataWidth : GroupSizeX * NrOutputBuffersW,
  localparam int unsigned NrOutputBufferReadReqs = ReadDataWidth / OutputBufferDataWidth <= GroupSizeX * NrOutputBuffersW ?  WriteDataWidth / OutputBufferDataWidth : GroupSizeX * NrOutputBuffersW,
  localparam int unsigned NrOutputBufferReqs = NrOutputBufferWriteReqs > NrOutputBufferReadReqs ? NrOutputBufferWriteReqs : NrOutputBufferReadReqs,

  localparam int unsigned NrInputBufferBundles = (GroupSizeX + GroupSizeW) / NrInputBufferReqs,
  localparam int unsigned NrOutputBufferBundles = GroupSizeX * NrOutputBuffersW / NrOutputBufferReqs,

  localparam type input_buffer_req_t = struct packed {
    logic                            valid;
    logic [InputBufferAddrWidth-1:0] addr;
    logic [InputBufferDataWidth-1:0] wdata;
  },

  localparam type output_buffer_req_t = struct packed {
    logic                             valid;
    logic [OutputBufferAddrWidth-1:0] addr;
    logic                             we;
    logic [OutputBufferDataWidth-1:0] wdata;
  },

  localparam type output_buffer_rsp_t = struct packed {
    logic                             valid;
    logic [OutputBufferDataWidth-1:0] rdata;
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
  input  logic                                                                                               clk_i,
  input  logic                                                                                               rst_ni,
  input  logic [GroupIdWidth-1:0]                                                                            group_id_i,

  input  write_req_t                                                                                         write_req_i,
  output write_req_t                                                                                         write_req_o,

  input  read_req_t                                                                                          read_req_i,
  output read_req_t                                                                                          read_req_o,
  output read_rsp_t                                                                                          read_rsp_o,
  input  read_rsp_t                                                                                          read_rsp_i,

  output input_buffer_req_t [NrInputBufferBundles-1:0][NrInputBufferReqs-1:0]                                input_buffer_req_o,

  output output_buffer_req_t [NrOutputBufferBundles-1:0][NrOutputBufferReqs-1:0][NrOutputBufferChannels-1:0] output_buffer_req_o,
  input  output_buffer_rsp_t [NrOutputBufferBundles-1:0][NrOutputBufferReqs-1:0][NrOutputBufferChannels-1:0] output_buffer_rsp_i
);

  // If WriteDataWidth =/= ReadDataWidth, read or write requests may not fill an entire bundle
  localparam int unsigned OutputBufferWriteSelWidth = $clog2(NrOutputBufferWriteReqs/NrOutputBufferReqs);
  localparam int unsigned OutputBufferReadSelWidth = $clog2(NrOutputBufferReadReqs/NrOutputBufferReqs);

  logic write_is_local;

  assign write_is_local = write_req_i.valid && write_req_i.addr[WriteAddrWidth-1-:GroupIdWidth] == group_id_i;

  write_req_t write_req_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : write_req_resiter
    if (~rst_ni) begin
      write_req_q <= '0;
    end else begin
      if (~write_is_local) begin
        write_req_q <= write_req_i;
      end else if (write_req_q.valid) begin
        write_req_q.valid <= 1'b0;
      end
    end
  end

  assign write_req_o = write_req_q;


  logic read_is_local;

  assign read_is_local = read_req_i.valid && read_req_i.addr[ReadAddrWidth-1-:GroupIdWidth] == group_id_i;

  read_req_t read_req_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : read_req_resiter
    if (~rst_ni) begin
      read_req_q <= '0;
    end else begin
      if (~read_is_local) begin
        read_req_q <= read_req_i;
      end else if (read_req_q.valid) begin
        read_req_q.valid <= 1'b0;
      end
    end
  end

  assign read_req_o = read_req_q;


  read_rsp_t read_rsp_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : read_rsp_resiter
    if (~rst_ni) begin
      read_rsp_q <= '0;
    end else begin
      if (read_rsp_i.valid) begin
        read_rsp_q <= read_rsp_i;
      end else if (read_rsp_q.valid) begin
        read_rsp_q.valid <= 1'b0;
      end
    end
  end

  // Local requests generation
  always_comb begin : local_requests_assignment
    input_buffer_req_o   = '0;
    output_buffer_req_o  = '0;

    if (write_req_i.valid) begin
      if (write_req_i.addr[WriteAddrWidth-GroupIdWidth-1]) begin
        // Output Buffers
        int unsigned bundle_sel, write_sel;

        if (NrOutputBufferBundles != 1) begin
          bundle_sel = write_req_i.addr[OutputBufferAddrWidth+OutputBufferWriteSelWidth+:$clog2(NrOutputBufferBundles)];
        end else begin
          bundle_sel = 0;
        end

        if (OutputBufferWriteSelWidth != 0) begin
          write_sel = write_req_i.addr[OutputBufferAddrWidth+:OutputBufferWriteSelWidth];
        end else begin
          write_sel = 0;
        end

        for (int unsigned i = 0; i < NrOutputBufferReqs; i++) begin
          // Only assert selected requests if the write channel is narrower than the read channel
          if (i/NrOutputBufferWriteReqs == write_sel) begin
            // Writes are always performed on channel 0
            output_buffer_req_o[bundle_sel][i][0] = '{
              valid: write_req_i.valid,
              addr:  write_req_i.addr[OutputBufferAddrWidth-1:0],
              we:    1'b1,
              wdata: write_req_i.wdata[i*OutputBufferDataWidth+:OutputBufferDataWidth]
            };
          end
        end
      end else begin
        // Input Buffers
        int unsigned bundle_sel;

        if (NrInputBufferBundles != 1) begin
          bundle_sel = write_req_i.addr[InputBufferAddrWidth+:$clog2(NrInputBufferBundles)];
        end else begin
          bundle_sel = 0;
        end

        for (int unsigned i = 0; i < NrInputBufferReqs; i++) begin
          input_buffer_req_o[bundle_sel][i] = '{
            valid: write_req_i.valid,
            addr:  write_req_i.addr[InputBufferAddrWidth-1:0],
            wdata: write_req_i.wdata[i*InputBufferDataWidth+:InputBufferDataWidth]
          };
        end
      end
    end

    if (read_req_i.valid) begin
      // Output Buffer
      int unsigned bundle_sel, read_sel;

      if (NrOutputBufferBundles != 1) begin
        bundle_sel = read_req_i.addr[OutputBufferAddrWidth+OutputBufferReadSelWidth+:$clog2(NrOutputBufferBundles)];
      end else begin
        bundle_sel = 0;
      end

      if (OutputBufferReadSelWidth != 0) begin
        read_sel = read_req_i.addr[OutputBufferAddrWidth+:OutputBufferReadSelWidth];
      end else begin
        read_sel = 0;
      end

      for (int unsigned i = 0; i < NrOutputBufferReqs; i++) begin
        // Only assert selected requests if the read channel is narrower than the write channel
        if (i/NrOutputBufferReadReqs == read_sel) begin
          // Reads can either be performed on channel 1 or 0, depending on whether the OutputBufferSplitReadWrite parameter is 1 or 0
          output_buffer_req_o[bundle_sel][i][NrOutputBufferChannels-1] = '{
            valid: read_req_i.valid,
            addr:  read_req_i.addr[OutputBufferAddrWidth-1:0],
            we:    1'b0,
            wdata: '0
          };
        end
      end
    end
  end

  // Local responses handling
  read_rsp_t local_rsp;

  always_comb begin : local_response_assignment
    logic [ReadDataWidth-1:0] rsp_rdata;

    local_rsp = '0;
    rsp_rdata = '0;

    for (int unsigned i = 0; i < NrOutputBufferBundles; i++) begin
      // We have to check for valid responses like this since reads may not fill a bundle
      for (int unsigned s = 0; s < NrOutputBufferReqs; s += NrOutputBufferReadReqs) begin
        if (output_buffer_rsp_i[i][s][NrOutputBufferChannels-1].valid) begin
          for (int unsigned r = 0; r < NrOutputBufferReadReqs; r++) begin
            rsp_rdata[r*OutputBufferDataWidth+:OutputBufferDataWidth] = output_buffer_rsp_i[i][s+r][NrOutputBufferChannels-1].rdata;
          end

          local_rsp = '{
            valid: output_buffer_rsp_i[i][s][NrOutputBufferChannels-1].valid,
            rdata: rsp_rdata
          };
        end
      end
    end
  end

  assign read_rsp_o = local_rsp | read_rsp_q;
endmodule