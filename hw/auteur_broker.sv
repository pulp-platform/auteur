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

  parameter int unsigned  GroupSizeX = 1,
  parameter int unsigned  GroupSizeW = 1,
  parameter int unsigned  IntercoWidth = 1,

  parameter int unsigned  InputBufferAddrWidth  = 1,
  parameter int unsigned  OutputBufferAddrWidth = 1,

  parameter int unsigned  NrOutputBufferReqs = 1,

  localparam int unsigned NrOutputBuffersW = GroupSizeW/IntercoWidth,

  localparam type input_buffer_req_t = struct packed {
    logic                            valid;
    logic [InputBufferAddrWidth-1:0] addr;
    logic [WriteDataWidth-1:0]       wdata;
  },

  localparam type output_buffer_req_t = struct packed {
    logic                             valid;
    logic [OutputBufferAddrWidth-1:0] addr;
    logic                             we;
    logic [WriteDataWidth-1:0]        wdata;
  },

  localparam type output_buffer_rsp_t = struct packed {
    logic                      valid;
    logic [WriteDataWidth-1:0] rdata;
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
  input  logic                                                                              clk_i,
  input  logic                                                                              rst_ni,
  input  logic [GroupIdWidth-1:0]                                                           group_id_i,

  input  write_req_t                                                                        write_req_i,
  output write_req_t                                                                        write_req_o,

  input  read_req_t                                                                         read_req_i,
  output read_req_t                                                                         read_req_o,
  output read_rsp_t                                                                         read_rsp_o,
  input  read_rsp_t                                                                         read_rsp_i,

  output input_buffer_req_t [GroupSizeX+GroupSizeW-1:0]                                     input_buffer_req_o,

  output output_buffer_req_t [GroupSizeX-1:0][NrOutputBuffersW-1:0][NrOutputBufferReqs-1:0] output_buffer_req_o,
  input  output_buffer_rsp_t [GroupSizeX-1:0][NrOutputBuffersW-1:0]                         output_buffer_rsp_i
);

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


  // Local request generation

  always_comb begin : local_requests_assignment
    input_buffer_req_o   = '0;
    output_buffer_req_o  = '0;

    if (write_req_i.valid) begin
      if (write_req_i.addr[WriteAddrWidth-GroupIdWidth-1]) begin
        // Output Buffer
        int unsigned x_sel, w_sel;

        if (GroupSizeX != 1) begin
          x_sel = write_req_i.addr[OutputBufferAddrWidth+$clog2(NrOutputBuffersW)+:$clog2(GroupSizeX)];
        end else begin
          x_sel = 0;
        end

        if (NrOutputBuffersW != 1) begin
          w_sel = write_req_i.addr[OutputBufferAddrWidth+:$clog2(NrOutputBuffersW)];
        end else begin
          w_sel = 0;
        end

        output_buffer_req_o[x_sel][w_sel][0] = '{
          valid: write_req_i.valid,
          addr:  write_req_i.addr[OutputBufferAddrWidth-1:0],
          we:    1'b1,
          wdata: write_req_i.wdata
        };
      end else begin
        // Input Buffer
        int unsigned buf_addr;

        buf_addr = write_req_i.addr[InputBufferAddrWidth+:$clog2(GroupSizeX+GroupSizeW)];

        input_buffer_req_o[buf_addr] = '{
          valid: write_req_i.valid,
          addr:  write_req_i.addr[InputBufferAddrWidth-1:0],
          wdata: write_req_i.wdata
        };
      end
    end

    if (read_req_i.valid) begin
      // Output Buffer
      int unsigned x_sel, w_sel;

      if (GroupSizeX != 1) begin
        x_sel = write_req_i.addr[OutputBufferAddrWidth+$clog2(NrOutputBuffersW)+:$clog2(GroupSizeX)];
      end else begin
        x_sel = 0;
      end

      if (NrOutputBuffersW != 1) begin
        w_sel = write_req_i.addr[OutputBufferAddrWidth+:$clog2(NrOutputBuffersW)];
      end else begin
        w_sel = 0;
      end

      output_buffer_req_o[x_sel][w_sel][NrOutputBufferReqs-1] = '{
        valid: read_req_i.valid,
        addr:  read_req_i.addr[OutputBufferAddrWidth-1:0],
        we:    1'b0,
        wdata: '0
      };
    end
  end

  // Local responses handling

  read_rsp_t local_rsp;

  always_comb begin : local_response_assignment
    local_rsp = '0;

    for (int unsigned x = 0; x < GroupSizeX; x++) begin
      for (int unsigned w = 0; w < NrOutputBuffersW; w++) begin
        if (output_buffer_rsp_i[x][w].valid) begin
          local_rsp = '{
            valid: output_buffer_rsp_i[x][w].valid,
            rdata: output_buffer_rsp_i[x][w].rdata
          };
        end
      end
    end
  end

  assign read_rsp_o = local_rsp | read_rsp_q;
endmodule