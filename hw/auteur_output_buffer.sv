// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module auteur_output_buffer #(
  parameter int unsigned DataWidth = 32,
  parameter int unsigned ByteWidth = 8,
  parameter int unsigned Depth = 1,
  parameter int unsigned NrBanks = 2,
  parameter int unsigned BankAddrStart = 1,
  parameter int unsigned NrPorts = NrBanks,

  localparam int unsigned AddrWidth = Depth > 1 ? $clog2(Depth) : 1,

  localparam type req_t = struct packed {
    logic                 valid;
    logic [AddrWidth-1:0] addr;
    logic                 we;
    logic [DataWidth-1:0] wdata;
  },

  localparam type rsp_t = struct packed {
    logic                 valid;
    logic [DataWidth-1:0] rdata;
  }
) (
  input  logic               clk_i,
  input  logic               rst_ni,
  input  req_t [NrPorts-1:0] req_i,
  output rsp_t [NrPorts-1:0] rsp_o
);
  localparam int unsigned BankAddrWidth = Depth/NrBanks > 1 ? $clog2(Depth/NrBanks) : 1;
  localparam int unsigned BankSelWidth  = NrBanks > 1 ? $clog2(NrBanks) : 1;
  localparam int unsigned WinnerWidth   = NrPorts > 1 ? $clog2(NrPorts) : 1;

  logic [NrPorts-1:0][BankSelWidth-1:0] bank_sel_d, bank_sel_q;
  logic [NrPorts-1:0]                   req_valid_d, req_valid_q;
  logic [NrBanks-1:0][WinnerWidth-1:0]  winner;

  logic [NrPorts-1:0][BankAddrWidth-1:0] bank_addr;
  logic [NrBanks-1:0][DataWidth-1:0]     bank_rdata;

  for (genvar i = 0; i < NrPorts; i++) begin : gen_bank_selection
    if (BankAddrStart == BankSelWidth) begin
      assign bank_sel_d[i] = req_i[i].addr[BankAddrStart-1:0];
    end else if (BankAddrStart == 0) begin
      assign bank_sel_d[i] = req_i[i].addr[AddrWidth-1-:BankSelWidth];
    end else begin
      assign bank_sel_d[i] = {req_i[i].addr[AddrWidth-1-:BankSelWidth-BankAddrStart], req_i[i].addr[BankAddrStart-1:0]};
    end

    assign bank_addr[i] = req_i[i].addr[BankAddrStart+:BankAddrWidth];

    // Only register read transactions
    assign req_valid_d[i] = req_i[i].valid && ~req_i[i].we;

    always_ff @(posedge clk_i or negedge rst_ni) begin : track_selected_bank
      if (~rst_ni) begin
        bank_sel_q[i] <= '0;
      end else begin
        bank_sel_q[i] <= bank_sel_d[i];
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : track_req_valid
      if (~rst_ni) begin
        req_valid_q[i] <= 1'b0;
      end else begin
        req_valid_q[i] <= req_valid_d[i];
      end
    end
  end

  for (genvar i = 0; i < NrPorts; i++) begin : assign_rsp
    assign rsp_o[i].valid = req_valid_q[i];
    assign rsp_o[i].rdata = bank_rdata[bank_sel_q[i]];
  end

  for (genvar b = 0; b < NrBanks; b++) begin : gen_banks
    logic [NrPorts-1:0] bank_req;
    logic               req_valid;

    for (genvar i = 0; i < NrPorts; i++) begin : assign_bank_req
      assign bank_req[i] = bank_sel_d[i] == b && req_i[i].valid;
    end

    always_comb begin : arbiter
      winner[b] = 0;
      req_valid = 1'b0;

      for (int unsigned i = 0; i < NrPorts; i++) begin
        if (bank_req[i]) begin
          winner[b] = i;
          req_valid = 1'b1;
          break;
        end
      end
    end

    tc_sram_impl #(
      .NumWords (Depth/NrBanks),
      .DataWidth (DataWidth),
      .ByteWidth (ByteWidth),
      .NumPorts (1),
      .Latency (1)
    ) i_bank (
      .clk_i (clk_i),
      .rst_ni (rst_ni),
      .impl_i (1'b0),
      .impl_o (),
      .req_i (req_i[winner[b]].valid && req_valid),
      .we_i (req_i[winner[b]].we),
      .addr_i (bank_addr[winner[b]]),
      .wdata_i (req_i[winner[b]].wdata),
      .be_i ('1),
      .rdata_o (bank_rdata[b])
    );
  end

endmodule