// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`define AUTEUR_PIPE(__pipe_name, __depth, __dtype, __data_in, __data_out, __valid)                                  \
  typedef __dtype __pipe_name``_stages_t;                                                                           \
  __pipe_name``_stages_t [__depth:0] __pipe_name``_stages;                                                          \
  logic [__depth:0] __pipe_name``_stages_valid;                                                                     \
  for (genvar __pipe_name``_iter = 0; __pipe_name``_iter < __depth; __pipe_name``_iter++) begin : gen_``__pipe_name \
    always_ff @(posedge clk_i or negedge rst_ni) begin                                                              \
      if (~rst_ni) begin                                                                                            \
        __pipe_name``_stages[__pipe_name``_iter+1]       <= __pipe_name``_stages_t'('0);                            \
        __pipe_name``_stages_valid[__pipe_name``_iter+1] <= '0;                                                     \
      end else begin                                                                                                \
        if (__pipe_name``_stages_valid[__pipe_name``_iter]) begin                                                   \
          __pipe_name``_stages[__pipe_name``_iter+1] <= __pipe_name``_stages[__pipe_name``_iter];                   \
        end                                                                                                         \
        __pipe_name``_stages_valid[__pipe_name``_iter+1] <= __pipe_name``_stages_valid[__pipe_name``_iter];         \
      end                                                                                                           \
    end                                                                                                             \
  end                                                                                                               \
  assign __pipe_name``_stages[0]       = __data_in;                                                                 \
  assign __pipe_name``_stages_valid[0] = __valid;                                                                   \
  assign __data_out                    = __pipe_name``_stages[__depth];

`define AUTEUR_PIPE_VALID(__pipe_name, __depth, __valid_in, __valid_out)                                            \
  logic [__depth:0] __pipe_name``_stages;                                                                           \
  for (genvar __pipe_name``_iter = 0; __pipe_name``_iter < __depth; __pipe_name``_iter++) begin : gen_``__pipe_name \
    always_ff @(posedge clk_i or negedge rst_ni) begin                                                              \
      if (~rst_ni) begin                                                                                            \
        __pipe_name``_stages[__pipe_name``_iter+1] <= 1'b0;                                                         \
      end else begin                                                                                                \
        __pipe_name``_stages[__pipe_name``_iter+1] <= __pipe_name``_stages[__pipe_name``_iter];                     \
      end                                                                                                           \
    end                                                                                                             \
  end                                                                                                               \
  assign __pipe_name``_stages[0]       = __valid_in;                                                                \
  assign __valid_out                   = __pipe_name``_stages[__depth];

`define AUTEUR_FIFO(__fifo_name, __depth, __dtype, __data_in, __data_out, __push, __pop)  \
  if (__depth == 0) begin : gen_no_``__fifo_name                                          \
    assign __data_out = __data_in;                                                        \
  end else begin : gen_``__fifo_name                                                      \
    auteur_fifo #(                                                                        \
      .DEPTH (__depth),                                                                   \
      .dtype (__dtype)                                                                    \
    ) __fifo_name (                                                                       \
      .clk_i,                                                                             \
      .rst_ni,                                                                            \
      .flush_i (1'b0),                                                                    \
      .data_i (__data_in),                                                                \
      .push_i (__push),                                                                   \
      .data_o (__data_out),                                                               \
      .pop_i (__pop)                                                                      \
    );                                                                                    \
  end
