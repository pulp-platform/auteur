// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

package auteur_pkg;
  typedef struct {
    struct {
      struct {
        int unsigned inputs;
        int unsigned input_products;
        int unsigned scale_input_products;
      } mantissa_path;

      struct {
        int unsigned inputs;
        int unsigned input_products;
        int unsigned maximum_exponent;
        int unsigned final_shifts;
      } exponent_path;
    } input_path;

    struct {
      struct {
        int unsigned inputs;
        int unsigned scale_product;
      } mantissa_path;

      struct {
        int unsigned inputs;
        int unsigned scale_product;
      } exponent_path;
    } scale_path;

    int unsigned accumulation;
    int unsigned normalization;
  } dotp_pipe_cfg_t;

  function automatic int unsigned get_input_mant_delay(input dotp_pipe_cfg_t cfg);
    int unsigned delay = 0;

    delay += cfg.input_path.mantissa_path.inputs;
    delay += cfg.input_path.mantissa_path.input_products;
    delay += cfg.input_path.mantissa_path.scale_input_products;

    return delay;
  endfunction

  function automatic int unsigned get_input_exp_delay(input dotp_pipe_cfg_t cfg);
    int unsigned delay = 0;

    delay += cfg.input_path.exponent_path.inputs;
    delay += cfg.input_path.exponent_path.input_products;
    delay += cfg.input_path.exponent_path.maximum_exponent;
    delay += cfg.input_path.exponent_path.final_shifts;

    return delay;
  endfunction

  function automatic int unsigned get_max_exp_delay(input dotp_pipe_cfg_t cfg);
    int unsigned delay = 0;

    delay += get_exp_mant_input_margin(cfg);
    delay += cfg.input_path.exponent_path.inputs;
    delay += cfg.input_path.exponent_path.input_products;
    delay += cfg.input_path.exponent_path.maximum_exponent;

    return delay;
  endfunction

  function automatic int unsigned get_exp_overflow_delay(input dotp_pipe_cfg_t cfg);
    int unsigned delay = 0;

    delay += cfg.input_path.exponent_path.maximum_exponent;
    delay += cfg.input_path.exponent_path.final_shifts;
    delay += cfg.accumulation;

    return delay;
  endfunction

  function automatic int unsigned get_mant_scales_inputs_margin(input dotp_pipe_cfg_t cfg);
    return cfg.input_path.mantissa_path.inputs + cfg.input_path.mantissa_path.input_products
         - cfg.scale_path.mantissa_path.inputs - cfg.scale_path.mantissa_path.scale_product;
  endfunction

  function automatic int unsigned get_exp_scales_inputs_margin(input dotp_pipe_cfg_t cfg);
    return get_exp_mant_input_margin(cfg) + cfg.input_path.exponent_path.inputs + cfg.input_path.exponent_path.input_products
         - cfg.scale_path.exponent_path.inputs - cfg.scale_path.exponent_path.scale_product;
  endfunction

  function automatic int unsigned get_exp_mant_input_margin(input dotp_pipe_cfg_t cfg);
    return get_input_mant_delay(cfg) - get_input_exp_delay(cfg);
  endfunction

  function automatic int unsigned get_max_join_width(input int unsigned i, input int unsigned max_width);
    int unsigned res   = 1;
    int unsigned width = 2;

    while ((i+1) % width == 0 && width <= max_width) begin
      res   = res << 1;
      width = width << 1;
    end

    return res;
  endfunction
endpackage