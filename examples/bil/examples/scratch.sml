EVAL ``1c <> 2c``;

(SIMP_CONV (srw_ss()) [n2b_def] ``1c <> 2c``);

strip_comb ``1c``;

strip_comb ``1c <> 2c``;

prove (``1c <> 2c``,
       (FULL_SIMP_TAC (srw_ss()) [n2b_8_def, n2bs_def])


SIMP_CONV (bool_ss) [n2b_8_def] ``1c``;
