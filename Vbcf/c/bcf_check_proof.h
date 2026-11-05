/*
 * BCF's entry point, `bcf_check_proof`, on top of the verified checker.
 * Include after vbcf.c.  This wrapper is the only hand-written C between the
 * kernel and the printed checker, and it is trusted: it views the
 * verifier's `struct bcf_expr` array as the 32-bit words of its wire format
 * (as `copy_from_bpfptr` does for the proof), ignores the logger, and turns
 * the checker's error number into the negative errno BCF returns.
 */
int bcf_check_proof(struct bcf_expr *goal_exprs, u32 goal, bpfptr_t proof,
		    u32 proof_size, bcf_logger_cb logger, u32 level,
		    void *private)
{
	return -(int)vbcf_check_proof((u32 *)goal_exprs, goal, proof,
				      proof_size);
}
