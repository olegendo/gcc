/* Check that the sts.l fpul instruction is generated.

   This might need some more parameters (compiler options) to control the
   behavior.
   For example, the original SH4 implementation has a pipeline exception:
	When a single-precision FTRC instruction is followed by
	an STS FPUL, Rn instruction, the latency of the FTRC instruction is
	1 cycle (as opposed to 3/4 cycles normally).

  Moreover, the "sts fpul,Rn" and "ftrc" instructions can be exectued in
  parallel, while "sts.l fpul" does not qualify for parallel execution.

  However, on other SH implementations it might be better to use the sts.l
  alternative, at least to conserve code size.  */

/* { dg-do compile { target { any_fpu } } }  */
/* { dg-options "-O2" } */
/* { dg-final { scan-assembler-not "sts\tfpul" } } */
/* { dg-final { scan-assembler-not "mov.l" } } */
/* { dg-final { scan-assembler-times "sts.l\tfpul" 8 } } */

void
test_0 (float* in, int* out)
{
  /* Expected:
  	add	#16,r5
	fmov.s	@r4+,fr1
	fmov.s	@r4+,fr0
	ftrc	fr1,fpul
	fmov.s	@r4+,fr2
	sts.l	fpul,@-r5
	ftrc	fr0,fpul
	fmov.s	@r4,fr3
	sts.l	fpul,@-r5
	ftrc	fr2,fpul
	sts.l	fpul,@-r5
	ftrc	fr3,fpul
	rts
	sts.l	fpul,@-r5
  */
  out[3] = (int)in[0];
  out[2] = (int)in[1];
  out[1] = (int)in[2];
  out[0] = (int)in[3];
}

void
test_1 (float* in, int* out)
{
  /* AMS should be able to reorder the stores.  This will also require
     some insn reordering for the calculations, to utilize the fpul register
     effectively.  Expected:
	fmov.s	@r4+,fr0
	fmov.s	@r4+,fr1
	fmov.s	@r4+,fr2
	fmov.s	@r4+,fr3
	add	#16,r5
	ftrc	fr3,fpul
	sts.l	fpul,@-r5
	ftrc	fr2,fpul
	sts.l	fpul,@-r5
	ftrc	fr1,fpul
	sts.l	fpul,@-r5
	ftrc	fr0,fpul
	rts
	sts.l	fpul,@-r5
  */
  out[0] = (int)in[0];
  out[1] = (int)in[1];
  out[2] = (int)in[2];
  out[3] = (int)in[3];
}

