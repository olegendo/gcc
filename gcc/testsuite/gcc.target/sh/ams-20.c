/* Check that the sts.l fpul instruction is generated.  */

/* { dg-do compile { target { any_fpu } } }  */
/* { dg-options "-O2" } */
/* { dg-final { scan-assembler-not "sts\tfpul" } } */
/* { dg-final { scan-assembler-not "mov.l" } } */
/* { dg-final { scan-assembler-times "sts.l\tfpul" 2 } } */

void
test_0 (float x, int* out)
{
  /* This one is rather easy, as there are pre-dec modes for normal SImode
     stores and for FPUL regs.  */
  *--out = (int)x;
}

void
test_1 (float x, int* out)
{
  /* This one is a bit more difficult.  We expect something like this:
	ftrc	fr5,fpul
	add	#4,r4
	rts
	sts.l	fpul,@-r4

     To get there, AMS must somehow see that FPUL will be used as the
     source operand of the store.  Or at least the AMS delegate has to
     see that and somehow make AMS select the pre-dec alternative
     (either bias the cost or put it as the sole alternative).

     The delegate could trace back SImode stores and see if they came from
     an ftrc insn.  But that'd tax all SImode stores.
     Alternatively, the FPUL could be preallocated and propagated into the
     SImode store.  For that it might actually be a good idea to make FPUL
     a fixed hard reg as opposed to allocatable reg.  */

  *out = (int)x;
}
