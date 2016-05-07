/* Check that the sts.l fpul instruction is generated.
   We expect something like this:

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

/* { dg-do compile { target { any_fpu } } }  */
/* { dg-options "-O2" } */
/* { dg-final { scan-assembler-not "sts\tfpul" } } */
/* { dg-final { scan-assembler-not "mov.l" } } */
/* { dg-final { scan-assembler-times "sts.l\tfpul" 4 } } */

void
test (float* in, int* out)
{
  out[3] = (int)in[0];
  out[2] = (int)in[1];
  out[1] = (int)in[2];
  out[0] = (int)in[3];
}
