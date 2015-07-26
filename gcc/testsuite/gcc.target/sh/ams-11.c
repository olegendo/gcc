/* On non-SH2A the expected handling of outliers in access sequences is
   to use reg+reg modes with a constant load.
   On SH2A the FPU load with displacement can be used.  However, because it's
   a 4 byte insn the other loads should be done with a post-inc.
   We expect to see something like this
	mov.w	.L2,r0
	fmov.s	@r5+,fr0
	fmov.s	@(r0,r5),fr1
	fadd	fr1,fr0
	fmov.s	@r5,fr1
	rts	
	fadd	fr1,fr0
	.align 1
.L2:
	.short	396
*/

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "fmov.s\t@\\(r0,r\[0-9]\+" 1 { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-not "fmov.s\t@\\(r0,r\[0-9]\+" { target { sh2a } } } }  */

/* { dg-final { scan-assembler-times "fmov.s\t@r\[0-9]\+\\+,fr" 1 } }  */
/* { dg-final { scan-assembler-times "fmov.s\t@r\[0-9]\+,fr" 1 } }  */

float
fun_0 (int i, float* a)
{
  return a[0] + a[100] + a[1];
}