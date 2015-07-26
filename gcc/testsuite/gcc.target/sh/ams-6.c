/* Expected non-SH2A:
	mov	#72,r0
	fmov.s	@r4,fr2
	fmov.s	@(r0,r4),fr1
	add	#68,r4
	add	#4,r5
	fadd	fr1,fr2
	fmov.s	fr2,@r4
	fmov.s	@r5,fr2
	add	#64,r5
	fadd	fr2,fr1
	fmov.s	fr1,@r5    11*2 = 22 bytes

   This can be further improved by correlating the different access sequences
   and using the difference of base registers as an offset and reordering
   accesses.

	mov	r5,r0
	sub	r4,r0		// r0 = r5 - r4
	fmov.s	@r4+,fr0	// load a[0]
	fmov.s	@(r0,r4),fr1	// load b[1]
	add	#68,r4
	fmov.s	@r4,fr2		// load a[18]
	fadd	fr2,fr0
	fadd	fr2,fr1
	fmov.s	fr0,@-r4	// store a[17]
	fmov.s	fr1,@(r0,r4)	// store b[17]    10*2 = 20 bytes
	
   On SH2A we can use FP loads/stores with displacement (4 byte insns):
	fmov.s	@(72,r4),fr1
	fmov.s	@r4,fr2
	fadd	fr1,fr2
	fmov.s	fr2,@(68,r4)
	fmov.s	@(4,r5),fr2
	fadd	fr2,fr1
	fmov.s	fr1,@(68,r5)   4*4 + 3*2 = 22 bytes
*/

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "fmov.s\t@r\[0-9]\+" 2 { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-times "fmov.s\t@\\(r0,r\[0-9]\+" 1 { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-times "fmov.s\tfr\[0-9]\+,@r\[0-9]\+" 2 { target { ! sh2a } } } }  */

/* { dg-final { scan-assembler-times "fmov.s\t@r\[0-9]\+" 1 { target { sh2a } } } }  */
/* { dg-final { scan-assembler-times "fmov.s\t@\\(72,r\[0-9]\+" 1 { target { sh2a } } } }  */
/* { dg-final { scan-assembler-times "fmov.s\t@\\(4,r\[0-9]\+" 1 { target { sh2a } } } }  */
/* { dg-final { scan-assembler-times "fmov.s\tfr\[0-9]\+,@\\(68,r\[0-9]\+" 2 { target { sh2a } } } }  */

void
fun (float* a, float* b)
{
  a[17] = a[0] + a[18];
  b[17] = b[1] + a[18];
}