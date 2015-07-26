/* A minimal solution for this displacement fitting problem:
	mov.w	.L4,r2		// 912
	mov.l	.L3,r1		// 12123
	add	r2,r5
	mov.l	r1,@(24,r5)
	mov.w	.L5,r0		// 1160-912=248
	mov.l	r1,@(r0,r5)
	mov.l	r1,@(32,r5)
	mov.l	r1,@r5
.L3:
	.short 12123
.L4:
	.short 912
.L5:
	.short 248
	
     If constant optimization is done after AMS and constants are calculated
     it can be improved further:
	mov.w	.L4,r0		// 912
	mov.l	.L3,r1		// 12123
	add	r0,r5
	mov.l	r1,@(24,r5)
	shlr2	r0
	mov.l	r1,@(32,r5)
	add	#20,r0
	mov.l	r1,@r5
	mov.l	r1,@(r0,r5)
.L3:
	.short 12123
.L4:
	.short 912
	
     On SH2A it should look like:
	movi20	#12123,r1
	movi20	#912,r2
	add	r2,r5
	mov.l	r1,@(24,r5)
	mov.l	r1,@(248,r5)
	mov.l	r1,@(32,r5)
	mov.l	r1,@r5
*/

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(24,r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(32,r\[0-9]\+" 1 } }  */

/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(r0,r\[0-9]\+" 1 { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(248,r\[0-9]\+" 1 { target { sh2a } } } }  */

void
fun (int i, int* a)
{
  i = 234;		/* 936	+24  */
  a[i] = 12123;

  i = 290;		/* 1160 +248  */
  a[i] = 12123;

  i = 236;		/* 944	+32  */
  a[i] = 12123;

  i = 228;		/* 912	+0  */
  a[i] = 12123;
}