/* On non-SH2A expect something like this
  	mov.w	.L2,r0
	mov	#10,r1
	mov.l	r1,@(r0,r4)
	mov	#20,r1
	mov.w	.L3,r0
	rts	
	mov.l	r1,@(r0,r4)
	.align 1
.L2:
	.short	-512
.L3:
	.short	512

     This is already minimal, assuming that a constant optimization pass
     will convert the second constant load into a neg Rm,Rn insn.
     
     On SH2A it will be something like this
	mov	#10,r1
	movi20	#-512,r0
	mov.l	r1,@(r0,r4)
	mov	#20,r1
	mov.l	r1,@(512,r4)
	rts/n
*/

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(r0,r\[0-9]\+" 2 { target { ! sh2a } } } }  */

/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(r0,r\[0-9]\+" 1 { target { sh2a } } } }  */
/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(512,r\[0-9]\+" 1 { target { sh2a } } } }  */

void
fun (int* arr1)
{
  *(arr1 - 128) = 10;
  *(arr1 + 128) = 20;
}