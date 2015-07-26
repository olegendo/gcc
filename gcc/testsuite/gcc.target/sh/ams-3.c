/* On non-SH2A expect something like this
	mov	#72,r0
	mov.b	@(r0,r4),r2
	mov	#4,r1
	cmp/gt	r1,r2
	rts	
	movt	r0

     On SH2A it will be something like this
	mov.b	@(72,r4),r4
	mov	#4,r1
	cmp/gt	r1,r4
	rts	
	movt	r0
*/

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov\t#72,r0" 1 { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-times "mov.b\t@\\(r0,r\[0-9]\+" 1 { target { ! sh2a } } } }  */

/* { dg-final { scan-assembler-times "mov.b\t@\\(72,r\[0-9]\+" 1 { target { sh2a } } } }  */

int
fun (char* x)
{
  int xx = x[72];
  return xx > 4;
}