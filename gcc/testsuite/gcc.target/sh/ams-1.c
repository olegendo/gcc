/* Expected code is something like this:
  	mov.l	@r5+,r0
	mov.l	@(60,r5),r1
	add	r1,r0
	mov.l	@r5+,r1
	add	r1,r0
	mov.l	@(60,r5),r1
	rts
	add	r1,r0
*/

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.l\t\@\\(60,r\[0-9]\+" 2 } }  */
/* { dg-final { scan-assembler-times "mov.l\t\@r\[0-9]\+\\+" 2 } }  */

int fun (int i, int* a)
{
  return a[0] + a[16] + a[1] + a[17];
}