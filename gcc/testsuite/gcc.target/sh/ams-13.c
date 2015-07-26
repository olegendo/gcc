/* { dg-do compile }  */
/* { dg-options "-O2" }  */

char*
fun_0 (char* p)
{
  *--p = 1;
  *--p = 1;
  return p;

  /* Expect something like
	mov	#1,r1
	mov.b	r1,@-r4
	mov	r4,r0
	rts	
	mov.b	r1,@-r0
  */

/* { dg-final { scan-assembler-times "mov.b\tr\[0-9]\+,@-r\[0-9]\+" 2 } }  */
/* { dg-final { scan-assembler-not "add" } }  */
}