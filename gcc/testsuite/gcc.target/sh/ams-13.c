/* { dg-do compile }  */
/* { dg-options "-O2" }  */
/* { dg-final { scan-assembler-times "mov.b\tr\[0-9]\+,@-r\[0-9]\+" 4 } }  */
/* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@-r\[0-9]\+" 4 } }  */
/* { dg-final { scan-assembler-not "add" } }  */

/* Expect something like
	mov	#1,r1
	mov.b	r1,@-r4
	mov	r4,r0
	rts	
	mov.b	r1,@-r0
*/

char*
fun_0 (char* p)
{
  *--p = 1;
  *--p = 1;
  return p;
}

char*
fun_1 (char* p)
{
  *(p - 1) = 1;
  *(p - 2) = 1;
  return p - 2;
}

int*
fun_2 (int* p)
{
  *--p = 1;
  *--p = 1;
  return p;
}

int*
fun_3 (int* p)
{
  *(p - 1) = 1;
  *(p - 2) = 1;
  return p - 2;
}
