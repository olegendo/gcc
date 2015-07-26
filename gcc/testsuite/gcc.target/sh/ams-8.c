/* { dg-do compile }  */
/* { dg-options "-O2" }  */

void
fun (int* arr1, unsigned int index, int* arr2)
{
  arr1[index*3+1] = 10;
  arr2[index*3+2] = 10;

  /* Expected:
  	mov	r5,r1
	add	r1,r1
	add	r1,r5
	mov	r5,r1
	shll2	r1
	mov	#10,r2
	add	r1,r4
	mov.l	r2,@(4,r4)
	add	r1,r6
	rts	
	mov.l	r2,@(8,r6)
  */

  /* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(4,r\[0-9]\+" 1 } }  */
  /* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(8,r\[0-9]\+" 1 } }  */
  /* { dg-final { scan-assembler-times "shll2" 1 } }  */
  /* { dg-final { scan-assembler-times "add\tr\[0-9]\+,r\[0-9]\+" 4 } }  */
}