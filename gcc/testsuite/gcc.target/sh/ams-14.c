/* Check that AMS can deal with different interleaved access sequences.  */
/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.\[bwl]\tr\[0-9]\+,@\\(\[0-9]\+" 2 } }  */
/* { dg-final { scan-assembler-times "mov.\[bwl]\t@r\[0-9]\+\\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.\[bwl]\tr\[0-9]\+,@-r\[0-9]\+" 5 } }  */

int
fun_0 (int* arr1, int index, int* arr2)
{
  arr1[index+1] = 10;
  *--arr2 = 30;
  arr1[index+2] = 20;
  *--arr2 = 40;
  
  /* Expect something like
	shll2	r5
	add	r5,r4
	mov	#10,r1
	mov.l	r1,@(4,r4)
	mov	#30,r1
	mov.l	r1,@-r6
	mov	#20,r1
	mov.l	r1,@(8,r4)
	mov	#40,r1
	rts	
	mov.l	r1,@-r6
  */
}

void
fun_1 (short* arr1, int index, short* arr2)
{
  int a = arr1[0];
  arr2[-1] = 0;
  int b = arr1[1];
  arr2[-2] = 0;
  
  arr2[-3] = a + b;
  
  /* Expect something like
	mov.w	@r4+,r3
	mov	#0,r2
	mov.w	r2,@-r6
	mov.w	@r4,r1
	mov.w	r2,@-r6
	add	r3,r1
	rts	
	mov.w	r1,@-r6
  */
}