/* Check that AMS does not un-CSE address register related calculations.
   Also, in this particular case, using (reg + reg) mode is a little bit
   better than post inc, because the loads can be done earlier.

	shll2	r6			shll2	r6
	mov	r6,r0			add	r6,r5
	mov.l	@(r0,r5),r3		add	r6,r4
	mov.l	@(r0,r4),r1		mov.l	@r5+,r3
	add	#16,r0			mov.l	@r4+,r1
	sub	r3,r1			sub	r3,r1
	mov.l	@(r0,r4),r3		mov.l	@r4,r3
	mov.l	@(r0,r5),r2		mov.l	@r5,r2
	....
*/

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "shll2" 1 } }  */
/* { dg-final { scan-assembler-not "mov.l\t@r\[0-9]\+\\+" } }  */
/* { dg-final { scan-assembler-times "mov.l\t@\\(r0,r\[0-9]\+\\)" 4 } }  */

unsigned int
test_00 (unsigned int* x, unsigned int* y, int i)
{
  return (x[i + 0] - y[i + 0] - x[i + 4] -  y[i + 4]) - i*4;
}
