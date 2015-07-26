/*  The following cases should all result in the following loads
	mov.l	@r4
	mov.l	@(4,r4)
	mov.l	@(8,r4)
	mov.l	@(12,r4)

    Displacement fitting should find the appropriate base address register
    offset.
*/

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.l\t@r\[0-9]\+" 3 } }  */
/* { dg-final { scan-assembler-times "mov.l\t@\\(4,r\[0-9]\+" 3 } }  */
/* { dg-final { scan-assembler-times "mov.l\t@\\(8,r\[0-9]\+" 3 } }  */
/* { dg-final { scan-assembler-times "mov.l\t@\\(12,r\[0-9]\+" 3 } }  */

int
fun_0 (int* x)
{
  return x[0] + x[1] + x[2] + x[3];
}

int
fun_1 (int* x)
{
  x += 50;
  return x[0] + x[1] + x[2] + x[3];
}

int
fun_2 (int* x)
{
  x += 155;
  return x[0] + x[1] + x[2] + x[3];
}