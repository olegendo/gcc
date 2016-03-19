/* Check that AMS does not un-CSE.  */

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "shll2" 1 } }  */

unsigned int
test_00 (unsigned int* x, unsigned int* y, int i)
{
  return (x[i + 0] - y[i + 0] - x[i + 4] -  y[i + 4]) - i*4;
}
