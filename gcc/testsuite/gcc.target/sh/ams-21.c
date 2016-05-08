/* Check that the sts.l macl instruction is generated.  
   This is similar to the "sts.l fpul" cases.  */

/* { dg-do compile }  */
/* { dg-options "-O2" } */
/* { dg-final { scan-assembler-not "sts\tmacl" } } */
/* { dg-final { scan-assembler-not "mov.l" } } */
/* { dg-final { scan-assembler-times "sts.l\tmacl" 4 } } */

void
test_0 (int* out, int a, int b)
{
  out[0] = a * b;
}

void
test_1 (int* out, int a, int b)
{
  *--out = a * b;
}

void
test_2 (int* out, int a, int b, int c)
{
  out[1] = a * c;
  out[0] = a * b;
}

void
test_3 (int* out, int a, int b, int c)
{
  /* AMS should reorder the stores (and inherently the calculations)
     somehow.  */
  out[0] = a * b;
  out[1] = a * c;
}
