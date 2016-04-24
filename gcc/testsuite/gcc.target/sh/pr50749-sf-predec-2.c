/* PR target/50749: Verify that subsequent pre-decrement addressings
   are generated.  */
/* { dg-do compile }  */
/* { dg-options "-O2" } */
/* { dg-skip-if "" { "sh*-*-*" } { "-m1" "-m2*" "-m4al" "*nofpu" "-m4-340*" "-m4-400*" "-m4-500*" "-m5*" } { "" } }  */
/* { dg-final { scan-assembler-times "fmov.s\tfr\[0-9]\+,@-r\[0-9]\+" 13 { xfail *-*-*} } } */

float*
test_func_00 (float* p, float c)
{
  *--p = c;
  *--p = c;
  return p;
}

float*
test_func_01 (float* p, float c)
{
  *--p = c;
  *--p = c;
  *--p = c;
  return p;
}

void
foo (float mat[])
{
  float *p = &mat[16];

  *--p = 0;  *--p = 0;  *--p = 0;  *--p = 0;
  *--p = 0;  *--p = 0;  *--p = 0;  *--p = 0;
}
