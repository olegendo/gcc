/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.\[bwl]\tr0,@r\[0-9]\+\\+" 6 { target { sh2a } } } }  */
/* { dg-final { scan-assembler-times "mov.\[bwl]\t@r\[0-9]\+\\-,r0" 3 { target { sh2a } } } }  */

/* On SH2A we have a post-inc store which can be used for the code generated
   by __builtin_memset.  */
void
test_00 (char* dstb)
{
  __builtin_memset (dstb, 0, 15);
}

/* 3 or more adjacent stores should use post-inc mode.  */
void
test_01 (char* x, int y)
{
  x[0] = y;
  x[1] = y;
  x[2] = y;
}

/* Expect post-dec loads here.  */
int
test_02 (char* x, int y)
{
  return x[0] ^ x[-1] ^ x[-2] ^ x[-3];
}