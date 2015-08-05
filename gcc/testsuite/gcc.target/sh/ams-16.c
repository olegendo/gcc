/* On SH2A we have a post-inc store which can be used for the code generated
   by __builtin_memset.  */
/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.\[bwl]\tr0,@r\[0-9]\+\\+" 4 { target { sh2a } } } }  */

void
fun (char* dstb)
{
  __builtin_memset (dstb, 0, 15);
}