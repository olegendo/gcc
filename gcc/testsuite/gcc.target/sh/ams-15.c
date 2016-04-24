/* SImode displacement loads are as cheap as post-inc loads, so usually
   AMS will output displacement loads if they fit.  However, in this case
   post-inc loads should be used because it eliminates address calculation
   insns.
*/
/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.l\t@r\[0-9]\+\\+" 3 } }  */
/* { dg-final { scan-assembler-not "add" } }  */

int*
fun_0 (int* a, int* b)
{
  b[0] = a[0] ^ a[1] ^ a[2];
  return &a[3];
}
