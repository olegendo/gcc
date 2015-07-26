/* On non-SH2A the expected handling of outliers in access sequences is
   to use reg+reg modes with a constant load.  */

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.\[bwl]\t@\\(r0,r\[0-9]\+" 3 { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-not "mov.\[bwl]\t@\\(r0,r\[0-9]\+" { target { sh2a } } } }  */

/* { dg-final { scan-assembler-times "add" 6 } }  */

int
fun_0 (int i, int* a)
{
  return a[0] + a[100] + a[1];
}

int
fun_1 (int i, short* a)
{
  return a[0] + a[100] + a[1];
}

int
fun_2 (int i, char* a)
{
  return a[0] + a[100] + a[1];
}