/* Expect @(reg + reg) mode usage in this case.  */

/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.\[bwl]\t@\\(r0,r\[0-9]\+" 3 } }  */

int
fun_0 (int* a)
{
  return *((int*)__builtin_assume_aligned ((int*)((unsigned int)a * 2), 4));
}

int
fun_1 (short* a)
{
  return *((short*)__builtin_assume_aligned ((short*)((unsigned int)a * 2), 2));
}

int
fun_2 (char* a)
{
  return *((char*)__builtin_assume_aligned ((char*)((unsigned int)a * 2), 1));
}