/* Check that GBR address modes are selected by AMS when the GBR is retrieved
   in a different basic block than the memory access.  */
/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-not "stc\tgbr" } }  */
/* { dg-final { scan-assembler-times "mov.l\t@\\([0-9]\+,gbr" 3 } }  */

int
fun_0 (int x)
{
  int* p = (int*)__builtin_thread_pointer ();
  
  int a = p[0];
  int b;
  
  if (x == 4)
    b = p[50];
  else
    b = p[128];
    
  return a + b;
}
