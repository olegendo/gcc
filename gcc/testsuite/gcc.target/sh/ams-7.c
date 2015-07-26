/* { dg-do compile }  */
/* { dg-options "-O2" }  */

int
fun_0 (int* arr1, int index, int* arr2)
{
  arr1[index+1] = 10;
  arr1[index+2] = 10;

  return (index+1) * 4;

  /* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(4,r\[0-9]\+" 1 } }  */
  /* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(8,r\[0-9]\+" 1 } }  */
  /* 1x shll2  */
  /* 1x add reg,reg  */
}

int
fun_1 (short* arr1, int index, short* arr2)
{
  arr1[index+1] = 10;
  arr1[index+2] = 10;

  return (index+1) * 2;

  /* { dg-final { scan-assembler-times "mov.w\tr\[0-9]\+,@\\(2,r\[0-9]\+" 1 } }  */
  /* { dg-final { scan-assembler-times "mov.w\tr\[0-9]\+,@\\(4,r\[0-9]\+" 1 } }  */
  /* 1x add reg,reg instead of shll  */
  /* 1x add reg,reg  */
}

void
fun_2 (char* arr1, unsigned int index)
{
  arr1[index*2+1] = 10;

  /* { dg-final { scan-assembler-times "mov.b\tr\[0-9]\+,@\\(1,r\[0-9]\+" 1 } }  */
  /* 2x add reg,reg  */
}

void
fun_3 (int* arr, unsigned index)
{
  arr[index] = 10;

  /* { dg-final { scan-assembler-times "mov.l\tr\[0-9]\+,@\\(r0,r\[0-9]\+" 1 } }  */
  /* 1x shll2  */
}


/* { dg-final { scan-assembler-times "shll2" 2 } }  */
/* { dg-final { scan-assembler-times "add\tr\[0-9]\+,r\[0-9]\+" 5 } }  */