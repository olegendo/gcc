/* { dg-do compile }  */
/* { dg-options "-O2" }  */

/* { dg-final { scan-assembler-times "mov.b\t\@\\(1,r\[0-9]\+" 1 } }  */
/* { dg-final { scan-assembler-times "mov.b\t\@\\(2,r\[0-9]\+" 1 } }  */

/* { dg-final { scan-assembler-times "mov.b\t\@r\[0-9]\+\\+" 13 } }  */
/* { dg-final { scan-assembler-times "mov.w\t\@r\[0-9]\+\\+" 12 } }  */

int
fun_00 (char* x, char* y, int z)
{
  /* Expect displacement mode for 2 accesses.  */
  return ((x[1] & x[2]) == 0) + z;
}

int
fun_01 (char* x, char* y, int z)
{
  /* Expect post-inc mode for 3 or more accesses.  */
  return ((x[1] & x[2] & x[3]) == 0) + z;
}

int
fun_02 (char* x, char* y, int z)
{
  /* Expect post-inc mode for 3 or more accesses.  */
  return ((x[1] & x[2] & x[3] & x[4] & x[5] & x[6]) == 0) + z;
}

int
fun_03 (char* x)
{
  /* Expect post-inc mode even for 2 accesses if first offset is 0.  */
  return x[0] + x[1];
}

int
fun_04 (char* x)
{
  /* Expect post-inc mode even for 2 accesses if first offset is 0.  */
  return x[0] + x[1] + x[2] + x[3];
}

int
fun_05 (unsigned short* x, int y, int z)
{
  return (x[0] + x[1] + x[2] + x[3] + x[4] + x[5] + x[6] + x[7] + x[8]
	  + x[9] + x[10]) ? y : z;
}

char*
fun_06 (char* x, char* y, int z, int* zz)
{
  /* Expect post-inc mode for 3 or more accesses or addr reg uses.  */
  *zz = ((x[1] & x[2]) == 0) + z;
  return &x[3];
}

short*
fun_07 (short* x, short* y, int z, int* zz)
{
  /* Expect post-inc mode for 3 or more accesses or addr reg uses.  */
  *zz = ((x[1] & x[2]) == 0) + z;
  return &x[3];
}