/* In this case AMS would introduce a counterproductive pre-dec store usage
   on non-SH2A, which requires a reg copy and doesn't benefit the overall
   code.  On SH2A a post-inc store can be used in this case.  */

/* { dg-do compile }  */
/* { dg-options "-O2" } */

/* { dg-final { scan-assembler-not "mov.b\tr\[0-9],@\\-r\[0-9]" { target { ! sh2a } } } }  */
/* { dg-final { scan-assembler-times "mov.b\tr0,@r\[0-9]" 2 { target { sh2a } } } }  */

void
rtv_from_u16 (unsigned char ** pp, unsigned short v)
{
  unsigned char * p = *pp;

  *p++ = (v & 0xff00) >> 8;
  *p++ =  v & 0x00ff;

  *pp = p;
}
