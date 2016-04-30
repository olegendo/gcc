/* This is basically the same test case as g++.dg/opt/ams-18.C, but rewritten
   as plain C.  This has some small differences in how the expanded code
   is optimized.  */

/* { dg-do compile { target sh*-*-* } }  */
/* { dg-options "-O2" }  */

/*

without AMS:
	mov	r5,r0
	tst	#1,r0
	add	r6,r4
	bt	.L17
	mov.l	@r4,r5
	add	r5,r0
	add	#-1,r0
	mov.l	@r0,r0
.L17:
	jmp	@r0
	nop

with AMS expect it to use a (reg + reg) mode:

	mov	r5,r0
	tst	#1,r0
	add	r6,r4
	bt	.L17
	mov.l	@r4,r5
	add	#-1,r0
	mov.l	@(r0,r5),r0
.L17:
	jmp	@r0
	nop
*/

/* { dg-final { scan-assembler-times "mov.l\t@\\(r0,r\[0-9]\+\\)" 1 } }  */
/* { dg-final { scan-assembler-times "mov\t" 1 } }  */
/* { dg-final { scan-assembler-times "add\t" 2 } }  */
/* { dg-final { scan-assembler-times "mov.l\t" 2 } }  */

struct pf_t
{
  unsigned int __pfn;
  int __delta;
};

void
test (unsigned int thizz, struct pf_t pf)
{
  thizz += pf.__delta;

  if (pf.__pfn & 1)
    pf.__pfn = *(unsigned int*)(*((unsigned int*)thizz) + pf.__pfn - 1);

  ((void (*)(unsigned int))pf.__pfn)(thizz);
}
