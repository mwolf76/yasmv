#ifndef LLVM2SMV_VERIFIER_H
#define LLVM2SMV_VERIFIER_H
/* Model hooks: declarations only. Every nondet call samples a fresh value. */
void __VERIFIER_assert(int condition);
void __VERIFIER_assume(int condition);
void __VERIFIER_error(void);
_Bool __VERIFIER_nondet_bool(void);
char __VERIFIER_nondet_char(void);
unsigned char __VERIFIER_nondet_uchar(void);
short __VERIFIER_nondet_short(void);
unsigned short __VERIFIER_nondet_ushort(void);
int __VERIFIER_nondet_int(void);
unsigned int __VERIFIER_nondet_uint(void);
long __VERIFIER_nondet_long(void);
unsigned long __VERIFIER_nondet_ulong(void);
long long __VERIFIER_nondet_longlong(void);
unsigned long long __VERIFIER_nondet_ulonglong(void);
#endif
