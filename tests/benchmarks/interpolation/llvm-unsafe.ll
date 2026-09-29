source_filename = "interpolation-unsafe"
target triple = "x86_64-unknown-linux-gnu"
target datalayout = "e-p:64:64-i64:64-n8:16:32:64-S128"
declare i8 @__VERIFIER_nondet_uchar()
declare void @__VERIFIER_assert(i32)
define i8 @main() {
entry:
  %input = call i8 @__VERIFIER_nondet_uchar()
  %value = and i8 %input, 3
  %ok = icmp ule i8 %value, 2
  %condition = zext i1 %ok to i32
  call void @__VERIFIER_assert(i32 %condition)
  ret i8 0
}
