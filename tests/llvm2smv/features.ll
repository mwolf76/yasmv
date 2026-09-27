; Inventory must include the helper called on a statically false branch.
target datalayout = "e-p:64:64-i64:64-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
@data = global [2 x i8] [i8 3, i8 7]
@alias = alias [2 x i8], ptr @data

define i32 @main() {
entry:
  br i1 false, label %unused, label %done
unused:
  %value = call i65 @helper(i65 1) [ "deopt"(i32 0) ]
  br label %done
done:
  ret i32 0
}

define i65 @helper(i65 %x) mustprogress willreturn {
entry:
  %sum = add nsw i65 %x, 1
  %chosen = freeze i65 poison
  %quotient = udiv exact i65 %sum, 2
  %v = load volatile i8, ptr @data
  call void @external(ptr @data)
  ret i65 %quotient
}

declare void @external(ptr)

define float @unrelated() {
  ret float 0.0
}
