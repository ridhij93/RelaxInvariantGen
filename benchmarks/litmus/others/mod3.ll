; ModuleID = 'mod3.c'
source_filename = "mod3.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [11 x i8] c"x % 3 == 0\00", align 1
@.str.1 = private unnamed_addr constant [7 x i8] c"mod3.c\00", align 1
@__PRETTY_FUNCTION__.main = private unnamed_addr constant [11 x i8] c"int main()\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  store i32 0, i32* %retval, align 4
  %call = call i32 (...) @__VERIFIER_nondet_int()
  store i32 %call, i32* %x, align 4
  store i32 1, i32* %y, align 4
  br label %while.cond

while.cond:                                       ; preds = %if.end14, %entry
  %call1 = call i32 (...) @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call1, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %0 = load i32, i32* %x, align 4
  %rem = urem i32 %0, 3
  %cmp = icmp eq i32 %rem, 1
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %while.body
  %1 = load i32, i32* %x, align 4
  %add = add i32 %1, 2
  store i32 %add, i32* %x, align 4
  store i32 0, i32* %y, align 4
  br label %if.end14

if.else:                                          ; preds = %while.body
  %2 = load i32, i32* %x, align 4
  %rem2 = urem i32 %2, 3
  %cmp3 = icmp eq i32 %rem2, 2
  br i1 %cmp3, label %if.then4, label %if.else6

if.then4:                                         ; preds = %if.else
  %3 = load i32, i32* %x, align 4
  %add5 = add i32 %3, 1
  store i32 %add5, i32* %x, align 4
  store i32 0, i32* %y, align 4
  br label %if.end13

if.else6:                                         ; preds = %if.else
  %call7 = call i32 (...) @__VERIFIER_nondet_int()
  %tobool8 = icmp ne i32 %call7, 0
  br i1 %tobool8, label %if.then9, label %if.else11

if.then9:                                         ; preds = %if.else6
  %4 = load i32, i32* %x, align 4
  %add10 = add i32 %4, 4
  store i32 %add10, i32* %x, align 4
  store i32 1, i32* %y, align 4
  br label %if.end

if.else11:                                        ; preds = %if.else6
  %5 = load i32, i32* %x, align 4
  %add12 = add i32 %5, 5
  store i32 %add12, i32* %x, align 4
  store i32 1, i32* %y, align 4
  br label %if.end

if.end:                                           ; preds = %if.else11, %if.then9
  br label %if.end13

if.end13:                                         ; preds = %if.end, %if.then4
  br label %if.end14

if.end14:                                         ; preds = %if.end13, %if.then
  br label %while.cond

while.end:                                        ; preds = %while.cond
  %6 = load i32, i32* %y, align 4
  %cmp15 = icmp eq i32 %6, 0
  br i1 %cmp15, label %if.then16, label %if.end22

if.then16:                                        ; preds = %while.end
  %7 = load i32, i32* %x, align 4
  %rem17 = urem i32 %7, 3
  %cmp18 = icmp eq i32 %rem17, 0
  br i1 %cmp18, label %if.then19, label %if.else20

if.then19:                                        ; preds = %if.then16
  br label %if.end21

if.else20:                                        ; preds = %if.then16
  call void @__assert_fail(i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1, i64 0, i64 0), i32 26, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__PRETTY_FUNCTION__.main, i64 0, i64 0)) #3
  unreachable

if.end21:                                         ; preds = %if.then19
  br label %if.end22

if.end22:                                         ; preds = %if.end21, %while.end
  ret i32 0
}

declare dso_local i32 @__VERIFIER_nondet_int(...) #1

; Function Attrs: noreturn nounwind
declare dso_local void @__assert_fail(i8*, i8*, i32, i8*) #2

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 11.1.0"}
