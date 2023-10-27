; ModuleID = 'cowr.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%union.pthread_attr_t = type { i64, [48 x i8] }

@a = global i32 0, align 4
@x = common global i32 0, align 4
@.str = private unnamed_addr constant [17 x i8] c"! (x==1 && a==1)\00", align 1
@.str.1 = private unnamed_addr constant [7 x i8] c"cowr.c\00", align 1
@__PRETTY_FUNCTION__.main = private unnamed_addr constant [11 x i8] c"int main()\00", align 1

; Function Attrs: nounwind uwtable
define i8* @thread1(i8* %threadid) #0 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  %p = alloca i32, align 4
  store i8* %threadid, i8** %2, align 8
  store i32 1, i32* @x, align 4
  %3 = load i32, i32* @x, align 4
  store i32 %3, i32* %p, align 4
  %4 = load i32, i32* %p, align 4
  %5 = icmp eq i32 %4, 2
  br i1 %5, label %6, label %7

; <label>:6                                       ; preds = %0
  store i32 1, i32* @a, align 4
  br label %7

; <label>:7                                       ; preds = %6, %0
  %8 = load i8*, i8** %1, align 8
  ret i8* %8
}

; Function Attrs: nounwind uwtable
define i8* @thread2(i8* %threadid) #0 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  store i8* %threadid, i8** %2, align 8
  store i32 2, i32* @x, align 4
  %3 = load i8*, i8** %1, align 8
  ret i8* %3
}

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %i = alloca i32, align 4
  %j = alloca i32, align 4
  %rc1 = alloca i32, align 4
  %rc2 = alloca i32, align 4
  %threads = alloca [2 x i64], align 16
  store i32 0, i32* %1, align 4
  store i32 0, i32* %i, align 4
  store i32 1, i32* %j, align 4
  %2 = getelementptr inbounds [2 x i64], [2 x i64]* %threads, i64 0, i64 0
  %3 = load i32, i32* %i, align 4
  %4 = sext i32 %3 to i64
  %5 = inttoptr i64 %4 to i8*
  %6 = call i32 @pthread_create(i64* %2, %union.pthread_attr_t* null, i8* (i8*)* @thread1, i8* %5) #4
  store i32 %6, i32* %rc1, align 4
  %7 = getelementptr inbounds [2 x i64], [2 x i64]* %threads, i64 0, i64 1
  %8 = load i32, i32* %j, align 4
  %9 = sext i32 %8 to i64
  %10 = inttoptr i64 %9 to i8*
  %11 = call i32 @pthread_create(i64* %7, %union.pthread_attr_t* null, i8* (i8*)* @thread2, i8* %10) #4
  store i32 %11, i32* %rc2, align 4
  %12 = getelementptr inbounds [2 x i64], [2 x i64]* %threads, i64 0, i64 0
  %13 = load i64, i64* %12, align 16
  %14 = call i32 @pthread_join(i64 %13, i8** null)
  %15 = getelementptr inbounds [2 x i64], [2 x i64]* %threads, i64 0, i64 1
  %16 = load i64, i64* %15, align 8
  %17 = call i32 @pthread_join(i64 %16, i8** null)
  %18 = load i32, i32* @x, align 4
  %19 = icmp eq i32 %18, 1
  br i1 %19, label %20, label %23

; <label>:20                                      ; preds = %0
  %21 = load i32, i32* @a, align 4
  %22 = icmp eq i32 %21, 1
  br i1 %22, label %24, label %23

; <label>:23                                      ; preds = %20, %0
  br label %26

; <label>:24                                      ; preds = %20
  call void @__assert_fail(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1, i32 0, i32 0), i32 36, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__PRETTY_FUNCTION__.main, i32 0, i32 0)) #5
  unreachable
                                                  ; No predecessors!
  br label %26

; <label>:26                                      ; preds = %25, %23
  %27 = load i32, i32* %1, align 4
  ret i32 %27
}

; Function Attrs: nounwind
declare i32 @pthread_create(i64*, %union.pthread_attr_t*, i8* (i8*)*, i8*) #1

declare i32 @pthread_join(i64, i8**) #2

; Function Attrs: noreturn nounwind
declare void @__assert_fail(i8*, i8*, i32, i8*) #3

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }
attributes #5 = { noreturn nounwind }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.0-2ubuntu3~trusty5 (tags/RELEASE_380/final)"}
