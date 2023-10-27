; ModuleID = 'corr2.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%union.pthread_attr_t = type { i64, [48 x i8] }

@x = global i32 0, align 4
@a = global i32 0, align 4
@b = global i32 0, align 4
@.str = private unnamed_addr constant [37 x i8] c"! ((a==1 && b==1) || (a==2 && b==2))\00", align 1
@.str.1 = private unnamed_addr constant [8 x i8] c"corr2.c\00", align 1
@__PRETTY_FUNCTION__.main = private unnamed_addr constant [11 x i8] c"int main()\00", align 1

; Function Attrs: nounwind uwtable
define i8* @thread1(i8* %threadid) #0 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  store i8* %threadid, i8** %2, align 8
  store i32 1, i32* @x, align 4
  %3 = load i8*, i8** %1, align 8
  ret i8* %3
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
define i8* @thread3(i8* %threadid) #0 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  %p = alloca i32, align 4
  %q = alloca i32, align 4
  store i8* %threadid, i8** %2, align 8
  %3 = load i32, i32* @x, align 4
  store i32 %3, i32* %p, align 4
  %4 = load i32, i32* @x, align 4
  store i32 %4, i32* %q, align 4
  %5 = load i32, i32* %p, align 4
  %6 = icmp eq i32 %5, 1
  br i1 %6, label %7, label %11

; <label>:7                                       ; preds = %0
  %8 = load i32, i32* %q, align 4
  %9 = icmp eq i32 %8, 2
  br i1 %9, label %10, label %11

; <label>:10                                      ; preds = %7
  store i32 1, i32* @a, align 4
  br label %11

; <label>:11                                      ; preds = %10, %7, %0
  %12 = load i32, i32* %p, align 4
  %13 = icmp eq i32 %12, 2
  br i1 %13, label %14, label %18

; <label>:14                                      ; preds = %11
  %15 = load i32, i32* %q, align 4
  %16 = icmp eq i32 %15, 1
  br i1 %16, label %17, label %18

; <label>:17                                      ; preds = %14
  store i32 2, i32* @a, align 4
  br label %18

; <label>:18                                      ; preds = %17, %14, %11
  %19 = load i8*, i8** %1, align 8
  ret i8* %19
}

; Function Attrs: nounwind uwtable
define i8* @thread4(i8* %threadid) #0 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  %r = alloca i32, align 4
  %s = alloca i32, align 4
  store i8* %threadid, i8** %2, align 8
  %3 = load i32, i32* @x, align 4
  store i32 %3, i32* %r, align 4
  %4 = load i32, i32* @x, align 4
  store i32 %4, i32* %s, align 4
  %5 = load i32, i32* %r, align 4
  %6 = icmp eq i32 %5, 2
  br i1 %6, label %7, label %11

; <label>:7                                       ; preds = %0
  %8 = load i32, i32* %s, align 4
  %9 = icmp eq i32 %8, 1
  br i1 %9, label %10, label %11

; <label>:10                                      ; preds = %7
  store i32 1, i32* @b, align 4
  br label %11

; <label>:11                                      ; preds = %10, %7, %0
  %12 = load i32, i32* %r, align 4
  %13 = icmp eq i32 %12, 1
  br i1 %13, label %14, label %18

; <label>:14                                      ; preds = %11
  %15 = load i32, i32* %s, align 4
  %16 = icmp eq i32 %15, 2
  br i1 %16, label %17, label %18

; <label>:17                                      ; preds = %14
  store i32 2, i32* @b, align 4
  br label %18

; <label>:18                                      ; preds = %17, %14, %11
  %19 = load i8*, i8** %1, align 8
  ret i8* %19
}

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %i = alloca i32, align 4
  %j = alloca i32, align 4
  %rc1 = alloca i32, align 4
  %rc2 = alloca i32, align 4
  %rc3 = alloca i32, align 4
  %rc4 = alloca i32, align 4
  %threads = alloca [4 x i64], align 16
  store i32 0, i32* %1, align 4
  store i32 0, i32* %i, align 4
  store i32 1, i32* %j, align 4
  %2 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 0
  %3 = load i32, i32* %i, align 4
  %4 = sext i32 %3 to i64
  %5 = inttoptr i64 %4 to i8*
  %6 = call i32 @pthread_create(i64* %2, %union.pthread_attr_t* null, i8* (i8*)* @thread1, i8* %5) #4
  store i32 %6, i32* %rc1, align 4
  %7 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 1
  %8 = load i32, i32* %j, align 4
  %9 = sext i32 %8 to i64
  %10 = inttoptr i64 %9 to i8*
  %11 = call i32 @pthread_create(i64* %7, %union.pthread_attr_t* null, i8* (i8*)* @thread2, i8* %10) #4
  store i32 %11, i32* %rc2, align 4
  %12 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 2
  %13 = load i32, i32* %i, align 4
  %14 = sext i32 %13 to i64
  %15 = inttoptr i64 %14 to i8*
  %16 = call i32 @pthread_create(i64* %12, %union.pthread_attr_t* null, i8* (i8*)* @thread3, i8* %15) #4
  store i32 %16, i32* %rc3, align 4
  %17 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 3
  %18 = load i32, i32* %j, align 4
  %19 = sext i32 %18 to i64
  %20 = inttoptr i64 %19 to i8*
  %21 = call i32 @pthread_create(i64* %17, %union.pthread_attr_t* null, i8* (i8*)* @thread4, i8* %20) #4
  store i32 %21, i32* %rc4, align 4
  %22 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 0
  %23 = load i64, i64* %22, align 16
  %24 = call i32 @pthread_join(i64 %23, i8** null)
  %25 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 1
  %26 = load i64, i64* %25, align 8
  %27 = call i32 @pthread_join(i64 %26, i8** null)
  %28 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 2
  %29 = load i64, i64* %28, align 16
  %30 = call i32 @pthread_join(i64 %29, i8** null)
  %31 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 3
  %32 = load i64, i64* %31, align 8
  %33 = call i32 @pthread_join(i64 %32, i8** null)
  %34 = load i32, i32* @a, align 4
  %35 = icmp eq i32 %34, 1
  br i1 %35, label %36, label %39

; <label>:36                                      ; preds = %0
  %37 = load i32, i32* @b, align 4
  %38 = icmp eq i32 %37, 1
  br i1 %38, label %46, label %39

; <label>:39                                      ; preds = %36, %0
  %40 = load i32, i32* @a, align 4
  %41 = icmp eq i32 %40, 2
  br i1 %41, label %42, label %45

; <label>:42                                      ; preds = %39
  %43 = load i32, i32* @b, align 4
  %44 = icmp eq i32 %43, 2
  br i1 %44, label %46, label %45

; <label>:45                                      ; preds = %42, %39
  br label %48

; <label>:46                                      ; preds = %42, %36
  call void @__assert_fail(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.1, i32 0, i32 0), i32 62, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__PRETTY_FUNCTION__.main, i32 0, i32 0)) #5
  unreachable
                                                  ; No predecessors!
  br label %48

; <label>:48                                      ; preds = %47, %45
  %49 = load i32, i32* %1, align 4
  ret i32 %49
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
