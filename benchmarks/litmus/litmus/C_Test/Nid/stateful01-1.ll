; ModuleID = 'stateful01-1.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%union.pthread_mutex_t = type { %struct.__pthread_mutex_s }
%struct.__pthread_mutex_s = type { i32, i32, i32, i32, i32, i16, i16, %struct.__pthread_internal_list }
%struct.__pthread_internal_list = type { %struct.__pthread_internal_list*, %struct.__pthread_internal_list* }
%union.pthread_mutexattr_t = type { i32 }
%union.pthread_attr_t = type { i64, [48 x i8] }

@ma = common global %union.pthread_mutex_t zeroinitializer, align 8
@data1 = common global i32 0, align 4
@data2 = common global i32 0, align 4
@mb = common global %union.pthread_mutex_t zeroinitializer, align 8
@.str = private unnamed_addr constant [5 x i8] c"1==2\00", align 1
@.str.1 = private unnamed_addr constant [15 x i8] c"stateful01-1.c\00", align 1
@__PRETTY_FUNCTION__.main = private unnamed_addr constant [11 x i8] c"int main()\00", align 1

; Function Attrs: nounwind uwtable
define i8* @thread1(i8* %arg) #0 {
  %1 = alloca i8*, align 8
  store i8* %arg, i8** %1, align 8
  %2 = call i32 @pthread_mutex_lock(%union.pthread_mutex_t* @ma) #4
  %3 = load i32, i32* @data1, align 4
  %4 = add nsw i32 %3, 1
  store i32 %4, i32* @data1, align 4
  %5 = call i32 @pthread_mutex_unlock(%union.pthread_mutex_t* @ma) #4
  %6 = call i32 @pthread_mutex_lock(%union.pthread_mutex_t* @ma) #4
  %7 = load i32, i32* @data2, align 4
  %8 = add nsw i32 %7, 1
  store i32 %8, i32* @data2, align 4
  %9 = call i32 @pthread_mutex_unlock(%union.pthread_mutex_t* @ma) #4
  ret i8* null
}

; Function Attrs: nounwind
declare i32 @pthread_mutex_lock(%union.pthread_mutex_t*) #1

; Function Attrs: nounwind
declare i32 @pthread_mutex_unlock(%union.pthread_mutex_t*) #1

; Function Attrs: nounwind uwtable
define i8* @thread2(i8* %arg) #0 {
  %1 = alloca i8*, align 8
  store i8* %arg, i8** %1, align 8
  %2 = call i32 @pthread_mutex_lock(%union.pthread_mutex_t* @ma) #4
  %3 = load i32, i32* @data1, align 4
  %4 = add nsw i32 %3, 5
  store i32 %4, i32* @data1, align 4
  %5 = call i32 @pthread_mutex_unlock(%union.pthread_mutex_t* @ma) #4
  %6 = call i32 @pthread_mutex_lock(%union.pthread_mutex_t* @ma) #4
  %7 = load i32, i32* @data2, align 4
  %8 = sub nsw i32 %7, 6
  store i32 %8, i32* @data2, align 4
  %9 = call i32 @pthread_mutex_unlock(%union.pthread_mutex_t* @ma) #4
  ret i8* null
}

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %t1 = alloca i64, align 8
  %t2 = alloca i64, align 8
  store i32 0, i32* %1, align 4
  %2 = call i32 @pthread_mutex_init(%union.pthread_mutex_t* @ma, %union.pthread_mutexattr_t* null) #4
  %3 = call i32 @pthread_mutex_init(%union.pthread_mutex_t* @mb, %union.pthread_mutexattr_t* null) #4
  store i32 10, i32* @data1, align 4
  store i32 10, i32* @data2, align 4
  %4 = call i32 @pthread_create(i64* %t1, %union.pthread_attr_t* null, i8* (i8*)* @thread1, i8* null) #4
  %5 = call i32 @pthread_create(i64* %t2, %union.pthread_attr_t* null, i8* (i8*)* @thread2, i8* null) #4
  %6 = load i64, i64* %t1, align 8
  %7 = call i32 @pthread_join(i64 %6, i8** null)
  %8 = load i64, i64* %t2, align 8
  %9 = call i32 @pthread_join(i64 %8, i8** null)
  %10 = load i32, i32* @data1, align 4
  %11 = icmp eq i32 %10, 16
  br i1 %11, label %12, label %16

; <label>:12                                      ; preds = %0
  %13 = load i32, i32* @data2, align 4
  %14 = icmp eq i32 %13, 5
  br i1 %14, label %15, label %16

; <label>:15                                      ; preds = %12
  call void @__assert_fail(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str, i32 0, i32 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.1, i32 0, i32 0), i32 55, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__PRETTY_FUNCTION__.main, i32 0, i32 0)) #5
  unreachable

; <label>:16                                      ; preds = %12, %0
  ret i32 0
}

; Function Attrs: nounwind
declare i32 @pthread_mutex_init(%union.pthread_mutex_t*, %union.pthread_mutexattr_t*) #1

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
