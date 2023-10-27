; ModuleID = 'queue.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%union.pthread_mutex_t = type { %struct.__pthread_mutex_s }
%struct.__pthread_mutex_s = type { i32, i32, i32, i32, i32, i16, i16, %struct.__pthread_internal_list }
%struct.__pthread_internal_list = type { %struct.__pthread_internal_list*, %struct.__pthread_internal_list* }
%struct.QType = type { [20 x i32], i32, i32, i32 }
%union.pthread_mutexattr_t = type { i32 }
%union.pthread_attr_t = type { i64, [48 x i8] }

@.str = private unnamed_addr constant [16 x i8] c"queue is empty\0A\00", align 1
@.str.1 = private unnamed_addr constant [15 x i8] c"queue is full\0A\00", align 1
@m = common global %union.pthread_mutex_t zeroinitializer, align 8
@queue = common global %struct.QType zeroinitializer, align 4
@.str.2 = private unnamed_addr constant [5 x i8] c"1==2\00", align 1
@.str.3 = private unnamed_addr constant [8 x i8] c"queue.c\00", align 1
@__PRETTY_FUNCTION__.t1 = private unnamed_addr constant [17 x i8] c"void *t1(void *)\00", align 1
@stored_elements = common global [20 x i32] zeroinitializer, align 16
@enqueue_flag = common global i8 0, align 1
@dequeue_flag = common global i8 0, align 1
@__PRETTY_FUNCTION__.t2 = private unnamed_addr constant [17 x i8] c"void *t2(void *)\00", align 1
@__PRETTY_FUNCTION__.main = private unnamed_addr constant [11 x i8] c"int main()\00", align 1

; Function Attrs: nounwind uwtable
define void @init(%struct.QType* %q) #0 {
  %1 = alloca %struct.QType*, align 8
  store %struct.QType* %q, %struct.QType** %1, align 8
  %2 = load %struct.QType*, %struct.QType** %1, align 8
  %3 = getelementptr inbounds %struct.QType, %struct.QType* %2, i32 0, i32 1
  store i32 0, i32* %3, align 4
  %4 = load %struct.QType*, %struct.QType** %1, align 8
  %5 = getelementptr inbounds %struct.QType, %struct.QType* %4, i32 0, i32 2
  store i32 0, i32* %5, align 4
  %6 = load %struct.QType*, %struct.QType** %1, align 8
  %7 = getelementptr inbounds %struct.QType, %struct.QType* %6, i32 0, i32 3
  store i32 0, i32* %7, align 4
  ret void
}

; Function Attrs: nounwind uwtable
define i32 @empty(%struct.QType* %q) #0 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.QType*, align 8
  store %struct.QType* %q, %struct.QType** %2, align 8
  %3 = load %struct.QType*, %struct.QType** %2, align 8
  %4 = getelementptr inbounds %struct.QType, %struct.QType* %3, i32 0, i32 1
  %5 = load i32, i32* %4, align 4
  %6 = load %struct.QType*, %struct.QType** %2, align 8
  %7 = getelementptr inbounds %struct.QType, %struct.QType* %6, i32 0, i32 2
  %8 = load i32, i32* %7, align 4
  %9 = icmp eq i32 %5, %8
  br i1 %9, label %10, label %12

; <label>:10                                      ; preds = %0
  %11 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str, i32 0, i32 0))
  store i32 -1, i32* %1, align 4
  br label %13

; <label>:12                                      ; preds = %0
  store i32 0, i32* %1, align 4
  br label %13

; <label>:13                                      ; preds = %12, %10
  %14 = load i32, i32* %1, align 4
  ret i32 %14
}

declare i32 @printf(i8*, ...) #1

; Function Attrs: nounwind uwtable
define i32 @full(%struct.QType* %q) #0 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.QType*, align 8
  store %struct.QType* %q, %struct.QType** %2, align 8
  %3 = load %struct.QType*, %struct.QType** %2, align 8
  %4 = getelementptr inbounds %struct.QType, %struct.QType* %3, i32 0, i32 3
  %5 = load i32, i32* %4, align 4
  %6 = icmp eq i32 %5, 20
  br i1 %6, label %7, label %9

; <label>:7                                       ; preds = %0
  %8 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.1, i32 0, i32 0))
  store i32 -2, i32* %1, align 4
  br label %10

; <label>:9                                       ; preds = %0
  store i32 0, i32* %1, align 4
  br label %10

; <label>:10                                      ; preds = %9, %7
  %11 = load i32, i32* %1, align 4
  ret i32 %11
}

; Function Attrs: nounwind uwtable
define i32 @enqueue(%struct.QType* %q, i32 %x) #0 {
  %1 = alloca %struct.QType*, align 8
  %2 = alloca i32, align 4
  store %struct.QType* %q, %struct.QType** %1, align 8
  store i32 %x, i32* %2, align 4
  %3 = load i32, i32* %2, align 4
  %4 = load %struct.QType*, %struct.QType** %1, align 8
  %5 = getelementptr inbounds %struct.QType, %struct.QType* %4, i32 0, i32 2
  %6 = load i32, i32* %5, align 4
  %7 = sext i32 %6 to i64
  %8 = load %struct.QType*, %struct.QType** %1, align 8
  %9 = getelementptr inbounds %struct.QType, %struct.QType* %8, i32 0, i32 0
  %10 = getelementptr inbounds [20 x i32], [20 x i32]* %9, i64 0, i64 %7
  store i32 %3, i32* %10, align 4
  %11 = load %struct.QType*, %struct.QType** %1, align 8
  %12 = getelementptr inbounds %struct.QType, %struct.QType* %11, i32 0, i32 3
  %13 = load i32, i32* %12, align 4
  %14 = add nsw i32 %13, 1
  store i32 %14, i32* %12, align 4
  %15 = load %struct.QType*, %struct.QType** %1, align 8
  %16 = getelementptr inbounds %struct.QType, %struct.QType* %15, i32 0, i32 2
  %17 = load i32, i32* %16, align 4
  %18 = icmp eq i32 %17, 20
  br i1 %18, label %19, label %22

; <label>:19                                      ; preds = %0
  %20 = load %struct.QType*, %struct.QType** %1, align 8
  %21 = getelementptr inbounds %struct.QType, %struct.QType* %20, i32 0, i32 2
  store i32 1, i32* %21, align 4
  br label %27

; <label>:22                                      ; preds = %0
  %23 = load %struct.QType*, %struct.QType** %1, align 8
  %24 = getelementptr inbounds %struct.QType, %struct.QType* %23, i32 0, i32 2
  %25 = load i32, i32* %24, align 4
  %26 = add nsw i32 %25, 1
  store i32 %26, i32* %24, align 4
  br label %27

; <label>:27                                      ; preds = %22, %19
  ret i32 0
}

; Function Attrs: nounwind uwtable
define i32 @dequeue(%struct.QType* %q) #0 {
  %1 = alloca %struct.QType*, align 8
  %x = alloca i32, align 4
  store %struct.QType* %q, %struct.QType** %1, align 8
  %2 = load %struct.QType*, %struct.QType** %1, align 8
  %3 = getelementptr inbounds %struct.QType, %struct.QType* %2, i32 0, i32 1
  %4 = load i32, i32* %3, align 4
  %5 = sext i32 %4 to i64
  %6 = load %struct.QType*, %struct.QType** %1, align 8
  %7 = getelementptr inbounds %struct.QType, %struct.QType* %6, i32 0, i32 0
  %8 = getelementptr inbounds [20 x i32], [20 x i32]* %7, i64 0, i64 %5
  %9 = load i32, i32* %8, align 4
  store i32 %9, i32* %x, align 4
  %10 = load %struct.QType*, %struct.QType** %1, align 8
  %11 = getelementptr inbounds %struct.QType, %struct.QType* %10, i32 0, i32 3
  %12 = load i32, i32* %11, align 4
  %13 = add nsw i32 %12, -1
  store i32 %13, i32* %11, align 4
  %14 = load %struct.QType*, %struct.QType** %1, align 8
  %15 = getelementptr inbounds %struct.QType, %struct.QType* %14, i32 0, i32 1
  %16 = load i32, i32* %15, align 4
  %17 = icmp eq i32 %16, 20
  br i1 %17, label %18, label %21

; <label>:18                                      ; preds = %0
  %19 = load %struct.QType*, %struct.QType** %1, align 8
  %20 = getelementptr inbounds %struct.QType, %struct.QType* %19, i32 0, i32 1
  store i32 1, i32* %20, align 4
  br label %26

; <label>:21                                      ; preds = %0
  %22 = load %struct.QType*, %struct.QType** %1, align 8
  %23 = getelementptr inbounds %struct.QType, %struct.QType* %22, i32 0, i32 1
  %24 = load i32, i32* %23, align 4
  %25 = add nsw i32 %24, 1
  store i32 %25, i32* %23, align 4
  br label %26

; <label>:26                                      ; preds = %21, %18
  %27 = load i32, i32* %x, align 4
  ret i32 %27
}

; Function Attrs: nounwind uwtable
define i8* @t1(i8* %arg) #0 {
  %1 = alloca i8*, align 8
  %value = alloca i32, align 4
  %i = alloca i32, align 4
  store i8* %arg, i8** %1, align 8
  %2 = call i32 @pthread_mutex_lock(%union.pthread_mutex_t* @m) #4
  store i32 3, i32* %value, align 4
  %3 = load i32, i32* %value, align 4
  %4 = call i32 @enqueue(%struct.QType* @queue, i32 %3)
  %5 = icmp ne i32 %4, 0
  br i1 %5, label %6, label %7

; <label>:6                                       ; preds = %0
  call void @__assert_fail(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.2, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.3, i32 0, i32 0), i32 93, i8* getelementptr inbounds ([17 x i8], [17 x i8]* @__PRETTY_FUNCTION__.t1, i32 0, i32 0)) #5
  unreachable

; <label>:7                                       ; preds = %0
  %8 = load i32, i32* %value, align 4
  store i32 %8, i32* getelementptr inbounds ([20 x i32], [20 x i32]* @stored_elements, i64 0, i64 0), align 16
  %9 = call i32 @empty(%struct.QType* @queue)
  %10 = icmp ne i32 %9, 0
  br i1 %10, label %11, label %12

; <label>:11                                      ; preds = %7
  call void @__assert_fail(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.2, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.3, i32 0, i32 0), i32 99, i8* getelementptr inbounds ([17 x i8], [17 x i8]* @__PRETTY_FUNCTION__.t1, i32 0, i32 0)) #5
  unreachable

; <label>:12                                      ; preds = %7
  %13 = call i32 @pthread_mutex_unlock(%union.pthread_mutex_t* @m) #4
  store i32 0, i32* %i, align 4
  br label %14

; <label>:14                                      ; preds = %31, %12
  %15 = load i32, i32* %i, align 4
  %16 = icmp slt i32 %15, 19
  br i1 %16, label %17, label %34

; <label>:17                                      ; preds = %14
  %18 = call i32 @pthread_mutex_lock(%union.pthread_mutex_t* @m) #4
  %19 = load i8, i8* @enqueue_flag, align 1
  %20 = trunc i8 %19 to i1
  br i1 %20, label %21, label %29

; <label>:21                                      ; preds = %17
  store i32 3, i32* %value, align 4
  %22 = load i32, i32* %value, align 4
  %23 = call i32 @enqueue(%struct.QType* @queue, i32 %22)
  %24 = load i32, i32* %value, align 4
  %25 = load i32, i32* %i, align 4
  %26 = add nsw i32 %25, 1
  %27 = sext i32 %26 to i64
  %28 = getelementptr inbounds [20 x i32], [20 x i32]* @stored_elements, i64 0, i64 %27
  store i32 %24, i32* %28, align 4
  store i8 0, i8* @enqueue_flag, align 1
  store i8 1, i8* @dequeue_flag, align 1
  br label %29

; <label>:29                                      ; preds = %21, %17
  %30 = call i32 @pthread_mutex_unlock(%union.pthread_mutex_t* @m) #4
  br label %31

; <label>:31                                      ; preds = %29
  %32 = load i32, i32* %i, align 4
  %33 = add nsw i32 %32, 1
  store i32 %33, i32* %i, align 4
  br label %14

; <label>:34                                      ; preds = %14
  ret i8* null
}

; Function Attrs: nounwind
declare i32 @pthread_mutex_lock(%union.pthread_mutex_t*) #2

; Function Attrs: noreturn nounwind
declare void @__assert_fail(i8*, i8*, i32, i8*) #3

; Function Attrs: nounwind
declare i32 @pthread_mutex_unlock(%union.pthread_mutex_t*) #2

; Function Attrs: nounwind uwtable
define i8* @t2(i8* %arg) #0 {
  %1 = alloca i8*, align 8
  %i = alloca i32, align 4
  store i8* %arg, i8** %1, align 8
  store i32 0, i32* %i, align 4
  br label %2

; <label>:2                                       ; preds = %23, %0
  %3 = load i32, i32* %i, align 4
  %4 = icmp slt i32 %3, 20
  br i1 %4, label %5, label %26

; <label>:5                                       ; preds = %2
  %6 = call i32 @pthread_mutex_lock(%union.pthread_mutex_t* @m) #4
  %7 = load i8, i8* @dequeue_flag, align 1
  %8 = trunc i8 %7 to i1
  br i1 %8, label %9, label %21

; <label>:9                                       ; preds = %5
  %10 = call i32 @dequeue(%struct.QType* @queue)
  %11 = icmp ne i32 %10, 0
  %12 = xor i1 %11, true
  %13 = zext i1 %12 to i32
  %14 = load i32, i32* %i, align 4
  %15 = sext i32 %14 to i64
  %16 = getelementptr inbounds [20 x i32], [20 x i32]* @stored_elements, i64 0, i64 %15
  %17 = load i32, i32* %16, align 4
  %18 = icmp eq i32 %13, %17
  br i1 %18, label %19, label %20

; <label>:19                                      ; preds = %9
  call void @__assert_fail(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.2, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.3, i32 0, i32 0), i32 136, i8* getelementptr inbounds ([17 x i8], [17 x i8]* @__PRETTY_FUNCTION__.t2, i32 0, i32 0)) #5
  unreachable

; <label>:20                                      ; preds = %9
  store i8 0, i8* @dequeue_flag, align 1
  store i8 1, i8* @enqueue_flag, align 1
  br label %21

; <label>:21                                      ; preds = %20, %5
  %22 = call i32 @pthread_mutex_unlock(%union.pthread_mutex_t* @m) #4
  br label %23

; <label>:23                                      ; preds = %21
  %24 = load i32, i32* %i, align 4
  %25 = add nsw i32 %24, 1
  store i32 %25, i32* %i, align 4
  br label %2

; <label>:26                                      ; preds = %2
  ret i8* null
}

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %id1 = alloca i64, align 8
  %id2 = alloca i64, align 8
  store i32 0, i32* %1, align 4
  store i8 1, i8* @enqueue_flag, align 1
  store i8 0, i8* @dequeue_flag, align 1
  call void @init(%struct.QType* @queue)
  %2 = call i32 @empty(%struct.QType* @queue)
  %3 = icmp ne i32 %2, 0
  %4 = xor i1 %3, true
  %5 = zext i1 %4 to i32
  %6 = icmp eq i32 %5, -1
  br i1 %6, label %7, label %8

; <label>:7                                       ; preds = %0
  call void @__assert_fail(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.2, i32 0, i32 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.3, i32 0, i32 0), i32 159, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__PRETTY_FUNCTION__.main, i32 0, i32 0)) #5
  unreachable

; <label>:8                                       ; preds = %0
  %9 = call i32 @pthread_mutex_init(%union.pthread_mutex_t* @m, %union.pthread_mutexattr_t* null) #4
  %10 = call i32 @pthread_create(i64* %id1, %union.pthread_attr_t* null, i8* (i8*)* @t1, i8* bitcast (%struct.QType* @queue to i8*)) #4
  %11 = call i32 @pthread_create(i64* %id2, %union.pthread_attr_t* null, i8* (i8*)* @t2, i8* bitcast (%struct.QType* @queue to i8*)) #4
  %12 = load i64, i64* %id1, align 8
  %13 = call i32 @pthread_join(i64 %12, i8** null)
  %14 = load i64, i64* %id2, align 8
  %15 = call i32 @pthread_join(i64 %14, i8** null)
  ret i32 0
}

; Function Attrs: nounwind
declare i32 @pthread_mutex_init(%union.pthread_mutex_t*, %union.pthread_mutexattr_t*) #2

; Function Attrs: nounwind
declare i32 @pthread_create(i64*, %union.pthread_attr_t*, i8* (i8*)*, i8*) #2

declare i32 @pthread_join(i64, i8**) #1

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }
attributes #5 = { noreturn nounwind }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.0-2ubuntu3~trusty5 (tags/RELEASE_380/final)"}
