; ModuleID = 'RWC.cpp'
source_filename = "RWC.cpp"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"class.std::ios_base::Init" = type { i8 }
%union.pthread_attr_t = type { i64, [48 x i8] }

@_ZStL8__ioinit = internal global %"class.std::ios_base::Init" zeroinitializer, align 1
@__dso_handle = external hidden global i8
@x = dso_local global i32 0, align 4
@y = dso_local global i32 0, align 4
@a = dso_local global i32 0, align 4
@b = dso_local global i32 0, align 4
@.str = private unnamed_addr constant [17 x i8] c"a != 1 || b != 1\00", align 1
@.str.1 = private unnamed_addr constant [8 x i8] c"RWC.cpp\00", align 1
@__PRETTY_FUNCTION__.main = private unnamed_addr constant [11 x i8] c"int main()\00", align 1
@llvm.global_ctors = appending global [1 x { i32, void ()*, i8* }] [{ i32, void ()*, i8* } { i32 65535, void ()* @_GLOBAL__sub_I_RWC.cpp, i8* null }]

; Function Attrs: noinline uwtable
define internal void @__cxx_global_var_init() #0 section ".text.startup" {
entry:
  call void @_ZNSt8ios_base4InitC1Ev(%"class.std::ios_base::Init"* @_ZStL8__ioinit)
  %0 = call i32 @__cxa_atexit(void (i8*)* bitcast (void (%"class.std::ios_base::Init"*)* @_ZNSt8ios_base4InitD1Ev to void (i8*)*), i8* getelementptr inbounds (%"class.std::ios_base::Init", %"class.std::ios_base::Init"* @_ZStL8__ioinit, i32 0, i32 0), i8* @__dso_handle) #3
  ret void
}

declare dso_local void @_ZNSt8ios_base4InitC1Ev(%"class.std::ios_base::Init"*) unnamed_addr #1

; Function Attrs: nounwind
declare dso_local void @_ZNSt8ios_base4InitD1Ev(%"class.std::ios_base::Init"*) unnamed_addr #2

; Function Attrs: nounwind
declare dso_local i32 @__cxa_atexit(void (i8*)*, i8*, i8*) #3

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @_Z7thread1Pv(i8* %threadid) #4 {
entry:
  %threadid.addr = alloca i8*, align 8
  store i8* %threadid, i8** %threadid.addr, align 8
  store i32 1, i32* @x, align 4
  call void @llvm.trap()
  unreachable
}

; Function Attrs: cold noreturn nounwind
declare void @llvm.trap() #5

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @_Z7thread2Pv(i8* %threadid) #4 {
entry:
  %threadid.addr = alloca i8*, align 8
  %p = alloca i32, align 4
  %q = alloca i32, align 4
  store i8* %threadid, i8** %threadid.addr, align 8
  %0 = load i32, i32* @x, align 4
  store i32 %0, i32* %p, align 4
  %1 = load i32, i32* @y, align 4
  store i32 %1, i32* %q, align 4
  %2 = load i32, i32* %p, align 4
  %cmp = icmp eq i32 %2, 1
  br i1 %cmp, label %land.lhs.true, label %if.end

land.lhs.true:                                    ; preds = %entry
  %3 = load i32, i32* %q, align 4
  %cmp1 = icmp eq i32 %3, 0
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %land.lhs.true
  store i32 1, i32* @a, align 4
  br label %if.end

if.end:                                           ; preds = %if.then, %land.lhs.true, %entry
  call void @llvm.trap()
  unreachable
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i8* @_Z7thread3Pv(i8* %threadid) #4 {
entry:
  %threadid.addr = alloca i8*, align 8
  %r = alloca i32, align 4
  store i8* %threadid, i8** %threadid.addr, align 8
  store i32 1, i32* @y, align 4
  %0 = load i32, i32* @x, align 4
  store i32 %0, i32* %r, align 4
  %1 = load i32, i32* %r, align 4
  %cmp = icmp eq i32 %1, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  store i32 1, i32* @b, align 4
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  call void @llvm.trap()
  unreachable
}

; Function Attrs: noinline norecurse optnone uwtable
define dso_local i32 @main() #6 {
entry:
  %retval = alloca i32, align 4
  %i = alloca i32, align 4
  %j = alloca i32, align 4
  %rc1 = alloca i32, align 4
  %rc2 = alloca i32, align 4
  %rc3 = alloca i32, align 4
  %threads = alloca [3 x i64], align 16
  store i32 0, i32* %retval, align 4
  store i32 0, i32* %i, align 4
  store i32 1, i32* %j, align 4
  %arrayidx = getelementptr inbounds [3 x i64], [3 x i64]* %threads, i64 0, i64 0
  %0 = load i32, i32* %i, align 4
  %conv = sext i32 %0 to i64
  %1 = inttoptr i64 %conv to i8*
  %call = call i32 @pthread_create(i64* %arrayidx, %union.pthread_attr_t* null, i8* (i8*)* @_Z7thread1Pv, i8* %1) #3
  store i32 %call, i32* %rc1, align 4
  %arrayidx1 = getelementptr inbounds [3 x i64], [3 x i64]* %threads, i64 0, i64 1
  %2 = load i32, i32* %j, align 4
  %conv2 = sext i32 %2 to i64
  %3 = inttoptr i64 %conv2 to i8*
  %call3 = call i32 @pthread_create(i64* %arrayidx1, %union.pthread_attr_t* null, i8* (i8*)* @_Z7thread2Pv, i8* %3) #3
  store i32 %call3, i32* %rc2, align 4
  %arrayidx4 = getelementptr inbounds [3 x i64], [3 x i64]* %threads, i64 0, i64 2
  %4 = load i32, i32* %j, align 4
  %conv5 = sext i32 %4 to i64
  %5 = inttoptr i64 %conv5 to i8*
  %call6 = call i32 @pthread_create(i64* %arrayidx4, %union.pthread_attr_t* null, i8* (i8*)* @_Z7thread3Pv, i8* %5) #3
  store i32 %call6, i32* %rc3, align 4
  %arrayidx7 = getelementptr inbounds [3 x i64], [3 x i64]* %threads, i64 0, i64 0
  %6 = load i64, i64* %arrayidx7, align 16
  %call8 = call i32 @pthread_join(i64 %6, i8** null)
  %arrayidx9 = getelementptr inbounds [3 x i64], [3 x i64]* %threads, i64 0, i64 1
  %7 = load i64, i64* %arrayidx9, align 8
  %call10 = call i32 @pthread_join(i64 %7, i8** null)
  %arrayidx11 = getelementptr inbounds [3 x i64], [3 x i64]* %threads, i64 0, i64 2
  %8 = load i64, i64* %arrayidx11, align 16
  %call12 = call i32 @pthread_join(i64 %8, i8** null)
  %9 = load i32, i32* @a, align 4
  %cmp = icmp ne i32 %9, 1
  br i1 %cmp, label %lor.end, label %lor.rhs

lor.rhs:                                          ; preds = %entry
  %10 = load i32, i32* @b, align 4
  %cmp13 = icmp ne i32 %10, 1
  br label %lor.end

lor.end:                                          ; preds = %lor.rhs, %entry
  %11 = phi i1 [ true, %entry ], [ %cmp13, %lor.rhs ]
  br i1 %11, label %cond.true, label %cond.false

cond.true:                                        ; preds = %lor.end
  br label %cond.end

cond.false:                                       ; preds = %lor.end
  call void @__assert_fail(i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.1, i64 0, i64 0), i32 50, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__PRETTY_FUNCTION__.main, i64 0, i64 0)) #8
  unreachable

12:                                               ; No predecessors!
  br label %cond.end

cond.end:                                         ; preds = %12, %cond.true
  %13 = load i32, i32* %retval, align 4
  ret i32 %13
}

; Function Attrs: nounwind
declare dso_local i32 @pthread_create(i64*, %union.pthread_attr_t*, i8* (i8*)*, i8*) #2

declare dso_local i32 @pthread_join(i64, i8**) #1

; Function Attrs: noreturn nounwind
declare dso_local void @__assert_fail(i8*, i8*, i32, i8*) #7

; Function Attrs: noinline uwtable
define internal void @_GLOBAL__sub_I_RWC.cpp() #0 section ".text.startup" {
entry:
  call void @__cxx_global_var_init()
  ret void
}

attributes #0 = { noinline uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }
attributes #4 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { cold noreturn nounwind }
attributes #6 = { noinline norecurse optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #8 = { noreturn nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 11.1.0"}
