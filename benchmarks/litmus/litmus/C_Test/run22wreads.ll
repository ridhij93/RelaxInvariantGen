; ModuleID = '/home/ridhi/Documents/litmus/run22wreads.cpp'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"class.std::ios_base::Init" = type { i8 }
%"class.std::basic_ostream" = type { i32 (...)**, %"class.std::basic_ios" }
%"class.std::basic_ios" = type { %"class.std::ios_base", %"class.std::basic_ostream"*, i8, i8, %"class.std::basic_streambuf"*, %"class.std::ctype"*, %"class.std::num_put"*, %"class.std::num_get"* }
%"class.std::ios_base" = type { i32 (...)**, i64, i64, i32, i32, i32, %"struct.std::ios_base::_Callback_list"*, %"struct.std::ios_base::_Words", [8 x %"struct.std::ios_base::_Words"], i32, %"struct.std::ios_base::_Words"*, %"class.std::locale" }
%"struct.std::ios_base::_Callback_list" = type { %"struct.std::ios_base::_Callback_list"*, void (i32, %"class.std::ios_base"*, i32)*, i32, i32 }
%"struct.std::ios_base::_Words" = type { i8*, i64 }
%"class.std::locale" = type { %"class.std::locale::_Impl"* }
%"class.std::locale::_Impl" = type { i32, %"class.std::locale::facet"**, i64, %"class.std::locale::facet"**, i8** }
%"class.std::locale::facet" = type <{ i32 (...)**, i32, [4 x i8] }>
%"class.std::basic_streambuf" = type { i32 (...)**, i8*, i8*, i8*, i8*, i8*, i8*, %"class.std::locale" }
%"class.std::ctype" = type <{ %"class.std::locale::facet.base", [4 x i8], %struct.__locale_struct*, i8, [7 x i8], i32*, i32*, i16*, i8, [256 x i8], [256 x i8], i8, [6 x i8] }>
%"class.std::locale::facet.base" = type <{ i32 (...)**, i32 }>
%struct.__locale_struct = type { [13 x %struct.__locale_data*], i16*, i32*, i32*, [13 x i8*] }
%struct.__locale_data = type opaque
%"class.std::num_put" = type { %"class.std::locale::facet.base", [4 x i8] }
%"class.std::num_get" = type { %"class.std::locale::facet.base", [4 x i8] }
%union.pthread_attr_t = type { i64, [48 x i8] }

@_ZStL8__ioinit = internal global %"class.std::ios_base::Init" zeroinitializer, align 1
@__dso_handle = external global i8
@x = global i32 0, align 4
@y = global i32 0, align 4
@a = global i32 0, align 4
@b = global i32 0, align 4
@_ZSt4cout = external global %"class.std::basic_ostream", align 8
@.str = private unnamed_addr constant [17 x i8] c"Assertion Failed\00", align 1
@.str.1 = private unnamed_addr constant [4 x i8] c"xy:\00", align 1
@.str.2 = private unnamed_addr constant [2 x i8] c" \00", align 1
@llvm.global_ctors = appending global [1 x { i32, void ()*, i8* }] [{ i32, void ()*, i8* } { i32 65535, void ()* @_GLOBAL__sub_I_run22wreads.cpp, i8* null }]

; Function Attrs: uwtable
define internal void @__cxx_global_var_init() #0 section ".text.startup" {
  call void @_ZNSt8ios_base4InitC1Ev(%"class.std::ios_base::Init"* @_ZStL8__ioinit)
  %1 = call i32 @__cxa_atexit(void (i8*)* bitcast (void (%"class.std::ios_base::Init"*)* @_ZNSt8ios_base4InitD1Ev to void (i8*)*), i8* getelementptr inbounds (%"class.std::ios_base::Init", %"class.std::ios_base::Init"* @_ZStL8__ioinit, i32 0, i32 0), i8* @__dso_handle) #3
  ret void
}

declare void @_ZNSt8ios_base4InitC1Ev(%"class.std::ios_base::Init"*) #1

; Function Attrs: nounwind
declare void @_ZNSt8ios_base4InitD1Ev(%"class.std::ios_base::Init"*) #2

; Function Attrs: nounwind
declare i32 @__cxa_atexit(void (i8*)*, i8*, i8*) #3

; Function Attrs: nounwind uwtable
define i8* @_Z7thread1Pv(i8* %threadid) #4 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  store i8* %threadid, i8** %2, align 8
  store i32 2, i32* @x, align 4
  store i32 1, i32* @y, align 4
  call void @llvm.trap()
  unreachable
                                                  ; No predecessors!
  %4 = load i8*, i8** %1, align 8
  ret i8* %4
}

; Function Attrs: noreturn nounwind
declare void @llvm.trap() #5

; Function Attrs: nounwind uwtable
define i8* @_Z7thread2Pv(i8* %threadid) #4 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  store i8* %threadid, i8** %2, align 8
  store i32 2, i32* @y, align 4
  store i32 1, i32* @x, align 4
  call void @llvm.trap()
  unreachable
                                                  ; No predecessors!
  %4 = load i8*, i8** %1, align 8
  ret i8* %4
}

; Function Attrs: nounwind uwtable
define i8* @_Z7thread3Pv(i8* %threadid) #4 {
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
  call void @llvm.trap()
  unreachable
                                                  ; No predecessors!
  %13 = load i8*, i8** %1, align 8
  ret i8* %13
}

; Function Attrs: nounwind uwtable
define i8* @_Z7thread4Pv(i8* %threadid) #4 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  %r = alloca i32, align 4
  %s = alloca i32, align 4
  store i8* %threadid, i8** %2, align 8
  %3 = load i32, i32* @y, align 4
  store i32 %3, i32* %r, align 4
  %4 = load i32, i32* @y, align 4
  store i32 %4, i32* %s, align 4
  %5 = load i32, i32* %r, align 4
  %6 = icmp eq i32 %5, 1
  br i1 %6, label %7, label %11

; <label>:7                                       ; preds = %0
  %8 = load i32, i32* %s, align 4
  %9 = icmp eq i32 %8, 2
  br i1 %9, label %10, label %11

; <label>:10                                      ; preds = %7
  store i32 1, i32* @b, align 4
  br label %11

; <label>:11                                      ; preds = %10, %7, %0
  call void @llvm.trap()
  unreachable
                                                  ; No predecessors!
  %13 = load i8*, i8** %1, align 8
  ret i8* %13
}

; Function Attrs: norecurse uwtable
define i32 @main() #6 {
  %1 = alloca i32, align 4
  %i = alloca i32, align 4
  %rc1 = alloca i32, align 4
  %rc2 = alloca i32, align 4
  %rc3 = alloca i32, align 4
  %rc4 = alloca i32, align 4
  %threads = alloca [4 x i64], align 16
  store i32 0, i32* %1, align 4
  store i32 0, i32* %i, align 4
  %2 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 0
  %3 = load i32, i32* %i, align 4
  %4 = sext i32 %3 to i64
  %5 = inttoptr i64 %4 to i8*
  %6 = call i32 @pthread_create(i64* %2, %union.pthread_attr_t* null, i8* (i8*)* @_Z7thread1Pv, i8* %5) #3
  store i32 %6, i32* %rc1, align 4
  %7 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 1
  %8 = load i32, i32* %i, align 4
  %9 = sext i32 %8 to i64
  %10 = inttoptr i64 %9 to i8*
  %11 = call i32 @pthread_create(i64* %7, %union.pthread_attr_t* null, i8* (i8*)* @_Z7thread2Pv, i8* %10) #3
  store i32 %11, i32* %rc2, align 4
  %12 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 2
  %13 = load i32, i32* %i, align 4
  %14 = sext i32 %13 to i64
  %15 = inttoptr i64 %14 to i8*
  %16 = call i32 @pthread_create(i64* %12, %union.pthread_attr_t* null, i8* (i8*)* @_Z7thread3Pv, i8* %15) #3
  store i32 %16, i32* %rc3, align 4
  %17 = getelementptr inbounds [4 x i64], [4 x i64]* %threads, i64 0, i64 3
  %18 = load i32, i32* %i, align 4
  %19 = sext i32 %18 to i64
  %20 = inttoptr i64 %19 to i8*
  %21 = call i32 @pthread_create(i64* %17, %union.pthread_attr_t* null, i8* (i8*)* @_Z7thread4Pv, i8* %20) #3
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
  br i1 %35, label %36, label %42

; <label>:36                                      ; preds = %0
  %37 = load i32, i32* @b, align 4
  %38 = icmp eq i32 %37, 1
  br i1 %38, label %39, label %42

; <label>:39                                      ; preds = %36
  %40 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(%"class.std::basic_ostream"* dereferenceable(272) @_ZSt4cout, i8* getelementptr inbounds ([17 x i8], [17 x i8]* @.str, i32 0, i32 0))
  %41 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSolsEPFRSoS_E(%"class.std::basic_ostream"* %40, %"class.std::basic_ostream"* (%"class.std::basic_ostream"*)* @_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_)
  br label %42

; <label>:42                                      ; preds = %39, %36, %0
  %43 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(%"class.std::basic_ostream"* dereferenceable(272) @_ZSt4cout, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i32 0, i32 0))
  %44 = load i32, i32* @a, align 4
  %45 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSolsEi(%"class.std::basic_ostream"* %43, i32 %44)
  %46 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(%"class.std::basic_ostream"* dereferenceable(272) %45, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i32 0, i32 0))
  %47 = load i32, i32* @b, align 4
  %48 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSolsEi(%"class.std::basic_ostream"* %46, i32 %47)
  %49 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(%"class.std::basic_ostream"* dereferenceable(272) %48, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i32 0, i32 0))
  %50 = load i32, i32* @x, align 4
  %51 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSolsEi(%"class.std::basic_ostream"* %49, i32 %50)
  %52 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(%"class.std::basic_ostream"* dereferenceable(272) %51, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i32 0, i32 0))
  %53 = load i32, i32* @y, align 4
  %54 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZNSolsEi(%"class.std::basic_ostream"* %52, i32 %53)
  %55 = call dereferenceable(272) %"class.std::basic_ostream"* @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c(%"class.std::basic_ostream"* dereferenceable(272) %54, i8 signext 10)
  %56 = load i32, i32* %1, align 4
  ret i32 %56
}

; Function Attrs: nounwind
declare i32 @pthread_create(i64*, %union.pthread_attr_t*, i8* (i8*)*, i8*) #2

declare i32 @pthread_join(i64, i8**) #1

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(%"class.std::basic_ostream"* dereferenceable(272), i8*) #1

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZNSolsEPFRSoS_E(%"class.std::basic_ostream"*, %"class.std::basic_ostream"* (%"class.std::basic_ostream"*)*) #1

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_(%"class.std::basic_ostream"* dereferenceable(272)) #1

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c(%"class.std::basic_ostream"* dereferenceable(272), i8 signext) #1

declare dereferenceable(272) %"class.std::basic_ostream"* @_ZNSolsEi(%"class.std::basic_ostream"*, i32) #1

; Function Attrs: uwtable
define internal void @_GLOBAL__sub_I_run22wreads.cpp() #0 section ".text.startup" {
  call void @__cxx_global_var_init()
  ret void
}

attributes #0 = { uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }
attributes #4 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noreturn nounwind }
attributes #6 = { norecurse uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.0-2ubuntu3~trusty5 (tags/RELEASE_380/final)"}
