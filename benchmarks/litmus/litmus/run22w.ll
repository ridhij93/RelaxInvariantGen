source_filename = "test"
target datalayout = "e-m:e-p:64:64-i64:64-f80:128-n8:16:32:64-S128"

@global_var_600ff8 = local_unnamed_addr global i64 0
@global_var_600e00 = global i64 0
@global_var_400b17 = constant [17 x i8] c"Assertion failed\00"
@global_var_601080 = global i64 0
@global_var_60119c = external global i64
@global_var_601070 = global i64 0
@global_var_600de8 = global i64 4196624
@global_var_600df8 = global i64 4196592
@global_var_601190 = local_unnamed_addr global i8 0
@global_var_601194 = local_unnamed_addr global i32 0
@global_var_601198 = local_unnamed_addr global i32 0

define i64 @function_400768() local_unnamed_addr {
dec_label_pc_400768:
  %v0_40076c = load i64, i64* @global_var_600ff8, align 8
  %v1_400773 = icmp eq i64 %v0_40076c, 0
  br i1 %v1_400773, label %dec_label_pc_40077d, label %dec_label_pc_400778

dec_label_pc_400778:                              ; preds = %dec_label_pc_400768
  %v0_400778 = call i64 @function_4007a0()
  br label %dec_label_pc_40077d

dec_label_pc_40077d:                              ; preds = %dec_label_pc_400778, %dec_label_pc_400768
  %rax.0 = phi i64 [ 0, %dec_label_pc_400768 ], [ %v0_400778, %dec_label_pc_400778 ]
  ret i64 %rax.0
}

define i64 @function_4007a0() local_unnamed_addr {
dec_label_pc_4007a0:
  %v0_4007a0 = call i64 @__gmon_start__.1()
  ret i64 %v0_4007a0
}

define i64 @function_4007b0() local_unnamed_addr {
dec_label_pc_4007b0:
  %v0_4007b0 = call i64 @_ZNSt8ios_base4InitC1Ev()
  ret i64 %v0_4007b0
}

define i32 @function_4007c0(i64 %main, i32 %argc, i8** %ubp_av, void ()* %init, void ()* %fini, void ()* %rtld_fini) local_unnamed_addr {
dec_label_pc_4007c0:
  %v11_4007c0 = call i32 @__libc_start_main(i64 %main, i32 %argc, i8** %ubp_av, void ()* %init, void ()* %fini, void ()* %rtld_fini)
  ret i32 %v11_4007c0
}

define i32 @function_4007d0(void (i64*)* %func, i64* %arg, i64* %dso_handle) local_unnamed_addr {
dec_label_pc_4007d0:
  %v6_4007d0 = call i32 @__cxa_atexit(void (i64*)* %func, i64* %arg, i64* %dso_handle)
  ret i32 %v6_4007d0
}

define i64 @_ZNSt8ios_base4InitD1Ev.3() local_unnamed_addr {
dec_label_pc_4007e0:
  %v0_4007e0 = call i64 @_ZNSt8ios_base4InitD1Ev()
  ret i64 %v0_4007e0
}

define i64 @function_4007f0(i64* %arg1, i8* %arg2) local_unnamed_addr {
dec_label_pc_4007f0:
  %v4_4007f0 = call i64 @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(i64* %arg1, i8* %arg2)
  ret i64 %v4_4007f0
}

define i32 @function_400800(i32* %newthread, i64* %attr, i64* (i64*)* %start_routine, i64* %arg) local_unnamed_addr {
dec_label_pc_400800:
  %v8_400800 = call i32 @pthread_create(i32* %newthread, i64* %attr, i64* (i64*)* %start_routine, i64* %arg)
  ret i32 %v8_400800
}

define i32 @function_400810(i32 %th, i64** %thread_return) local_unnamed_addr {
dec_label_pc_400810:
  %v4_400810 = call i32 @pthread_join(i32 %th, i64** %thread_return)
  ret i32 %v4_400810
}

define i64 @function_400820(i64* (i64*)* %arg1) local_unnamed_addr {
dec_label_pc_400820:
  %v2_400820 = call i64 @_ZNSolsEPFRSoS_E(i64* (i64*)* %arg1)
  ret i64 %v2_400820
}

define i64 @_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_.2(i64* %arg1) local_unnamed_addr {
dec_label_pc_400830:
  %v2_400830 = call i64 @_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_(i64* %arg1)
  ret i64 %v2_400830
}

define i64 @entry_point(i64 %arg1, i64 %arg2, i64 %arg3, i64 %arg4) local_unnamed_addr {
dec_label_pc_400840:
  %stack_var_8 = alloca i64, align 8
  %tmp29 = bitcast i64* %stack_var_8 to i8**
  %v2_400864 = trunc i64 %arg4 to i32
  %v13_400864 = inttoptr i64 %arg3 to void ()*
  %v14_400864 = call i32 @__libc_start_main(i64 4196722, i32 %v2_400864, i8** nonnull %tmp29, void ()* inttoptr (i64 4197008 to void ()*), void ()* inttoptr (i64 4197120 to void ()*), void ()* %v13_400864)
  %v0_400869 = call i64 @__asm_hlt()
  unreachable
}

define i64 @function_400870() local_unnamed_addr {
dec_label_pc_400870:
  ret i64 7
}

define i64 @function_4008b0(i64* %arg1) local_unnamed_addr {
dec_label_pc_4008b0:
  ret i64 0
}

define i64 @function_4008f0() local_unnamed_addr {
dec_label_pc_4008f0:
  %tmp2 = call i64 @__decompiler_undefined_function_0()
  %v0_4008f0 = load i8, i8* @global_var_601190, align 1
  %v7_4008f0 = icmp eq i8 %v0_4008f0, 0
  %v1_4008f7 = icmp eq i1 %v7_4008f0, false
  br i1 %v1_4008f7, label %dec_label_pc_40090a, label %dec_label_pc_4008f9

dec_label_pc_4008f9:                              ; preds = %dec_label_pc_4008f0
  %v0_4008fd = call i64 @function_400870()
  store i8 1, i8* @global_var_601190, align 1
  br label %dec_label_pc_40090a

dec_label_pc_40090a:                              ; preds = %dec_label_pc_4008f9, %dec_label_pc_4008f0
  %rax.0 = phi i64 [ %tmp2, %dec_label_pc_4008f0 ], [ %v0_4008fd, %dec_label_pc_4008f9 ]
  ret i64 %rax.0
}

define i64 @function_400910() local_unnamed_addr {
dec_label_pc_400910:
  %v2_40091b = call i64 @function_4008b0(i64* nonnull @global_var_600e00)
  ret i64 %v2_40091b
}

define i64 @function_400936(i64 %arg1) local_unnamed_addr {
dec_label_pc_400936:
  %tmp3 = call i64 @__decompiler_undefined_function_0()
  store i32 2, i32* @global_var_601194, align 4
  store i32 1, i32* @global_var_601198, align 4
  ret i64 %tmp3
}

define i64 @function_400954(i64 %arg1) local_unnamed_addr {
dec_label_pc_400954:
  %tmp3 = call i64 @__decompiler_undefined_function_0()
  store i32 3, i32* @global_var_601198, align 4
  store i32 4, i32* @global_var_601194, align 4
  ret i64 %tmp3
}

define i64 @function_400972() local_unnamed_addr {
dec_label_pc_400972:
  %stack_var_-16 = alloca i64, align 8
  %stack_var_-24 = alloca i64, align 8
  %tmp46 = bitcast i64* %stack_var_-24 to i32*
  %v10_4009a4 = call i32 @pthread_create(i32* nonnull %tmp46, i64* null, i64* (i64*)* inttoptr (i64 4196662 to i64* (i64*)*), i64* null)
  %tmp47 = bitcast i64* %stack_var_-16 to i32*
  %v10_4009cc = call i32 @pthread_create(i32* nonnull %tmp47, i64* null, i64* (i64*)* inttoptr (i64 4196692 to i64* (i64*)*), i64* inttoptr (i64 1 to i64*))
  %v3_4009d4 = load i64, i64* %stack_var_-24, align 8
  %v1_4009dd = trunc i64 %v3_4009d4 to i32
  %v6_4009e0 = call i32 @pthread_join(i32 %v1_4009dd, i64** null)
  %v3_4009e5 = load i64, i64* %stack_var_-16, align 8
  %v1_4009ee = trunc i64 %v3_4009e5 to i32
  %v6_4009f1 = call i32 @pthread_join(i32 %v1_4009ee, i64** null)
  %v0_4009f6 = load i32, i32* @global_var_601194, align 4
  %v11_4009fc = icmp eq i32 %v0_4009f6, 2
  %v1_4009ff = icmp eq i1 %v11_4009fc, false
  br i1 %v1_4009ff, label %dec_label_pc_400a28, label %dec_label_pc_400a01

dec_label_pc_400a01:                              ; preds = %dec_label_pc_400972
  %v0_400a01 = load i32, i32* @global_var_601198, align 4
  %v11_400a07 = icmp eq i32 %v0_400a01, 3
  %v1_400a0a = icmp eq i1 %v11_400a07, false
  br i1 %v1_400a0a, label %dec_label_pc_400a28, label %dec_label_pc_400a0c

dec_label_pc_400a0c:                              ; preds = %dec_label_pc_400a01
  %v5_400a16 = call i64 @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(i64* nonnull @global_var_601080, i8* getelementptr inbounds ([17 x i8], [17 x i8]* @global_var_400b17, i64 0, i64 0))
  %v1_400a20 = inttoptr i64 %v5_400a16 to i64* (i64*)*
  %v3_400a23 = call i64 @_ZNSolsEPFRSoS_E(i64* (i64*)* %v1_400a20)
  br label %dec_label_pc_400a28

dec_label_pc_400a28:                              ; preds = %dec_label_pc_400a0c, %dec_label_pc_400a01, %dec_label_pc_400972
  ret i64 0
}

define i64 @function_400a2f(i64 %arg1, i64 %arg2) local_unnamed_addr {
dec_label_pc_400a2f:
  %tmp7 = call i64 @__decompiler_undefined_function_0()
  %v4_400a3d = trunc i64 %arg1 to i32
  %v14_400a3d = icmp eq i32 %v4_400a3d, 1
  %v1_400a41 = icmp eq i1 %v14_400a3d, false
  br i1 %v1_400a41, label %dec_label_pc_400a6a, label %dec_label_pc_400a43

dec_label_pc_400a43:                              ; preds = %dec_label_pc_400a2f
  %v4_400a43 = trunc i64 %arg2 to i32
  %v14_400a43 = icmp eq i32 %v4_400a43, 65535
  %v1_400a4a = icmp eq i1 %v14_400a43, false
  br i1 %v1_400a4a, label %dec_label_pc_400a6a, label %dec_label_pc_400a4c

dec_label_pc_400a4c:                              ; preds = %dec_label_pc_400a43
  %v0_400a51 = call i64 @_ZNSt8ios_base4InitC1Ev()
  %v7_400a65 = call i32 @__cxa_atexit(void (i64*)* inttoptr (i64 4196320 to void (i64*)*), i64* nonnull @global_var_60119c, i64* nonnull @global_var_601070)
  %v9_400a65 = sext i32 %v7_400a65 to i64
  br label %dec_label_pc_400a6a

dec_label_pc_400a6a:                              ; preds = %dec_label_pc_400a4c, %dec_label_pc_400a43, %dec_label_pc_400a2f
  %rax.0 = phi i64 [ %tmp7, %dec_label_pc_400a2f ], [ %tmp7, %dec_label_pc_400a43 ], [ %v9_400a65, %dec_label_pc_400a4c ]
  ret i64 %rax.0
}

define i64 @function_400a6c() local_unnamed_addr {
dec_label_pc_400a6c:
  %v2_400a7a = call i64 @function_400a2f(i64 1, i64 65535)
  ret i64 %v2_400a7a
}

define i64 @function_400a90(i64 %arg1, i64 %arg2, i64 %arg3) local_unnamed_addr {
dec_label_pc_400a90:
  %v0_400abe = call i64 @function_400768()
  br i1 icmp eq (i64 ashr (i64 sub (i64 ptrtoint (i64* @global_var_600df8 to i64), i64 ptrtoint (i64* @global_var_600de8 to i64)), i64 3), i64 0), label %dec_label_pc_400ae6, label %dec_label_pc_400ad0

dec_label_pc_400ad0:                              ; preds = %dec_label_pc_400a90, %dec_label_pc_400ad0
  %rbx.0 = phi i64 [ %v1_400add, %dec_label_pc_400ad0 ], [ 0, %dec_label_pc_400a90 ]
  %v1_400add = add i64 %rbx.0, 1
  %v12_400ae1 = icmp eq i64 %v1_400add, ashr (i64 sub (i64 ptrtoint (i64* @global_var_600df8 to i64), i64 ptrtoint (i64* @global_var_600de8 to i64)), i64 3)
  %v1_400ae4 = icmp eq i1 %v12_400ae1, false
  br i1 %v1_400ae4, label %dec_label_pc_400ad0, label %dec_label_pc_400ae6

dec_label_pc_400ae6:                              ; preds = %dec_label_pc_400ad0, %dec_label_pc_400a90
  ret i64 %v0_400abe
}

define i64 @function_400b00() local_unnamed_addr {
dec_label_pc_400b00:
  %tmp = call i64 @__decompiler_undefined_function_0()
  ret i64 %tmp
}

define i64 @function_400b04() local_unnamed_addr {
dec_label_pc_400b04:
  %tmp1 = call i64 @__decompiler_undefined_function_0()
  ret i64 %tmp1
}

declare i64 @__gmon_start__.1() local_unnamed_addr

declare i64 @_ZNSt8ios_base4InitC1Ev() local_unnamed_addr

declare i32 @__libc_start_main(i64, i32, i8**, void ()*, void ()*, void ()*) local_unnamed_addr

declare i32 @__cxa_atexit(void (i64*)*, i64*, i64*) local_unnamed_addr

declare i64 @_ZNSt8ios_base4InitD1Ev() local_unnamed_addr

declare i64 @_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc(i64*, i8*) local_unnamed_addr

declare i32 @pthread_create(i32*, i64*, i64* (i64*)*, i64*) local_unnamed_addr

declare i32 @pthread_join(i32, i64**) local_unnamed_addr

declare i64 @_ZNSolsEPFRSoS_E(i64* (i64*)*) local_unnamed_addr

declare i64 @_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_(i64*) local_unnamed_addr

declare i64 @__asm_hlt() local_unnamed_addr

declare i64 @__decompiler_undefined_function_0() local_unnamed_addr
