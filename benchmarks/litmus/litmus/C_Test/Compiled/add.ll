source_filename = "test"
target datalayout = "e-m:e-p:64:64-i64:64-f80:128-n8:16:32:64-S128"

@global_var_600ff8 = local_unnamed_addr global i64 0
@global_var_601057 = local_unnamed_addr global i64 0
@global_var_600e10 = local_unnamed_addr global i64 0
@global_var_400992 = constant [5 x i8] c"main\00"
@global_var_400958 = constant [6 x i8] c"add.c\00"
@global_var_400960 = constant [37 x i8] c"! ((a==1 && b==1) || (a==2 && b==2))\00"
@global_var_400985 = constant [13 x i8] c"a==1 && b==1\00"
@global_var_600e00 = local_unnamed_addr global i64 4195968
@global_var_600e08 = local_unnamed_addr global i64 4195936
@0 = external global i32
@global_var_601050 = local_unnamed_addr global i8 0
@global_var_601054 = local_unnamed_addr global i32 0
@global_var_601058 = local_unnamed_addr global i32 0
@global_var_60105c = local_unnamed_addr global i32 0

define i64 @main(i64 %argc, i8** %argv) local_unnamed_addr {
dec_label_pc_40075e:
  %stack_var_-16 = alloca i64, align 8
  %stack_var_-24 = alloca i64, align 8
  %stack_var_-32 = alloca i64, align 8
  %stack_var_-40 = alloca i64, align 8
  %tmp86 = bitcast i64* %stack_var_-40 to i32*
  %v10_400790 = call i32 @pthread_create(i32* nonnull %tmp86, i64* null, i64* (i64*)* inttoptr (i64 4196006 to i64* (i64*)*), i64* null)
  %tmp87 = bitcast i64* %stack_var_-32 to i32*
  %v10_4007b8 = call i32 @pthread_create(i32* nonnull %tmp87, i64* null, i64* (i64*)* inttoptr (i64 4196026 to i64* (i64*)*), i64* inttoptr (i64 1 to i64*))
  %tmp88 = bitcast i64* %stack_var_-24 to i32*
  %v10_4007e0 = call i32 @pthread_create(i32* nonnull %tmp88, i64* null, i64* (i64*)* inttoptr (i64 4196046 to i64* (i64*)*), i64* null)
  %tmp89 = bitcast i64* %stack_var_-16 to i32*
  %v10_400808 = call i32 @pthread_create(i32* nonnull %tmp89, i64* null, i64* (i64*)* inttoptr (i64 4196118 to i64* (i64*)*), i64* inttoptr (i64 1 to i64*))
  %v3_400810 = load i64, i64* %stack_var_-40, align 8
  %v1_400819 = trunc i64 %v3_400810 to i32
  %v6_40081c = call i32 @pthread_join(i32 %v1_400819, i64** null)
  %v3_400821 = load i64, i64* %stack_var_-32, align 8
  %v1_40082a = trunc i64 %v3_400821 to i32
  %v6_40082d = call i32 @pthread_join(i32 %v1_40082a, i64** null)
  %v3_400832 = load i64, i64* %stack_var_-24, align 8
  %v1_40083b = trunc i64 %v3_400832 to i32
  %v6_40083e = call i32 @pthread_join(i32 %v1_40083b, i64** null)
  %v3_400843 = load i64, i64* %stack_var_-16, align 8
  %v1_40084c = trunc i64 %v3_400843 to i32
  %v6_40084f = call i32 @pthread_join(i32 %v1_40084c, i64** null)
  %v0_400854 = load i32, i32* @global_var_601058, align 4
  %v11_40085a = icmp eq i32 %v0_400854, 1
  %v0_40085f = load i32, i32* @global_var_60105c, align 4
  %v11_400865 = icmp eq i32 %v0_40085f, 1
  %or.cond = icmp eq i1 %v11_40085a, %v11_400865
  br i1 %or.cond, label %dec_label_pc_400880, label %dec_label_pc_40086a

dec_label_pc_40086a:                              ; preds = %dec_label_pc_40075e
  %v11_400870 = icmp eq i32 %v0_400854, 2
  %v11_40087b = icmp eq i32 %v0_40085f, 2
  %tmp90 = icmp eq i1 %v11_400870, %v11_40087b
  br i1 %tmp90, label %dec_label_pc_400880, label %dec_label_pc_400899

dec_label_pc_400880:                              ; preds = %dec_label_pc_40086a, %dec_label_pc_40075e
  call void @__assert_fail(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @global_var_400960, i64 0, i64 0), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @global_var_400958, i64 0, i64 0), i32 62, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @global_var_400992, i64 0, i64 0))
  %v0_400899.pre = load i32, i32* @global_var_601058, align 4
  %v0_4008a4.pre = load i32, i32* @global_var_60105c, align 4
  br label %dec_label_pc_400899

dec_label_pc_400899:                              ; preds = %dec_label_pc_40086a, %dec_label_pc_400880
  %v0_4008a4 = phi i32 [ %v0_40085f, %dec_label_pc_40086a ], [ %v0_4008a4.pre, %dec_label_pc_400880 ]
  %v0_400899 = phi i32 [ %v0_400854, %dec_label_pc_40086a ], [ %v0_400899.pre, %dec_label_pc_400880 ]
  %v11_40089f = icmp eq i32 %v0_400899, 1
  %v11_4008aa = icmp eq i32 %v0_4008a4, 1
  %or.cond2 = icmp eq i1 %v11_4008aa, %v11_40089f
  br i1 %or.cond2, label %dec_label_pc_4008c8, label %dec_label_pc_4008af

dec_label_pc_4008af:                              ; preds = %dec_label_pc_400899
  call void @__assert_fail(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @global_var_400985, i64 0, i64 0), i8* getelementptr inbounds ([6 x i8], [6 x i8]* @global_var_400958, i64 0, i64 0), i32 63, i8* getelementptr inbounds ([5 x i8], [5 x i8]* @global_var_400992, i64 0, i64 0))
  br label %dec_label_pc_4008c8

dec_label_pc_4008c8:                              ; preds = %dec_label_pc_400899, %dec_label_pc_4008af
  %rax.0 = phi i64 [ ptrtoint (i32* @0 to i64), %dec_label_pc_4008af ], [ 1, %dec_label_pc_400899 ]
  ret i64 %rax.0
}

declare i32 @pthread_create(i32*, i64*, i64* (i64*)*, i64*) local_unnamed_addr

declare void @__assert_fail(i8*, i8*, i32, i8*) local_unnamed_addr

declare i32 @pthread_join(i32, i64**) local_unnamed_addr
