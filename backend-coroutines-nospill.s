	.file	"backend_coroutines_nospill.ceaa13f951ed4119-cgu.0"
	.section	.text._RINvNtCsg6cFVrRmIVl_4core3ptr14write_volatilehECshK4jsiytOIL_26backend_coroutines_nospill,"ax",@progbits
	.globl	_RINvNtCsg6cFVrRmIVl_4core3ptr14write_volatilehECshK4jsiytOIL_26backend_coroutines_nospill
	.p2align	4
	.type	_RINvNtCsg6cFVrRmIVl_4core3ptr14write_volatilehECshK4jsiytOIL_26backend_coroutines_nospill,@function
_RINvNtCsg6cFVrRmIVl_4core3ptr14write_volatilehECshK4jsiytOIL_26backend_coroutines_nospill:
	.cfi_startproc
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	movq	%rdx, (%rsp)
	movq	%rdi, 8(%rsp)
	movb	%sil, %al
	movb	%al, 23(%rsp)
	jmp	.LBB0_1
.LBB0_1:
	movq	(%rsp), %rdx
	movq	8(%rsp), %rdi
	movl	$1, %esi
	callq	_RNvNvNtCsg6cFVrRmIVl_4core3ptr14write_volatile18precondition_checkCshK4jsiytOIL_26backend_coroutines_nospill
	movq	8(%rsp), %rax
	movb	23(%rsp), %cl
	movb	%cl, (%rax)
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end0:
	.size	_RINvNtCsg6cFVrRmIVl_4core3ptr14write_volatilehECshK4jsiytOIL_26backend_coroutines_nospill, .Lfunc_end0-_RINvNtCsg6cFVrRmIVl_4core3ptr14write_volatilehECshK4jsiytOIL_26backend_coroutines_nospill
	.cfi_endproc

	.section	.text._RINvNtCsg6cFVrRmIVl_4core3ptr9drop_glueNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0EBF_,"ax",@progbits
	.globl	_RINvNtCsg6cFVrRmIVl_4core3ptr9drop_glueNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0EBF_
	.p2align	4
	.type	_RINvNtCsg6cFVrRmIVl_4core3ptr9drop_glueNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0EBF_,@function
_RINvNtCsg6cFVrRmIVl_4core3ptr9drop_glueNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0EBF_:
	.cfi_startproc
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	movq	%rdi, 8(%rsp)
	movq	(%rdi), %rax
	movq	%rax, 16(%rsp)
	cmpq	$0, %rax
	jne	.LBB1_2
.LBB1_1:
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
	retq
.LBB1_2:
	.cfi_def_cfa_offset 32
	movq	8(%rsp), %rdi
	movq	16(%rsp), %rax
	movl	$1, %esi
	xorl	%ecx, %ecx
	movl	%ecx, %r8d
	movq	%r8, %rdx
	movq	%r8, %rcx
	callq	*%rax
	movq	%rax, %rcx
	movq	8(%rsp), %rax
	movq	%rcx, (%rax)
	jmp	.LBB1_1
.Lfunc_end1:
	.size	_RINvNtCsg6cFVrRmIVl_4core3ptr9drop_glueNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0EBF_, .Lfunc_end1-_RINvNtCsg6cFVrRmIVl_4core3ptr9drop_glueNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0EBF_
	.cfi_endproc

	.section	.text._RNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0B3_,"ax",@progbits
	.p2align	4
	.type	_RNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0B3_,@function
_RNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0B3_:
	.cfi_startproc
	subq	$56, %rsp
	.cfi_def_cfa_offset 64
	movq	%rdi, 40(%rsp)
	andq	$7, %rdi
	cmpq	$0, %rdi
	jne	.LBB2_2
	movq	40(%rsp), %rax
	cmpq	$0, %rax
	sete	%al
	andb	$-1, %al
	xorb	$-1, %al
	testb	$1, %al
	jne	.LBB2_3
	jmp	.LBB2_4
.LBB2_2:
	movq	40(%rsp), %rsi
	movl	$8, %edi
	leaq	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c(%rip), %rdx
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking36panic_misaligned_pointer_dereference@GOTPCREL(%rip)
.LBB2_3:
	movq	40(%rsp), %rax
	movq	(%rax), %rax
	movq	%rax, 32(%rsp)
	cmpq	$0, %rax
	sete	%al
	andb	$1, %al
	movb	%al, 55(%rsp)
	testb	$1, 55(%rsp)
	jne	.LBB2_5
	jmp	.LBB2_6
.LBB2_4:
	leaq	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c(%rip), %rdi
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking30panic_null_pointer_dereference@GOTPCREL(%rip)
.LBB2_5:
	ud2
.LBB2_6:
	movq	40(%rsp), %rdi
	movq	32(%rsp), %rax
	xorl	%esi, %esi
	leaq	51(%rsp), %rdx
	leaq	53(%rsp), %rcx
	leaq	54(%rsp), %r8
	callq	*%rax
	movq	%rax, %rcx
	movq	40(%rsp), %rax
	movq	%rcx, 24(%rsp)
	andq	$7, %rax
	cmpq	$0, %rax
	jne	.LBB2_8
	movq	40(%rsp), %rax
	cmpq	$0, %rax
	sete	%al
	andb	$-1, %al
	xorb	$-1, %al
	testb	$1, %al
	jne	.LBB2_9
	jmp	.LBB2_10
.LBB2_8:
	movq	40(%rsp), %rsi
	movl	$8, %edi
	leaq	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c(%rip), %rdx
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking36panic_misaligned_pointer_dereference@GOTPCREL(%rip)
.LBB2_9:
	movq	24(%rsp), %rax
	movq	40(%rsp), %rcx
	movq	%rax, (%rcx)
	cmpq	$0, %rax
	sete	%al
	andb	$1, %al
	movb	%al, 55(%rsp)
	testb	$1, 55(%rsp)
	jne	.LBB2_11
	jmp	.LBB2_12
.LBB2_10:
	leaq	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c(%rip), %rdi
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking30panic_null_pointer_dereference@GOTPCREL(%rip)
.LBB2_11:
	leaq	54(%rsp), %rax
	movq	%rax, 16(%rsp)
	andq	$0, %rax
	cmpq	$0, %rax
	je	.LBB2_13
	jmp	.LBB2_14
.LBB2_12:
	leaq	53(%rsp), %rax
	movq	%rax, 8(%rsp)
	andq	$0, %rax
	cmpq	$0, %rax
	je	.LBB2_18
	jmp	.LBB2_19
.LBB2_13:
	leaq	54(%rsp), %rax
	cmpq	$0, %rax
	sete	%al
	andb	$0, %al
	xorb	$-1, %al
	testb	$1, %al
	jne	.LBB2_15
	jmp	.LBB2_16
.LBB2_14:
	movq	16(%rsp), %rsi
	movl	$1, %edi
	leaq	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c(%rip), %rdx
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking36panic_misaligned_pointer_dereference@GOTPCREL(%rip)
.LBB2_15:
	movb	$1, 52(%rsp)
	jmp	.LBB2_17
.LBB2_16:
	leaq	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c(%rip), %rdi
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking30panic_null_pointer_dereference@GOTPCREL(%rip)
.LBB2_17:
	movb	52(%rsp), %al
	andb	$1, %al
	addq	$56, %rsp
	.cfi_def_cfa_offset 8
	retq
.LBB2_18:
	.cfi_def_cfa_offset 64
	leaq	53(%rsp), %rax
	cmpq	$0, %rax
	sete	%al
	andb	$0, %al
	xorb	$-1, %al
	testb	$1, %al
	jne	.LBB2_20
	jmp	.LBB2_21
.LBB2_19:
	movq	8(%rsp), %rsi
	movl	$1, %edi
	leaq	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c(%rip), %rdx
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking36panic_misaligned_pointer_dereference@GOTPCREL(%rip)
.LBB2_20:
	movb	$0, 52(%rsp)
	jmp	.LBB2_17
.LBB2_21:
	leaq	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c(%rip), %rdi
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking30panic_null_pointer_dereference@GOTPCREL(%rip)
.Lfunc_end2:
	.size	_RNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0B3_, .Lfunc_end2-_RNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0B3_
	.cfi_endproc

	.section	.text._RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_,"ax",@progbits
	.p2align	4
	.type	_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_,@function
_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_:
.Lfunc_begin0:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception0
	subq	$1112, %rsp
	.cfi_def_cfa_offset 1120
	movq	%rdi, 16(%rsp)
	movb	%sil, %al
	movq	%rdx, 24(%rsp)
	movq	%rcx, 32(%rsp)
	movq	%r8, 40(%rsp)
	testb	$1, %al
	jne	.LBB3_1
	jmp	.LBB3_3
.LBB3_1:
	movq	$0, 48(%rsp)
	xorl	%eax, %eax
	movq	%rax, 8(%rsp)
.LBB3_2:
	movq	8(%rsp), %rax
	addq	$1112, %rsp
	.cfi_def_cfa_offset 8
	retq
.LBB3_3:
	.cfi_def_cfa_offset 1120
	movb	$0, 1095(%rsp)
	leaq	71(%rsp), %rdi
	movq	%rdi, (%rsp)
	xorl	%esi, %esi
	movl	$1024, %edx
	movq	memset@GOTPCREL(%rip), %rax
	callq	*%rax
	movq	(%rsp), %rdi
.Ltmp0:
	callq	_RNvCshK4jsiytOIL_26backend_coroutines_nospill5touch
.Ltmp1:
	jmp	.LBB3_5
.LBB3_4:
.Ltmp2:
	movq	%rax, %rcx
	movl	%edx, %eax
	movq	%rcx, 1096(%rsp)
	movl	%eax, 1104(%rsp)
	testb	$1, 1095(%rsp)
	jne	.LBB3_6
	jmp	.LBB3_7
.LBB3_5:
	movq	16(%rsp), %rax
	movb	$3, 8(%rax)
	leaq	_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_.resume.0(%rip), %rax
	movq	%rax, 8(%rsp)
	jmp	.LBB3_2
.LBB3_6:
	movq	$0, 48(%rsp)
	xorl	%eax, %eax
	movq	%rax, 8(%rsp)
	jmp	.LBB3_2
.LBB3_7:
	movq	1096(%rsp), %rdi
	callq	_Unwind_Resume@PLT
.Lfunc_end3:
	.size	_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_, .Lfunc_end3-_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_
	.cfi_endproc
	.section	.gcc_except_table._RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_,"a",@progbits
	.p2align	2, 0x0
GCC_except_table3:
.Lexception0:
	.byte	255
	.byte	255
	.byte	1
	.uleb128 .Lcst_end0-.Lcst_begin0
.Lcst_begin0:
	.uleb128 .Lfunc_begin0-.Lfunc_begin0
	.uleb128 .Ltmp0-.Lfunc_begin0
	.byte	0
	.byte	0
	.uleb128 .Ltmp0-.Lfunc_begin0
	.uleb128 .Ltmp1-.Ltmp0
	.uleb128 .Ltmp2-.Lfunc_begin0
	.byte	0
	.uleb128 .Ltmp1-.Lfunc_begin0
	.uleb128 .Lfunc_end3-.Ltmp1
	.byte	0
	.byte	0
.Lcst_end0:
	.p2align	2, 0x0

	.section	.text._RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_.resume.0,"ax",@progbits
	.p2align	4
	.type	_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_.resume.0,@function
_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_.resume.0:
	.cfi_startproc
	subq	$960, %rsp
	.cfi_def_cfa_offset 968
	movq	%rdi, -128(%rsp)
	movb	%sil, %al
	movq	%rdx, 952(%rsp)
	movq	%rcx, 944(%rsp)
	movq	%r8, 936(%rsp)
	testb	$1, %al
	jne	.LBB4_1
	jmp	.LBB4_3
.LBB4_1:
	movb	$1, -97(%rsp)
.LBB4_2:
	xorl	%eax, %eax
	addq	$960, %rsp
	.cfi_def_cfa_offset 8
	retq
.LBB4_3:
	.cfi_def_cfa_offset 968
	movq	-128(%rsp), %rax
	movb	$1, 8(%rax)
	movq	$0, 928(%rsp)
	jmp	.LBB4_2
.Lfunc_end4:
	.size	_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_.resume.0, .Lfunc_end4-_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_.resume.0
	.cfi_endproc

	.section	.text._RNvCshK4jsiytOIL_26backend_coroutines_nospill5touch,"ax",@progbits
	.p2align	4
	.type	_RNvCshK4jsiytOIL_26backend_coroutines_nospill5touch,@function
_RNvCshK4jsiytOIL_26backend_coroutines_nospill5touch:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	movl	$42, %esi
	leaq	.Lalloc_8d704448724a9a4fc98b90cde0d0f0b2(%rip), %rdx
	callq	*_RINvNtCsg6cFVrRmIVl_4core3ptr14write_volatilehECshK4jsiytOIL_26backend_coroutines_nospill@GOTPCREL(%rip)
	popq	%rax
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end5:
	.size	_RNvCshK4jsiytOIL_26backend_coroutines_nospill5touch, .Lfunc_end5-_RNvCshK4jsiytOIL_26backend_coroutines_nospill5touch
	.cfi_endproc

	.section	.text._RNvMNtNtCsg6cFVrRmIVl_4core3ptr9const_ptrPu13is_aligned_toCshK4jsiytOIL_26backend_coroutines_nospill,"ax",@progbits
	.globl	_RNvMNtNtCsg6cFVrRmIVl_4core3ptr9const_ptrPu13is_aligned_toCshK4jsiytOIL_26backend_coroutines_nospill
	.p2align	4
	.type	_RNvMNtNtCsg6cFVrRmIVl_4core3ptr9const_ptrPu13is_aligned_toCshK4jsiytOIL_26backend_coroutines_nospill,@function
_RNvMNtNtCsg6cFVrRmIVl_4core3ptr9const_ptrPu13is_aligned_toCshK4jsiytOIL_26backend_coroutines_nospill:
	.cfi_startproc
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	movq	%rsi, %rcx
	movq	%rdi, 8(%rsp)
	movq	%rcx, 16(%rsp)
	movq	%rcx, %rax
	shrq	%rax
	movabsq	$6148914691236517205, %rdx
	andq	%rdx, %rax
	subq	%rax, %rcx
	movabsq	$3689348814741910323, %rdx
	movq	%rcx, %rax
	andq	%rdx, %rax
	shrq	$2, %rcx
	andq	%rdx, %rcx
	addq	%rcx, %rax
	movq	%rax, %rcx
	shrq	$4, %rcx
	addq	%rcx, %rax
	movabsq	$1085102592571150095, %rcx
	andq	%rcx, %rax
	movabsq	$72340172838076673, %rcx
	imulq	%rcx, %rax
	shrq	$56, %rax
	cmpl	$1, %eax
	jne	.LBB6_2
	movq	8(%rsp), %rax
	movq	16(%rsp), %rcx
	subq	$1, %rcx
	andq	%rcx, %rax
	cmpq	$0, %rax
	sete	%al
	andb	$1, %al
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
	retq
.LBB6_2:
	.cfi_def_cfa_offset 32
	leaq	.Lalloc_fad0cd83b7d1858a846a172eb260e593(%rip), %rdi
	movl	$85, %esi
	leaq	.Lalloc_8279c84e0b07e9461fc64e474bce4e46(%rip), %rdx
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking9panic_fmt@GOTPCREL(%rip)
.Lfunc_end6:
	.size	_RNvMNtNtCsg6cFVrRmIVl_4core3ptr9const_ptrPu13is_aligned_toCshK4jsiytOIL_26backend_coroutines_nospill, .Lfunc_end6-_RNvMNtNtCsg6cFVrRmIVl_4core3ptr9const_ptrPu13is_aligned_toCshK4jsiytOIL_26backend_coroutines_nospill
	.cfi_endproc

	.section	.text._RNvNvNtCsg6cFVrRmIVl_4core3ptr14write_volatile18precondition_checkCshK4jsiytOIL_26backend_coroutines_nospill,"ax",@progbits
	.p2align	4
	.type	_RNvNvNtCsg6cFVrRmIVl_4core3ptr14write_volatile18precondition_checkCshK4jsiytOIL_26backend_coroutines_nospill,@function
_RNvNvNtCsg6cFVrRmIVl_4core3ptr14write_volatile18precondition_checkCshK4jsiytOIL_26backend_coroutines_nospill:
.Lfunc_begin1:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception1
	subq	$24, %rsp
	.cfi_def_cfa_offset 32
	movq	%rdx, 8(%rsp)
.Ltmp3:
	movq	_RNvMNtNtCsg6cFVrRmIVl_4core3ptr9const_ptrPu13is_aligned_toCshK4jsiytOIL_26backend_coroutines_nospill@GOTPCREL(%rip), %rax
	callq	*%rax
.Ltmp4:
	movb	%al, 23(%rsp)
	jmp	.LBB7_2
.LBB7_1:
.Ltmp5:
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking19panic_cannot_unwind@GOTPCREL(%rip)
.LBB7_2:
	movb	23(%rsp), %al
	testb	$1, %al
	jne	.LBB7_4
	jmp	.LBB7_3
.LBB7_3:
	movq	8(%rsp), %rcx
	leaq	.Lalloc_c848f501c9a24e1e115677405b6cf8e4(%rip), %rdi
	movl	$431, %esi
	xorl	%edx, %edx
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking18panic_nounwind_fmt@GOTPCREL(%rip)
.LBB7_4:
	addq	$24, %rsp
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end7:
	.size	_RNvNvNtCsg6cFVrRmIVl_4core3ptr14write_volatile18precondition_checkCshK4jsiytOIL_26backend_coroutines_nospill, .Lfunc_end7-_RNvNvNtCsg6cFVrRmIVl_4core3ptr14write_volatile18precondition_checkCshK4jsiytOIL_26backend_coroutines_nospill
	.cfi_endproc
	.section	.gcc_except_table._RNvNvNtCsg6cFVrRmIVl_4core3ptr14write_volatile18precondition_checkCshK4jsiytOIL_26backend_coroutines_nospill,"a",@progbits
	.p2align	2, 0x0
GCC_except_table7:
.Lexception1:
	.byte	255
	.byte	155
	.uleb128 .Lttbase0-.Lttbaseref0
.Lttbaseref0:
	.byte	1
	.uleb128 .Lcst_end1-.Lcst_begin1
.Lcst_begin1:
	.uleb128 .Ltmp3-.Lfunc_begin1
	.uleb128 .Ltmp4-.Ltmp3
	.uleb128 .Ltmp5-.Lfunc_begin1
	.byte	1
.Lcst_end1:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase0:
	.byte	0
	.p2align	2, 0x0

	.section	.text.test_coro,"ax",@progbits
	.globl	test_coro
	.p2align	4
	.type	test_coro,@function
test_coro:
.Lfunc_begin2:
	.cfi_startproc
	.cfi_personality 155, DW.ref.rust_eh_personality
	.cfi_lsda 27, .Lexception2
	subq	$40, %rsp
	.cfi_def_cfa_offset 48
	leaq	_RNSNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro04rampB5_(%rip), %rax
	movq	%rax, 8(%rsp)
	movb	$0, 16(%rsp)
	jmp	.LBB8_3
.LBB8_1:
.Ltmp9:
	movq	_RINvNtCsg6cFVrRmIVl_4core3ptr9drop_glueNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0EBF_@GOTPCREL(%rip), %rax
	leaq	8(%rsp), %rdi
	callq	*%rax
.Ltmp10:
	jmp	.LBB8_6
.LBB8_2:
.Ltmp8:
	movq	%rax, %rcx
	movl	%edx, %eax
	movq	%rcx, 24(%rsp)
	movl	%eax, 32(%rsp)
	jmp	.LBB8_1
.LBB8_3:
.Ltmp6:
	leaq	8(%rsp), %rdi
	callq	_RNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0B3_
.Ltmp7:
	jmp	.LBB8_4
.LBB8_4:
	leaq	8(%rsp), %rdi
	callq	*_RINvNtCsg6cFVrRmIVl_4core3ptr9drop_glueNCNvCshK4jsiytOIL_26backend_coroutines_nospill9test_coro0EBF_@GOTPCREL(%rip)
	addq	$40, %rsp
	.cfi_def_cfa_offset 8
	retq
.LBB8_5:
	.cfi_def_cfa_offset 48
.Ltmp11:
	callq	*_RNvNtCsg6cFVrRmIVl_4core9panicking16panic_in_cleanup@GOTPCREL(%rip)
.LBB8_6:
	movq	24(%rsp), %rdi
	callq	_Unwind_Resume@PLT
.Lfunc_end8:
	.size	test_coro, .Lfunc_end8-test_coro
	.cfi_endproc
	.section	.gcc_except_table.test_coro,"a",@progbits
	.p2align	2, 0x0
GCC_except_table8:
.Lexception2:
	.byte	255
	.byte	155
	.uleb128 .Lttbase1-.Lttbaseref1
.Lttbaseref1:
	.byte	1
	.uleb128 .Lcst_end2-.Lcst_begin2
.Lcst_begin2:
	.uleb128 .Ltmp9-.Lfunc_begin2
	.uleb128 .Ltmp10-.Ltmp9
	.uleb128 .Ltmp11-.Lfunc_begin2
	.byte	1
	.uleb128 .Ltmp6-.Lfunc_begin2
	.uleb128 .Ltmp7-.Ltmp6
	.uleb128 .Ltmp8-.Lfunc_begin2
	.byte	0
	.uleb128 .Ltmp7-.Lfunc_begin2
	.uleb128 .Lfunc_end8-.Ltmp7
	.byte	0
	.byte	0
.Lcst_end2:
	.byte	127
	.byte	0
	.p2align	2, 0x0
.Lttbase1:
	.byte	0
	.p2align	2, 0x0

	.type	.Lalloc_60c76054b4213120fa29e4c605f3517d,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lalloc_60c76054b4213120fa29e4c605f3517d:
	.asciz	"tests/codegen-llvm/backend-coroutines-nospill.rs"
	.size	.Lalloc_60c76054b4213120fa29e4c605f3517d, 49

	.type	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c,@object
	.section	.data.rel.ro..Lalloc_5775c1eb588720edb8d29b630b6ddf9c,"aw",@progbits
	.p2align	3, 0x0
.Lalloc_5775c1eb588720edb8d29b630b6ddf9c:
	.quad	.Lalloc_60c76054b4213120fa29e4c605f3517d
	.asciz	"0\000\000\000\000\000\000\000\020\000\000\000\036\000\000"
	.size	.Lalloc_5775c1eb588720edb8d29b630b6ddf9c, 24

	.type	.Lalloc_8d704448724a9a4fc98b90cde0d0f0b2,@object
	.section	.data.rel.ro..Lalloc_8d704448724a9a4fc98b90cde0d0f0b2,"aw",@progbits
	.p2align	3, 0x0
.Lalloc_8d704448724a9a4fc98b90cde0d0f0b2:
	.quad	.Lalloc_60c76054b4213120fa29e4c605f3517d
	.asciz	"0\000\000\000\000\000\000\000\013\000\000\000\016\000\000"
	.size	.Lalloc_8d704448724a9a4fc98b90cde0d0f0b2, 24

	.type	.Lalloc_fad0cd83b7d1858a846a172eb260e593,@object
	.section	.rodata..Lalloc_fad0cd83b7d1858a846a172eb260e593,"a",@progbits
.Lalloc_fad0cd83b7d1858a846a172eb260e593:
	.ascii	"is_aligned_to: align is not a power-of-two"
	.size	.Lalloc_fad0cd83b7d1858a846a172eb260e593, 42

	.type	.Lalloc_462d48c71ecbcc11b125140bcb84ed12,@object
	.section	.rodata.str1.1,"aMS",@progbits,1
.Lalloc_462d48c71ecbcc11b125140bcb84ed12:
	.asciz	"library/core/src/ptr/const_ptr.rs"
	.size	.Lalloc_462d48c71ecbcc11b125140bcb84ed12, 34

	.type	.Lalloc_8279c84e0b07e9461fc64e474bce4e46,@object
	.section	.data.rel.ro..Lalloc_8279c84e0b07e9461fc64e474bce4e46,"aw",@progbits
	.p2align	3, 0x0
.Lalloc_8279c84e0b07e9461fc64e474bce4e46:
	.quad	.Lalloc_462d48c71ecbcc11b125140bcb84ed12
	.asciz	"!\000\000\000\000\000\000\000L\005\000\000\r\000\000"
	.size	.Lalloc_8279c84e0b07e9461fc64e474bce4e46, 24

	.type	.Lalloc_c848f501c9a24e1e115677405b6cf8e4,@object
	.section	.rodata..Lalloc_c848f501c9a24e1e115677405b6cf8e4,"a",@progbits
.Lalloc_c848f501c9a24e1e115677405b6cf8e4:
	.ascii	"unsafe precondition(s) violated: ptr::write_volatile requires that the pointer argument is aligned\n\nThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety."
	.size	.Lalloc_c848f501c9a24e1e115677405b6cf8e4, 215

	.hidden	DW.ref.rust_eh_personality
	.weak	DW.ref.rust_eh_personality
	.section	.data.DW.ref.rust_eh_personality,"awG",@progbits,DW.ref.rust_eh_personality,comdat
	.p2align	3, 0x0
	.type	DW.ref.rust_eh_personality,@object
	.size	DW.ref.rust_eh_personality, 8
DW.ref.rust_eh_personality:
	.quad	rust_eh_personality
	.ident	"rustc version 1.98.0-dev"
	.section	".note.GNU-stack","",@progbits
