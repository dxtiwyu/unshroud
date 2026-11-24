; unshroud - run one guest instruction on this CPU.
; void unshroud_native(NState* s, void* code)
; NState: gpr[16] at 0 (rsp slot unused), rflags at 128, mxcsr at 136, ymm[16] at 160 (32 bytes each)
; The frame is described (FRAME, .pushreg, .allocstack, .savexmm128): a fault of the instruction unwinds to the caller's
; handler. Frame: [rsp] code, [rsp+8] state, [rsp+16..175] xmm6-15. The caller restores MXCSR and the direction flag.
.code
unshroud_native PROC FRAME
  push rbx
  .pushreg rbx
  push rbp
  .pushreg rbp
  push rdi
  .pushreg rdi
  push rsi
  .pushreg rsi
  push r12
  .pushreg r12
  push r13
  .pushreg r13
  push r14
  .pushreg r14
  push r15
  .pushreg r15
  sub rsp, 184
  .allocstack 184
  movdqa [rsp+16], xmm6
  .savexmm128 xmm6, 16
  movdqa [rsp+32], xmm7
  .savexmm128 xmm7, 32
  movdqa [rsp+48], xmm8
  .savexmm128 xmm8, 48
  movdqa [rsp+64], xmm9
  .savexmm128 xmm9, 64
  movdqa [rsp+80], xmm10
  .savexmm128 xmm10, 80
  movdqa [rsp+96], xmm11
  .savexmm128 xmm11, 96
  movdqa [rsp+112], xmm12
  .savexmm128 xmm12, 112
  movdqa [rsp+128], xmm13
  .savexmm128 xmm13, 128
  movdqa [rsp+144], xmm14
  .savexmm128 xmm14, 144
  movdqa [rsp+160], xmm15
  .savexmm128 xmm15, 160
  .endprolog
  mov [rsp], rdx
  mov [rsp+8], rcx
  mov rax, rcx
  ldmxcsr dword ptr [rax+136]
  vmovdqu ymm0, ymmword ptr [rax+160]
  vmovdqu ymm1, ymmword ptr [rax+192]
  vmovdqu ymm2, ymmword ptr [rax+224]
  vmovdqu ymm3, ymmword ptr [rax+256]
  vmovdqu ymm4, ymmword ptr [rax+288]
  vmovdqu ymm5, ymmword ptr [rax+320]
  vmovdqu ymm6, ymmword ptr [rax+352]
  vmovdqu ymm7, ymmword ptr [rax+384]
  vmovdqu ymm8, ymmword ptr [rax+416]
  vmovdqu ymm9, ymmword ptr [rax+448]
  vmovdqu ymm10, ymmword ptr [rax+480]
  vmovdqu ymm11, ymmword ptr [rax+512]
  vmovdqu ymm12, ymmword ptr [rax+544]
  vmovdqu ymm13, ymmword ptr [rax+576]
  vmovdqu ymm14, ymmword ptr [rax+608]
  vmovdqu ymm15, ymmword ptr [rax+640]
  push qword ptr [rax+128]
  popfq
  mov rcx, [rax+8]
  mov rdx, [rax+16]
  mov rbx, [rax+24]
  mov rbp, [rax+40]
  mov rsi, [rax+48]
  mov rdi, [rax+56]
  mov r8, [rax+64]
  mov r9, [rax+72]
  mov r10, [rax+80]
  mov r11, [rax+88]
  mov r12, [rax+96]
  mov r13, [rax+104]
  mov r14, [rax+112]
  mov r15, [rax+120]
  mov rax, [rax]
  call qword ptr [rsp]
  push rax
  mov rax, [rsp+16]
  mov [rax+8], rcx
  mov [rax+16], rdx
  mov [rax+24], rbx
  mov [rax+40], rbp
  mov [rax+48], rsi
  mov [rax+56], rdi
  mov [rax+64], r8
  mov [rax+72], r9
  mov [rax+80], r10
  mov [rax+88], r11
  mov [rax+96], r12
  mov [rax+104], r13
  mov [rax+112], r14
  mov [rax+120], r15
  pop rcx
  mov [rax], rcx
  pushfq
  pop qword ptr [rax+128]
  cld
  stmxcsr dword ptr [rax+136]
  vmovdqu ymmword ptr [rax+160], ymm0
  vmovdqu ymmword ptr [rax+192], ymm1
  vmovdqu ymmword ptr [rax+224], ymm2
  vmovdqu ymmword ptr [rax+256], ymm3
  vmovdqu ymmword ptr [rax+288], ymm4
  vmovdqu ymmword ptr [rax+320], ymm5
  vmovdqu ymmword ptr [rax+352], ymm6
  vmovdqu ymmword ptr [rax+384], ymm7
  vmovdqu ymmword ptr [rax+416], ymm8
  vmovdqu ymmword ptr [rax+448], ymm9
  vmovdqu ymmword ptr [rax+480], ymm10
  vmovdqu ymmword ptr [rax+512], ymm11
  vmovdqu ymmword ptr [rax+544], ymm12
  vmovdqu ymmword ptr [rax+576], ymm13
  vmovdqu ymmword ptr [rax+608], ymm14
  vmovdqu ymmword ptr [rax+640], ymm15
  vzeroupper
  movdqa xmm6, [rsp+16]
  movdqa xmm7, [rsp+32]
  movdqa xmm8, [rsp+48]
  movdqa xmm9, [rsp+64]
  movdqa xmm10, [rsp+80]
  movdqa xmm11, [rsp+96]
  movdqa xmm12, [rsp+112]
  movdqa xmm13, [rsp+128]
  movdqa xmm14, [rsp+144]
  movdqa xmm15, [rsp+160]
  add rsp, 184
  pop r15
  pop r14
  pop r13
  pop r12
  pop rsi
  pop rdi
  pop rbp
  pop rbx
  ret
unshroud_native ENDP
END
