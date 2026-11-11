; NASM 32-bit (P1-P4 architecture)
; Assuming ESI = memory base pointer
; EAX = index A, EBX = index B, ECX = branch target C

_subleq_step:
    ; Scale indices to 4-byte dwords
    mov edx, [esi + eax*4]      ; Load mem[A] into EDX
    
    ; Perform the Church SUB operation natively
    sub [esi + ebx*4], edx      ; mem[B] = mem[B] - mem[A]
    
    ; Perform the Church ISZERO / Branch
    jle _take_branch            ; Jump if result <= 0
    
    ; Default fallthrough (Advance PC by 3)
    add dword [instruction_ptr], 3
    ret

_take_branch:
    ; Update PC to C
    mov [instruction_ptr], ecx
    ret
