/*
 * Copyright (C) Ahmad <ahmedparr93@gmail.com>
 * SPDX-License-Identifier: AGPL-3.0-only
 */
#include "subleq_vm.h"

#include <ctype.h>
#include <stdlib.h>
#include <string.h>

void subleq_vm_init(subleq_vm *vm, subleq_mode mode)
{
    memset(vm, 0, sizeof *vm);
    vm->mode = mode;
    vm->mask = (mode == SUBLEQ_MODE_DIRECTIVE) ? 0xFFFFFFFFu : 0xFFFFu;
    vm->prof = (uint64_t *)calloc(SUBLEQ_MEM_CELLS, sizeof(uint64_t));
    vm->use_stdio = 1;
}

void subleq_vm_free(subleq_vm *vm)
{
    free(vm->prof);
    vm->prof = NULL;
    free(vm->out);
    vm->out = NULL;
}

uint32_t subleq_get(const subleq_vm *vm, uint32_t addr)
{
    return vm->mem[addr % SUBLEQ_MEM_CELLS] & vm->mask;
}

void subleq_set(subleq_vm *vm, uint32_t addr, uint32_t v)
{
    vm->mem[addr % SUBLEQ_MEM_CELLS] = v & vm->mask;
}

static int is_watched(const subleq_vm *vm, uint32_t addr)
{
    int i;
    addr %= SUBLEQ_MEM_CELLS;
    for (i = 0; i < vm->nwp; i++)
        if (vm->wp[i] % SUBLEQ_MEM_CELLS == addr)
            return 1;
    return 0;
}

int subleq_add_break(subleq_vm *vm, uint32_t addr)
{
    int i;
    addr &= vm->mask;
    for (i = 0; i < vm->nbp; i++)
        if (vm->bp[i] == addr)
            return 0;
    if (vm->nbp >= (int)SUBLEQ_MAX_BP)
        return -1;
    vm->bp[vm->nbp++] = addr;
    return 0;
}

int subleq_add_watch(subleq_vm *vm, uint32_t addr)
{
    int i;
    addr %= SUBLEQ_MEM_CELLS;
    for (i = 0; i < vm->nwp; i++)
        if (vm->wp[i] == addr)
            return 0;
    if (vm->nwp >= (int)SUBLEQ_MAX_WP)
        return -1;
    vm->wp[vm->nwp++] = addr;
    return 0;
}

static void out_byte(subleq_vm *vm, unsigned char c)
{
    if (vm->use_stdio) {
        fputc((int)c, stdout);
        return;
    }
    if (vm->out_len + 1 >= vm->out_cap) {
        size_t ncap = vm->out_cap ? vm->out_cap * 2 : 256;
        char *n = (char *)realloc(vm->out, ncap);
        if (!n)
            return;
        vm->out = n;
        vm->out_cap = ncap;
    }
    vm->out[vm->out_len++] = (char)c;
    vm->out[vm->out_len] = 0;
}

static uint32_t in_word(subleq_vm *vm)
{
    int ch;
    if (vm->use_stdio) {
        ch = getchar();
        if (ch == EOF)
            return vm->mask; /* 0xFFFF in eForth, 0xFFFFFFFF in directive */
        return (uint32_t)ch & vm->mask;
    }
    if (vm->in_pos >= vm->in_len)
        return vm->mask;
    return vm->in[vm->in_pos++];
}

int subleq_load_dec_file(subleq_vm *vm, FILE *f)
{
    unsigned long cells = 0;
    long value;
    int c, sign, digits;

    while (cells < SUBLEQ_MEM_CELLS) {
        sign = 1;
        digits = 0;
        value = 0;
        c = fgetc(f);
        while (c != EOF && (isspace((unsigned char)c) || c == ',' || c == ';')) {
            if (c == ';') { /* comment to end of line */
                while (c != EOF && c != '\n')
                    c = fgetc(f);
            } else {
                c = fgetc(f);
            }
        }
        if (c == EOF)
            break;
        if (c == '-' || c == '+') {
            if (c == '-')
                sign = -1;
            c = fgetc(f);
        }
        if (!isdigit((unsigned char)c)) {
            /* skip unknown token */
            while (c != EOF && !isspace((unsigned char)c) && c != ',')
                c = fgetc(f);
            continue;
        }
        while (isdigit((unsigned char)c)) {
            digits = 1;
            value = value * 10 + (c - '0');
            c = fgetc(f);
        }
        if (digits) {
            long v = value * sign;
            /* Store as two's complement in the machine width. */
            if (vm->mode == SUBLEQ_MODE_EFORTH)
                vm->mem[cells++] = (uint32_t)(v & 0xFFFF);
            else
                vm->mem[cells++] = (uint32_t)v;
        }
        if (c != EOF && c != ',' && !isspace((unsigned char)c))
            ungetc(c, f);
    }
    vm->load_cells = (uint32_t)cells;
    vm->pc = 0;
    vm->halted = 0;
    vm->steps = 0;
    return (int)cells;
}

int subleq_load_dec(subleq_vm *vm, const char *path)
{
    FILE *f = fopen(path, "rb");
    int n;
    if (!f)
        return -1;
    n = subleq_load_dec_file(vm, f);
    fclose(f);
    return n;
}

static int at_breakpoint(const subleq_vm *vm)
{
    int i;
    for (i = 0; i < vm->nbp; i++)
        if (vm->bp[i] == vm->pc)
            return 1;
    return 0;
}

int subleq_step(subleq_vm *vm)
{
    uint32_t a, b, c, r, pc, mask;
    int32_t r_signed;
    int do_branch;

    vm->hit_break = 0;
    vm->hit_watch = 0;
    vm->last_wrote = 0;

    if (vm->halted || vm->trap)
        return 0;

    pc = vm->pc;
    mask = vm->mask;

    if (vm->mode == SUBLEQ_MODE_EFORTH && pc >= SUBLEQ_EFORTH_HALT) {
        vm->halted = 1;
        return 0;
    }

    if (vm->prof)
        vm->prof[pc % SUBLEQ_MEM_CELLS]++;

    a = subleq_get(vm, pc);
    b = subleq_get(vm, pc + 1);
    c = subleq_get(vm, pc + 2);
    vm->last_a = a;
    vm->last_b = b;
    vm->last_c = c;
    vm->last_r = 0;

    if (vm->mode == SUBLEQ_MODE_EFORTH) {
        if (a == 0xFFFFu) {
            uint32_t v = in_word(vm) & 0xFFFFu;
            vm->last_wrote = 1;
            vm->last_write_addr = b;
            vm->last_write_old = subleq_get(vm, b);
            subleq_set(vm, b, v);
            if (is_watched(vm, b)) {
                vm->hit_watch = 1;
                vm->hit_addr = b % SUBLEQ_MEM_CELLS;
            }
            vm->pc = (pc + 3) & mask;
            vm->steps++;
            return 1;
        }
        if (b == 0xFFFFu) {
            out_byte(vm, (unsigned char)(subleq_get(vm, a) & 0xFFu));
            vm->pc = (pc + 3) & mask;
            vm->steps++;
            return 1;
        }
        r = (subleq_get(vm, b) - subleq_get(vm, a)) & 0xFFFFu;
        vm->last_r = r;
        vm->last_wrote = 1;
        vm->last_write_addr = b;
        vm->last_write_old = subleq_get(vm, b);
        subleq_set(vm, b, r);
        if (is_watched(vm, b)) {
            vm->hit_watch = 1;
            vm->hit_addr = b % SUBLEQ_MEM_CELLS;
        }
        /* Branch if result is 0 or the sign bit is set (int16 <= 0). */
        if (r == 0 || (r & 0x8000u))
            vm->pc = c & 0xFFFFu;
        else
            vm->pc = (pc + 3) & 0xFFFFu;
        if (vm->pc >= SUBLEQ_EFORTH_HALT)
            vm->halted = 1;
        vm->steps++;
        return 1;
    }

    /* Directive machine: 32-bit wrap, a==-1 input, b<0 output, a==-2 trap, c==-1 halt. */
    r_signed = 0;
    (void)r_signed;
    if ((int32_t)a == -2) {
        vm->trap = 1;
        vm->steps++;
        return 1;
    }
    if ((int32_t)c == -1 && (int32_t)a != -1 && (int32_t)b >= 0) {
        /* Halt encoding used by some images: still perform the subtract? Spec:
           halt when c=-1. We halt after this instruction's side effects. */
    }
    if ((int32_t)a == -1) {
        uint32_t v = in_word(vm);
        vm->last_wrote = 1;
        vm->last_write_addr = b;
        vm->last_write_old = subleq_get(vm, b);
        subleq_set(vm, b, v);
        if (is_watched(vm, b)) {
            vm->hit_watch = 1;
            vm->hit_addr = b % SUBLEQ_MEM_CELLS;
        }
        if ((int32_t)c == -1)
            vm->halted = 1;
        else
            vm->pc = c; /* typical input also uses c as next? Our notes: standard subleq still branches */
        /* Use standard control: advance, unless we treat c as next always for I/O.
           Keep consistent with subtract path: after I/O, pc = pc+3 (no branch). */
        vm->pc = (int32_t)c == -1 ? pc : (pc + 3);
        if ((int32_t)c == -1)
            vm->halted = 1;
        vm->steps++;
        return 1;
    }
    if ((int32_t)b < 0) {
        /* word output of mem[a] */
        uint32_t v = subleq_get(vm, a);
        /* emit as a decimal word followed by space, matching many directive dumps;
           for byte-like values also push the low 8 bits into the byte stream. */
        char tmp[32];
        int n, i;
        n = snprintf(tmp, sizeof tmp, "%d ", (int32_t)v);
        for (i = 0; i < n; i++)
            out_byte(vm, (unsigned char)tmp[i]);
        if ((int32_t)c == -1)
            vm->halted = 1;
        else
            vm->pc = pc + 3;
        vm->steps++;
        return 1;
    }
    r = (subleq_get(vm, b) - subleq_get(vm, a)) & 0xFFFFFFFFu;
    vm->last_r = r;
    vm->last_wrote = 1;
    vm->last_write_addr = b;
    vm->last_write_old = subleq_get(vm, b);
    subleq_set(vm, b, r);
    if (is_watched(vm, b)) {
        vm->hit_watch = 1;
        vm->hit_addr = b % SUBLEQ_MEM_CELLS;
    }
    if ((int32_t)c == -1) {
        vm->halted = 1;
        vm->steps++;
        return 1;
    }
    do_branch = ((int32_t)r <= 0);
    vm->pc = do_branch ? c : (pc + 3);
    vm->steps++;
    return 1;
}

uint64_t subleq_run(subleq_vm *vm, uint64_t n)
{
    uint64_t start = vm->steps;
    uint64_t allow = (n == 0) ? UINT64_MAX : n;
    while (allow > 0 && !vm->halted && !vm->trap) {
        /* Breakpoints fire *before* the instruction at that PC, except at step 0
           so that `run` from a freshly loaded image is not stuck on pc=0 if
           someone set a start breakpoint after starting. */
        if (vm->steps > start && at_breakpoint(vm)) {
            vm->hit_break = 1;
            vm->hit_addr = vm->pc;
            break;
        }
        if (!subleq_step(vm))
            break;
        allow--;
        if (vm->hit_watch)
            break;
    }
    return vm->steps - start;
}

/* snprintf used in directive output: pull stdio already included via header. */
