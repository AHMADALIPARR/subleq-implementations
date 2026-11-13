/*
 * 16-bit eForth / 32-bit directive SUBLEQ virtual machine (library).
 * Copyright (C) Ahmad <ahmedparr93@gmail.com>
 * SPDX-License-Identifier: AGPL-3.0-only
 */
#ifndef SUBLEQ_VM_H
#define SUBLEQ_VM_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#define SUBLEQ_MEM_CELLS 65536u
#define SUBLEQ_EFORTH_HALT 32768u
#define SUBLEQ_MAX_BP 64
#define SUBLEQ_MAX_WP 64

typedef enum {
    SUBLEQ_MODE_EFORTH = 0,
    SUBLEQ_MODE_DIRECTIVE = 1
} subleq_mode;

typedef struct subleq_vm {
    uint32_t mem[SUBLEQ_MEM_CELLS];
    uint32_t mask;          /* 0xFFFFu or 0xFFFFFFFFu */
    uint32_t pc;
    uint32_t last_a, last_b, last_c, last_r;
    int last_wrote;
    uint32_t last_write_addr;
    uint32_t last_write_old;
    int halted;
    int trap;
    subleq_mode mode;
    uint64_t steps;
    uint64_t *prof;         /* per-address instruction counts, 65536 entries */
    uint32_t bp[SUBLEQ_MAX_BP];
    int nbp;
    uint32_t wp[SUBLEQ_MAX_WP];
    int nwp;
    int hit_break;
    int hit_watch;
    uint32_t hit_addr;
    uint32_t load_cells;
    /* I/O: if use_stdio, use getchar/putchar; else use buffers. */
    int use_stdio;
    char *out;
    size_t out_len, out_cap;
    const unsigned char *in;
    size_t in_len, in_pos;
} subleq_vm;

void subleq_vm_init(subleq_vm *vm, subleq_mode mode);
void subleq_vm_free(subleq_vm *vm);

/* Load whitespace- or comma-separated signed integers. Returns cells loaded, or -1. */
int subleq_load_dec(subleq_vm *vm, const char *path);
int subleq_load_dec_file(subleq_vm *vm, FILE *f);

/* One instruction. Returns 1 if a step ran, 0 if already halted/trapped. */
int subleq_step(subleq_vm *vm);

/* Run up to n steps or until halt/break/watch. n==0 means "until halt". */
uint64_t subleq_run(subleq_vm *vm, uint64_t n);

int subleq_add_break(subleq_vm *vm, uint32_t addr);
int subleq_add_watch(subleq_vm *vm, uint32_t addr);

uint32_t subleq_get(const subleq_vm *vm, uint32_t addr);
void subleq_set(subleq_vm *vm, uint32_t addr, uint32_t v);

#endif
