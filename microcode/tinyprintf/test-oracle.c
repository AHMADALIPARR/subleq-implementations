/*
 * Exhaustive comparison of the assembled intfmt.dec image against
 * the checked C oracles tfp_u16toa / tfp_i16toa.
 *
 * Copyright (C) Ahmad <ahmedparr93@gmail.com>
 * SPDX-License-Identifier: AGPL-3.0-only
 */
#define TINYPRINTF_OVERRIDE_LIBC 0
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#include "../../debugger/subleq_vm.h"
#include "../../debugger/tinyprintf_checked.h"

/* From intfmt.lst (assembled labels). */
#define ADDR_INPUT 12
#define ADDR_CAP   13
#define ADDR_WIDTH 14
#define ADDR_MODE  15
#define ADDR_LEN   16
#define ADDR_BUF   32
#define FUEL       100000ULL

static void snapshot(const subleq_vm *vm, uint32_t *dst)
{
    memcpy(dst, vm->mem, SUBLEQ_MEM_CELLS * sizeof(uint32_t));
}

static void restore(subleq_vm *vm, const uint32_t *src)
{
    memcpy(vm->mem, src, SUBLEQ_MEM_CELLS * sizeof(uint32_t));
    vm->pc = 0;
    vm->halted = 0;
    vm->trap = 0;
    vm->steps = 0;
    vm->hit_break = 0;
    vm->hit_watch = 0;
}

static void read_buf(const subleq_vm *vm, char *dst, int cap)
{
    int i;
    if (cap <= 0)
        return;
    for (i = 0; i < cap; i++)
        dst[i] = (char)(subleq_get(vm, (uint32_t)(ADDR_BUF + i)) & 0xFFu);
}

int main(int argc, char **argv)
{
    const char *image = (argc > 1) ? argv[1] : "microcode/tinyprintf/intfmt.dec";
    subleq_vm vm;
    uint32_t *base = NULL;
    unsigned v;
    unsigned long long nrun = 0, fails = 0;
    unsigned long long umin = ~0ULL, umax = 0, usum = 0;
    unsigned long long imin = ~0ULL, imax = 0, isum = 0;
    int nload;
    FILE *log = NULL;

    if (argc > 2)
        log = fopen(argv[2], "w");

    subleq_vm_init(&vm, SUBLEQ_MODE_EFORTH);
    vm.use_stdio = 0;
    nload = subleq_load_dec(&vm, image);
    if (nload < 0) {
        fprintf(stderr, "cannot load %s\n", image);
        return 1;
    }
    base = (uint32_t *)malloc(SUBLEQ_MEM_CELLS * sizeof(uint32_t));
    if (!base)
        return 1;
    snapshot(&vm, base);

    for (v = 0; v < 65536u; v++) {
        char exp[16], got[16];
        int elen, glen;
        uint64_t st;

        /* u16, cap=8, width=0 */
        restore(&vm, base);
        subleq_set(&vm, ADDR_INPUT, v);
        subleq_set(&vm, ADDR_CAP, 8);
        subleq_set(&vm, ADDR_WIDTH, 0);
        subleq_set(&vm, ADDR_MODE, 0);
        st = subleq_run(&vm, FUEL);
        if (!vm.halted) {
            fprintf(stderr, "u16 %u: did not halt in %llu steps pc=%u\n",
                    v, (unsigned long long)st, (unsigned)vm.pc);
            fails++;
            break;
        }
        memset(got, 0, sizeof got);
        read_buf(&vm, got, 8);
        memset(exp, 0, sizeof exp);
        elen = tfp_u16toa(exp, 8, v);
        glen = (int)subleq_get(&vm, ADDR_LEN);
        if (elen != glen || strcmp(exp, got) != 0) {
            if (fails < 20)
                fprintf(stderr, "u16 FAIL v=%u len exp=%d got=%d str exp=[%s] got=[%s] steps=%llu\n",
                        v, elen, glen, exp, got, (unsigned long long)st);
            fails++;
        }
        if (st < umin) umin = st;
        if (st > umax) umax = st;
        usum += st;
        nrun++;

        /* i16, cap=8, width=0 */
        restore(&vm, base);
        subleq_set(&vm, ADDR_INPUT, v);
        subleq_set(&vm, ADDR_CAP, 8);
        subleq_set(&vm, ADDR_WIDTH, 0);
        subleq_set(&vm, ADDR_MODE, 1);
        st = subleq_run(&vm, FUEL);
        if (!vm.halted) {
            fprintf(stderr, "i16 %u: did not halt pc=%u\n", v, (unsigned)vm.pc);
            fails++;
            break;
        }
        memset(got, 0, sizeof got);
        read_buf(&vm, got, 8);
        memset(exp, 0, sizeof exp);
        elen = tfp_i16toa(exp, 8, (int16_t)v);
        glen = (int)subleq_get(&vm, ADDR_LEN);
        if (elen != glen || strcmp(exp, got) != 0) {
            if (fails < 20)
                fprintf(stderr, "i16 FAIL bits=%u n=%d len exp=%d got=%d str exp=[%s] got=[%s] steps=%llu\n",
                        v, (int)(int16_t)v, elen, glen, exp, got, (unsigned long long)st);
            fails++;
        }
        if (st < imin) imin = st;
        if (st > imax) imax = st;
        isum += st;
        nrun++;
    }

    /* Bounded / cap edge cases on a few values */
    {
        static const unsigned samples[] = {0, 1, 10, 99, 100, 32767, 32768, 65535};
        unsigned si, cap;
        for (si = 0; si < sizeof samples / sizeof samples[0]; si++) {
            for (cap = 0; cap <= 6; cap++) {
                char exp[16], got[16];
                int elen, glen;
                v = samples[si];
                restore(&vm, base);
                subleq_set(&vm, ADDR_INPUT, v);
                subleq_set(&vm, ADDR_CAP, cap);
                subleq_set(&vm, ADDR_WIDTH, 0);
                subleq_set(&vm, ADDR_MODE, 1);
                subleq_run(&vm, FUEL);
                memset(got, 0, sizeof got);
                if (cap > 0)
                    read_buf(&vm, got, (int)cap);
                memset(exp, 0, sizeof exp);
                elen = tfp_i16toa(cap ? exp : NULL, cap, (int16_t)v);
                glen = (int)subleq_get(&vm, ADDR_LEN);
                if (elen != glen) {
                    fprintf(stderr, "cap FAIL bits=%u cap=%u len exp=%d got=%d\n", v, cap, elen, glen);
                    fails++;
                } else if (cap == 0) {
                    /* no writes; length already compared */
                } else {
                    size_t vis = ((size_t)elen + 1 < cap) ? (size_t)elen + 1 : cap;
                    if (memcmp(exp, got, vis) != 0) {
                        fprintf(stderr, "cap FAIL bits=%u cap=%u vis=%zu exp=[%s] got=[%s]\n",
                                v, cap, vis, exp, got);
                        fails++;
                    }
                }
                nrun++;
            }
        }
    }

    fprintf(stderr, "oracle sweep runs=%llu fails=%llu\n", nrun, fails);
    fprintf(stderr, "u16toa steps min=%llu max=%llu mean=%llu (65536 values)\n",
            umin, umax, usum / 65536ull);
    fprintf(stderr, "i16toa steps min=%llu max=%llu mean=%llu (65536 values)\n",
            imin, imax, isum / 65536ull);
    if (log) {
        fprintf(log, "runs=%llu fails=%llu\n", nrun, fails);
        fprintf(log, "u16toa_steps_min=%llu\n", umin);
        fprintf(log, "u16toa_steps_max=%llu\n", umax);
        fprintf(log, "u16toa_steps_mean=%llu\n", usum / 65536ull);
        fprintf(log, "i16toa_steps_min=%llu\n", imin);
        fprintf(log, "i16toa_steps_max=%llu\n", imax);
        fprintf(log, "i16toa_steps_mean=%llu\n", isum / 65536ull);
        fclose(log);
    }
    subleq_vm_free(&vm);
    free(base);
    return fails ? 1 : 0;
}
