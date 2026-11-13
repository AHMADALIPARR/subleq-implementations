/*
 * SUBLEQ microcode debugger (eForth 16-bit and directive 32-bit).
 * All user-facing text goes through checked tfp_* (tinyprintf_checked).
 *
 * Copyright (C) Ahmad <ahmedparr93@gmail.com>
 * SPDX-License-Identifier: AGPL-3.0-only
 */
#define TINYPRINTF_OVERRIDE_LIBC 0
#define TINYPRINTF_DEFINE_TFP_PRINTF 1
#define TINYPRINTF_DEFINE_TFP_SPRINTF 1

#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "subleq_vm.h"
#include "tinyprintf_checked.h"

static FILE *g_out;

static void out_putf(void *p, char c)
{
    (void)p;
    fputc((int)c, g_out ? g_out : stdout);
}

static void emit(const char *fmt, ...)
{
    char buf[1024];
    va_list ap;
    va_start(ap, fmt);
    tfp_vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    fputs(buf, g_out ? g_out : stdout);
}

static void usage(void)
{
    emit("usage: subleq_dbg [options] IMAGE.dec\n"
         "  --mode=eforth|directive   machine width and I/O (default: eforth)\n"
         "  --trace                   print PC/A/B/C on every step\n"
         "  --profile                 enable per-address counts\n"
         "  --profile-out FILE        write heat map after run/quit\n"
         "  --break ADDR              PC breakpoint (repeatable)\n"
         "  --watch ADDR              cell write watchpoint (repeatable)\n"
         "  --max N                   cap executed instructions\n"
         "  --run                     run until halt/break/max (non-interactive)\n"
         "  --dump ADDR:LEN           dump cells after a --run\n"
         "  --quiet                   suppress trace banners\n"
         "  -c 'cmd;cmd'              run debugger commands then exit\n");
}

static uint32_t parse_u(const char *s, int *ok)
{
    char *end = NULL;
    unsigned long v;
    errno = 0;
    v = strtoul(s, &end, 0);
    if (ok)
        *ok = (end != s && errno == 0);
    return (uint32_t)v;
}

static void print_state(const subleq_vm *vm)
{
    emit("PC=%u A=%u B=%u C=%u R=%u steps=%llu halted=%d trap=%d\n",
         (unsigned)vm->pc, (unsigned)vm->last_a, (unsigned)vm->last_b,
         (unsigned)vm->last_c, (unsigned)vm->last_r,
         (unsigned long long)vm->steps, vm->halted, vm->trap);
}

static void print_trace(const subleq_vm *vm, uint32_t pc_before)
{
    emit("T %u: SUBLEQ %u %u %u -> R=%u PC'=%u\n",
         (unsigned)pc_before, (unsigned)vm->last_a, (unsigned)vm->last_b,
         (unsigned)vm->last_c, (unsigned)vm->last_r, (unsigned)vm->pc);
}

static void dump_mem(const subleq_vm *vm, uint32_t addr, uint32_t len)
{
    uint32_t i;
    for (i = 0; i < len; i++) {
        if ((i % 8) == 0)
            emit("%5u:", (unsigned)((addr + i) % SUBLEQ_MEM_CELLS));
        emit(" %6d", (int)(int16_t)(subleq_get(vm, addr + i) & 0xFFFFu));
        if ((i % 8) == 7)
            emit("\n");
    }
    if ((len % 8) != 0)
        emit("\n");
}

static void dump_profile(const subleq_vm *vm, FILE *f, int topn)
{
    uint32_t i;
    uint64_t total = 0;
    /* Simple insertion of the top N addresses; N is small. */
    uint32_t *idx = (uint32_t *)malloc((size_t)topn * sizeof(uint32_t));
    uint64_t *cnt = (uint64_t *)calloc((size_t)topn, sizeof(uint64_t));
    int nfill = 0, k;
    if (!idx || !cnt) {
        free(idx);
        free(cnt);
        return;
    }
    if (!vm->prof) {
        free(idx);
        free(cnt);
        return;
    }
    for (i = 0; i < SUBLEQ_MEM_CELLS; i++) {
        uint64_t c = vm->prof[i];
        total += c;
        if (c == 0)
            continue;
        if (f)
            fprintf(f, "%u %llu\n", (unsigned)i, (unsigned long long)c);
        if (nfill < topn) {
            idx[nfill] = i;
            cnt[nfill] = c;
            nfill++;
        } else {
            int minj = 0;
            for (k = 1; k < topn; k++)
                if (cnt[k] < cnt[minj])
                    minj = k;
            if (c > cnt[minj]) {
                idx[minj] = i;
                cnt[minj] = c;
            }
        }
    }
    emit("profile total_steps=%llu unique_pcs counted in top %d:\n",
         (unsigned long long)total, nfill);
    /* sort descending, nfill is tiny */
    for (k = 0; k < nfill; k++) {
        int j, best = k;
        for (j = k + 1; j < nfill; j++)
            if (cnt[j] > cnt[best])
                best = j;
        if (best != k) {
            uint32_t ti = idx[k];
            uint64_t tc = cnt[k];
            idx[k] = idx[best];
            cnt[k] = cnt[best];
            idx[best] = ti;
            cnt[best] = tc;
        }
        emit("  PC %5u  %llu\n", (unsigned)idx[k], (unsigned long long)cnt[k]);
    }
    free(idx);
    free(cnt);
}

static int cmd_one(subleq_vm *vm, char *line, int *trace, uint64_t max_steps)
{
    char *cmd, *arg, *arg2, *p;
    int ok;
    uint32_t addr, len, val;
    uint32_t pc_before;
    uint64_t left, ran;

    while (*line && isspace((unsigned char)*line))
        line++;
    if (*line == 0 || *line == '#')
        return 0;
    cmd = line;
    p = line;
    while (*p && !isspace((unsigned char)*p))
        p++;
    if (*p) { *p++ = 0; while (*p && isspace((unsigned char)*p)) p++; }
    arg = (*p) ? p : NULL;
    if (arg) {
        char *q = arg;
        while (*q && !isspace((unsigned char)*q))
            q++;
        if (*q) { *q++ = 0; while (*q && isspace((unsigned char)*q)) q++; }
        arg2 = (*q) ? q : NULL;
        if (arg2) {
            char *r = arg2;
            while (*r && !isspace((unsigned char)*r))
                r++;
            *r = 0;
        }
    } else {
        arg2 = NULL;
    }
    if (!cmd || !*cmd)
        return 0;
    if (strcmp(cmd, "q") == 0 || strcmp(cmd, "quit") == 0)
        return 1;
    if (strcmp(cmd, "p") == 0 || strcmp(cmd, "state") == 0) {
        print_state(vm);
        return 0;
    }
    if (strcmp(cmd, "s") == 0 || strcmp(cmd, "step") == 0) {
        if (vm->halted) {
            emit("already halted\n");
            return 0;
        }
        pc_before = vm->pc;
        subleq_step(vm);
        if (*trace)
            print_trace(vm, pc_before);
        else
            print_state(vm);
        if (vm->hit_watch)
            emit("watch hit addr=%u\n", (unsigned)vm->hit_addr);
        return 0;
    }
    if (strcmp(cmd, "r") == 0 || strcmp(cmd, "run") == 0) {
        uint64_t n = arg ? (uint64_t)strtoull(arg, NULL, 0) : 1;
        ran = 0;
        while (ran < n && !vm->halted && !vm->trap) {
            pc_before = vm->pc;
            if (!subleq_step(vm))
                break;
            ran++;
            if (*trace)
                print_trace(vm, pc_before);
            if (vm->hit_watch) {
                emit("watch hit addr=%u after %llu step(s)\n",
                     (unsigned)vm->hit_addr, (unsigned long long)ran);
                break;
            }
            if (vm->hit_break) {
                emit("break hit PC=%u after %llu step(s)\n",
                     (unsigned)vm->hit_addr, (unsigned long long)ran);
                break;
            }
        }
        emit("ran %llu steps; ", (unsigned long long)ran);
        print_state(vm);
        return 0;
    }
    if (strcmp(cmd, "c") == 0 || strcmp(cmd, "cont") == 0) {
        left = max_steps ? max_steps - vm->steps : 0;
        if (max_steps && vm->steps >= max_steps) {
            emit("max steps already reached\n");
            return 0;
        }
        ran = subleq_run(vm, left);
        emit("ran %llu steps; ", (unsigned long long)ran);
        print_state(vm);
        if (vm->hit_break)
            emit("break hit PC=%u\n", (unsigned)vm->hit_addr);
        if (vm->hit_watch)
            emit("watch hit addr=%u\n", (unsigned)vm->hit_addr);
        return 0;
    }
    if (strcmp(cmd, "b") == 0 || strcmp(cmd, "break") == 0) {
        if (!arg) {
            emit("usage: b ADDR\n");
            return 0;
        }
        addr = parse_u(arg, &ok);
        if (!ok || subleq_add_break(vm, addr) != 0)
            emit("cannot set breakpoint\n");
        else
            emit("breakpoint PC=%u\n", (unsigned)addr);
        return 0;
    }
    if (strcmp(cmd, "w") == 0 || strcmp(cmd, "watch") == 0) {
        if (!arg) {
            emit("usage: w ADDR\n");
            return 0;
        }
        addr = parse_u(arg, &ok);
        if (!ok || subleq_add_watch(vm, addr) != 0)
            emit("cannot set watchpoint\n");
        else
            emit("watch addr=%u\n", (unsigned)addr);
        return 0;
    }
    if (strcmp(cmd, "d") == 0 || strcmp(cmd, "dump") == 0) {
        addr = arg ? parse_u(arg, &ok) : 0;
        len = arg2 ? parse_u(arg2, &ok) : 16;
        dump_mem(vm, addr, len);
        return 0;
    }
    if (strcmp(cmd, "set") == 0) {
        if (!arg || !arg2) {
            emit("usage: set ADDR VAL\n");
            return 0;
        }
        addr = parse_u(arg, &ok);
        val = parse_u(arg2, &ok);
        subleq_set(vm, addr, val);
        emit("mem[%u]=%u\n", (unsigned)addr, (unsigned)subleq_get(vm, addr));
        return 0;
    }
    if (strcmp(cmd, "t") == 0 || strcmp(cmd, "trace") == 0) {
        *trace = !*trace;
        emit("trace %s\n", *trace ? "on" : "off");
        return 0;
    }
    if (strcmp(cmd, "stats") == 0 || strcmp(cmd, "profile") == 0) {
        dump_profile(vm, NULL, 16);
        return 0;
    }
    if (strcmp(cmd, "help") == 0 || strcmp(cmd, "h") == 0) {
        emit("commands: s step, r N, c cont, b ADDR, w ADDR, d ADDR LEN,\n"
             "  p state, t trace, set ADDR VAL, stats, q quit\n");
        return 0;
    }
    emit("unknown command '%s' (h for help)\n", cmd);
    return 0;
}

int main(int argc, char **argv)
{
    subleq_vm vm;
    subleq_mode mode = SUBLEQ_MODE_EFORTH;
    const char *image = NULL;
    const char *cmds = NULL;
    const char *prof_out = NULL;
    const char *dump_spec = NULL;
    int trace = 0, do_run = 0, quiet = 0, do_profile = 1;
    uint64_t max_steps = 0;
    uint32_t breaks[SUBLEQ_MAX_BP];
    uint32_t watches[SUBLEQ_MAX_WP];
    int nbreaks = 0, nwatches = 0, i, nload, done;
    char line[512];

    g_out = stdout;
    init_printf(NULL, out_putf);

    for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            usage();
            return 0;
        }
        if (strncmp(argv[i], "--mode=", 7) == 0) {
            if (strcmp(argv[i] + 7, "eforth") == 0)
                mode = SUBLEQ_MODE_EFORTH;
            else if (strcmp(argv[i] + 7, "directive") == 0)
                mode = SUBLEQ_MODE_DIRECTIVE;
            else {
                emit("unknown mode\n");
                return 2;
            }
        } else if (strcmp(argv[i], "--trace") == 0) {
            trace = 1;
        } else if (strcmp(argv[i], "--profile") == 0) {
            do_profile = 1;
        } else if (strcmp(argv[i], "--profile-out") == 0 && i + 1 < argc) {
            prof_out = argv[++i];
            do_profile = 1;
        } else if (strcmp(argv[i], "--break") == 0 && i + 1 < argc) {
            int ok;
            if (nbreaks < (int)SUBLEQ_MAX_BP)
                breaks[nbreaks++] = parse_u(argv[++i], &ok);
        } else if (strcmp(argv[i], "--watch") == 0 && i + 1 < argc) {
            int ok;
            if (nwatches < (int)SUBLEQ_MAX_WP)
                watches[nwatches++] = parse_u(argv[++i], &ok);
        } else if (strcmp(argv[i], "--max") == 0 && i + 1 < argc) {
            max_steps = strtoull(argv[++i], NULL, 0);
        } else if (strcmp(argv[i], "--run") == 0) {
            do_run = 1;
        } else if (strcmp(argv[i], "--dump") == 0 && i + 1 < argc) {
            dump_spec = argv[++i];
        } else if (strcmp(argv[i], "--quiet") == 0) {
            quiet = 1;
        } else if (strcmp(argv[i], "-c") == 0 && i + 1 < argc) {
            cmds = argv[++i];
        } else if (argv[i][0] == '-') {
            emit("unknown option %s\n", argv[i]);
            usage();
            return 2;
        } else {
            image = argv[i];
        }
    }
    if (!image) {
        usage();
        return 2;
    }

    subleq_vm_init(&vm, mode);
    (void)do_profile;
    nload = subleq_load_dec(&vm, image);
    if (nload < 0) {
        emit("failed to load %s\n", image);
        subleq_vm_free(&vm);
        return 1;
    }
    if (!quiet)
        emit("loaded %d cells from %s mode=%s\n", nload, image,
             mode == SUBLEQ_MODE_EFORTH ? "eforth" : "directive");
    for (i = 0; i < nbreaks; i++)
        subleq_add_break(&vm, breaks[i]);
    for (i = 0; i < nwatches; i++)
        subleq_add_watch(&vm, watches[i]);

    if (do_run) {
        uint64_t ran = subleq_run(&vm, max_steps);
        if (!quiet) {
            emit("ran %llu steps; ", (unsigned long long)ran);
            print_state(&vm);
        }
        if (dump_spec) {
            char tmp[64];
            char *colon;
            uint32_t addr, len;
            tfp_snprintf(tmp, sizeof tmp, "%s", dump_spec);
            colon = strchr(tmp, ':');
            if (colon) {
                *colon = 0;
                addr = (uint32_t)strtoul(tmp, NULL, 0);
                len = (uint32_t)strtoul(colon + 1, NULL, 0);
            } else {
                addr = (uint32_t)strtoul(tmp, NULL, 0);
                len = 16;
            }
            dump_mem(&vm, addr, len);
        }
        if (!quiet)
            dump_profile(&vm, NULL, 8);
    }

    if (cmds) {
        char buf[1024];
        char *sp, *tok;
        tfp_snprintf(buf, sizeof buf, "%s", cmds);
        sp = buf;
        done = 0;
        while (!done && *sp) {
            char one[512];
            tok = sp;
            while (*sp && *sp != ';')
                sp++;
            if (*sp == ';') { *sp = 0; sp++; }
            tfp_snprintf(one, sizeof one, "%s", tok);
            done = cmd_one(&vm, one, &trace, max_steps);
        }
    } else if (!do_run) {
        done = 0;
        while (!done) {
            emit("dbg> ");
            fflush(stdout);
            if (!fgets(line, (int)sizeof line, stdin))
                break;
            done = cmd_one(&vm, line, &trace, max_steps);
        }
    }

    if (prof_out) {
        FILE *f = fopen(prof_out, "w");
        if (f) {
            dump_profile(&vm, f, 16);
            fclose(f);
        }
    }
    subleq_vm_free(&vm);
    return 0;
}
