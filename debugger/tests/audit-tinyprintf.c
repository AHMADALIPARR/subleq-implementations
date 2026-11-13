/*
 * Audit tests for the six reported issues in tinyprintf.c.
 * Build with: cc -std=c11 -Wall -Wextra -DTINYPRINTF_OVERRIDE_LIBC=0
 *              -fsanitize=undefined,address -g -I.. \
 *              -o audit-tinyprintf audit-tinyprintf.c ../tinyprintf.c
 *
 * Compares tfp_* against glibc snprintf where applicable.
 * Copyright (C) Ahmad <ahmedparr93@gmail.com>
 * SPDX-License-Identifier: AGPL-3.0-only
 */
#define TINYPRINTF_OVERRIDE_LIBC 0
#define TINYPRINTF_DEFINE_TFP_PRINTF 1
#define TINYPRINTF_DEFINE_TFP_SPRINTF 1

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <stdint.h>
#include "../tinyprintf.h"

static void stdout_putf(void *p, char c)
{
    (void)p;
    fputc(c, stdout);
}

static int fails;

static void note(const char *s)
{
    fprintf(stderr, "%s\n", s);
}

/* ---------- Issue 3: size==0 ---------- */
static void test_issue3(void)
{
    char buf[64];
    int t, g;
    memset(buf, 'Z', sizeof buf);
    t = tfp_snprintf(buf, 0, "hello-%d", 42);
    g = snprintf(NULL, 0, "hello-%d", 42);
    fprintf(stderr, "ISSUE3 tfp_snprintf(size=0) = %d; glibc snprintf(NULL,0) = %d; buf[0]='%c'\n",
            t, g, buf[0]);
    if (t == 0 && g > 0)
        fprintf(stderr, "ISSUE3 CONFIRMED: tfp returns 0 instead of the would-be length %d\n", g);
    else if (t == g)
        fprintf(stderr, "ISSUE3 REFUTED: return values match (%d)\n", t);
    else
        fprintf(stderr, "ISSUE3 PARTIAL: tfp=%d glibc=%d (neither 0-only nor equal)\n", t, g);
}

/* ---------- Issue 2: a2u digit > base vs >= base ---------- */
/* "%10ad" should be width 10, conversion 'a' (or invalid), not width 110 + 'd'. */
static void test_issue2(void)
{
    char tbuf[128], gbuf[128];
    int t, g;
    /* If 'a' is wrongly accepted as a decimal width digit (value 10),
     * width becomes 10*10+10=110 and the conversion is 'd'. */
    t = tfp_snprintf(tbuf, sizeof tbuf, "%10ad", 5);
    g = snprintf(gbuf, sizeof gbuf, "%10ad", 5);
    fprintf(stderr, "ISSUE2 tfp  '%%10ad' -> [%s] ret=%d (len=%zu)\n", tbuf, t, strlen(tbuf));
    fprintf(stderr, "ISSUE2 glibc '%%10ad' -> [%s] ret=%d (len=%zu)\n", gbuf, g, strlen(gbuf));
    if (strlen(tbuf) == 110 && tbuf[109] == '5')
        fprintf(stderr, "ISSUE2 CONFIRMED: 'a' was consumed as a decimal width digit (width 110)\n");
    else if (strcmp(tbuf, gbuf) == 0)
        fprintf(stderr, "ISSUE2 REFUTED for this case: outputs match\n");
    else
        fprintf(stderr, "ISSUE2 outputs differ (investigate)\n");
}

/* ---------- Issue 1: INT_MIN negation UB ---------- */
static void test_issue1(void)
{
    char tbuf[64], gbuf[64];
    int t, g;
    fprintf(stderr, "ISSUE1: calling tfp_snprintf(\"%%d\", INT_MIN) ; INT_MIN=%d\n", INT_MIN);
    t = tfp_snprintf(tbuf, sizeof tbuf, "%d", INT_MIN);
    g = snprintf(gbuf, sizeof gbuf, "%d", INT_MIN);
    fprintf(stderr, "ISSUE1 tfp  [%s] ret=%d\n", tbuf, t);
    fprintf(stderr, "ISSUE1 glibc [%s] ret=%d\n", gbuf, g);
    if (strcmp(tbuf, gbuf) != 0)
        fprintf(stderr, "ISSUE1 RESULT MISMATCH in addition to possible UB\n");
    fprintf(stderr, "ISSUE1: if UBSAN reported 'negation of -2147483648 cannot be represented', CONFIRMED\n");
}

/* ---------- Issue 6: vsprintf no capacity ---------- */
static void test_issue6(void)
{
    /* Small buffer, long output. ASAN should report overflow. */
    char tiny[8];
    memset(tiny, 'A', sizeof tiny);
    fprintf(stderr, "ISSUE6: tfp_sprintf into 8-byte buffer with a 40-char message\n");
    tfp_sprintf(tiny, "OVERFLOW-%s-%d-XXXX", "ABCDEFGHIJ", 12345678);
    fprintf(stderr, "ISSUE6: returned to caller; tiny='%s' (if you see this without ASAN, overflow was silent)\n", tiny);
}

/* ---------- Issue 5: width/prec overflow ---------- */
static void test_issue5(void)
{
    char tbuf[256], gbuf[256];
    int t;
    /* 10 nines: 9999999999 > UINT_MAX (4294967295) — unsigned multiply in a2u overflows */
    fprintf(stderr, "ISSUE5: parsing %%9999999999d (width larger than UINT_MAX)\n");
    t = tfp_snprintf(tbuf, sizeof tbuf, "%9999999999d", 7);
    fprintf(stderr, "ISSUE5 tfp ret=%d len=%zu content_head=%.40s\n", t, strlen(tbuf), tbuf);
    /* Assignment of unsigned width to int: %2147483648d is UINT 2147483648 > INT_MAX */
    fprintf(stderr, "ISSUE5: parsing %%2147483648d (UINT value INT_MAX+1 assigned to int width)\n");
    t = tfp_snprintf(tbuf, sizeof tbuf, "%2147483648d", 7);
    fprintf(stderr, "ISSUE5 tfp ret=%d len=%zu (may be huge or negative-width behavior)\n", t, strlen(tbuf));
    /* Compare a still-in-range but large width against glibc, using a cap on buffer */
    t = tfp_snprintf(tbuf, sizeof tbuf, "%200d", 7);
    snprintf(gbuf, sizeof gbuf, "%200d", 7);
    fprintf(stderr, "ISSUE5 control %%200d tfp_len=%zu glibc_len=%zu match=%s\n",
            strlen(tbuf), strlen(gbuf), strcmp(tbuf, gbuf) == 0 ? "yes" : "no");
    (void)gbuf;
}

/* ---------- Issue 4: putchw vs glibc sweep ---------- */
static int issue4_diffs;

static void one_fmt(const char *fmt, int v)
{
    char tbuf[256], gbuf[256];
    int t = tfp_snprintf(tbuf, sizeof tbuf, fmt, v);
    int g = snprintf(gbuf, sizeof gbuf, fmt, v);
    if (t != g || strcmp(tbuf, gbuf) != 0) {
        issue4_diffs++;
        if (issue4_diffs <= 40) {
            fprintf(stderr, "ISSUE4 DIFF fmt=%s v=%d tfp=[%s] ret=%d glibc=[%s] ret=%d\n",
                    fmt, v, tbuf, t, gbuf, g);
        }
    }
}

static void one_fmt_u(const char *fmt, unsigned v)
{
    char tbuf[256], gbuf[256];
    int t = tfp_snprintf(tbuf, sizeof tbuf, fmt, v);
    int g = snprintf(gbuf, sizeof gbuf, fmt, v);
    if (t != g || strcmp(tbuf, gbuf) != 0) {
        issue4_diffs++;
        if (issue4_diffs <= 40) {
            fprintf(stderr, "ISSUE4 DIFF fmt=%s u=%u tfp=[%s] ret=%d glibc=[%s] ret=%d\n",
                    fmt, v, tbuf, t, gbuf, g);
        }
    }
}

static void one_fmt_s(const char *fmt, const char *s)
{
    char tbuf[256], gbuf[256];
    int t = tfp_snprintf(tbuf, sizeof tbuf, fmt, s);
    int g = snprintf(gbuf, sizeof gbuf, fmt, s);
    if (t != g || strcmp(tbuf, gbuf) != 0) {
        issue4_diffs++;
        if (issue4_diffs <= 40) {
            fprintf(stderr, "ISSUE4 DIFF fmt=%s s=%s tfp=[%s] ret=%d glibc=[%s] ret=%d\n",
                    fmt, s, tbuf, t, gbuf, g);
        }
    }
}

static void test_issue4(void)
{
    static const int ivals[] = {0, 1, -1, 5, 42, -42, 255, -255, 12345, -12345, INT_MAX, INT_MIN};
    static const unsigned uvals[] = {0, 1, 7, 8, 15, 16, 255, 0xabcd, UINT_MAX};
    static const char *svals[] = {"", "a", "ab", "hello", "ABCDEFGH"};
    static const char *d_fmts[] = {
        "%d", "%i", "%8d", "%08d", "%-8d", "%-08d",
        "%.0d", "%.1d", "%.3d", "%.8d",
        "%8.0d", "%8.3d", "%08.3d", "%-8.3d", "%-08.3d",
        "%+d", "%+8d", "%+08d", "%+.3d", "%+8.3d",
        "% d", "% 8d", "% 08d",
        "%*.*d"
    };
    static const char *u_fmts[] = {
        "%u", "%8u", "%08u", "%-8u",
        "%x", "%X", "%#x", "%#X", "%08x", "%#08x", "%-#8x", "%#8.3x",
        "%o", "%#o", "%08o", "%#08o", "%.0o", "%#.0o",
        "%.0u", "%8.0u", "%8.3x"
    };
    static const char *s_fmts[] = {
        "%s", "%8s", "%-8s", "%.0s", "%.3s", "%8.3s", "%-8.3s", "%08s"
    };
    unsigned i, j;
    issue4_diffs = 0;
    for (i = 0; i < sizeof ivals / sizeof ivals[0]; i++) {
        for (j = 0; j < sizeof d_fmts / sizeof d_fmts[0]; j++) {
            if (strcmp(d_fmts[j], "%*.*d") == 0) {
                char tbuf[256], gbuf[256];
                int t = tfp_snprintf(tbuf, sizeof tbuf, "%*.*d", 8, 3, ivals[i]);
                int g = snprintf(gbuf, sizeof gbuf, "%*.*d", 8, 3, ivals[i]);
                if (t != g || strcmp(tbuf, gbuf) != 0) {
                    issue4_diffs++;
                    if (issue4_diffs <= 40)
                        fprintf(stderr, "ISSUE4 DIFF fmt=%%*.*d v=%d tfp=[%s] glibc=[%s]\n",
                                ivals[i], tbuf, gbuf);
                }
            } else {
                one_fmt(d_fmts[j], ivals[i]);
            }
        }
    }
    for (i = 0; i < sizeof uvals / sizeof uvals[0]; i++)
        for (j = 0; j < sizeof u_fmts / sizeof u_fmts[0]; j++)
            one_fmt_u(u_fmts[j], uvals[i]);
    for (i = 0; i < sizeof svals / sizeof svals[0]; i++)
        for (j = 0; j < sizeof s_fmts / sizeof s_fmts[0]; j++)
            one_fmt_s(s_fmts[j], svals[i]);
    fprintf(stderr, "ISSUE4 sweep diffs vs glibc snprintf: %d\n", issue4_diffs);
    if (issue4_diffs > 0)
        fprintf(stderr, "ISSUE4 CONFIRMED: %d formatting mismatches vs glibc\n", issue4_diffs);
    else
        fprintf(stderr, "ISSUE4 REFUTED on this sweep: no mismatches\n");
}

int main(int argc, char **argv)
{
    const char *which = (argc > 1) ? argv[1] : "all";
    init_printf(NULL, stdout_putf);
    if (strcmp(which, "all") == 0 || strcmp(which, "3") == 0) test_issue3();
    if (strcmp(which, "all") == 0 || strcmp(which, "2") == 0) test_issue2();
    if (strcmp(which, "all") == 0 || strcmp(which, "1") == 0) test_issue1();
    if (strcmp(which, "all") == 0 || strcmp(which, "4") == 0) test_issue4();
    if (strcmp(which, "all") == 0 || strcmp(which, "5") == 0) test_issue5();
    /* Issue 6 last: it may crash under ASAN */
    if (strcmp(which, "all") == 0 || strcmp(which, "6") == 0) test_issue6();
    (void)fails;
    return 0;
}
