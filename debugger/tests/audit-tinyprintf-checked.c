/*
 * Re-audit of tinyprintf_checked.c: each of the six issues must be fixed.
 * Build (see Makefile.debugger): sanitizers on, TINYPRINTF_OVERRIDE_LIBC=0.
 * Exit 0 if all checks pass, 1 otherwise.
 *
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
#include "../tinyprintf_checked.h"

static void stdout_putf(void *p, char c)
{
    (void)p;
    fputc(c, stdout);
}

static int fails;

static void fail(const char *s)
{
    fprintf(stderr, "FAIL: %s\n", s);
    fails++;
}

static void pass(const char *s)
{
    fprintf(stderr, "PASS: %s\n", s);
}

static void test_issue3(void)
{
    char buf[64];
    int t, g;
    memset(buf, 'Z', sizeof buf);
    t = tfp_snprintf(buf, 0, "hello-%d", 42);
    g = snprintf(NULL, 0, "hello-%d", 42);
    fprintf(stderr, "ISSUE3 tfp_snprintf(size=0)=%d glibc=%d buf[0]='%c'\n", t, g, buf[0]);
    if (t == g && buf[0] == 'Z')
        pass("issue 3: size==0 returns length and writes nothing");
    else
        fail("issue 3: size==0 should return glibc length and leave buf[0]");
}

static void test_issue2(void)
{
    char tbuf[128];
    int t;
    {
        const char fmt[] = {'%', '1', '0', 'a', 'd', 0};
        int (*fp)(char *, size_t, const char *, ...) = tfp_snprintf;
        t = fp(tbuf, sizeof tbuf, fmt, 5);
    }
    fprintf(stderr, "ISSUE2 tfp '%%10ad' -> [%s] ret=%d len=%zu\n", tbuf, t, strlen(tbuf));
    if (strlen(tbuf) == 110 && tbuf[109] == '5')
        fail("issue 2: 'a' was still consumed as a width digit");
    else {
        /* With the fix, width is 10 and conversion 'a' is not valid, so
           'a' is skipped and the following literal 'd' is emitted. */
        pass("issue 2: 'a' is not a decimal width digit (no width-110 field)");
    }
}

static void test_issue1(void)
{
    char tbuf[64], gbuf[64];
    int t, g;
    t = tfp_snprintf(tbuf, sizeof tbuf, "%d", INT_MIN);
    g = snprintf(gbuf, sizeof gbuf, "%d", INT_MIN);
    fprintf(stderr, "ISSUE1 tfp=[%s] ret=%d glibc=[%s] ret=%d\n", tbuf, t, gbuf, g);
    if (t == g && strcmp(tbuf, gbuf) == 0)
        pass("issue 1: INT_MIN formats without signed negation, matches glibc");
    else
        fail("issue 1: INT_MIN mismatch vs glibc");
}

static void test_issue6(void)
{
    char tiny[8];
    int t;
    memset(tiny, 'A', sizeof tiny);
    t = tfp_sprintf_checked(tiny, sizeof tiny, "OVERFLOW-%s-%d-XXXX", "ABCDEFGHIJ", 12345678);
    fprintf(stderr, "ISSUE6 tfp_sprintf_checked ret=%d tiny='%s' (cap=8)\n", t, tiny);
    if (t < 8)
        fail("issue 6: expected untruncated length >= 8");
    else if (tiny[7] != '\0')
        fail("issue 6: missing NUL at cap-1");
    else if (strlen(tiny) > 7)
        fail("issue 6: wrote past capacity");
    else
        pass("issue 6: bounded sprintf_checked does not overflow and NUL-terminates");
}

static void test_issue5(void)
{
    char tbuf[256], gbuf[256];
    int t, w;
    /* Fast hook: a2u saturates at INT_MAX instead of wrapping (1410065407)
       or assigning INT_MAX+1 to a signed int width. Full snprintf of an
       INT_MAX-wide field would take minutes under ASAN, so we do not loop it. */
    w = tfp_checked_parse_width("9999999999");
    fprintf(stderr, "ISSUE5 parse 9999999999 -> %d (INT_MAX=%d)\n", w, INT_MAX);
    if (w != INT_MAX)
        fail("issue 5: 9999999999 did not saturate at INT_MAX");
    else
        pass("issue 5: 9999999999 saturates at INT_MAX (not 1410065407)");
    w = tfp_checked_parse_width("2147483648");
    fprintf(stderr, "ISSUE5 parse 2147483648 -> %d\n", w);
    if (w != INT_MAX)
        fail("issue 5: 2147483648 (INT_MAX+1) did not saturate at INT_MAX");
    else
        pass("issue 5: 2147483648 saturates at INT_MAX (non-negative)");
    w = tfp_checked_parse_width("200");
    if (w != 200)
        fail("issue 5: parse 200");

    t = tfp_snprintf(tbuf, sizeof tbuf, "%200d", 7);
    snprintf(gbuf, sizeof gbuf, "%200d", 7);
    fprintf(stderr, "ISSUE5 control %%200d tfp_len=%zu glibc_len=%zu match=%s\n",
            strlen(tbuf), strlen(gbuf), strcmp(tbuf, gbuf) == 0 ? "yes" : "no");
    if (strcmp(tbuf, gbuf) == 0 && t == 200)
        pass("issue 5: in-range %%200d still matches glibc");
    else
        fail("issue 5: %%200d no longer matches glibc");
}

static int issue4_diffs;

static void one_fmt(const char *fmt, int v)
{
    char tbuf[256], gbuf[256];
    int t = tfp_snprintf(tbuf, sizeof tbuf, fmt, v);
    int g = snprintf(gbuf, sizeof gbuf, fmt, v);
    if (t != g || strcmp(tbuf, gbuf) != 0) {
        issue4_diffs++;
        if (issue4_diffs <= 40)
            fprintf(stderr, "ISSUE4 DIFF fmt=%s v=%d tfp=[%s] ret=%d glibc=[%s] ret=%d\n",
                    fmt, v, tbuf, t, gbuf, g);
    }
}

static void one_fmt_u(const char *fmt, unsigned v)
{
    char tbuf[256], gbuf[256];
    int t = tfp_snprintf(tbuf, sizeof tbuf, fmt, v);
    int g = snprintf(gbuf, sizeof gbuf, fmt, v);
    if (t != g || strcmp(tbuf, gbuf) != 0) {
        issue4_diffs++;
        if (issue4_diffs <= 40)
            fprintf(stderr, "ISSUE4 DIFF fmt=%s u=%u tfp=[%s] ret=%d glibc=[%s] ret=%d\n",
                    fmt, v, tbuf, t, gbuf, g);
    }
}

static void one_fmt_s(const char *fmt, const char *s)
{
    char tbuf[256], gbuf[256];
    int t = tfp_snprintf(tbuf, sizeof tbuf, fmt, s);
    int g = snprintf(gbuf, sizeof gbuf, fmt, s);
    if (t != g || strcmp(tbuf, gbuf) != 0) {
        issue4_diffs++;
        if (issue4_diffs <= 40)
            fprintf(stderr, "ISSUE4 DIFF fmt=%s s=%s tfp=[%s] ret=%d glibc=[%s] ret=%d\n",
                    fmt, s, tbuf, t, gbuf, g);
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
        "% d", "% 8d", "% 08d"
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
    for (i = 0; i < sizeof ivals / sizeof ivals[0]; i++)
        for (j = 0; j < sizeof d_fmts / sizeof d_fmts[0]; j++)
            one_fmt(d_fmts[j], ivals[i]);
    for (i = 0; i < sizeof uvals / sizeof uvals[0]; i++)
        for (j = 0; j < sizeof u_fmts / sizeof u_fmts[0]; j++)
            one_fmt_u(u_fmts[j], uvals[i]);
    for (i = 0; i < sizeof svals / sizeof svals[0]; i++)
        for (j = 0; j < sizeof s_fmts / sizeof s_fmts[0]; j++)
            one_fmt_s(s_fmts[j], svals[i]);
    /* %*.*d */
    for (i = 0; i < sizeof ivals / sizeof ivals[0]; i++) {
        char tbuf[256], gbuf[256];
        int t = tfp_snprintf(tbuf, sizeof tbuf, "%*.*d", 8, 3, ivals[i]);
        int g = snprintf(gbuf, sizeof gbuf, "%*.*d", 8, 3, ivals[i]);
        if (t != g || strcmp(tbuf, gbuf) != 0) {
            issue4_diffs++;
            if (issue4_diffs <= 40)
                fprintf(stderr, "ISSUE4 DIFF fmt=%%*.*d v=%d tfp=[%s] glibc=[%s]\n",
                        ivals[i], tbuf, gbuf);
        }
    }
    fprintf(stderr, "ISSUE4 sweep diffs vs glibc snprintf: %d\n", issue4_diffs);
    if (issue4_diffs == 0)
        pass("issue 4: supported-flag sweep matches glibc");
    else
        fail("issue 4: remaining formatting mismatches vs glibc");
}

static void test_oracles(void)
{
    char b[8];
    int n;
    n = tfp_i16toa(b, sizeof b, -32768);
    if (n != 6 || strcmp(b, "-32768") != 0)
        fail("oracle i16toa(-32768)");
    else
        pass("oracle i16toa(-32768) = -32768");
    n = tfp_u16toa(b, 0, 65535);
    if (n != 5)
        fail("oracle u16toa(65535) length");
    else
        pass("oracle u16toa(65535) length 5 with cap 0");
    memset(b, 'Z', sizeof b);
    n = tfp_i16toa(b, 1, -12);
    if (n != 3 || b[0] != '\0')
        fail("oracle i16toa cap 1");
    else
        pass("oracle i16toa cap 1 writes only NUL, returns 3");
}

int main(void)
{
    init_printf(NULL, stdout_putf);
    test_issue3();
    test_issue2();
    test_issue1();
    test_issue4();
    test_issue5();
    test_issue6();
    test_oracles();
    fprintf(stderr, "checked re-audit: %s (%d failures)\n", fails ? "FAIL" : "PASS", fails);
    return fails ? 1 : 0;
}
