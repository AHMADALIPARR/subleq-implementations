/* Copyright (C) Ahmad <ahmedparr93@gmail.com>
 * SPDX-License-Identifier: AGPL-3.0-only
 *
 * IBX-1 integer-only Gaussian butterfly network — C23 native baseline.
 *
 * Topology, input data, arithmetic width, and number of butterfly
 * operations are identical to the Racket/Factor/SUBLEQ versions.
 * This file is the reference results and native performance baseline.
 * The SUBLEQ implementation (programs/ibx-subleq.rkt) measures how
 * efficiently the directive machine executes the same computation.
 *
 * Butterfly (4 integer operations, no multiply, no float):
 *   re[a] = xr - yi
 *   im[a] = xi + yr
 *   re[b] = xr + yi
 *   im[b] = xi - yr
 *
 * Energy invariant: E_out = N * E_in  (N = 1024 → scale 1024).
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#define N 1024

static void butterfly(int32_t *re, int32_t *im, int a, int b) {
    int32_t xr = re[a], xi = im[a];
    int32_t yr = re[b], yi = im[b];
    re[a] = xr - yi;
    im[a] = xi + yr;
    re[b] = xr + yi;
    im[b] = xi - yr;
}

static void stage(int32_t *re, int32_t *im, int d) {
    int block_size = 2 * d;
    int nblocks = N / block_size;
    for (int block = 0; block < nblocks; block++) {
        for (int j = 0; j < d; j++) {
            int a = block * block_size + j;
            int b = a + d;
            butterfly(re, im, a, b);
        }
    }
}

static void transform(int32_t *re, int32_t *im) {
    for (int d = 1; d < N; d *= 2)
        stage(re, im, d);
}

static int64_t energy(const int32_t *re, const int32_t *im) {
    int64_t e = 0;
    for (int j = 0; j < N; j++)
        e += (int64_t)re[j] * re[j] + (int64_t)im[j] * im[j];
    return e;
}

static void make_input(int32_t *re, int32_t *im) {
    for (int j = 0; j < N; j++) {
        re[j] = (j % 17) - 8;
        im[j] = 0;
    }
}

int main(void) {
    /* Small vector check (matches Factor/Racket) */
    int32_t re4[4] = {1, 2, 3, 4};
    int32_t im4[4] = {0, 0, 0, 0};
    /* Run the same stages on N=4 by temporarily treating it as a small transform */
    for (int d = 1; d < 4; d *= 2) {
        int block_size = 2 * d;
        int nblocks = 4 / block_size;
        for (int block = 0; block < nblocks; block++) {
            for (int j = 0; j < d; j++) {
                int a = block * block_size + j;
                int b = a + d;
                butterfly(re4, im4, a, b);
            }
        }
    }
    bool small_ok = (re4[0] == -3 && re4[1] == 5 && re4[2] == 5 && re4[3] == -3 &&
                     im4[0] == 5 && im4[1] == 1 && im4[2] == -1 && im4[3] == -5);
    printf("C23 small vector: %s\n", small_ok ? "PASS" : "FAIL");
    if (!small_ok) return 1;

    /* N=1024 energy invariant */
    int32_t *re = calloc(N, sizeof(int32_t));
    int32_t *im = calloc(N, sizeof(int32_t));
    if (!re || !im) return 2;
    make_input(re, im);
    int64_t before = energy(re, im);
    transform(re, im);
    int64_t after = energy(re, im);
    bool energy_ok = (after == (int64_t)N * before);
    printf("C23 N=1024 energy: before=%lld after=%lld scale=%d %s\n",
           (long long)before, (long long)after, N, energy_ok ? "PASS" : "FAIL");
    free(re);
    free(im);
    return energy_ok ? 0 : 1;
}
