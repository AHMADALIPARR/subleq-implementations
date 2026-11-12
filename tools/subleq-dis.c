/* subleq-dis.c - SUBLEQ raw image disassembler with pattern hints
 * C11, no dependencies.
 * Usage: subleq-dis image.txt
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int32_t words[1 << 20];
static size_t nwords = 0;

static int read_text(FILE *f) {
  int32_t v;
  while (fscanf(f, "%d", &v) == 1) {
    if (nwords >= sizeof(words)/sizeof(words[0])) return -1;
    words[nwords++] = v;
  }
  return 0;
}

static const char *pattern_hint(size_t pc, int32_t a, int32_t b, int32_t c) {
  /* very light pattern recognition for common macros */
  if (a == b && c == pc + 3) return "  ; zero cell";
  if (a == b && c >= 0 && c != pc + 3) return "  ; unconditional jump";
  if (a < 0 && b < 0) return "  ; halt";
  if (a == -1) return "  ; input";
  if (b == -1) return "  ; output";
  if (a == -2) return "  ; trap";
  return "";
}

int main(int argc, char **argv) {
  FILE *f = stdin;
  if (argc > 1) {
    f = fopen(argv[1], "r");
    if (!f) { perror(argv[1]); return 1; }
  }
  if (read_text(f) < 0) { fprintf(stderr, "image too large\n"); return 1; }
  if (f != stdin) fclose(f);

  printf("; SUBLEQ image, %zu words\n", nwords);
  for (size_t pc = 0; pc + 2 < nwords; pc += 3) {
    int32_t a = words[pc], b = words[pc+1], c = words[pc+2];
    printf("%04zx: subleq %d, %d, %d%s\n", pc, a, b, c, pattern_hint(pc, a, b, c));
  }
  return 0;
}
