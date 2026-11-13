/*
File: tinyprintf.h

Copyright (C) 2004 Kustaa Nyholm

This library can be licensed either under MIT, BSD or LGPL license,
consistent with the accompanying tinyprintf.c provided by the user.

This library is really just two files: 'tinyprintf.h' and 'tinyprintf.c'.
They provide a simple and small printf functionality to be used in
embedded systems. Distributed in source form; compile them into your
project.

Two printf variants are provided: printf and the 'sprintf' family of
functions ('snprintf', 'sprintf', 'vsnprintf', 'vsprintf').

To use the printf, supply a character output function and call
init_printf(putp, putf) before tfp_printf.

The printf and sprintf functions are actually macros that translate to
'tfp_printf' and 'tfp_sprintf' when 'TINYPRINTF_OVERRIDE_LIBC' is set
(default). Setting it to 0 makes it possible to use them along with
'stdio.h' printf's in a single source file.

It is also possible to avoid defining tfp_printf and/or tfp_sprintf by
clearing 'TINYPRINTF_DEFINE_TFP_PRINTF' and/or
'TINYPRINTF_DEFINE_TFP_SPRINTF' to 0.

Checked-path header for tinyprintf_checked.c. The original
tinyprintf.h is kept verbatim. Adds tfp_*_checked and 16-bit oracles.

regs Kusti, 23.10.2004
*/

#ifndef __TFP_PRINTF__
#define __TFP_PRINTF__

#include <stdarg.h>
#include <stddef.h>

/* Global configuration */

#ifndef TINYPRINTF_DEFINE_TFP_PRINTF
# define TINYPRINTF_DEFINE_TFP_PRINTF 1
#endif

#ifndef TINYPRINTF_DEFINE_TFP_SPRINTF
# define TINYPRINTF_DEFINE_TFP_SPRINTF 1
#endif

#ifndef TINYPRINTF_OVERRIDE_LIBC
# define TINYPRINTF_OVERRIDE_LIBC 1
#endif

#ifdef __GNUC__
# define _TFP_SPECIFY_PRINTF_FMT(fmt_idx,arg1_idx) \
    __attribute__((format (printf, fmt_idx, arg1_idx)))
#else
# define _TFP_SPECIFY_PRINTF_FMT(fmt_idx,arg1_idx)
#endif

#ifdef __cplusplus
extern "C" {
#endif

typedef void (*putcf) (void *, char);

/*
 * tfp_format is the central function. For each output character after
 * formatting, putf(putp, ch) is called.
 */
void tfp_format(void *putp, putcf putf, const char *fmt, va_list va);

#if TINYPRINTF_DEFINE_TFP_SPRINTF
int tfp_vsnprintf(char *str, size_t size, const char *format, va_list ap);
int tfp_snprintf(char *str, size_t size, const char *format, ...)
    _TFP_SPECIFY_PRINTF_FMT(3, 4);
int tfp_vsprintf(char *str, const char *format, va_list ap);
int tfp_sprintf(char *str, const char *format, ...)
    _TFP_SPECIFY_PRINTF_FMT(2, 3);
/* Bounded alternatives (issue 6). tfp_vsprintf remains unbounded. */
int tfp_vsprintf_checked(char *str, size_t size, const char *format, va_list ap);
int tfp_sprintf_checked(char *str, size_t size, const char *format, ...)
    _TFP_SPECIFY_PRINTF_FMT(3, 4);
/* Canonical 16-bit decimal oracles (unsigned magnitude for negatives).
   snprintf-style: return untruncated length; NUL-terminate iff cap>0. */
int tfp_checked_parse_width(const char *s);
int tfp_u16toa(char *dst, size_t cap, unsigned v);
int tfp_i16toa(char *dst, size_t cap, int v);
# if TINYPRINTF_OVERRIDE_LIBC
#  define vsnprintf tfp_vsnprintf
#  define snprintf tfp_snprintf
#  define vsprintf tfp_vsprintf
#  define sprintf tfp_sprintf
# endif
#endif

#if TINYPRINTF_DEFINE_TFP_PRINTF
void init_printf(void *putp, putcf putf);
void tfp_printf(const char *fmt, ...) _TFP_SPECIFY_PRINTF_FMT(1, 2);
# if TINYPRINTF_OVERRIDE_LIBC
#  define printf tfp_printf
# endif
#endif

#ifdef __cplusplus
}
#endif

#endif
