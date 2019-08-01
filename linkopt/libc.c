#include <stddef.h>
#include <stdarg.h>
#include <stdint.h>
#include "printf.h"

int putchar(int);
void _putchar(char character) {
  putchar(character);
}

extern void abort(void);

void _PDCLIB_assert99( const char * const message1, const char * const function, const char * const message2 )
{
    // fputs( message1, stderr );
    // fputs( function, stderr );
    // fputs( message2, stderr );
    abort();
}

static void __attribute__((__noreturn__)) __chk_fail (void) {
  abort();
}

int __snprintf_chk(char * str, size_t maxlen, int flag, size_t strlen, const char * format, ...) {
  va_list arg;
  int ret;

  va_start (arg, format);
  ret = vsnprintf_(str, maxlen, format, arg);
  va_end (arg);

  if(__builtin_expect(ret+1 > maxlen && maxlen < strlen, 0))
    __chk_fail();

  return ret;
}

int snprintf(char * str, size_t len, const char * format, ...) {
  va_list arg;
  int ret;

  va_start (arg, format);
  ret = vsnprintf_(str, len, format, arg);
  va_end (arg);

  return ret;
}

int printf(const char * format, ...) {
  va_list arg;
  int ret;

  va_start (arg, format);
  ret = vprintf_(format, arg);
  va_end (arg);

  return ret;
}

size_t strlen(const char *s) {
  size_t i = 0;
  while(s[i]) ++i;
  return i;
}

size_t strnlen(const char *s, size_t maxlen) {
  size_t i = 0;
  while(i < maxlen && s[i]) ++i;
  return i;
}

char *strcat(char *restrict s1, const char *restrict s2) {
  char *orig = s1;
  while(*s1) ++s1;
  while((*s1 = *s2)) ++s1, ++s2;
  return orig;
}

char *strncat(char *restrict s1, const char *restrict s2, size_t n) {
  char *orig = s1;
  while(*s1) ++s1;
  do {
    if(n-- <= 0) {
      *s1 = 0;
      return orig;
    }
    if(!(*s1 = *s2)) {
      return orig;
    }
    ++s1, ++s2;
  } while(1);
}

char *__strncat_chk(char *restrict s1, const char *restrict s2, size_t n, size_t dstlen) {
  char *orig = s1;
  do {
    if(__builtin_expect(dstlen-- <= 0, 0))
      __chk_fail();
    if(!*s1)
      break;
    ++s1;
  } while(1);

  do {
    if(n-- <= 0) {
      *s1 = 0;
      return orig;
    }
    if(!(*s1 = *s2)) {
      return orig;
    }
    ++s1, ++s2;
    if(__builtin_expect(dstlen-- <= 0, 0))
      __chk_fail();
  } while(1);
}

void *memcpy(void *restrict dst, const void *restrict src, size_t n) {
  void *orig = dst;
  char *restrict x = (char*)dst;
  const char *restrict y = (const char*)src;
  while(n-- > 0) {
    *x = *y;
    ++x, ++y;
  }
  return orig;
}

void *memmove(void *dst, const void *src, size_t n) {
  void *orig = dst;
  char *x = (char*)dst;
  const char *y = (const char*)src;
  while(n-- > 0) {
    *x = *y;
    ++x, ++y;
  }
  return orig;
}

void *__memcpy_chk (void *dest, const void *src, size_t len, size_t dstlen) {
  if(__builtin_expect(dstlen < len, 0))
    __chk_fail();
  return memcpy(dest, src, len);
}

int memcmp(const void *s1, const void *s2, size_t n) {
  const char *x = (const char*)s1;
  const char *y = (const char*)s2;
  while(n-- > 0) {
    int diff = (int)(unsigned char)*x - (int)(unsigned char)*y;
    if(diff != 0)
      return diff;
    ++x, ++y;
  }
  return 0;
}

int strcmp(const char *s1, const char *s2) {
  const char *x = (const char*)s1;
  const char *y = (const char*)s2;
  while(*x || *y) {
    int diff = (int)(unsigned char)*x - (int)(unsigned char)*y;
    if(diff != 0)
      return diff;
    ++x, ++y;
  }
  return 0;
}

int strncmp(const char *s1, const char *s2, size_t n) {
  const char *x = (const char*)s1;
  const char *y = (const char*)s2;
  while(n-- > 0 && (*x || *y)) {
    int diff = (int)(unsigned char)*x - (int)(unsigned char)*y;
    if(diff != 0)
      return diff;
    ++x, ++y;
  }
  return 0;
}

void *memset(void *b, int c, size_t len) {
  void *orig = b;
  char *x = (char*)b;
  while(len-- > 0)
    *x = c;
  return orig;
}

void *__memset_chk(void *dest, int val, size_t len, size_t dstlen) {
  if(__builtin_expect(dstlen < len, 0))
    __chk_fail();
  return memset(dest, val, len);
}

void __attribute__((__noreturn__)) __assert_rtn(const char *func, const char *file, int line, const char *expr) {
  printf("%s:%d:%s assert(%s)\n", file, line, func, expr);
  abort();
}
