/* Minimal declarations of the UCRT stdio functions used by lrat-check.c. */
#ifndef SHIM_STDIO_H
#define SHIM_STDIO_H
#include <stddef.h>
typedef struct _iobuf { void *_Placeholder; } FILE;
FILE *__acrt_iob_func(unsigned index);
#define stdin  (__acrt_iob_func(0))
#define stdout (__acrt_iob_func(1))
#define stderr (__acrt_iob_func(2))
#define EOF (-1)
FILE *fopen(const char *, const char *);
int fclose(FILE *);
int printf(const char *, ...);
int fprintf(FILE *, const char *, ...);
int fscanf(FILE *, const char *, ...);
char *fgets(char *, int, FILE *);
int fflush(FILE *);
#endif
