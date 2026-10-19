/* assert as lrat-check.c uses it, on top of the declarations in stdio.h and stdlib.h. */
#ifndef SHIM_ASSERT_H
#define SHIM_ASSERT_H
#include <stdio.h>
#include <stdlib.h>
#define assert(e) ((e) ? (void)0 : (fprintf(stderr, "assertion failed: %s (%s:%d)\n", #e, __FILE__, __LINE__), abort()))
#endif
