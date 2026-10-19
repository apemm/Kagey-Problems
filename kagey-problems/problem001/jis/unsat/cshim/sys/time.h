/* gettimeofday, which lrat-check.c uses for its timing line. */
#ifndef SHIM_SYS_TIME_H
#define SHIM_SYS_TIME_H
struct timeval { long tv_sec; long tv_usec; };
int gettimeofday(struct timeval *, void *);
#endif
