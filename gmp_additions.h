#ifndef __GMP_ADDITIONS_H
#define __GMP_ADDITIONS_H
/**
 * This file just provides a few definitions that were not
 * available on snowy.
*/
#include <stdint.h>
#include <stdlib.h>
#include <stdarg.h>

#include    <gmp.h>

typedef unsigned long mp_bitcnt_t;

#ifndef mpz_inits
void mpz_inits(mpz_t x,...);
#endif

#ifndef mpz_clears
void mpz_clears(mpz_t x,...);
#endif

#endif
