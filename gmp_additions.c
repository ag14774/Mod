#include "gmp_additions.h"

#ifndef mpz_inits
void mpz_inits(mpz_t x,...) {

  va_list  ap;

  va_start (ap, x);

  while (x != NULL) {
    mpz_init(x);
    x = va_arg (ap, mpz_ptr);
  }

  va_end (ap);
}
#endif

#ifndef mpz_clears
void mpz_clears(mpz_t x,...) {
  va_list  ap;

  va_start (ap, x);

  while (x != NULL) {
    mpz_clear(x);
    x = va_arg (ap, mpz_ptr);
  }

  va_end (ap);
}
#endif
