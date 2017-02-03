#include "modmul.h"

/*
Perform stage 1:

- read each 3-tuple of N, e and m from stdin,
- compute the RSA encryption c, then
- write the ciphertext c to stdout.
*/

void stage1() {

  mpz_t N,e,m,c;
  rsa_pk_t rsa_pk;
  mpz_inits(N,e,m,c,NULL);
  rsa_pk_init(rsa_pk);

  while(1) {
    if (gmp_scanf("%ZX\n",N) == EOF) break;
    gmp_scanf("%ZX\n",e);
    gmp_scanf("%ZX\n",m);
    rsa_pk_set(rsa_pk, N, e);
    rsa_encrypt(c, rsa_pk, m);
    gmp_printf("%ZX\n",c);
  }

  rsa_pk_clear(rsa_pk);
  mpz_clears(N,e,m,c);

}

/*
Perform stage 2:

- read each 9-tuple of N, d, p, q, d_p, d_q, i_p, i_q and c from stdin,
- compute the RSA decryption m, then
- write the plaintext m to stdout.
*/

void stage2() {

  mpz_t N,d,p,q,d_p,d_q,i_p,i_q,m,c;
  rsa_sk_t rsa_sk;
  mpz_inits(N, d, p, q, d_p, d_q, i_p, i_q, m, c, NULL);
  rsa_sk_init(rsa_sk);

  while(1) {
    if (gmp_scanf("%ZX\n",N) == EOF) break;
    gmp_scanf("%ZX\n",d);
    gmp_scanf("%ZX\n",p);
    gmp_scanf("%ZX\n",q);
    gmp_scanf("%ZX\n",d_p);
    gmp_scanf("%ZX\n",d_q);
    gmp_scanf("%ZX\n",i_p);
    gmp_scanf("%ZX\n",i_q);
    gmp_scanf("%ZX\n",c);
    rsa_sk_set(rsa_sk, N, d, p, q, d_p, d_q, i_p, i_q);
    rsa_decrypt(m, rsa_sk, c);
    gmp_printf("%ZX\n",m);
  }

  mpz_clears(N,d,p,q,d_p,d_q,i_p,i_q,m,c,NULL);
  rsa_sk_clear(rsa_sk);

}

/*
Perform stage 3:

- read each 5-tuple of p, q, g, h and m from stdin,
- compute the ElGamal encryption c = (c_1,c_2), then
- write the ciphertext c to stdout.
*/

void stage3(char test) {

  mpz_t p, q, g, h, m, c1, c2;
  mpz_t test_r;
  mpz_init_set_ui( test_r, 1 );
  elg_key_t elg_pk;
  mpz_inits(p, q, g, h, m, c1, c2, NULL);
  elg_key_init(elg_pk);

  while(1) {
    if (gmp_scanf("%ZX\n",p) == EOF) break;
    gmp_scanf("%ZX\n",q);
    gmp_scanf("%ZX\n",g);
    gmp_scanf("%ZX\n",h);
    gmp_scanf("%ZX\n",m);
    elg_key_set(elg_pk, p, q, g, h);
    if ( test )
      elg_encrypt2(c1, c2, elg_pk, m, test_r);
    else
      elg_encrypt(c1, c2, elg_pk, m);
    gmp_printf("%ZX\n%ZX\n",c1,c2);
  }

  mpz_clears(p, q, g, h, m, c1, c2, test_r, NULL);
  elg_key_clear(elg_pk);

}

/*
Perform stage 4:

- read each 5-tuple of p, q, g, x and c = (c_1,c_2) from stdin,
- compute the ElGamal decryption m, then
- write the plaintext m to stdout.
*/

void stage4() {

  mpz_t p, q, g, x, m, c1, c2;
  elg_key_t elg_sk;
  mpz_inits(p, q, g, x, m, c1, c2, NULL);
  elg_key_init(elg_sk);

  while(1) {
    if (gmp_scanf("%ZX\n",p) == EOF) break;
    gmp_scanf("%ZX\n",q);
    gmp_scanf("%ZX\n",g);
    gmp_scanf("%ZX\n",x);
    gmp_scanf("%ZX\n",c1);
    gmp_scanf("%ZX\n",c2);
    elg_key_set(elg_sk, p, q, g, x);
    elg_decrypt(m, elg_sk, c1, c2);
    gmp_printf("%ZX\n",m);
  }

  mpz_clears(p, q, g, x, m, c1, c2, NULL);
  elg_key_clear(elg_sk);

}

/*
The main function acts as a driver for the assignment by simply invoking
the correct function for the requested stage.
*/

int main( int argc, char* argv[] ) {

  if( 3 != argc && 2 != argc) {
    abort();
  }

  if     ( !strcmp( argv[ 1 ], "stage1" ) ) {
    stage1();
  }
  else if( !strcmp( argv[ 1 ], "stage2" ) ) {
    stage2();
  }
  else if( !strcmp( argv[ 1 ], "stage3" ) ) {
    if ( !strcmp( argv[argc-1], "testing" ) ) {
      stage3(1);
    }
    else {
      stage3(0);
    }
  }
  else if( !strcmp( argv[ 1 ], "stage4" ) ) {
    stage4();
  }
  else {
    abort();
  }

  return 0;
}
