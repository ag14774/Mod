#ifndef __CRYPTO_H
#define __CRYPTO_H

#include  <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

#include <string.h>
#include    <gmp.h>

#define WINDOW_SIZE 4
#define TABLE_SIZE (1<<(WINDOW_SIZE-1)) /*Half the size. Only odd numbers*/

int mpzn_extract_bits(const mpz_t in, int start, int end);
void mpzn_add(mpz_t out, const mpz_t a, const mpz_t b, const mpz_t N);
void mpzn_sub(mpz_t out, const mpz_t a, const mpz_t b, const mpz_t N);
void mpzn_mul(mpz_t out, const mpz_t a, const mpz_t b, const mpz_t N);
void mpzn_pow(mpz_t out, const mpz_t b, const mpz_t e, const mpz_t N);

/*********************************************/

typedef struct {
  mpz_t N;
  mpz_t e;
} __rsa_pk_struct;

typedef struct {
  mpz_t N;
  mpz_t d;
  mpz_t p;
  mpz_t q;
  mpz_t d_p;
  mpz_t d_q;
  mpz_t i_p;
  mpz_t i_q;
} __rsa_sk_struct;

typedef __rsa_pk_struct rsa_pk_t[1];
typedef __rsa_sk_struct rsa_sk_t[1];

void rsa_pk_init(rsa_pk_t rsa_pk);
void rsa_sk_init(rsa_sk_t rsa_sk);
void rsa_pk_init2(rsa_pk_t rsa_pk, mp_bitcnt_t n);
void rsa_sk_init2(rsa_sk_t rsa_sk, mp_bitcnt_t n);
void rsa_pk_clear(rsa_pk_t rsa_pk);
void rsa_sk_clear(rsa_sk_t rsa_sk);
void rsa_pk_set(rsa_pk_t rsa_pk, const mpz_t N, const mpz_t e);
void rsa_sk_set(rsa_sk_t rsa_sk, const mpz_t N, const mpz_t d, const mpz_t p,
                const mpz_t q, const mpz_t d_p, const mpz_t d_q,
                const mpz_t i_p, const mpz_t i_q);
void rsa_encrypt(mpz_t c, const rsa_pk_t rsa_pk, const mpz_t m);
void rsa_decrypt(mpz_t m, const rsa_sk_t rsa_sk, const mpz_t c);

/********************ElGamal********************/

typedef struct {
  mpz_t p;
  mpz_t q;
  mpz_t g;
  mpz_t key;
  mpz_t i_x;
} __elg_key_struct;

typedef __elg_key_struct elg_key_t[1];

void elg_key_init(elg_key_t elg_key);
void elg_key_init2(elg_key_t elg_key, mp_bitcnt_t n);
void elg_key_clear(elg_key_t elg_key);
void elg_key_set(elg_key_t elg_key, const mpz_t p, const mpz_t q,
                                    const mpz_t g, const mpz_t key);
void elg_encrypt(mpz_t c1, mpz_t c2, const elg_key_t elg_pk, const mpz_t m);
void elg_encrypt2(mpz_t c1, mpz_t c2, const elg_key_t elg_pk, const mpz_t m, const mpz_t r);
void elg_decrypt(mpz_t m, const elg_key_t elg_sk, const mpz_t c1, const mpz_t c2);

#endif
