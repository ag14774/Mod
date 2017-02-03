#include "crypto.h"

void rsa_pk_init(rsa_pk_t rsa_pk) {
  mpz_inits(rsa_pk->N, rsa_pk->e, NULL);
}

void rsa_sk_init(rsa_sk_t rsa_sk) {
  mpz_inits(rsa_sk->N, rsa_sk->d, rsa_sk->p, rsa_sk->q, rsa_sk->d_p,
            rsa_sk->d_q, rsa_sk->i_p, rsa_sk->i_q, NULL);
}

void rsa_pk_init2(rsa_pk_t rsa_pk, mp_bitcnt_t n) {
  printf("Not yet implemented!\n");
}

void rsa_sk_init2(rsa_sk_t rsa_sk, mp_bitcnt_t n) {
  printf("Not yet implemented!\n");
}

void rsa_pk_clear(rsa_pk_t rsa_pk) {
  mpz_clears(rsa_pk->N, rsa_pk->e, NULL);
}

void rsa_sk_clear(rsa_sk_t rsa_sk) {
  mpz_clears(rsa_sk->N, rsa_sk->d, rsa_sk->p, rsa_sk->q, rsa_sk->d_p,
            rsa_sk->d_q, rsa_sk->i_p, rsa_sk->i_q, NULL);

}

void rsa_pk_set(rsa_pk_t rsa_pk, const mpz_t N, const mpz_t e) {
  mpz_set(rsa_pk->N, N);
  mpz_set(rsa_pk->e, e);
}

void rsa_sk_set(rsa_sk_t rsa_sk, const mpz_t N, const mpz_t d, const mpz_t p,
                const mpz_t q, const mpz_t d_p, const mpz_t d_q,
                const mpz_t i_p, const mpz_t i_q) {
  mpz_set(rsa_sk->N, N);
  mpz_set(rsa_sk->d, d);
  mpz_set(rsa_sk->p, p);
  mpz_set(rsa_sk->q, q);
  mpz_set(rsa_sk->d_p, d_p);
  mpz_set(rsa_sk->d_q, d_q);
  mpz_set(rsa_sk->i_p, i_p);
  mpz_set(rsa_sk->i_q, i_q);
}

void rsa_encrypt(mpz_t c, const rsa_pk_t rsa_pk, const mpz_t m) {
  mpz_powm(c, m, rsa_pk->e, rsa_pk->N);
}

void rsa_decrypt(mpz_t m, const rsa_sk_t rsa_sk, const mpz_t c) {
  mpz_t a,b;
  mpz_inits(a, b, NULL);

  mpz_powm(a, c, rsa_sk->d_q, rsa_sk->q);
  mpz_mul(b, rsa_sk->p, rsa_sk->i_p);
  mpz_mod(b, b, rsa_sk->N);
  mpz_mul(m, a, b);

  mpz_mod(m, m, rsa_sk->N);

  mpz_powm(a, c, rsa_sk->d_p, rsa_sk->p);
  mpz_mul(b, rsa_sk->q, rsa_sk->i_q);
  mpz_mod(b, b, rsa_sk->N);
  mpz_addmul(m, a, b);

  mpz_mod(m, m, rsa_sk->N);

  mpz_clears(a, b, NULL);
}

void elg_key_init(elg_key_t elg_key) {
  mpz_inits(elg_key->p, elg_key->q, elg_key->g, elg_key->key, elg_key->i_x, NULL);
}

void elg_key_init2(elg_key_t elg_key, mp_bitcnt_t n) {
  printf("Not yet implemented!\n");
}

void elg_key_clear(elg_key_t elg_key) {
  mpz_clears(elg_key->p, elg_key->q, elg_key->g, elg_key->key, NULL);
}

void elg_key_set(elg_key_t elg_key, const mpz_t p, const mpz_t q,
                                    const mpz_t g, const mpz_t key) {
  mpz_set(elg_key->p, p);
  mpz_set(elg_key->q, q);
  mpz_set(elg_key->g, g);
  mpz_set(elg_key->key, key);
  mpz_sub(elg_key->i_x, q, key);
}

void elg_encrypt(mpz_t c1, mpz_t c2, const elg_key_t elg_pk, const mpz_t m) {
  mpz_t r;
  mpz_init( r );

  // generate randomness
  elg_encrypt2(c1, c2, elg_pk, m, r);

  mpz_clear( r );
}

void elg_encrypt2(mpz_t c1, mpz_t c2, const elg_key_t elg_pk, const mpz_t m, const mpz_t r) {
  mpz_t rq;
  mpz_init( rq );

  mpz_mod(rq, r, elg_pk->q);
  mpz_powm(c1, elg_pk->g, rq, elg_pk->p);
  mpz_powm(c2, elg_pk->key, rq, elg_pk->p);
  mpz_mul(c2, c2, m);
  mpz_mod(c2, c2, elg_pk->p);

  mpz_clear( rq );
}

void elg_decrypt(mpz_t m, const elg_key_t elg_sk, const mpz_t c1, const mpz_t c2) {
  mpz_t c1_i_x;
  mpz_init( c1_i_x );

  mpz_powm(c1_i_x, c1, elg_sk->i_x, elg_sk->p);
  mpz_mul(m, c2, c1_i_x);
  mpz_mod(m, m, elg_sk->p);

  mpz_clear( c1_i_x );
}
