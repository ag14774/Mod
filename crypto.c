#include "crypto.h"

void mont_init(zn_mont_t out, const mpz_t N) {
  mpz_init_set(out->N, N);
  mpz_init_set_ui(out->rho_sqr, 1);
  out->l_n = (out->N)->_mp_size;
  out->w = sizeof(mp_limb_t)*8;
  out->omega = 1;
  for(int i = 0; i < (out->w-1); i++) {
    out->omega = out->omega * out->omega * (out->N)->_mp_d[0];
  }
  out->omega = ~(out->omega-1);
  for(int i = 0; i < (2*out->l_n*out->w); i++) {
    mpzn_add(out->rho_sqr, out->rho_sqr, out->rho_sqr, out->N);
  }
}

void mont_clear(zn_mont_t in) {
  mpz_clear(in->N);
  mpz_clear(in->rho_sqr);
}

void mont_mul(mpz_t out, const mpz_t x, const mpz_t y, const zn_mont_t mont) {
  mp_limb_t u;
  mpz_t temp;
  mpz_init_set_ui( temp, 0 );

  for(int i = 0; i < mont->l_n; i++) {
    mp_limb_t y_i = mpz_getlimbn(y, i);
    mp_limb_t temp_0 = mpz_getlimbn(temp, 0);
    mp_limb_t x_0 = mpz_getlimbn(x, 0);
    u = (temp_0 + y_i * x_0) * mont->omega;
    mpz_addmul_ui(temp, x, y_i);
    mpz_addmul_ui(temp, mont->N, u);
    mpz_tdiv_q_2exp(temp, temp, mont->w);
    //mpz_divexact_ui(temp, temp, 1<<mont->w);
  }
  if (mpz_cmp(temp, mont->N) > 0) {
    mpz_sub(temp, temp, mont->N);
  }

  mpz_set(out, temp);
  mpz_clear(temp);
}

void mont_mul_ui(mpz_t out, const mpz_t x, const mp_limb_t y, const zn_mont_t mont) {
  mp_limb_t u;
  mpz_t temp;
  mpz_init_set_ui( temp, 0 );

  mp_limb_t temp_0 = mpz_getlimbn(temp, 0);
  mp_limb_t x_0 = mpz_getlimbn(x, 0);

  u = (temp_0 + y * x_0) * mont->omega;
  mpz_addmul_ui(temp, x, y);
  mpz_addmul_ui(temp, mont->N, u);
  mpz_tdiv_q_2exp(temp, temp, mont->w);
  for(int i = 1; i < mont->l_n; i++) {
    temp_0 = mpz_getlimbn(temp, 0);
    x_0 = mpz_getlimbn(x, 0);
    u = temp_0 * mont->omega;
    mpz_addmul_ui(temp, mont->N, u);
    mpz_tdiv_q_2exp(temp, temp, mont->w);
    //mpz_divexact_ui(temp, temp, 1<<mont->w);
  }
  if (mpz_cmp(temp, mont->N) >= 0) {
    mpz_sub(temp, temp, mont->N);
  }

  mpz_set(out, temp);
  mpz_clear(temp);
}

void mont_red(mpz_t out, const mpz_t t, const zn_mont_t mont) {
  mp_limb_t u;
  mpz_t temp, temp2, base_i, base;
  mpz_init_set( temp, t );
  mpz_init( temp2 );
  mpz_init_set_ui( base, 1);
  mpz_init_set_ui( base_i, 1);
  mpz_mul_2exp(base, base, mont->w);

  for(int i = 0; i < mont->l_n; i++) {
    mp_limb_t temp_i = mpz_getlimbn(temp, i);
    u = temp_i * mont->omega;
    mpz_mul( temp2, mont->N, base_i);
    mpz_addmul_ui(temp, temp2, u);
    mpz_mul( base_i, base_i, base );
  }
  mpz_divexact( temp, temp, base_i );
  if (mpz_cmp(temp, mont->N) >= 0) {
    mpz_sub(temp, temp, mont->N);
  }
  mpz_set(out, temp);
  mpz_clears(temp, temp2, base_i, base, NULL);
}

void mont_pow(mpz_t out, const mpz_t b, const mpz_t e, const zn_mont_t mont) {
  mpz_t table[TABLE_SIZE];
  mpz_t temp;
  int32_t i; //bit index
  int32_t l; //end of window index
  int32_t u; //window in decimal

  mpz_init(temp);
  mpz_init_set(table[0], b);
  mont_mul(temp, b, b, mont); //make sure it is okay to call with same args

  /*Precompute table*/
  for(int k=1;k<TABLE_SIZE;k++) {
    mpz_init(table[k]);
    mont_mul(table[k], table[k-1], temp, mont);
  }

  mpz_set_ui(temp, 1);
  mont_mul(temp, temp, mont->rho_sqr, mont);
  i = mpz_sizeinbase(e, 2) - 1;

  while(i >= 0) {

    char bit = mpz_tstbit(e, i);
    if(!bit) {
      l = i;
      u = 0;
    }
    else {
      l = i - WINDOW_SIZE + 1;
      l = l&~(l>>31); //max(l,0)
      while (!mpz_tstbit(e, l)) l++;
      u = mpzn_extract_bits(e, i, l);
    }

    for(int k=0;k<i-l+1;k++) {
      mont_mul(temp,temp,temp,mont); //make sure it is okay to call with same args
    }

    if(u != 0) {
      mont_mul(temp, temp, table[(u-1)/2], mont);
    }

    i = l - 1;
  }
  mpz_set(out, temp);

  mpz_clear(temp);
  for(int k=0;k<TABLE_SIZE;k++) mpz_clear(table[k]);
}

/*start from left to right so start>end*/
int mpzn_extract_bits(const mpz_t in, int start, int end) {
  int r = 0;
  for(int i=start;i>=end;i--) {
    r <<= 1;
    r += mpz_tstbit(in,i);
  }
  return r;
}

void mpzn_add(mpz_t out, const mpz_t a, const mpz_t b, const mpz_t N) {
  mpz_add(out,a,b);
  if(mpz_cmp(out,N) >= 0) {
    mpz_sub(out, out, N);
  }
}

void mpzn_sub(mpz_t out, const mpz_t a, const mpz_t b, const mpz_t N) {

  if(mpz_cmp(b,a) > 0) {
    mpz_sub(out, b, a);
    mpz_sub(out, N, out);
  }
  else {
    mpz_sub(out, a, b);
  }

}

void mpzn_mul(mpz_t out, const mpz_t a, const mpz_t b, const mpz_t N) {
  /*a and b must be less that N*/
  zn_mont_t mont;
  mont_init( mont, N );

  mpzn_mul2(out, a, b, mont);

  mont_clear( mont );

}

void mpzn_mul2(mpz_t out, const mpz_t a, const mpz_t b, const zn_mont_t mont) {
  /*a and b must be less that mont->N*/
  mpz_t a_m, b_m;
  mpz_inits(a_m, b_m, NULL);

  mont_mul(a_m, a, mont->rho_sqr, mont);
  mont_mul(b_m, b, mont->rho_sqr, mont);
  mont_mul(out, a_m, b_m, mont);
  mont_mul_ui(out, out, 1, mont);

  mpz_clears(a_m, b_m, NULL);
}

void mpzn_pow(mpz_t out, const mpz_t b, const mpz_t e, const mpz_t N) {

  zn_mont_t mont;
  mont_init( mont, N );

  mpzn_pow2(out, b, e, mont);

  mont_clear( mont );

}

void mpzn_pow2(mpz_t out, const mpz_t b, const mpz_t e, const zn_mont_t mont) {
  /*a and b must be less that mont->N*/
  mpz_t b_m;
  mpz_init(b_m);

  mont_mul(b_m, b, mont->rho_sqr, mont);
  mont_pow(out, b_m, e, mont);
  mont_mul_ui(out, out, 1, mont);

  mpz_clear(b_m);
}

void mpzn_mod(mpz_t out, const mpz_t t, const mpz_t N) {
  zn_mont_t zN;
  mont_init( zN, N );

  mpzn_mod2( out, t, zN );

  mont_clear( zN );
}

void mpzn_mod2(mpz_t out, const mpz_t t, const zn_mont_t mont) {

  mont_red(out, t, mont);
  mont_mul(out, out, mont->rho_sqr, mont);

}

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
  mpzn_pow(c, m, rsa_pk->e, rsa_pk->N);
}

void rsa_decrypt(mpz_t m, const rsa_sk_t rsa_sk, const mpz_t c) {
  zn_mont_t zN, zq, zp;
  mpz_t b, cq, cp;
  mpz_t ipm, iqm, pm, qm, m_p, m_q;
  mpz_inits(b, cq, cp, ipm, iqm, pm, qm, m_p, m_q, NULL);
  mont_init( zN, rsa_sk->N );
  mont_init( zq, rsa_sk->q );
  mont_init( zp, rsa_sk->p );

  mpzn_mod2(cq, c, zq);
  mpzn_mod2(cp, c, zp);

  mpzn_pow2(m_q, cq, rsa_sk->d_q, zq);
  mpzn_pow2(m_p, cp, rsa_sk->d_p, zp);

  mont_mul(m_p, m_p, zN->rho_sqr, zN);
  mont_mul(pm, rsa_sk->p, zN->rho_sqr, zN);
  mont_mul(ipm, rsa_sk->i_p, zN->rho_sqr, zN);

  mont_mul(m_q, m_q, zN->rho_sqr, zN);
  mont_mul(qm, rsa_sk->q, zN->rho_sqr, zN);
  mont_mul(iqm, rsa_sk->i_q, zN->rho_sqr, zN);

  mont_mul(b, pm, ipm, zN);
  mont_mul(m_q, m_q, b, zN);

  mont_mul(b, qm, iqm, zN);
  mont_mul(m_p, m_p, b, zN);

  mpzn_add(m, m_q, m_p, rsa_sk->N);

  mont_mul_ui(m, m, 1, zN);

  mont_clear( zN );
  mont_clear( zq );
  mont_clear( zp );
  mpz_clears(b, cq, cp, ipm, iqm, pm, qm, m_p, m_q, NULL);
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
  zn_mont_t zp;
  mont_init( zp, elg_pk->p);

  mpzn_mod(rq, r, elg_pk->q);
  mpzn_pow2(c1, elg_pk->g, rq, zp);
  mont_mul(c2, elg_pk->key, zp->rho_sqr, zp);
  mont_pow(c2, c2, rq, zp);
  mont_mul(rq, m, zp->rho_sqr, zp);
  mont_mul(c2, c2, rq, zp);
  mont_mul_ui(c2, c2, 1, zp);

  mont_clear( zp );
  mpz_clear( rq );
}

void elg_decrypt(mpz_t m, const elg_key_t elg_sk, const mpz_t c1, const mpz_t c2) {
  mpz_t c1_i_x;
  zn_mont_t zp;
  mpz_init( c1_i_x );
  mont_init( zp, elg_sk->p );

  mont_mul(c1_i_x, c1, zp->rho_sqr, zp);
  mont_mul(m, c2, zp->rho_sqr, zp);
  mont_pow(c1_i_x, c1_i_x, elg_sk->i_x, zp);
  mont_mul(m, m, c1_i_x, zp);
  mont_mul_ui(m, m, 1, zp);

  mont_clear( zp );
  mpz_clear( c1_i_x );
}
