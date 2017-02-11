#include "crypto.h"
#include "sha256.h"

static inline size_t get_hex_line(unsigned char *buff, size_t buff_size) {
  size_t counter = 0;
  char *res = fgets((char*)buff, buff_size, stdin);
  while(res) {
    if(*res <= '9' && *res >= '0') {
      *res = *res - '0';
      counter++;
      res++;
    }
    else if(*res <= 'F' && *res >= 'A') {
      *res = *res - 'A' + 10;
      counter++;
      res++;
    }
    else if(*res <= 'f' && *res >= 'a') {
      *res = *res - 'a' + 10;
      counter++;
      res++;
    }
    else {
      *res = '\0';
      return counter;
    }
  }
  return counter;
}

static inline int mpn_lop( const mp_limb_t* x, int l_x ) {
  while( ( l_x > 1 ) && ( x[ l_x - 1 ] == 0 ) ) {
    l_x--;
  }
  return l_x;
}

int umpz_init_hex_stdin(mpz_t op) {
  unsigned char buff[1024];
  buff[0]='\0';
  int len = get_hex_line(buff, 1024);
  return umpz_init_hex(op, buff, len);
}

int umpz_init_hex(mpz_t op, const unsigned char* str, const int length) {
  unsigned int bits = length * 4 + BITS_PER_LIMB; //Because it's hex + one extra limb
  if((op->_mp_alloc*BITS_PER_LIMB) < bits)
    mpz_realloc2(op, bits);
  memset(op->_mp_d, 0, bits>>3);
  int r=0;
  if(length > 0) {
    mpn_set_str(op->_mp_d, str, length, 16);
    r=1;
  }
  op->_mp_size = mpn_lop( op->_mp_d, 1+length/(sizeof(mp_limb_t)<<1) );
  //gmp_printf("%ZX\n",op);
  return r;
}

void umpz_mul(mpz_t out, const mpz_t a, const mpz_t b) {
  mp_limb_t *temp = out->_mp_d;
  int total_limbs = a->_mp_size + b->_mp_size;
  if(total_limbs > out->_mp_alloc) {
    mpz_realloc2(out, total_limbs * BITS_PER_LIMB);
    temp = out->_mp_d;
  }
  if(a->_mp_d == out->_mp_d || b->_mp_d == out->_mp_d) {
    temp = (mp_limb_t*)malloc(sizeof(mp_limb_t) * total_limbs);
  }
  if(umpz_cmp(a,b) >= 0) {
    mpn_mul(temp, a->_mp_d, a->_mp_size, b->_mp_d, b->_mp_size);
  }
  else {
    mpn_mul(temp, b->_mp_d, b->_mp_size, a->_mp_d, a->_mp_size);
  }
  out->_mp_size = mpn_lop(temp, total_limbs);
  if( temp != out->_mp_d ) {
    memcpy(out->_mp_d, temp, out->_mp_size * sizeof(mp_limb_t));
    free(temp);
  }
}

void umpz_mul_ui(mpz_t out, const mpz_t a, const mp_limb_t b) {
  int total_limbs = a->_mp_size + 1;
  if(total_limbs > out->_mp_alloc) {
    mpz_realloc2(out, total_limbs * BITS_PER_LIMB);
  }
  mp_limb_t carry = mpn_mul_1(out->_mp_d, a->_mp_d, a->_mp_size, b);
  out->_mp_d[total_limbs - 1] = carry;
  out->_mp_size = mpn_lop(out->_mp_d, total_limbs);
}

void umpz_add(mpz_t out, const mpz_t a, const mpz_t b) {
  int total_limbs;
  if(umpz_cmp(a, b) >= 0) {
    total_limbs = a->_mp_size + 1;
    if(total_limbs > out->_mp_alloc) {
      mpz_realloc2(out, total_limbs * BITS_PER_LIMB);
    }
    out->_mp_d[total_limbs - 1] = mpn_add(out->_mp_d, a->_mp_d, a->_mp_size,
                                                      b->_mp_d, b->_mp_size);

  }
  else {
    total_limbs = b->_mp_size + 1;
    if(total_limbs > out->_mp_alloc) {
      mpz_realloc2(out, total_limbs * BITS_PER_LIMB);
    }
    out->_mp_d[total_limbs - 1] = mpn_add(out->_mp_d, b->_mp_d, b->_mp_size,
                                                      a->_mp_d, a->_mp_size);
  }
  out->_mp_size = mpn_lop( out->_mp_d, total_limbs);
}

//void umpz_add_ui(mpz_t out, const mpz_t a, const mpz_t b) {}

void umpz_sub(mpz_t out, const mpz_t a, const mpz_t b) {
  int total_limbs = a->_mp_size;
  if(total_limbs > out->_mp_alloc) {
    mpz_realloc2(out, total_limbs * BITS_PER_LIMB);
  }
  mpn_sub(out->_mp_d, a->_mp_d, a->_mp_size, b->_mp_d, b->_mp_size);
  out->_mp_size = mpn_lop( out->_mp_d, total_limbs );
}

//void umpz_sub_ui(mpz_t out, const mpz_t a, const mpz_t b) {}

void umpz_addmul_ui(mpz_t out, const mpz_t a, mp_limb_t b) {

  int total_limbs = (a->_mp_size > out->_mp_size) ? (a->_mp_size) : (out->_mp_size);
  total_limbs++;
  if(total_limbs > out->_mp_alloc) {
    mpz_realloc2(out, total_limbs * BITS_PER_LIMB);
  }
  if(out->_mp_size < a->_mp_size) {
    memset(&out->_mp_d[out->_mp_size], 0, sizeof(mp_limb_t)*(a->_mp_size - out->_mp_size));
  }
  mp_limb_t carry = mpn_addmul_1(out->_mp_d, a->_mp_d, a->_mp_size, b);
  if(out->_mp_size <= a->_mp_size) {
    out->_mp_d[a->_mp_size] = carry;
  }
  else {
    carry = mpn_add_1(&out->_mp_d[a->_mp_size], &out->_mp_d[a->_mp_size],
                       out->_mp_size - a->_mp_size, carry);
    out->_mp_d[out->_mp_size] = carry;
  }
  out->_mp_size = mpn_lop(out->_mp_d, total_limbs);

}

void umpzn_limbrshift(mpz_t out, const mpz_t a, int i) {
  int total_limbs = a->_mp_size - i;

  if(total_limbs <= 0) {
    out->_mp_d[0] = 0;
    out->_mp_size = 1;
  }
  else {
    if(total_limbs > out->_mp_alloc) {
      mpz_realloc2(out, total_limbs * BITS_PER_LIMB);
    }
    for(int k=i;k<a->_mp_size;k++) {
      out->_mp_d[k-i] = a->_mp_d[k];
    }
    out->_mp_size = total_limbs;
  }

}

void umpzn_limblshift(mpz_t out, const mpz_t a, int i) {
  int total_limbs = a->_mp_size + i;
  if(total_limbs > out->_mp_alloc) {
    mpz_realloc2(out, total_limbs * BITS_PER_LIMB);
  }
  for(int k=a->_mp_size-1;k>=0;k--) {
    out->_mp_d[k+i] = a->_mp_d[k];
  }
  for(int k=0;k<i;k++) {
    out->_mp_d[k] = 0;
  }
  out->_mp_size = total_limbs;
}

int umpz_cmp(const mpz_t a, const mpz_t b) {
  if(a->_mp_size>b->_mp_size) {
    return 1;
  }
  else if(a->_mp_size<b->_mp_size) {
    return -1;
  }
  else {
    return mpn_cmp(a->_mp_d,b->_mp_d,a->_mp_size);
  }
}

void mont_init(zn_mont_t out, const mpz_t N) {
  mpz_init_set(out->N, N);
  mpz_init_set_ui(out->rho_sqr, 1);
  out->l_n = (out->N)->_mp_size;
  out->w = BITS_PER_LIMB;
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
    umpz_addmul_ui(temp, x, y_i);
    umpz_addmul_ui(temp, mont->N, u);
    umpzn_limbrshift(temp, temp, 1);
  }
  if (umpz_cmp(temp, mont->N) > 0) {
    umpz_sub(temp, temp, mont->N);
  }

  mpz_set(out, temp);
  mpz_clear(temp);
}

void mont_mul_ui(mpz_t out, const mpz_t x, const mp_limb_t y, const zn_mont_t mont) {
  mp_limb_t u;
  mpz_t temp;
  mpz_init( temp );

  mp_limb_t temp_0 = mpz_getlimbn(temp, 0);
  mp_limb_t x_0 = mpz_getlimbn(x, 0);

  u = (temp_0 + y * x_0) * mont->omega;
  umpz_mul_ui(temp, x, y);
  umpz_addmul_ui(temp, mont->N, u);
  umpzn_limbrshift(temp, temp, 1);
  for(int i = 1; i < mont->l_n; i++) {
    temp_0 = mpz_getlimbn(temp, 0);
    x_0 = mpz_getlimbn(x, 0);
    u = temp_0 * mont->omega;
    umpz_addmul_ui(temp, mont->N, u);
    umpzn_limbrshift(temp, temp, 1);
  }
  if (umpz_cmp(temp, mont->N) >= 0) {
    umpz_sub(temp, temp, mont->N);
  }

  mpz_set(out, temp);
  mpz_clear(temp);
}

void mont_red(mpz_t out, const mpz_t t, const zn_mont_t mont) {
  mp_limb_t u;
  mpz_t temp, temp2;
  mpz_init_set( temp, t );
  mpz_init_set( temp2, mont->N );

  for(int i = 0; i < mont->l_n; i++) {
    mp_limb_t temp_i = mpz_getlimbn(temp, i);
    u = temp_i * mont->omega;
    umpz_addmul_ui(temp, temp2, u);
    umpzn_limblshift( temp2, temp2, 1);
  }
  umpzn_limbrshift( temp, temp, mont->l_n );
  if (umpz_cmp(temp, mont->N) >= 0) {
    umpz_sub(temp, temp, mont->N);
  }
  mpz_set(out, temp);
  mpz_clears(temp, temp2, NULL);
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
  umpz_add(out,a,b);
  if(umpz_cmp(out,N) >= 0) {
    umpz_sub(out, out, N);
  }
}

void mpzn_sub(mpz_t out, const mpz_t a, const mpz_t b, const mpz_t N) {

  if(umpz_cmp(b,a) > 0) {
    umpz_sub(out, b, a);
    umpz_sub(out, N, out);
  }
  else {
    umpz_sub(out, a, b);
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

int _rdrand64_step(uint64_t *r) {
  unsigned char success;

  asm( "rdrand %0 ; setc %1"
       : "=r" (*r), "=qm" (success) );

  return (int) success;
}

uint64_t _rdrand64_retry() {
  uint64_t r;
  while(1) {
    if( _rdrand64_step( &r ) ) {
      return r;
    }
  }
  return 0;
}

void rdrand_get_n_bytes( unsigned int n, unsigned char *dest ) {
  uint32_t i;
  for(i=0;i<n;i+=8) {
    uint64_t rand64 = _rdrand64_retry();
    unsigned char* bytes = (unsigned char*)&rand64;
    for(uint j=0;j<8 && j<n;j++) {
      dest[i+j] = bytes[j];
    }
  }
}

void seed_state(gmp_randstate_t state) {
  unsigned char rand_data[32];
  unsigned char hash[32];
  SHA256_CTX ctx;
  sha256_init(&ctx);

  rdrand_get_n_bytes(32, rand_data);
  sha256_update(&ctx, rand_data, 32);

  FILE* file = fopen("/dev/urandom", "r");

  fread(rand_data, 32, sizeof(unsigned char), file);
  fclose(file);
  sha256_update(&ctx, rand_data, 32);

  sha256_final(&ctx, hash);

  mpz_t seed;
  mpz_init2(seed, 256);
  mpz_import(seed, 32, 1, sizeof(hash[0]), 0, 0, hash);
  gmp_randseed(state, seed);
  mpz_clear(seed);
  //gmp_randclear(state);

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
  mpz_t ipm, iqm, pm, qm;
  mpz_inits(b, cq, cp, ipm, iqm, pm, qm, NULL);
  mont_init( zN, rsa_sk->N );
  mont_init( zq, rsa_sk->q );
  mont_init( zp, rsa_sk->p );

  mpzn_mod2(cp, c, zp);
  mpzn_pow2(cp, cp, rsa_sk->d_p, zp);

  mont_mul(cp, cp, zN->rho_sqr, zN);
  mont_mul(pm, rsa_sk->p, zN->rho_sqr, zN);
  mont_mul(ipm, rsa_sk->i_p, zN->rho_sqr, zN);

  mpzn_mod2(cq, c, zq);
  mpzn_pow2(cq, cq, rsa_sk->d_q, zq);

  mont_mul(cq, cq, zN->rho_sqr, zN);
  mont_mul(qm, rsa_sk->q, zN->rho_sqr, zN);
  mont_mul(iqm, rsa_sk->i_q, zN->rho_sqr, zN);

  mont_mul(b, pm, ipm, zN);
  mont_mul(cq, cq, b, zN);

  mont_mul(b, qm, iqm, zN);
  mont_mul(cp, cp, b, zN);

  mpzn_add(m, cq, cp, rsa_sk->N);

  mont_mul_ui(m, m, 1, zN);

  mont_clear( zN );
  mont_clear( zq );
  mont_clear( zp );
  mpz_clears(b, cq, cp, ipm, iqm, pm, qm, NULL);
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
  umpz_sub(elg_key->i_x, q, key);
}

void elg_encrypt(mpz_t c1, mpz_t c2, const elg_key_t elg_pk, const mpz_t m, gmp_randstate_t state) {
  mpz_t r;
  mpz_init2( r, 256 );

  mpz_urandomm(r, state, elg_pk->q);
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
