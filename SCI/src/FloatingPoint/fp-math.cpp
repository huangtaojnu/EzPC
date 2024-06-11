/*
Authors: Deevashwer Rathee
Copyright:
Copyright (c) 2021 Microsoft Research
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#include "FloatingPoint/fp-math.h"
#include "FloatingPoint/fp-math-coeffs.h"

using namespace std;
using namespace sci;

#define FRAC_RANGE 9
#define FP_INTMD_M_BITS 27
#define FP_INTMD_E_BITS 8
#define PI_DOUBLE                                                              \
  3.1415926535897932384626433832795028841971693993751058209749445923078164062
#define LOG2E                                                                  \
  1.44269504088896340735992468100189213742664595415298593413544940693110921918118507988552662289350634449699
#define LOGE2                                                                  \
  0.693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418687
#define TWO_INV_SQRT_PI                                                        \
  1.128379167095512573896158903121545171688101258657997713688171443421284936882
#define SQRT2                                                                  \
  1.414213562373095048801688724209698078569671875376948073176679737990732478463
#define SQRT_2_INV_PI 0.7978845608028654 
    //sqrt(2/pi)
#define SQRT2 \
    1.414213562373095048801688724209698078569671875376948073176679737990732478463
#define INV_PI_DOUBLE \
    0.3183098861837906715377675267
#define C1\
    0.044715

  
FixArray get_idx_from_input(FixOp *fix, const FixArray &delta_m,
                            const FixArray &delta_e, int idx_m_bits,
                            int idx_e_bits, int e_offset) {
  assert(delta_m.party != PUBLIC && delta_e.party != PUBLIC);
  assert(delta_m.size == delta_e.size);
  assert(idx_m_bits + idx_e_bits <= delta_e.ell);
  FixArray idx_hi =
      fix->reduce(fix->add(delta_e, e_offset), idx_m_bits + idx_e_bits);
  idx_hi.signed_ = false;
  if (idx_m_bits == 0) {
    return idx_hi;
  }
  idx_hi = fix->mul(idx_hi, 1 << idx_m_bits, idx_m_bits + idx_e_bits);
  FixArray idx_lo = fix->truncate_reduce(delta_m, delta_m.ell - 1 - idx_m_bits);
  idx_lo = fix->sub(idx_lo, 1 << idx_m_bits);
  if (idx_m_bits + idx_e_bits < idx_m_bits + 1) {
    idx_lo = fix->reduce(idx_lo, idx_m_bits + idx_e_bits);
  }
  idx_lo.s = 0;
  BoolArray all_0 = fix->bool_op->input(ALICE, delta_m.size, uint8_t(0));
  FixArray idx = fix->add(
      idx_hi, fix->extend(idx_lo, idx_m_bits + idx_e_bits, all_0.data));
  return idx;
}

FPArray FPMath::tanpi(const FPArray &x) {
  assert(x.party != PUBLIC);
  assert(x.m_bits == 23);
  assert(x.e_bits == 8);
  assert(FP_INTMD_E_BITS == x.e_bits);

  BoolArray x_s, x_z;
  FixArray x_m, x_e;
  tie(x_s, x_z, x_m, x_e) = fp_op->get_components(x);

  BoolArray all_0 = bool_op->input(ALICE, x.size, uint8_t(0));
  BoolArray all_1 = bool_op->input(ALICE, x.size, 1);
  FPArray pos_x = fp_op->input(x.party, x.size, all_0.data, x_z.data,
          x_m.data, x_e.data, x.m_bits, x.e_bits);

  // Range Reduction:
  // Input: [2^-14, 2^23)
  // Output: [2^(-m_bits-REDUCED_RANGE_UB, 2^(-REDUCED_RANGE_UB))]

  // if x >= 2^-FRAC_RANGE
  BoolArray f0 = fix->GE(x_e, -FRAC_RANGE + x.e_bias());
  FixArray shift_amt = fix->add(x_e, FRAC_RANGE - x.e_bias());
  shift_amt.signed_ = false;
  FixArray N__ = fix->left_shift(x_m, shift_amt, x.m_bits + FRAC_RANGE + 1,
              22 + FRAC_RANGE, all_1.data);
  N__.s += FRAC_RANGE;
  FixArray N_ = fix->reduce(N__, FRAC_RANGE + x.m_bits);
  // f1 = N_ >= 2^(FRAC_RANGE + x.m_bits - 1)
  // Using f1 = N < 0 (signed) instead as the ring does not have 1-bit slack
  BoolArray f1 = fix->LT(N_, 0);
  N_ = fix->if_else(f1, fix->sub(1ULL << (FRAC_RANGE + x.m_bits), N_), N_);

  BoolArray f2 = fix->GE(N_, 1ULL << (FRAC_RANGE + x.m_bits - 2));
  N_ = fix->if_else(f2, fix->sub(1ULL << (FRAC_RANGE + x.m_bits - 1), N_), N_);

  FixArray f_m_ = fix->reduce(N_, x.m_bits);
  f_m_.s = x.m_bits;
  BoolArray msb_f_m_ = fix->LT(f_m_, 0);
  uint8_t *wrap_f_m_ = new uint8_t[x.size];
  fix->aux->MSB_to_Wrap(f_m_.data, msb_f_m_.data, wrap_f_m_, x.size, f_m_.ell);
  N_ = fix->truncate_reduce(N_, x.m_bits, wrap_f_m_);
  f_m_ = fix->extend(f_m_, x.m_bits + 1, msb_f_m_.data);

  BoolArray f_m__eq_zero = fix->EQ(f_m_, 0);
  BoolArray N__eq_zero = fix->EQ(N_, 0);

  FixArray f_e__if_if = fix->input(PUBLIC, x.size, uint64_t(0), x_e.signed_, x_e.ell, x_e.s);
  FixArray f_e__if =
      fix->if_else(N__eq_zero, f_e__if_if, -1 * FRAC_RANGE + x.e_bias());
  FixArray N__if = fix->if_else(N__eq_zero, N_, fix->sub(N_, 1));
  FixArray f_m__if = fix->if_else(N__eq_zero, f_m_, 1ULL << x.m_bits);
  BoolArray f_z_ = bool_op->AND(f_m__eq_zero, N__eq_zero);

  FixArray f_m__else = f_m_, N__else = N_;
  FixArray f_e__else = fix->input(PUBLIC, x.size, uint64_t(0), x_e.signed_, x_e.ell, x_e.s);
  fp_op->normalize(f_m__else, f_e__else, x.m_bits + FRAC_RANGE - x.e_bias());

  f_m_ = fix->if_else(f_m__eq_zero, f_m__if, f_m__else);
  FixArray f_e_ = fix->if_else(f_m__eq_zero, f_e__if, f_e__else);
  N_ = fix->if_else(f_m__eq_zero, N__if, N__else);

  // else
  FixArray N = fix->if_else(f0, N_, 0);
  N = fix->reduce(N, FRAC_RANGE - 2);
  FixArray f_m = fix->if_else(f0, f_m_, x_m);
  FixArray f_e = fix->if_else(f0, f_e_, x_e);
  BoolArray f_z = bool_op->if_else(f0, f_z_, x_z);
  BoolArray f_s = bool_op->input(ALICE, x.size, uint8_t(0));
  f1 = bool_op->if_else(f0, f1, 0);
  f2 = bool_op->if_else(f0, f2, 0);
  // increasing precision of f
  f_m = fix->scale_up(f_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);
  FPArray f = fp_op->input(x.party, x.size, f_s.data, f_z.data,
          f_m.data, f_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);

  // Spline Evaluation on f
  BoolArray cond1 = fix->LT(f_e, -14 + f.e_bias());

  // if f < 2^-14, f_tan = pi * f
  FPArray pi = fp_op->input<double>(PUBLIC, x.size, PI_DOUBLE,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  FPArray f_tan_if = fp_op->mul(f, pi, true);

  // else spline evaluation on f
  FixArray idx = get_idx_from_input(fix, f_m, f_e, 2, 3, 14 - x.e_bias());
  vector<FPArray> theta = fp_op->GetCoeffs(tan_coeffs, trig_knots_bits, idx, 20,
                                           FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  FPArray f_tan_else = fp_op->mul(theta[1], f, false);
  f_tan_else = fp_op->mul(f_tan_else, f, false);
  f_tan_else = fp_op->add(f_tan_else, theta[0], true, true, false);
  f_tan_else = fp_op->mul(f_tan_else, f, false);

  FPArray f_tan = fp_op->if_else(cond1, f_tan_if, f_tan_else);

  // Range Propagation
  FPArray N_tan = fp_op->LUT(tan_N, N, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  FPArray sum = fp_op->add(f_tan, N_tan, true, true, false);
  FPArray prod = fp_op->mul(f_tan, N_tan, false);
  // secret-sharing one as fp_op add does not support PUBLIC FPArrays
  FPArray one = fp_op->input<float>(ALICE, x.size, 1.0,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  prod = fp_op->sub(one, prod, true, false, false);

  FPArray num = fp_op->if_else(f2, prod, sum);
  FPArray den = fp_op->if_else(f2, sum, prod);
  FPArray z = fp_op->div(num, den, true, false);

  // Special Cases
  // Case I
  BoolArray cond2 = fix->GE(x_e, 23 + x.e_bias());
  // secret-sharing zero as fp_op if_else does not support PUBLIC FPArrays
  FPArray zero = fp_op->input<double>(ALICE, x.size, 0.0,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  z = fp_op->if_else(cond2, zero, z);

  // Case II
  BoolArray cond3 = fix->LT(x_e, x.e_bias() - 14);
  // increasing precision of x
  FixArray x_m_prec = fix->scale_up(x_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);
  FixArray x_e_prec = x_e;
  FPArray pos_x_prec = fp_op->input(x.party, x.size, all_0.data, x_z.data,
          x_m_prec.data, x_e_prec.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  FPArray pos_x_prec_pi = fp_op->mul(pos_x_prec, pi, true);
  z = fp_op->if_else(cond3, pos_x_prec_pi, z);

  // reduce precision to normal
  BoolArray z_s, z_z;
  FixArray z_m, z_e;
  tie(z_s, z_z, z_m, z_e) = fp_op->get_components(z);
  uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                             (1ULL << (FP_INTMD_M_BITS - x.m_bits - 1));
  BoolArray rnd_no_oflow = fix->LT(z_m, oflow_threshold);
  FixArray ret_m_if = fix->round_ties_to_even(z_m, FP_INTMD_M_BITS - x.m_bits);
  FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << x.m_bits));
  FixArray ret_e = fix->if_else(rnd_no_oflow, z_e, fix->add(z_e, 1));

  BoolArray ret_s = bool_op->XOR(f1, x_s);
  FPArray ret = fp_op->input(x.party, x.size, ret_s.data, z_z.data,
          ret_m.data, ret_e.data, x.m_bits, x.e_bits);

  delete[] wrap_f_m_;

  return ret;
}

FPArray FPMath::exp2(const FPArray &x) {
  assert(x.party != PUBLIC);
  assert(x.m_bits == 23);
  assert(x.e_bits == 8);
  assert(FP_INTMD_E_BITS == x.e_bits);

  BoolArray x_s, x_z;
  FixArray x_m, x_e;
  tie(x_s, x_z, x_m, x_e) = fp_op->get_components(x);

  BoolArray all_0 = bool_op->input(ALICE, x.size, uint8_t(0));
  BoolArray all_1 = bool_op->input(ALICE, x.size, 1);
  FixArray shift_amt = fix->add(x_e, 24 - x.e_bias());
  shift_amt.signed_ = false;
  FixArray m = fix->left_shift(x_m, shift_amt, x.m_bits + 32, 31, all_1.data);
  m.s += 24;
  FixArray f = fix->reduce(m, x.m_bits + 24);
  BoolArray msb_f = fix->LT(f, 0);
  uint8_t *wrap_f = new uint8_t[x.size];
  fix->aux->MSB_to_Wrap(f.data, msb_f.data, wrap_f, x.size, f.ell);
  FixArray N = fix->truncate_reduce(m, x.m_bits + 24, wrap_f);
  N.signed_ = true;
  N = fix->if_else(x_s, fix->mul(N, -1), N);
  f = fix->extend(f, x.m_bits + 25, msb_f.data);

  BoolArray f_eq_0 = fix->EQ(f, 0);
  BoolArray neg_f = bool_op->AND(x_s, bool_op->NOT(f_eq_0));
  f = fix->if_else(neg_f, fix->sub(1ULL << (x.m_bits + 24), f), f);
  N = fix->if_else(neg_f, fix->sub(N, 1), N);
  FixArray delta_m = f;
  FixArray delta_e = fix->input(PUBLIC, x.size, uint64_t(0), x_e.signed_, x_e.ell, x_e.s);
  fp_op->normalize(delta_m, delta_e, x.m_bits + 24 - x.e_bias());
  delta_m = fix->truncate_reduce(delta_m, 24 + x.m_bits - FP_INTMD_M_BITS);
  delta_e = fix->if_else(f_eq_0, 0, delta_e);
  FPArray delta = fp_op->input(x.party, x.size, all_0.data, f_eq_0.data,
          delta_m.data, delta_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);

  // if delta < 2^-14, mu = 1.0
  BoolArray cond = fix->LT(delta_e, -24 + delta.e_bias());
  // secret-sharing one as fp_op else_if does not support PUBLIC FPArrays
  FPArray one = fp_op->input<float>(ALICE, x.size, 1.0,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  FPArray mu_if = one;

  // else evaluate spline
  BoolArray e_lt_neg_6 = fix->LT(delta_e, delta.e_bias() - 6);
  FixArray delta_e_prime =
      fix->if_else(e_lt_neg_6, delta.e_bias() - 7, delta_e);
  FixArray idx =
      get_idx_from_input(fix, delta_m, delta_e_prime, 5, 3, 7 - delta.e_bias());
  vector<FPArray> theta = fp_op->GetCoeffs(
      exp2_coeffs, exp2_knots_bits, idx, 64, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  FPArray mu_else = fp_op->mul(theta[2], delta, false);
  mu_else = fp_op->add(mu_else, theta[1], true, true, false);
  mu_else = fp_op->mul(mu_else, delta, false);
  mu_else = fp_op->add(mu_else, theta[0], true, true, false);
  FPArray mu = fp_op->if_else(cond, mu_if, mu_else);

  BoolArray mu_s, mu_z;
  FixArray mu_m, mu_e;
  tie(mu_s, mu_z, mu_m, mu_e) = fp_op->get_components(mu);
  N = fix->extend(N, x.e_bits + 2);
  FixArray gamma_e = fix->add(mu_e, N);
  uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                             (1ULL << (FP_INTMD_M_BITS - x.m_bits - 1));
  BoolArray rnd_no_oflow = fix->LT(mu_m, oflow_threshold);
  FixArray gamma_m_if =
      fix->round_ties_to_even(mu_m, FP_INTMD_M_BITS - x.m_bits);
  FixArray gamma_m = fix->if_else(rnd_no_oflow, gamma_m_if, (1ULL << x.m_bits));
  gamma_e = fix->if_else(rnd_no_oflow, gamma_e, fix->add(gamma_e, 1));
  FPArray gamma = fp_op->input(x.party, x.size, all_0.data, all_0.data,
          gamma_m.data, gamma_e.data, x.m_bits, x.e_bits);

  // Special Cases
  // Case I
  BoolArray cond1 =
      bool_op->AND(bool_op->NOT(x_s), fix->GE(x_e, 7 + x.e_bias()));
  // secret-sharing inf as fp_op if_else does not support PUBLIC FPArrays
  FPArray inf = fp_op->input<double>(ALICE, x.size, INFINITY, x.m_bits, x.e_bits, false);
  gamma = fp_op->if_else(cond1, inf, gamma);

  // Case II
  BoolArray cond2 = fp_op->LT<double>(x, -126.0);
  // secret-sharing zero as fp_op if_else does not support PUBLIC FPArrays
  FPArray zero = fp_op->input<double>(ALICE, x.size, 0.0, x.m_bits, x.e_bits, false);
  gamma = fp_op->if_else(cond2, zero, gamma);

  // Case III
  BoolArray cond3 = fix->LE(x_e, -25 + x.e_bias());
  // secret-sharing one32 as fp_op if_else does not support PUBLIC FPArrays
  FPArray one32 = fp_op->input<double>(ALICE, x.size, 1.0, x.m_bits, x.e_bits, false);
  gamma = fp_op->if_else(cond3, one32, gamma);

  delete[] wrap_f;

  return gamma;
}

FPArray log_core(FPOp *fp_op, FixOp *fix, BoolOp *bool_op, const FPArray &x,
                 bool base_2 = false) {
  assert(x.party != PUBLIC);
  assert(x.m_bits == 23);
  assert(x.e_bits == 8);
  assert(FP_INTMD_E_BITS == x.e_bits);

  BoolArray x_s, x_z;
  FixArray x_m, x_e;
  tie(x_s, x_z, x_m, x_e) = fp_op->get_components(x);

  BoolArray all_0 = bool_op->input(ALICE, x.size, uint8_t(0));
  BoolArray all_1 = bool_op->input(ALICE, x.size, 1);

  BoolArray a = fix->EQ(x_e, -1 + x.e_bias());
  FixArray f_if = fix->sub(0, x_m);
  FixArray f_else = fix->sub(x_m, 1ULL << x.m_bits);
  FixArray f = fix->if_else(a, f_if, f_else);
  BoolArray f_eq_0 = fix->EQ(f, 0);
  FixArray delta_m = f;
  FixArray delta_e = fix->input(PUBLIC, x.size, uint64_t(0), x_e.signed_, x_e.ell, x_e.s);
  fp_op->normalize(delta_m, delta_e, x.m_bits - x.e_bias());
  FixArray delta_m_low_prec = delta_m;
  delta_m = fix->scale_up(delta_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);
  delta_e = fix->if_else(a, fix->sub(delta_e, 1), delta_e);
  delta_e = fix->if_else(f_eq_0, 0, delta_e);
  FPArray delta = fp_op->input(x.party, x.size, all_0.data, f_eq_0.data,
          delta_m.data, delta_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);

  // if delta < 2^-5
  BoolArray cond1 = fix->LT(delta_e, -5 + delta.e_bias());
  FixArray idx_1 = get_idx_from_input(fix, delta_m_low_prec, delta_e, 0, 5,
                                      24 - delta.e_bias());
  FixArray idx_2 = get_idx_from_input(fix, delta_m_low_prec, delta_e, 4, 3,
                                      5 - delta.e_bias());
  vector<FPArray> theta_1, theta_2;
  if (base_2) {
    theta_1 = fp_op->GetCoeffs(log2_coeffs_1, log_knots_bits_1, idx_1, 19,
                               FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    theta_2 = fp_op->GetCoeffs(log2_coeffs_2, log_knots_bits_2, idx_2, 35,
                               FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  } else {
    theta_1 = fp_op->GetCoeffs(ln_coeffs_1, log_knots_bits_1, idx_1, 19,
                               FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    theta_2 = fp_op->GetCoeffs(ln_coeffs_2, log_knots_bits_2, idx_2, 35,
                               FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  }

  assert(theta_1.size() == theta_2.size());
  assert(theta_1.size() == 8);
  vector<FPArray> theta(theta_1.size());
  for (int i = 0; i < theta_1.size(); i++) {
    theta[i] = fp_op->if_else(cond1, theta_1[i], theta_2[i]);
  }
  for (int i = 0; i < 4; i++) {
    theta[i] = fp_op->if_else(a, theta[i], theta[i + 4]);
  }
  FPArray mu = fp_op->mul(theta[3], delta, false);
  mu = fp_op->add(mu, theta[2], true, true, false);
  mu = fp_op->mul(mu, delta, false);
  mu = fp_op->add(mu, theta[1], true, true, false);
  mu = fp_op->mul(mu, delta, false);
  mu = fp_op->add(mu, theta[0], true, true, false);

  // else (delta == 0, mu = 0.0)
  // secret-sharing zero as fp_op if_else does not support PUBLIC FPArrays
  FPArray zero = fp_op->input<double>(ALICE, x.size, 0.0,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  mu = fp_op->if_else(f_eq_0, zero, mu);

  FixArray N = fix->reduce(x_e, 8);
  FPArray beta;
  if (base_2) {
    beta = fp_op->LUT(log2_int_to_float, N, 6, FP_INTMD_E_BITS);
    for (int i = 0; i < x.size; i++) {
      beta.m[i] <<= (FP_INTMD_M_BITS - 6);
    }
    beta.m_bits = FP_INTMD_M_BITS;
  } else {
    beta = fp_op->LUT(ln_int_to_float, N, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  }
  FPArray neg_mu = fp_op->input(mu.party, mu.size, all_1.data, mu.z,
          mu.m, mu.e, mu.m_bits, mu.e_bits);

  // reduce precision to normal
  FPArray gamma =
      fp_op->if_else(a, neg_mu, fp_op->add(beta, mu, true, true, false));
  BoolArray gamma_s, gamma_z;
  FixArray gamma_m, gamma_e;
  tie(gamma_s, gamma_z, gamma_m, gamma_e) = fp_op->get_components(gamma);
  uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                             (1ULL << (FP_INTMD_M_BITS - x.m_bits - 1));
  BoolArray rnd_no_oflow = fix->LT(gamma_m, oflow_threshold);
  FixArray ret_m_if =
      fix->round_ties_to_even(gamma_m, FP_INTMD_M_BITS - x.m_bits);
  FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << x.m_bits));
  FixArray ret_e = fix->if_else(rnd_no_oflow, gamma_e, fix->add(gamma_e, 1));

  FPArray ret = fp_op->input(x.party, x.size, gamma_s.data, gamma_z.data,
          ret_m.data, ret_e.data, x.m_bits, x.e_bits);

  return ret;
}

FPArray FPMath::log2(const FPArray &x) {
  return log_core(fp_op, fix, bool_op, x, true);
}

FPArray FPMath::ln(const FPArray &x) {
  return log_core(fp_op, fix, bool_op, x, false);
}

// returns mu
FPArray sinpi_core(FPOp *fp_op, FixOp *fix, BoolOp *bool_op, const FPArray &x,
                   const FixArray &m, FPArray &delta, BoolArray &a,
                   bool cos_invocation = false) {
  assert(x.party != PUBLIC && m.party != PUBLIC);
  assert(x.size == m.size);
  BoolArray all_0 = bool_op->input(ALICE, m.size, uint8_t(0));
  BoolArray all_1 = bool_op->input(ALICE, m.size, 1);

  FixArray f = fix->reduce(m, x.m_bits + 14);
  BoolArray msb_f = fix->LT(f, 0);
  uint8_t *wrap_f = new uint8_t[x.size];
  fix->aux->MSB_to_Wrap(f.data, msb_f.data, wrap_f, x.size, f.ell);
  FixArray a_fix = fix->truncate_reduce(m, x.m_bits + 14, wrap_f);
  a = fix->LSB(a_fix);
  f = fix->extend(f, x.m_bits + 15, msb_f.data);

  f = fix->if_else(msb_f, fix->sub(1ULL << (x.m_bits + 14), f), f);

  BoolArray f_eq_0 = fix->EQ(f, 0);
  FixArray delta_m = f;
  FixArray delta_e = fix->input(PUBLIC, x.size, uint64_t(0), true, x.e_bits + 2, 0);
  fp_op->normalize(delta_m, delta_e, x.m_bits + 14 - x.e_bias());
  delta_m = fix->truncate_reduce(delta_m, x.m_bits + 14 - FP_INTMD_M_BITS);
  delta_e = fix->if_else(f_eq_0, 0, delta_e);
  delta = fp_op->input(x.party, x.size, all_0.data, f_eq_0.data,
          delta_m.data, delta_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);

  // if delta < 2^-5
  BoolArray cond1 = fix->LT(delta_e, -5 + delta.e_bias());
  FixArray idx_1 =
      get_idx_from_input(fix, delta_m, delta_e, 0, 4, 14 - delta.e_bias());
  vector<FPArray> theta_1;
  if (cos_invocation) {
    theta_1 = fp_op->GetCoeffs(cos_coeffs_1, sin_knots_bits_1, idx_1, 9,
                               FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  } else {
    theta_1 = fp_op->GetCoeffs(sin_coeffs_1, sin_knots_bits_1, idx_1, 9,
                               FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  }

  // else if delta >= 2^-5
  BoolArray e_eq_neg_1 = fix->EQ(delta_e, delta.e_bias() - 1);
  FixArray idx_2 =
      get_idx_from_input(fix, delta_m, delta_e, 5, 2, 5 - delta.e_bias());
  idx_2 = fix->if_else(e_eq_neg_1, (1ULL << 7) - 1, idx_2);
  vector<FPArray> theta_2;
  if (cos_invocation) {
    theta_2 = fp_op->GetCoeffs(cos_coeffs_2, sin_knots_bits_2, idx_2, 34,
                               FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  } else {
    theta_2 = fp_op->GetCoeffs(sin_coeffs_2, sin_knots_bits_2, idx_2, 34,
                               FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  }
  assert(theta_1.size() == theta_2.size());
  assert(theta_1.size() == 3);
  vector<FPArray> theta(theta_1.size());
  for (int i = 0; i < theta_1.size(); i++) {
    theta[i] = fp_op->if_else(cond1, theta_1[i], theta_2[i]);
  }
  FPArray delta_sq = fp_op->mul(delta, delta, false);
  FPArray mu = fp_op->mul(theta[2], delta_sq, false);
  mu = fp_op->add(mu, theta[1], true, true, false);
  mu = fp_op->mul(mu, delta_sq, false);
  mu = fp_op->add(mu, theta[0], true, true, false);
  mu = fp_op->mul(mu, delta, false);

  delete[] wrap_f;

  return mu;
}

FPArray FPMath::sinpi(const FPArray &x) {
  assert(x.party != PUBLIC);
  assert(x.m_bits == 23);
  assert(x.e_bits == 8);
  assert(FP_INTMD_E_BITS == x.e_bits);

  BoolArray x_s, x_z;
  FixArray x_m, x_e;
  tie(x_s, x_z, x_m, x_e) = fp_op->get_components(x);

  BoolArray all_0 = bool_op->input(ALICE, x.size, uint8_t(0));
  BoolArray all_1 = bool_op->input(ALICE, x.size, 1);
  FixArray shift_amt = fix->add(x_e, 14 - x.e_bias());
  shift_amt.signed_ = false;
  FixArray m = fix->left_shift(x_m, shift_amt, x.m_bits + 14 + 1, 14 + 23, all_1.data);
  m.s += 14;

  BoolArray a;
  FPArray delta;
  FPArray mu = sinpi_core(fp_op, fix, bool_op, x, m, delta, a);

  BoolArray delta_s, delta_z;
  FixArray delta_m, delta_e;
  tie(delta_s, delta_z, delta_m, delta_e) = fp_op->get_components(delta);

  // else (delta < 2^-14, mu = pi * delta) and Special Case (x < 2^-14)
  BoolArray cond2 = fix->LT(delta_e, -14 + delta.e_bias());
  FPArray pi = fp_op->input<double>(PUBLIC, x.size, PI_DOUBLE,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  BoolArray cond3 = fix->LT(x_e, x.e_bias() - 14);
  // higher precision x
  FixArray x_m_prec = fix->scale_up(x_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);
  FixArray x_e_prec = x_e;
  FPArray pos_x_prec = fp_op->input(x.party, x.size, all_0.data, x_z.data,
          x_m_prec.data, x_e_prec.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  FPArray y = fp_op->if_else(cond3, pos_x_prec, delta);
  BoolArray cond_23 = bool_op->if_else(cond3, cond3, cond2);
  mu = fp_op->if_else(cond_23, fp_op->mul(y, pi, true), mu);
  a = bool_op->if_else(cond3, 0, a);

  // Special Cases
  // Case I (Case II already done above)
  BoolArray cond4 = fix->GE(x_e, 23 + x.e_bias());
  // secret-sharing zero as fp_op if_else does not support PUBLIC FPArrays
  FPArray zero = fp_op->input<double>(ALICE, x.size, 0.0,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  FPArray gamma = fp_op->if_else(cond4, zero, mu);

  // reduce precision to normal
  BoolArray gamma_s, gamma_z;
  FixArray gamma_m, gamma_e;
  tie(gamma_s, gamma_z, gamma_m, gamma_e) = fp_op->get_components(gamma);
  uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                             (1ULL << (FP_INTMD_M_BITS - x.m_bits - 1));
  BoolArray rnd_no_oflow = fix->LT(gamma_m, oflow_threshold);
  FixArray ret_m_if =
      fix->round_ties_to_even(gamma_m, FP_INTMD_M_BITS - x.m_bits);
  FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << x.m_bits));
  FixArray ret_e = fix->if_else(rnd_no_oflow, gamma_e, fix->add(gamma_e, 1));
  BoolArray ret_s = bool_op->XOR(a, x_s);

  FPArray ret = fp_op->input(x.party, x.size, ret_s.data, gamma_z.data,
          ret_m.data, ret_e.data, x.m_bits, x.e_bits);

  return ret;
}

FPArray FPMath::cospi(const FPArray &x) {
  assert(x.party != PUBLIC);
  assert(x.m_bits == 23);
  assert(x.e_bits == 8);
  assert(FP_INTMD_E_BITS == x.e_bits);

  BoolArray x_s, x_z;
  FixArray x_m, x_e;
  tie(x_s, x_z, x_m, x_e) = fp_op->get_components(x);

  BoolArray all_0 = bool_op->input(ALICE, x.size, uint8_t(0));
  BoolArray all_1 = bool_op->input(ALICE, x.size, 1);
  FixArray shift_amt = fix->add(x_e, 14 - x.e_bias());
  shift_amt.signed_ = false;
  FixArray m = fix->left_shift(x_m, shift_amt, x.m_bits + 14 + 1, 14 + 23, all_1.data);
  m = fix->add(m, 1ULL << (x.m_bits + 14 - 1));
  m.s += 14;

  BoolArray a;
  FPArray delta;
  FPArray mu = sinpi_core(fp_op, fix, bool_op, x, m, delta, a, true);

  BoolArray delta_s, delta_z;
  FixArray delta_m, delta_e;
  tie(delta_s, delta_z, delta_m, delta_e) = fp_op->get_components(delta);

  // else (delta < 2^-14, mu = pi * delta)
  BoolArray cond2 = fix->LT(delta_e, -14 + delta.e_bias());
  FPArray pi = fp_op->input<double>(PUBLIC, x.size, PI_DOUBLE,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  mu = fp_op->if_else(cond2, fp_op->mul(delta, pi, true), mu);
  for (int i = 0; i < x.size; i++) {
    mu.s[i] = a.data[i];
  }

  // Special Cases
  // secret-sharing one as fp_op add does not support PUBLIC FPArrays
  FPArray one = fp_op->input<float>(ALICE, x.size, 1.0,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);

  // Case I (x >= 2^23)
  BoolArray x_e_eq_23, x_e_gt_23;
  tie(x_e_gt_23, x_e_eq_23) = fix->MSB_and_zero_test(fix->sub(x.e_bias() + 23, x_e));
  BoolArray cond3 = bool_op->XOR(x_e_gt_23, x_e_eq_23);
  FPArray gamma = fp_op->if_else(cond3, one, mu);
  // If x_e == 23 and x_m & 1 == 1: output -1.0
  BoolArray lsb_x_m = fix->LSB(x_m);
  BoolArray case_1_s = bool_op->AND(lsb_x_m, x_e_eq_23);

  // Case II
  BoolArray cond4 = fix->LT(x_e, x.e_bias() - 14);
  gamma = fp_op->if_else(cond4, one, gamma);

  // reduce precision to normal
  BoolArray gamma_s, gamma_z;
  FixArray gamma_m, gamma_e;
  tie(gamma_s, gamma_z, gamma_m, gamma_e) = fp_op->get_components(gamma);
  uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                             (1ULL << (FP_INTMD_M_BITS - x.m_bits - 1));
  BoolArray rnd_no_oflow = fix->LT(gamma_m, oflow_threshold);
  FixArray ret_m_if =
      fix->round_ties_to_even(gamma_m, FP_INTMD_M_BITS - x.m_bits);
  FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << x.m_bits));
  FixArray ret_e = fix->if_else(rnd_no_oflow, gamma_e, fix->add(gamma_e, 1));
  BoolArray ret_s = bool_op->XOR(case_1_s, gamma_s);

  FPArray ret = fp_op->input(x.party, x.size, ret_s.data, gamma_z.data,
          ret_m.data, ret_e.data, x.m_bits, x.e_bits);

  return ret;
}

FPArray FPMath::exp(const FPArray &x) {
  assert(x.party != PUBLIC);
  assert(x.m_bits == 23);
  assert(x.e_bits == 8);
  assert(FP_INTMD_E_BITS == x.e_bits);

  BoolArray x_s, x_z;
  FixArray x_m, x_e;
  tie(x_s, x_z, x_m, x_e) = fp_op->get_components(x);

  BoolArray all_0 = bool_op->input(ALICE, x.size, uint8_t(0));
  BoolArray all_1 = bool_op->input(ALICE, x.size, 1);

  FPArray pos_x = fp_op->input(x.party, x.size, all_0.data, x_z.data,
          x_m.data, x_e.data, x.m_bits, x.e_bits);
  BoolArray pos_x_ge_LOGE2 = fp_op->GE<double>(pos_x, double(LOGE2));
  FixArray shift_amt = fix->add(x_e, 1 - x.e_bias());
  shift_amt.signed_ = false;
  FixArray m = fix->left_shift(x_m, shift_amt, x.m_bits + 10, 9, all_1.data);
  m.s += 1;
  FixArray N = fix->mul(m, uint64_t(LOG2E * (1ULL << FP_INTMD_M_BITS)),
                        x.m_bits + FP_INTMD_M_BITS + 11, all_0.data);
  N.s += FP_INTMD_M_BITS;
  N = fix->round_ties_to_even(N, x.m_bits + 1 + FP_INTMD_M_BITS);

  FixArray f = fix->mul(N, uint64_t(LOGE2 * (1ULL << (FP_INTMD_M_BITS + 7))),
                        FP_INTMD_M_BITS + 8, all_0.data);
  f.s = FP_INTMD_M_BITS + 7;
  f = fix->sub(fix->scale_up(m, FP_INTMD_M_BITS + 8, FP_INTMD_M_BITS + 7), f);
  BoolArray msb_f, zero_f;
  tie(msb_f, zero_f) = fix->MSB_and_zero_test(f);
  BoolArray a = bool_op->XOR(x_s, msb_f);
  f = fix->if_else(msb_f, fix->mul(f, -1), f);
  N = fix->if_else(x_s, fix->mul(N, -1), N);
  N.signed_ = true;

  FixArray delta_m = f;
  FixArray delta_e = fix->input(PUBLIC, x.size, uint64_t(0), x_e.signed_, x_e.ell, x_e.s);
  fp_op->normalize(delta_m, delta_e, FP_INTMD_M_BITS + 7 - x.e_bias());
  delta_m = fix->truncate_reduce(delta_m, 7);
  delta_e = fix->if_else(zero_f, 0, delta_e);
  FPArray delta = fp_op->input(x.party, x.size, all_0.data, zero_f.data,
          delta_m.data, delta_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);

  // if x < LOGE2, a = x_s, N = 0, delta = x
  FixArray x_m_prec = fix->scale_up(x_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);
  FixArray x_e_prec = x_e;
  FPArray pos_x_prec = fp_op->input(x.party, x.size, all_0.data, x_z.data,
          x_m_prec.data, x_e_prec.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  a = bool_op->if_else(pos_x_ge_LOGE2, a, x_s);
  N = fix->if_else(pos_x_ge_LOGE2, N, 0);
  delta = fp_op->if_else(pos_x_ge_LOGE2, delta, pos_x_prec);
  BoolArray delta_s, delta_z;
  tie(delta_s, delta_z, delta_m, delta_e) = fp_op->get_components(delta);

  // if delta < 2^-14, mu = 1.0
  BoolArray cond = fix->LT(delta_e, -24 + delta.e_bias());
  // secret-sharing one as fp_op add does not support PUBLIC FPArrays
  FPArray one = fp_op->input<float>(ALICE, x.size, 1.0,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  FPArray mu_if = one;

  // else evaluate spline
  // if delta < 2^-6
  BoolArray cond1 = fix->LT(delta_e, -6 + delta.e_bias());
  FixArray idx_1 =
      get_idx_from_input(fix, delta_m, delta_e, 0, 5, 24 - delta.e_bias());
  vector<FPArray> theta_1 =
      fp_op->GetCoeffs(exp_coeffs_1, exp_knots_bits_1, idx_1, 18,
                       FP_INTMD_M_BITS, FP_INTMD_E_BITS);

  // else if delta >= 2^-6
  FixArray idx_2 =
      get_idx_from_input(fix, delta_m, delta_e, 5, 3, 6 - delta.e_bias());
  vector<FPArray> theta_2 =
      fp_op->GetCoeffs(exp_coeffs_2, exp_knots_bits_2, idx_2, 44,
                       FP_INTMD_M_BITS, FP_INTMD_E_BITS);

  assert(theta_1.size() == theta_2.size());
  assert(theta_1.size() == 6);
  vector<FPArray> theta(theta_1.size());
  for (int i = 0; i < theta_1.size(); i++) {
    theta[i] = fp_op->if_else(cond1, theta_1[i], theta_2[i]);
  }
  for (int i = 0; i < 3; i++) {
    theta[i] = fp_op->if_else(a, theta[i + 3], theta[i]);
  }
  FPArray mu_else = fp_op->mul(theta[2], delta, false);
  mu_else = fp_op->add(mu_else, theta[1], true, true, false);
  mu_else = fp_op->mul(mu_else, delta, false);
  mu_else = fp_op->add(mu_else, theta[0], true, true, false);
  FPArray mu = fp_op->if_else(cond, mu_if, mu_else);

  BoolArray mu_s, mu_z;
  FixArray mu_m, mu_e;
  tie(mu_s, mu_z, mu_m, mu_e) = fp_op->get_components(mu);
  N = fix->extend(N, x.e_bits + 2);
  FixArray gamma_e = fix->add(mu_e, N);
  uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                             (1ULL << (FP_INTMD_M_BITS - x.m_bits - 1));
  BoolArray rnd_no_oflow = fix->LT(mu_m, oflow_threshold);
  FixArray gamma_m_if =
      fix->round_ties_to_even(mu_m, FP_INTMD_M_BITS - x.m_bits);
  FixArray gamma_m = fix->if_else(rnd_no_oflow, gamma_m_if, (1ULL << x.m_bits));
  gamma_e = fix->if_else(rnd_no_oflow, gamma_e, fix->add(gamma_e, 1));
  FPArray gamma = fp_op->input(x.party, x.size, all_0.data, all_0.data,
          gamma_m.data, gamma_e.data, x.m_bits, x.e_bits);

  // Special Cases
  // Case I
  BoolArray cond2 = fp_op->GE(x, 88.72283172607421875);
  // secret-sharing inf as fp_op if_else does not support PUBLIC FPArrays
  FPArray inf = fp_op->input<double>(ALICE, x.size, INFINITY, x.m_bits, x.e_bits, false);
  gamma = fp_op->if_else(cond2, inf, gamma);

  // Case II
  BoolArray cond3 = fp_op->LT(x, -87.33654022216796875);
  // secret-sharing zero as fp_op if_else does not support PUBLIC FPArrays
  FPArray zero = fp_op->input<double>(ALICE, x.size, 0.0, x.m_bits, x.e_bits, false);
  gamma = fp_op->if_else(cond3, zero, gamma);

  // Case III
  BoolArray cond4 = fix->LE(x_e, -25 + x.e_bias());
  // secret-sharing one32 as fp_op if_else does not support PUBLIC FPArrays
  FPArray one32 = fp_op->input<double>(ALICE, x.size, 1.0, x.m_bits, x.e_bits, false);
  gamma = fp_op->if_else(cond4, one32, gamma);

  return gamma;
}

FPArray FPMath::erf(const FPArray &x) {
  assert(x.party != PUBLIC);
  assert(x.m_bits == 23);
  assert(x.e_bits == 8);
  assert(FP_INTMD_E_BITS == x.e_bits);

  BoolArray x_s, x_z;
  FixArray x_m, x_e;
  tie(x_s, x_z, x_m, x_e) = fp_op->get_components(x);

  BoolArray all_0 = bool_op->input(ALICE, x.size, uint8_t(0));

  FixArray x_m_prec = fix->scale_up(x_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);
  FPArray delta = fp_op->input(x.party, x.size, all_0.data, x_z.data,
          x_m_prec.data, x_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  BoolArray delta_s, delta_z;
  FixArray delta_m, delta_e;
  tie(delta_s, delta_z, delta_m, delta_e) = fp_op->get_components(delta);

  // if delta < 1
  BoolArray cond1 = fix->LT(delta_e, delta.e_bias());
  BoolArray e_lt_neg_5 = fix->LT(delta_e, delta.e_bias() - 5);
  FixArray delta_e_prime =
      fix->if_else(e_lt_neg_5, delta.e_bias() - 6, delta_e);
  FixArray idx_1 =
      get_idx_from_input(fix, delta_m, delta_e_prime, 3, 3, 6 - delta.e_bias());
  vector<FPArray> theta_1;
  theta_1 = fp_op->GetCoeffs(erf_coeffs_1, erf_knots_bits_1, idx_1, 24,
                             FP_INTMD_M_BITS, FP_INTMD_E_BITS);
  // else if delta >= 1
  FixArray idx_2 =
      get_idx_from_input(fix, delta_m, delta_e, 5, 1, -1 * delta.e_bias());
  vector<FPArray> theta_2;
  theta_2 = fp_op->GetCoeffs(erf_coeffs_2, erf_knots_bits_2, idx_2, 46,
                             FP_INTMD_M_BITS, FP_INTMD_E_BITS);

  assert(theta_1.size() == theta_2.size());
  assert(theta_1.size() == 4);
  vector<FPArray> theta(theta_1.size());
  for (int i = 0; i < theta_1.size(); i++) {
    theta[i] = fp_op->if_else(cond1, theta_1[i], theta_2[i]);
  }
  FPArray mu = fp_op->mul(theta[3], delta, false);
  mu = fp_op->add(mu, theta[2], true, true, false);
  mu = fp_op->mul(mu, delta, false);
  mu = fp_op->add(mu, theta[1], true, true, false);
  mu = fp_op->mul(mu, delta, false);
  mu = fp_op->add(mu, theta[0], true, true, false);

  // Special Cases
  // Special Case I (x < 2^-12)
  BoolArray cond2 = fix->LT(x_e, -12 + delta.e_bias());
  FPArray two_inv_sqrt_pi = fp_op->input<double>(PUBLIC, x.size, TWO_INV_SQRT_PI,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  mu = fp_op->if_else(cond2, fp_op->mul(delta, two_inv_sqrt_pi, true), mu);

  // Case I (x >= 3.875)
  FPArray pos_x = fp_op->input(x.party, x.size, all_0.data, x_z.data,
          x_m.data, x_e.data, x.m_bits, x.e_bits);
  BoolArray cond3 = fp_op->GE(pos_x, 3.875);
  // secret-sharing one as fp_op add does not support PUBLIC FPArrays
  FPArray one = fp_op->input<double>(ALICE, x.size, 1.0,
          FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
  FPArray gamma = fp_op->if_else(cond3, one, mu);

  // reduce precision to normal
  BoolArray gamma_s, gamma_z;
  FixArray gamma_m, gamma_e;
  tie(gamma_s, gamma_z, gamma_m, gamma_e) = fp_op->get_components(gamma);
  uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                             (1ULL << (FP_INTMD_M_BITS - x.m_bits - 1));
  BoolArray rnd_no_oflow = fix->LT(gamma_m, oflow_threshold);
  FixArray ret_m_if =
      fix->round_ties_to_even(gamma_m, FP_INTMD_M_BITS - x.m_bits);
  FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << x.m_bits));
  FixArray ret_e = fix->if_else(rnd_no_oflow, gamma_e, fix->add(gamma_e, 1));
  BoolArray ret_s = x_s;

  FPArray ret = fp_op->input(x.party, x.size, ret_s.data, gamma_z.data,
          ret_m.data, ret_e.data, x.m_bits, x.e_bits);

  return ret;
}


FPArray FPMath::sigmoid_fp32(const FPArray &x) {
  assert(x.party != PUBLIC) ;
  assert(x.m_bits == 23) ;
  assert(x.e_bits == 8) ;

  FPArray one_flat = fp_op->input<float>(ALICE, x.size, (float)1.0, x.m_bits, x.e_bits) ;

  return fp_op->div(
    one_flat, 
    fp_op->add(
      one_flat,
      this->exp(fp_op->flip_sign(x))
    )
  ) ;
}

FPArray FPMath::sigmoid_bf16(const FPArray &x) {
  // currently only supports bfloat16
  assert(x.party != PUBLIC);
  assert(x.m_bits == 7);
  assert(x.e_bits == 8);

  BoolArray x_s, x_z;
  FixArray x_m, x_e;
  tie(x_s, x_z, x_m, x_e) = fp_op->get_components(x);
  BoolArray all_0 = bool_op->input(ALICE, x.size, uint8_t(0));

  x_e.signed_ = false;
  // idx = s || (e + 8) mod 2^4 || m - 2^7 = 12 bits
  FixArray idx_hi_s = fix->scale_up(fix->mul(fix->B2A(x_s, false, 5), 1ULL << 4), x.m_bits + 5, x.m_bits);
  // only 4 bits of exponent are needed
  FixArray idx_hi = fix->scale_up(fix->reduce(fix->add(x_e, 8 - x.e_bias()), 5), x.m_bits + 5, x.m_bits);
  FixArray idx_lo = fix->extend(fix->sub(x_m, 1ULL << x.m_bits), x.m_bits + 5);
  FixArray idx = fix->add(idx_hi_s, fix->add(idx_hi, idx_lo));
  // print_fix(idx);

  // all outputs are positive, so ignoring sign bit
  FixArray y_int = fix->LUT(sigmoid_bfloat16, idx, false, 15, x.m_bits);
  FixArray y_m = fix->add(fix->extend(fix->reduce(y_int, x.m_bits), x.m_bits + 1), 1ULL << x.m_bits);
  FixArray y_e = fix->truncate_reduce(y_int, x.m_bits);
  y_e.signed_ = true;
  y_e = fix->extend(y_e, x.e_bits + 2);
  FPArray y = fp_op->input(x.party, x.size, all_0.data, all_0.data,
          y_m.data, y_e.data, x.m_bits, x.e_bits);
  // print_fix(y_int);
  // print_fp(y);
  // print_fp(x);

  FPArray pos_x = fp_op->input(x.party, x.size, all_0.data, x_z.data,
          x_m.data, x_e.data, x.m_bits, x.e_bits);
  BoolArray cond1 = fp_op->LT(pos_x, 93.0);
  BoolArray cond2 = fix->GE(x_e, -8 + x.e_bias());
  FPArray zero_fp = fp_op->input<float>(ALICE, x.size, 0.0, x.m_bits, x.e_bits, false);
  FPArray y_ = fp_op->if_else(x_s, zero_fp, 1.0);

  y = fp_op->if_else(cond1, y, y_);
  y = fp_op->if_else(cond2, y, 0.5);
  return y;
}

FPArray FPMath::tanh_bf16(const FPArray &x) {
  assert(x.party != PUBLIC) ;
  assert(x.m_bits == 7);
  assert(x.e_bits == 8);

  int sz = x.size ;
  int m_bits, e_bits ;

  m_bits = x.m_bits ;
  e_bits = x.e_bits ;

  FPArray one_flat = fp_op->input<float>(ALICE, sz, (float)1.0, m_bits, e_bits) ;
  FPArray two_flat = fp_op->input<float>(ALICE, sz, (float)2.0, m_bits, e_bits) ;

  FPArray sig = fp_op->mul(
    this->sigmoid_bf16(
      fp_op->mul(two_flat, x)
    ), 
    two_flat) ;
  return fp_op->sub(sig, one_flat) ;
}

FPArray FPMath::tanh_fp32(const FPArray &x) {
  assert(x.party != PUBLIC) ;
  assert(x.m_bits == 23);
  assert(x.e_bits == 8);

  int sz = x.size ;
  int m_bits, e_bits ;

  m_bits = x.m_bits ;
  e_bits = x.e_bits ;

  FPArray one_flat = fp_op->input<float>(ALICE, sz, (float)1.0, m_bits, e_bits) ;
  FPArray two_flat = fp_op->input<float>(ALICE, sz, (float)2.0, m_bits, e_bits) ;

  FPArray sig = fp_op->mul(
    this->sigmoid_fp32(
      fp_op->mul(two_flat, x)
    ), 
    two_flat) ;
  return fp_op->sub(sig, one_flat) ;
}

vector<FPArray> FPMath::softmax_beacon(const vector<FPArray>& x) {
  int N = x.size();
  int n = x[0].size;
  int m_bits = x[0].m_bits;
  int e_bits = x[0].e_bits;
  assert(m_bits > 0);
  for(int i = 1; i < N; i++) {
    assert(x[i].party != PUBLIC);
    assert(x[i].m_bits == m_bits);
    assert(x[i].e_bits == e_bits);
    assert(x[i].size == n);
  }
  if (x[0].m_bits == BFLOAT16_M_BITS && x[0].e_bits == BFLOAT16_E_BITS) {
    vector<FPArray> y(x.size());
    for (int i = 0; i < x.size(); i++) {
      y[i] = fp_op->bfloat16_to_FP32(x[i]);
    }
    y = softmax_beacon(y);
    FPArray y_concat = concat(y);
    y_concat = fp_op->FP32_to_bfloat16(y_concat);
    for (int i = 0; i < x.size(); i++) {
      y[i] = y_concat.subset(i*x[0].size, (i+1)*x[0].size);
    }
    return y;
  }
  FPArray x_max = fp_op->max(x);
  FPArray x_max_flat(party, N*n, m_bits, e_bits);
  for (int i = 0; i < N; i++) {
    for (int j = 0; j < n; j++) {
      x_max_flat.s[i*n + j] = x_max.s[i];
      x_max_flat.z[i*n + j] = x_max.z[i];
      x_max_flat.m[i*n + j] = x_max.m[i];
      x_max_flat.e[i*n + j] = x_max.e[i];
    }
  }
  FPArray x_flat = concat(x);
  FPArray shifted_x_flat = fp_op->flip_sign(fp_op->sub(x_max_flat, x_flat, false, true, true));
  FPArray e_x_flat = this->exp(shifted_x_flat);

  vector<FPArray> e_x(N);
  for (int i = 0; i < N; i++) {
    e_x[i] = FPArray(party, n, m_bits, e_bits);
    memcpy(e_x[i].s, e_x_flat.s + i*n, n*sizeof(uint8_t));
    memcpy(e_x[i].z, e_x_flat.z + i*n, n*sizeof(uint8_t));
    memcpy(e_x[i].m, e_x_flat.m + i*n, n*sizeof(uint64_t));
    memcpy(e_x[i].e, e_x_flat.e + i*n, n*sizeof(uint64_t));
  }
  vector<FPArray> e_x_tr(n);
  for (int i = 0; i < n; i++) {
    e_x_tr[i] = FPArray(party, N, m_bits, e_bits);
    for (int j = 0; j < N; j++) {
      e_x_tr[i].s[j] = e_x[j].s[i];
      e_x_tr[i].z[j] = e_x[j].z[i];
      e_x_tr[i].m[j] = e_x[j].m[i];
      e_x_tr[i].e[j] = e_x[j].e[i];
    }
  }
  FPArray sum_e_x = fp_op->vector_sum(e_x);
  vector<FPArray> ret_tr = fp_op->div(e_x_tr, sum_e_x, false);
  vector<FPArray> ret(N);
  for (int i = 0; i < N; i++) {
    ret[i] = FPArray(party, n, m_bits, e_bits);
    for (int j = 0; j < n; j++) {
      ret[i].s[j] = ret_tr[j].s[i];
      ret[i].z[j] = ret_tr[j].z[i];
      ret[i].m[j] = ret_tr[j].m[i];
      ret[i].e[j] = ret_tr[j].e[i];
    }
  }
  return ret;
}

vector<FPArray> FPMath::softmax_secfloat(const vector<FPArray>& x) {
  int N = x.size();
  int n = x[0].size;
  int m_bits = x[0].m_bits;
  int e_bits = x[0].e_bits;
  assert(m_bits > 0);
  for(int i = 1; i < N; i++) {
    assert(x[i].party != PUBLIC);
    assert(x[i].m_bits == m_bits);
    assert(x[i].e_bits == e_bits);
    assert(x[i].size == n);
  }
  FPArray x_max = fp_op->max(x);
  FPArray x_max_flat(party, N*n, m_bits, e_bits);
  for (int i = 0; i < N; i++) {
    for (int j = 0; j < n; j++) {
      x_max_flat.s[i*n + j] = x_max.s[i];
      x_max_flat.z[i*n + j] = x_max.z[i];
      x_max_flat.m[i*n + j] = x_max.m[i];
      x_max_flat.e[i*n + j] = x_max.e[i];
    }
  }

  FPArray x_flat = concat(x);
  FPArray shifted_x_flat = fp_op->flip_sign(fp_op->sub(x_max_flat, x_flat, false, true, true));

  FPArray e_x_flat = this->exp(shifted_x_flat);

  vector<FPArray> e_x_tr(n);
  for (int i = 0; i < n; i++) {
    e_x_tr[i] = FPArray(party, N, m_bits, e_bits);
    for (int j = 0; j < N; j++) {
      e_x_tr[i].s[j] = e_x_flat.s[j*n + i];
      e_x_tr[i].z[j] = e_x_flat.z[j*n + i];
      e_x_tr[i].m[j] = e_x_flat.m[j*n + i];
      e_x_tr[i].e[j] = e_x_flat.e[j*n + i];
    }
  }
  FPArray sum_e_x;
  {
    vector<FPArray> tmp = e_x_tr;
    int num_adds_old = n; int num_adds_curr = n/2;
    while(num_adds_old > 1) {
      int odd_num_adds = num_adds_old & 1;
      vector<FPArray> lhs(num_adds_curr); vector<FPArray> rhs(num_adds_curr);
      for (int j = odd_num_adds; j < num_adds_old && j + 1 < num_adds_old; j += 2) {
        lhs[j/2] = tmp[j]; rhs[j/2] = tmp[j+1];
      }
      FPArray lhs_concat = concat(lhs);
      FPArray rhs_concat = concat(rhs);
      lhs_concat = fp_op->add(lhs_concat, rhs_concat);
      for (int j = 0; j < num_adds_old && j + 1 < num_adds_old; j += 2) {
        tmp[odd_num_adds + (j/2)] = lhs_concat.subset((j/2)*N, (j/2)*N + N);
      }
      num_adds_old = num_adds_curr + odd_num_adds;
      num_adds_curr = num_adds_old/2;
    }
    sum_e_x = tmp[0];
  }
  FPArray sum_e_x_replicated(party, N*n, m_bits, e_bits);
  for(int i = 0; i < N; i++) {
    for (int j = 0; j < n; j++) {
      sum_e_x_replicated.s[i*n + j] = sum_e_x.s[i];
      sum_e_x_replicated.z[i*n + j] = sum_e_x.z[i];
      sum_e_x_replicated.m[i*n + j] = sum_e_x.m[i];
      sum_e_x_replicated.e[i*n + j] = sum_e_x.e[i];
    }
  }

  FPArray ret_flat = fp_op->div(e_x_flat, sum_e_x_replicated);
  vector<FPArray> ret(N);
  for (int i = 0; i < N; i++) {
    ret[i] = FPArray(party, n, m_bits, e_bits);
    memcpy(ret[i].s, ret_flat.s + i*n, n*sizeof(uint8_t));
    memcpy(ret[i].z, ret_flat.z + i*n, n*sizeof(uint8_t));
    memcpy(ret[i].m, ret_flat.m + i*n, n*sizeof(uint64_t));
    memcpy(ret[i].e, ret_flat.e + i*n, n*sizeof(uint64_t));
  }
  return ret;
}

vector<FPArray> FPMath::softmax_jnu(const vector<FPArray>& x) {
  int N = x.size();
  int n = x[0].size;
  int m_bits = x[0].m_bits;
  int e_bits = x[0].e_bits;
  assert(m_bits > 0);
  for(int i = 1; i < N; i++) {
    assert(x[i].party != PUBLIC);
    assert(x[i].m_bits == m_bits);
    assert(x[i].e_bits == e_bits);
    assert(x[i].size == n);
  }
  FPArray x_max = fp_op->max(x);
  FPArray x_max_flat(party, N*n, m_bits, e_bits);
  for (int i = 0; i < N; i++) {
    for (int j = 0; j < n; j++) {
      x_max_flat.s[i*n + j] = x_max.s[i];
      x_max_flat.z[i*n + j] = x_max.z[i];
      x_max_flat.m[i*n + j] = x_max.m[i];
      x_max_flat.e[i*n + j] = x_max.e[i];
    }
  }

  FPArray x_flat = concat(x);
  FPArray shifted_x_flat = fp_op->flip_sign(fp_op->sub(x_max_flat, x_flat, false, true, true));

  FPArray e_x_flat = this->exp(shifted_x_flat);

  vector<FPArray> e_x_tr(n);
  for (int i = 0; i < n; i++) {
    e_x_tr[i] = FPArray(party, N, m_bits, e_bits);
    for (int j = 0; j < N; j++) {
      e_x_tr[i].s[j] = e_x_flat.s[j*n + i];
      e_x_tr[i].z[j] = e_x_flat.z[j*n + i];
      e_x_tr[i].m[j] = e_x_flat.m[j*n + i];
      e_x_tr[i].e[j] = e_x_flat.e[j*n + i];
    }
  }
  FPArray sum_e_x;
  {
    vector<FPArray> tmp = e_x_tr;
    int num_adds_old = n; int num_adds_curr = n/2;
    while(num_adds_old > 1) {
      int odd_num_adds = num_adds_old & 1;
      vector<FPArray> lhs(num_adds_curr); vector<FPArray> rhs(num_adds_curr);
      for (int j = odd_num_adds; j < num_adds_old && j + 1 < num_adds_old; j += 2) {
        lhs[j/2] = tmp[j]; rhs[j/2] = tmp[j+1];
      }
      FPArray lhs_concat = concat(lhs);
      FPArray rhs_concat = concat(rhs);
      lhs_concat = fp_op->add(lhs_concat, rhs_concat);
      for (int j = 0; j < num_adds_old && j + 1 < num_adds_old; j += 2) {
        tmp[odd_num_adds + (j/2)] = lhs_concat.subset((j/2)*N, (j/2)*N + N);
      }
      num_adds_old = num_adds_curr + odd_num_adds;
      num_adds_curr = num_adds_old/2;
    }
    sum_e_x = tmp[0];
  }
  FPArray one = fp_op->input<double>(ALICE, N, (double)1.0, m_bits, FP_INTMD_E_BITS, false);
  FPArray sum_e_x_inv = fp_op->div(one, sum_e_x);
  FPArray sum_e_x_inv_replicated(party, N*n, m_bits, e_bits);
  for(int i = 0; i < N; i++) {
    for (int j = 0; j < n; j++) {
      sum_e_x_inv_replicated.s[i*n + j] = sum_e_x_inv.s[i];
      sum_e_x_inv_replicated.z[i*n + j] = sum_e_x_inv.z[i];
      sum_e_x_inv_replicated.m[i*n + j] = sum_e_x_inv.m[i];
      sum_e_x_inv_replicated.e[i*n + j] = sum_e_x_inv.e[i];
    }
  }

  FPArray ret_flat = fp_op->mul(e_x_flat, sum_e_x_inv_replicated);
  vector<FPArray> ret(N);
  for (int i = 0; i < N; i++) {
    ret[i] = FPArray(party, n, m_bits, e_bits);
    memcpy(ret[i].s, ret_flat.s + i*n, n*sizeof(uint8_t));
    memcpy(ret[i].z, ret_flat.z + i*n, n*sizeof(uint8_t));
    memcpy(ret[i].m, ret_flat.m + i*n, n*sizeof(uint64_t));
    memcpy(ret[i].e, ret_flat.e + i*n, n*sizeof(uint64_t));
  }
  return ret;
}

FPArray FPMath::arcsinpi(const FPArray &alpha)
{
    assert(alpha.party != PUBLIC);
    assert(alpha.m_bits == 23);
    assert(alpha.e_bits == 8);
    assert(FP_INTMD_E_BITS == alpha.e_bits);

    BoolArray all_0 = bool_op->input(ALICE, alpha.size, uint8_t(0));
    //BoolArray all_1 = bool_op->input(ALICE, alpha.size, 1);

    BoolArray alpha_s, alpha_z;
    FixArray alpha_m, alpha_e;
    // 原始alpha
    tie(alpha_s, alpha_z, alpha_m, alpha_e) = fp_op->get_components(alpha);

    FixArray sigma_m = fix->scale_up(alpha_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);
    // 1.2
    // 提升精度后的alpha：sigma
    FPArray sigma = fp_op->input(alpha.party, alpha.size, all_0.data, alpha_z.data, sigma_m.data, alpha_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);

    // start

    // 1.3
    BoolArray e_lt_n14 = fix->LT(alpha_e, -14 + alpha.e_bias());
    // 1.8 && 1.12
    BoolArray e_lt_n2, e_eq_n2;
    tie(e_lt_n2, e_eq_n2) = fix->LT_and_EQ(alpha_e, -2 + alpha.e_bias());
    // 1.6
    BoolArray alpha_eq_1 = bool_op->AND(fix->EQ(alpha_e, alpha.e_bias()), fix->EQ(sigma_m, uint64_t(1) << FP_INTMD_M_BITS));
    FPArray zero_point_five = fp_op->input<double>(ALICE, alpha.size, 0.5, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
    // 1.4
    FPArray pi_inv = fp_op->input<double>(PUBLIC, sigma.size, INV_PI_DOUBLE, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
    FPArray beta = fp_op->mul(sigma, pi_inv);

    // 1.9 & 1.10
    FixArray idx_1 = get_idx_from_input(fix, sigma_m, alpha_e, 2, 4, 14 - alpha.e_bias());
    // 1.11
    vector<FPArray> theta_1 = fp_op->GetCoeffs(arcsin_coeffs_1, arcsin_knots_bits_1, idx_1, arcsin_coeffs_1[0].size(), FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    // 1.13
    FixArray idx_2 = get_idx_from_input(fix, sigma_m, alpha_e, 4, 0, 2 - alpha.e_bias());
    // 1.14
    vector<FPArray> theta_2 = fp_op->GetCoeffs(arcsin_coeffs_2, arcsin_knots_bits_2, idx_2, arcsin_coeffs_2[0].size(), FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    // 1.16
    FixArray idx_3 = get_idx_from_input(fix, sigma_m, alpha_e, 7, 0, 2 - alpha.e_bias());
    // 1.17
    vector<FPArray> theta_3 = fp_op->GetCoeffs(arcsin_coeffs_3, arcsin_knots_bits_3, idx_3, arcsin_coeffs_3[0].size(), FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    assert(theta_1.size() == theta_2.size());
    assert(theta_1.size() == theta_3.size());
    assert(theta_1.size() == 4);

    vector<FPArray> theta(theta_1.size());
    for (int i = 0; i < theta_1.size(); i++)
    {
        theta[i] = fp_op->if_else(e_eq_n2, theta_2[i], theta_3[i]);
        theta[i] = fp_op->if_else(e_lt_n2, theta_1[i], theta[i]);
    }
    // 1.18 & 1.19
    FPArray e_ge_n14_res = fp_op->add(fp_op->mul(fp_op->add(fp_op->mul(fp_op->add(fp_op->mul(theta[3], sigma), theta[2]), sigma), theta[1]), sigma), theta[0]);

    FPArray omega = fp_op->if_else(alpha_eq_1, zero_point_five, e_ge_n14_res);
    omega = fp_op->if_else(e_lt_n14, beta, omega);

    // 舍入
    BoolArray omega_s, omega_z;
    FixArray omega_m, omega_e;
    tie(omega_s, omega_z, omega_m, omega_e) = fp_op->get_components(omega);
    uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                               (1ULL << (FP_INTMD_M_BITS - alpha.m_bits - 1));
    BoolArray rnd_no_oflow = fix->LT(omega_m, oflow_threshold);
    FixArray ret_m_if =
        fix->round_ties_to_even(omega_m, FP_INTMD_M_BITS - alpha.m_bits);
    FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << alpha.m_bits));
    FixArray ret_e = fix->if_else(rnd_no_oflow, omega_e, fix->add(omega_e, 1));

    FPArray ret = fp_op->input(alpha.party, alpha.size, alpha_s.data, alpha_z.data,
                               ret_m.data, ret_e.data, alpha.m_bits, alpha.e_bits);

    return ret;
}

FPArray FPMath::arccospi(const FPArray &alpha)
{
    assert(alpha.party != PUBLIC);
    assert(alpha.m_bits == 23);
    assert(alpha.e_bits == 8);
    assert(FP_INTMD_E_BITS == alpha.e_bits);
    FPArray zero_point_five = fp_op->input<double>(ALICE, alpha.size, 0.5, alpha.m_bits, FP_INTMD_E_BITS, false);
    return fp_op->sub(zero_point_five,this->arcsinpi(alpha));
}

FPArray FPMath::arctanpi(const FPArray &alpha) {
    assert(alpha.party != PUBLIC);
    assert(alpha.m_bits == 23);
    assert(alpha.e_bits == 8);
    assert(FP_INTMD_E_BITS == alpha.e_bits);

    BoolArray all_0 = bool_op->input(ALICE, alpha.size, uint8_t(0));
    BoolArray all_1 = bool_op->input(ALICE, alpha.size, 1);

    BoolArray alpha_s, alpha_z;
    FixArray alpha_m, alpha_e;
    tie(alpha_s, alpha_z, alpha_m, alpha_e) = fp_op->get_components(alpha);
    FixArray gamma_m = fix->scale_up(alpha_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);
    // 提升精度后的alpha'
    FPArray gamma = fp_op->input(alpha.party, alpha.size, all_0.data, alpha_z.data, gamma_m.data, alpha_e.data,
                                 FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    

    // 2.3
    BoolArray alpha_eq_1 = bool_op->AND(fix->EQ(alpha_e, alpha.e_bias()), fix->EQ(gamma_m, uint64_t(1) << FP_INTMD_M_BITS));
    
    // 2.5
    BoolArray gamma_e_ge_0 = fix->GE(alpha_e, alpha.e_bias());


    FPArray pi_inv = fp_op->input<double>(PUBLIC, gamma.size, INV_PI_DOUBLE, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
    FPArray zero_point_five = fp_op->input<double>(ALICE, alpha.size, 0.5, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
    FPArray zero_point_two_five = fp_op->input<double>(ALICE, alpha.size, 0.25, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
    FPArray one = fp_op->input<double>(ALICE, alpha.size, 1.0, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);


    // 2.6
    FPArray sigma = fp_op->if_else(gamma_e_ge_0, fp_op->div(one,gamma), gamma);

    BoolArray sigma_s, sigma_z;
    FixArray sigma_m, sigma_e;
    tie(sigma_s, sigma_z,sigma_m, sigma_e) = fp_op->get_components(sigma);

    // 2.7
    BoolArray e_lt_n14 = fix->LT(sigma_e, -14 + alpha.e_bias());
    // 2.10
    BoolArray e_lt_n2 = fix->LT(sigma_e, -2 + alpha.e_bias());
    
    // 2.11 & 2.12
    FixArray idx_1 = get_idx_from_input(fix, sigma_m, sigma_e, 3, 4, 14 - alpha.e_bias());
    // 2.13
    vector<FPArray> theta_1 = fp_op->GetCoeffs(arctan_coeffs_1, arctan_knots_bits_1, idx_1, arctan_coeffs_1[0].size(), FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    // 2.15 & 2.16
    FixArray idx_2 = get_idx_from_input(fix, sigma_m, sigma_e, 4, 1, 2 - alpha.e_bias());
    // 2.17
    vector<FPArray> theta_2 = fp_op->GetCoeffs(arctan_coeffs_2, arctan_knots_bits_2, idx_2, arctan_coeffs_2[0].size(), FP_INTMD_M_BITS, FP_INTMD_E_BITS);

    assert(theta_1.size() == theta_2.size());
    assert(theta_1.size() == 4);
    vector<FPArray> theta(theta_1.size());
    for (int i = 0; i < theta_1.size(); i++)
    {
        theta[i] = fp_op->if_else(e_lt_n2, theta_1[i], theta_2[i]);
    }

    // 2.18 & 2.19
    FPArray e_ge_n14_res = fp_op->add(fp_op->mul(fp_op->add(fp_op->mul(fp_op->add(fp_op->mul(theta[3], sigma), theta[2]), sigma), theta[1]), sigma), theta[0]);

    FPArray psi = fp_op->if_else(e_lt_n14, fp_op->mul(sigma, pi_inv), e_ge_n14_res);
    psi = fp_op->if_else(alpha_eq_1, zero_point_two_five, psi);

    // 2.20
    FPArray omega = fp_op->if_else(gamma_e_ge_0,fp_op->sub(zero_point_five,psi), psi);


    // 舍入
    BoolArray omega_s, omega_z;
    FixArray omega_m, omega_e;
    tie(omega_s, omega_z, omega_m, omega_e) = fp_op->get_components(omega);
    uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                               (1ULL << (FP_INTMD_M_BITS - alpha.m_bits - 1));
    BoolArray rnd_no_oflow = fix->LT(omega_m, oflow_threshold);
    FixArray ret_m_if =
        fix->round_ties_to_even(omega_m, FP_INTMD_M_BITS - alpha.m_bits);
    FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << alpha.m_bits));
    FixArray ret_e = fix->if_else(rnd_no_oflow, omega_e, fix->add(omega_e, 1));

    FPArray ret = fp_op->input(alpha.party, alpha.size, alpha_s.data, alpha_z.data,
                               ret_m.data, ret_e.data, alpha.m_bits, alpha.e_bits);

    return ret;
}

FPArray FPMath::sqrt(const FPArray &alpha) {
    cout<<alpha.e_bias()<<endl;
    assert(alpha.party != PUBLIC);
    assert(alpha.m_bits == 23);
    assert(alpha.e_bits == 8);
    assert(FP_INTMD_E_BITS == alpha.e_bits);

    BoolArray all_0 = bool_op->input(ALICE, alpha.size, uint8_t(0));
    BoolArray all_1 = bool_op->input(ALICE, alpha.size, 1);

    

    BoolArray alpha_s, alpha_z;
    FixArray alpha_m, alpha_e;
    tie(alpha_s, alpha_z, alpha_m, alpha_e) = fp_op->get_components(alpha);

    FixArray fix_0 = fix->input(ALICE, alpha.size, uint64_t(alpha.e_bias()), alpha_e.signed_, alpha_e.ell, alpha_e.s);

    FixArray sigma_m = fix->scale_up(alpha_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);

    FPArray sqrt2 = fp_op->input<double>(PUBLIC, alpha.size, SQRT2, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
    // 3.2
    FPArray sigma = fp_op->input(alpha.party, alpha.size, all_0.data, alpha_z.data, sigma_m.data, fix_0.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    
    FixArray alpha_e_plus_1 = fix->add(alpha_e, 1);

    // 3.5
    BoolArray b = fix->LSB(alpha_e_plus_1);
    // 3.3
    FixArray a = fix->right_shift(alpha_e_plus_1, 1);

    a.s += 1; // right_shift decreases scale by 1

    // 3.4
    a = fix->add(a, (alpha.e_bias() - 1) / 2);
    // 3.6
    FixArray idx = get_idx_from_input(fix, sigma_m, alpha_e, 4, 0, - alpha.e_bias());
    // 3.7
    vector <FPArray> theta = fp_op->GetCoeffs(sqrt_coeffs, sqrt_knots_bits, idx, sqrt_coeffs[0].size(), FP_INTMD_M_BITS,
                                                FP_INTMD_E_BITS);
    // 3.8 & 3.9
    FPArray psi = fp_op->add(fp_op->mul(fp_op->add(fp_op->mul(fp_op->add(fp_op->mul(theta[3],sigma),theta[2]),sigma),theta[1]),sigma),theta[0]);
    
    // 3.10
    FPArray omega = fp_op->if_else(b,fp_op->mul(psi,sqrt2),psi);
    BoolArray omega_s, omega_z;
    FixArray omega_m, omega_e;
    tie(omega_s, omega_z, omega_m, omega_e) = fp_op->get_components(omega);
    omega_e = a;

    // 舍入

    uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                               (1ULL << (FP_INTMD_M_BITS - alpha.m_bits - 1));
    BoolArray rnd_no_oflow = fix->LT(omega_m, oflow_threshold);
    FixArray ret_m_if =
            fix->round_ties_to_even(omega_m, FP_INTMD_M_BITS - alpha.m_bits);
    FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << alpha.m_bits));
    FixArray ret_e = fix->if_else(rnd_no_oflow, omega_e, fix->add(omega_e, 1));

    FPArray ret = fp_op->input(alpha.party, alpha.size, alpha_s.data, alpha_z.data,
                               ret_m.data, ret_e.data, alpha.m_bits, alpha.e_bits);

    return ret;
}

FPArray FPMath::tanh(const FPArray &alpha) {
    assert(alpha.party != PUBLIC);
    assert(alpha.m_bits == 23);
    assert(alpha.e_bits == 8);
    assert(FP_INTMD_E_BITS == alpha.e_bits);

    BoolArray all_0 = bool_op->input(ALICE, alpha.size, uint8_t(0));
    //BoolArray all_1 = bool_op->input(ALICE, alpha.size, 1);

    BoolArray alpha_s, alpha_z;
    FixArray alpha_m, alpha_e;
    tie(alpha_s, alpha_z, alpha_m, alpha_e) = fp_op->get_components(alpha);

    FixArray gamma_m = fix->scale_up(alpha_m, FP_INTMD_M_BITS + 1, FP_INTMD_M_BITS);

    FPArray zero = fp_op->input<double>(ALICE, alpha.size, 0.0, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);
    FPArray one = fp_op->input<double>(ALICE, alpha.size, 1.0, FP_INTMD_M_BITS, FP_INTMD_E_BITS, false);

    // 4.2
    FPArray gamma = fp_op->input(alpha.party, alpha.size, all_0.data, alpha_z.data, gamma_m.data, alpha_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);

    // start

    // 4.3
    BoolArray e_ge_4 = fix->GE(alpha_e, 4 + alpha.e_bias());
    // 4.6
    BoolArray e_lt_n2 = fix->LT(alpha_e, -2 + alpha.e_bias());

    // 4.9
    FixArray shift_len = fix->sub(alpha_e,-2 + alpha.e_bias());
    shift_len.signed_ = false;

    FixArray m = fix->left_shift(gamma_m,shift_len,FP_INTMD_M_BITS+6,6);


    FixArray sigma_m = fix->reduce(m,FP_INTMD_M_BITS);


    sigma_m = fix->extend(sigma_m, FP_INTMD_M_BITS + 1);
    sigma_m.s = FP_INTMD_M_BITS;

    FixArray k_if_2 = fix->truncate_reduce(m,FP_INTMD_M_BITS);

    FixArray sigma_e = fix->input(ALICE,alpha.size,-2 + alpha.e_bias(), 0, alpha.e_bits + 2, 0);

    BoolArray sigma_z = fix->EQ(sigma_m, uint64_t(0)),sigma_s;
    fp_op->normalize(sigma_m,sigma_e,FP_INTMD_M_BITS);

    FPArray sigma = fp_op->input(alpha.party, alpha.size, all_0.data, sigma_z.data, sigma_m.data, sigma_e.data, FP_INTMD_M_BITS, FP_INTMD_E_BITS);
    

    FixArray k = fix->if_else(e_lt_n2, uint64_t(0), k_if_2);

    // 4.13
    FPArray psi = fp_op->LUT(tanh_k,k,FP_INTMD_M_BITS,FP_INTMD_E_BITS);

    sigma = fp_op->if_else(e_lt_n2,gamma,sigma);
    tie(sigma_s,sigma_z,sigma_m,sigma_e)=fp_op->get_components(sigma);

    BoolArray sigma_e_lt_n14 = fix->LT(sigma_e, -14 + alpha.e_bias());

    // 4.17
    FixArray idx = get_idx_from_input(fix, sigma_m, sigma_e, 3, 4, 14 - alpha.e_bias());

    // 4.18
    vector<FPArray> theta = fp_op->GetCoeffs(tanh_coeffs, tanh_knots_bits, idx, tanh_coeffs[0].size(), FP_INTMD_M_BITS, FP_INTMD_E_BITS);

    // 4.19 & 4.20
    FPArray omega=fp_op->add(fp_op->mul(fp_op->add(fp_op->mul(fp_op->add(fp_op->mul(theta[3], sigma), theta[2]), sigma), theta[1]), sigma), theta[0]);


    omega = fp_op->if_else(sigma_e_lt_n14,sigma,omega);



    // 4.21
    FPArray phi = fp_op->add(psi, omega), chi = fp_op->add(one,fp_op->mul(psi,omega));

    // 4.22
    FPArray iota = fp_op->div(phi, chi);
    iota = fp_op->if_else(e_ge_4, one, iota);


    BoolArray iota_s, iota_z;
    FixArray iota_m, iota_e;
    tie(iota_s, iota_z, iota_m, iota_e) = fp_op->get_components(iota);
    // 舍入

    uint64_t oflow_threshold = (1ULL << (FP_INTMD_M_BITS + 1)) -
                               (1ULL << (FP_INTMD_M_BITS - alpha.m_bits - 1));
    BoolArray rnd_no_oflow = fix->LT(iota_m, oflow_threshold);
    FixArray ret_m_if =
            fix->round_ties_to_even(iota_m, FP_INTMD_M_BITS - alpha.m_bits);
    FixArray ret_m = fix->if_else(rnd_no_oflow, ret_m_if, (1ULL << alpha.m_bits));
    FixArray ret_e = fix->if_else(rnd_no_oflow, iota_e, fix->add(iota_e, 1));

    FPArray ret = fp_op->input(alpha.party, alpha.size, alpha_s.data, alpha_z.data,
                               ret_m.data, ret_e.data, alpha.m_bits, alpha.e_bits);

    return ret;
}

FPArray FPMath::geo1(const FPArray &lambda1, const FPArray &lambda2,const FPArray &phi1,const FPArray &phi2){
    FPArray dlambda = fp_op->divpow2(fp_op->sub(lambda2,lambda1),1,false);
    FPArray dphi = fp_op->divpow2(fp_op->sub(phi2,phi1),1,false);
    FPArray t1 = this->sinpi(dphi),t2 = this->cospi(phi1), t3 = this->cospi(phi2), t4 = this->sinpi(dlambda);
    t1 = fp_op->mul(t1, t1);t4 = fp_op->mul(t4, t4);
    FPArray iota = fp_op->add(t1,fp_op->mul(fp_op->mul(t2,t3),t4));
    //return iota;
    FPArray res = fp_op->mulpow2(arcsinpi(sqrt(iota)),1,false);
    return res;
}

FPArray FPMath::geo2(const FPArray &lambda1, const FPArray &lambda2,const FPArray &phi1,const FPArray &phi2){
    FPArray dlambda = fp_op->sub(lambda2,lambda1);

    FPArray t1 = sinpi(dlambda),t2 = cospi(phi2), t3 = cospi(phi1), t4 = sinpi(phi2), t5 = sinpi(phi1), t6 = cospi(dlambda);
    FPArray ta = fp_op->mul(t1,t2),tb=fp_op->sub(fp_op->mul(t3,t4),fp_op->mul(t5,fp_op->mul(t2,t6)));
    FPArray nu = fp_op->div(ta,tb);
    FPArray res = this->arctanpi(nu);
    return res;

}

FPArray FPMath::gelu(const FPArray &alpha){
    assert(alpha.party != PUBLIC);
    assert(alpha.m_bits == 23);
    assert(alpha.e_bits == 8);
    assert(FP_INTMD_E_BITS == alpha.e_bits);
    FPArray c1 = fp_op->input<double>(ALICE, alpha.size, C1, alpha.m_bits, FP_INTMD_E_BITS, false);
    FPArray c2 = fp_op->input<double>(ALICE, alpha.size, SQRT_2_INV_PI, alpha.m_bits, FP_INTMD_E_BITS, false);
    FPArray one = fp_op->input<double>(ALICE, alpha.size, (double)1.0, alpha.m_bits, FP_INTMD_E_BITS, false);
    FPArray beta=fp_op->mul(c2,fp_op->add(alpha,fp_op->mul(fp_op->mul(alpha,alpha),fp_op->mul(alpha,c1))));
    FPArray gamma=fp_op->mul(alpha,fp_op->add(one,this->tanh(beta)));
    FPArray omega=fp_op->divpow2(gamma,1);
    return omega;

}

vector<FPArray> FPMath::layernorm(const vector<FPArray>&a){
    int N = a.size();
    int n = a[0].size;
    int party = a[0].party;
    int m_bits = a[0].m_bits;
    int e_bits = a[0].e_bits;
    for (int i = 1; i < N; i++) {
        assert(a[i].party == party);
        assert(a[i].m_bits == m_bits);
        assert(a[i].e_bits == e_bits);
        assert(a[i].size == n);
    }
    // len(a_sum) = len(mu) = N
    FPArray a_sum = fp_op->treesum(a);
    FPArray inv_n_N = fp_op->input<double>(ALICE, N, (double)1.0 / n, m_bits, FP_INTMD_E_BITS, false);
    FPArray mu = fp_op->mul(a_sum,inv_n_N);
    
    FPArray a_flat = concat(a);
    FPArray mu_flat(party, N*n, m_bits, e_bits);
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < n; j++) {
            mu_flat.s[i*n + j] = mu.s[i];
            mu_flat.z[i*n + j] = mu.z[i];
            mu_flat.m[i*n + j] = mu.m[i];
            mu_flat.e[i*n + j] = mu.e[i];
        }
    }

    FPArray b_flat=fp_op->sub(a_flat,mu_flat);
    FPArray c_flat=fp_op->mul(b_flat,b_flat);

    vector<FPArray>c(N);
    for(int i=0;i<N;i++){
        c[i] = FPArray(party, n, m_bits, e_bits);
        for(int j=0;j<n;j++){
            c[i].s[j]=c_flat.s[i*n+j];
            c[i].z[j]=c_flat.z[i*n+j];
            c[i].m[j]=c_flat.m[i*n+j];
            c[i].e[j]=c_flat.e[i*n+j];
        }
    }
    FPArray sigma=fp_op->sqrt(fp_op->mul(fp_op->treesum(c),inv_n_N));
    FPArray one = fp_op->input<double>(ALICE, N, (double)1.0, m_bits, FP_INTMD_E_BITS, false);
    FPArray inv_sigma=fp_op->div(one, sigma);
    FPArray inv_sigma_flat(party, N*n, m_bits, e_bits);
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < n; j++) {
            inv_sigma_flat.s[i*n + j] = inv_sigma.s[i];
            inv_sigma_flat.z[i*n + j] = inv_sigma.z[i];
            inv_sigma_flat.m[i*n + j] = inv_sigma.m[i];
            inv_sigma_flat.e[i*n + j] = inv_sigma.e[i];
        }
    }
    FPArray d_flat=fp_op->mul(b_flat, inv_sigma_flat);
    vector<FPArray>d(N);
    for(int i=0;i<N;i++){
        d[i] = FPArray(party, n, m_bits, e_bits);
        for(int j=0;j<n;j++){
            d[i].s[j]=d_flat.s[i*n+j];
            d[i].z[j]=d_flat.z[i*n+j];
            d[i].m[j]=d_flat.m[i*n+j];
            d[i].e[j]=d_flat.e[i*n+j];
        }
    }
    return d;
}
