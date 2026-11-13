/* k28: an active step derives only what beta reduction derives.
   tc_active_step reduces under lambda and substitutes without renaming: in the closed term
   \y. ((\x. \y. x) y) the inner beta step turns \y. x with x := y into \y. y, so the result is
   \y. \y. y (second projection) where beta gives \y. \z. y (first projection). With the quote
   constructors set by the theory, tc_active_step_occ posts that reduct into the protected space. */
#include "kc.h"

int main(void) {
  SETUP(tc_init(1u << 12, 1u << 8));
  int TM = tc_sort(0);
  Binder b1 = { (uint16_t)TM, 0, 0 };
  Binder b2[2] = { b1, b1 };
  Binder blam[2] = { { (uint16_t)TM, 1, 0 }, { (uint16_t)TM, 0, 1 } };
  int QUOTE = tc_con((uint16_t)TM, 0, 1, &b1), ACT = tc_con((uint16_t)TM, 0, 1, &b1);
  int LAM = tc_con((uint16_t)TM, 0, 2, blam), APP = tc_con((uint16_t)TM, 0, 2, b2);
  SETUP(QUOTE >= 0 && ACT >= 0 && LAM >= 0 && APP >= 0);
  tc_set_quote_con(QUOTE, ACT, LAM, APP);
  Term x = tc_bv((uint16_t)TM, 0), y = tc_bv((uint16_t)TM, 1);
  SETUP(x && y && x != y);
  Term k = tc_app(LAM, (Term[2]){ x, tc_app(LAM, (Term[2]){ y, x }) });          /* \x. \y. x */
  Term t = tc_app(LAM, (Term[2]){ y, tc_app(APP, (Term[2]){ k, y }) });           /* \y. (K y) */
  Term wrong = tc_app(LAM, (Term[2]){ y, tc_app(LAM, (Term[2]){ y, y }) });       /* \y. \y. y */
  SETUP(k && t && wrong);
  Occ o = tc_post(1, t);
  SETUP(o);
  tc_protect(1); tc_seal();
  Term r = tc_active_step(t);
  HOLDS(r != wrong, "one active step of \\y.(K y) is not \\y.\\y.y (no variable capture)");
  Occ p = tc_active_step_occ(o);
  HOLDS(!(p && tc_term(p) == wrong), "no captured reduct enters protected space 1");
  FINISH("k28_active_step_capture");
}
