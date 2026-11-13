#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tc_cetta_bridge.h"

static int g_checks = 0;
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
extern uint64_t tc_test_ordinary_flat_leaf_calls;
extern uint64_t tc_test_ordinary_flat_leaf_fired;
extern uint64_t tc_test_ordinary_flat_slow_calls;
#endif

#define CHECK(cond, msg) do { \
  g_checks++; \
  if (!(cond)) { \
    fprintf(stderr, "FAIL [test_cetta_bridge:%d]: %s\n", __LINE__, (msg)); \
    return false; \
  } \
} while (0)

static bool permit_flag_cb(void *ctx, const TcPreparedStep *firing, const TcPreparedEffect *effect) {
  (void)firing;
  (void)effect;
  const bool *allow = (const bool *)ctx;
  return allow && *allow;
}

/* Control 1 & 3A: Presentation.lean fixture(false) vs fixture(true) and Event.restrict */
static bool test_presentation_fixture_and_profiles(void) {
  CHECK(tc_init(1u << 16, 1u << 15), "tc_init");
  int s_name = tc_sort(SORT_PURE | SORT_FREE);
  int s_proc = tc_sort(SORT_PROVABLE);
  CHECK(s_name > 0 && s_proc > 0, "sorts");

  TcCettaIntern intern;
  CHECK(tc_cetta_intern_init(&intern, (uint16_t)s_name, (uint16_t)s_proc), "intern_init");

  /* Build CeTTa atom views for (Request Start Move) and (At Finish) */
  TcCettaAtomView a_req_kids[3] = {
    { CETTA_ATOM_SYM, "Request", 0, NULL },
    { CETTA_ATOM_SYM, "Start",   0, NULL },
    { CETTA_ATOM_SYM, "Move",    0, NULL }
  };
  TcCettaAtomView a_req = { CETTA_ATOM_EXPR, NULL, 3, a_req_kids };

  TcCettaAtomView a_at_kids[2] = {
    { CETTA_ATOM_SYM, "At",     0, NULL },
    { CETTA_ATOM_SYM, "Finish", 0, NULL }
  };
  TcCettaAtomView a_at = { CETTA_ATOM_EXPR, NULL, 2, a_at_kids };

  Term t_req = tc_cetta_intern_atom(&intern, &a_req);
  Term t_at  = tc_cetta_intern_atom(&intern, &a_at);
  CHECK(t_req != 0 && t_at != 0 && t_req != t_at, "interned Request and At atoms");

  /* Re-interning the same CeTTa atom structure returns the identical hash-consed Term */
  CHECK(tc_cetta_intern_atom(&intern, &a_req) == t_req, "hash-consed idempotence");

  enum { SP_REQ = 0, SP_OUT = 1 };
  tc_protect(SP_OUT);

  /* Rule R_EXECUTE: take (Request Start Move)@SP_REQ |- make (At Finish)@SP_OUT */
  tc_ctx(0, NULL);
  Rule r_exec = {
    .ntake = 1,
    .take  = { { t_req, SP_REQ } },
    .make  = { t_at,  SP_OUT },
    .fresh = -1
  };
  int R_EXEC = tc_rule(&r_exec);
  CHECK(R_EXEC >= 0, "R_EXEC installed");
  tc_seal();

  Occ occ_req = tc_post(SP_REQ, t_req);
  CHECK(occ_req != 0 && tc_alive(occ_req), "posted Request(Start, Move)");

  Occ take_arr[1] = { occ_req };
  TcPreparedStep cand = { .rule = R_EXEC, .take = take_arr };

  /* 0. General core has no evaluation default: NULL profile must be refused */
  TcPreparedEffect eff_null;
  TcAdmittedEvent ev_null;
  TcAdmissionReceipt rec_null;
  TcRefusalReason ref_null = TC_REFUSE_NONE;
  CHECK(tc_bridge_execute_candidate(&cand, NULL, &eff_null, &ev_null, &rec_null, &ref_null) == TC_BRIDGE_REFUSED,
        "NULL profile refused");
  CHECK(ref_null == TC_REFUSE_NO_PROFILE && !rec_null.admitted, "NULL profile refusal reason");
  CHECK(eff_null.prepared && eff_null.nmake == 1 && eff_null.make_terms[0] == t_at,
        "prepared effect still computed before profile check");
  CHECK(tc_alive(occ_req), "take occurrence untouched after NULL profile refusal");

  /* 1. Presentation.fixture(false): prepared holds, permitted fails -> refused with SAME prepared effect */
  bool flag_false = false;
  bool flag_true  = true;
  TcAdmissionProfile prof_false = tc_admission_custom_profile(
      "fixture(false)", true, true, true, false, &flag_false, permit_flag_cb);
  TcAdmissionProfile prof_true  = tc_admission_custom_profile(
      "fixture(true)",  true, true, true, false, &flag_true,  permit_flag_cb);

  TcPreparedEffect eff_false, eff_true;
  TcAdmittedEvent ev_false, ev_true;
  TcAdmissionReceipt rec_false, rec_true;
  TcRefusalReason ref_false = TC_REFUSE_NONE, ref_true = TC_REFUSE_NONE;

  TcBridgeOutcome out_false = tc_bridge_execute_candidate(
      &cand, &prof_false, &eff_false, &ev_false, &rec_false, &ref_false);
  CHECK(out_false == TC_BRIDGE_REFUSED, "fixture(false) refused candidate");
  CHECK(ref_false == TC_REFUSE_PROFILE_POLICY && !rec_false.admitted, "fixture(false) refusal reason");
  CHECK(eff_false.prepared && eff_false.nmake == 1 && eff_false.make_terms[0] == t_at,
        "fixture(false) prepared effect");
  CHECK(tc_alive(occ_req), "occ_req still alive after fixture(false) refusal");

  /* 2. Presentation.fixture(true): SAME candidate admitted under prof_true with IDENTICAL prepared effect */
  TcBridgeOutcome out_true = tc_bridge_execute_candidate(
      &cand, &prof_true, &eff_true, &ev_true, &rec_true, &ref_true);
  CHECK(out_true == TC_BRIDGE_ADMITTED, "fixture(true) admitted candidate");
  CHECK(ref_true == TC_REFUSE_NONE && rec_true.admitted, "fixture(true) receipt issued");
  CHECK(rec_true.out != 0 && rec_true.out_term == t_at, "fixture(true) receipt output term");
  CHECK(!tc_alive(occ_req), "linear take consumed on commit");

  /* Verify the prepared effect is identical across both admission profiles */
  CHECK(eff_false.prepared == eff_true.prepared &&
        eff_false.rule == eff_true.rule &&
        eff_false.nmake == eff_true.nmake &&
        eff_false.make_terms[0] == eff_true.make_terms[0] &&
        eff_false.make_spaces[0] == eff_true.make_spaces[0],
        "identical TcPreparedEffect across refusing and admitting profiles");

  /* Verify EffectCore.Event.restrict (tc_event_restrict) */
  TcAdmissionProfile prof_super = tc_admission_guard_profile(false);
  TcAdmittedEvent ev_restricted;
  CHECK(tc_event_restrict(&ev_true, &prof_super, &ev_restricted), "Event.restrict to broader profile succeeds");
  CHECK(ev_restricted.prepared.make_terms[0] == ev_true.prepared.make_terms[0] &&
        ev_restricted.receipt.out == ev_true.receipt.out &&
        ev_restricted.profile == &prof_super,
        "Event.restrict preserves firing, prepared effect, and receipt");
  CHECK(!tc_event_restrict(&ev_true, &prof_false, &ev_restricted),
        "Event.restrict to refusing profile is rejected");

  return true;
}

/* Control 2 & 3B: Absent-resource, double-take, absent-guard, count-guard, reach-guard,
   and guard-enforcing vs guard-relaxed admission profiles on the same prepared effect */
static bool test_guards_and_refusal_controls(void) {
  CHECK(tc_init(1u << 16, 1u << 15), "tc_init");
  int s_val = tc_sort(SORT_PURE | SORT_FREE);
  int s_fact = tc_sort(SORT_PROVABLE);
  int s_hnd = tc_sort(0);
  uint16_t sp_sort = tc_space_sort();

  Binder b_v1[1] = { { (uint16_t)s_val, 0, 0 } };
  Binder b_v2[2] = { { (uint16_t)s_val, 0, 0 }, { (uint16_t)s_val, 0, 0 } };
  Binder b_sp[1] = { { sp_sort, 0, 0 } };

  int C_COIN   = tc_con((uint16_t)s_fact, 0, 1, b_v1);
  int C_LOCK   = tc_con((uint16_t)s_fact, 0, 1, b_v1);
  int C_PAIR   = tc_con((uint16_t)s_fact, 0, 2, b_v2);
  int C_FIRED  = tc_con((uint16_t)s_fact, 0, 1, b_v1);
  int C_HANDLE = tc_con((uint16_t)s_hnd,  0, 1, b_sp);
  tc_set_handle_con(C_HANDLE);

  enum { SP_BOARD = 0, SP_LOCK = 1, SP_OUT = 2 };
  tc_protect(SP_OUT);

  Binder vars[2] = { { (uint16_t)s_val, 0, 0 }, { (uint16_t)s_val, 0, 0 } };
  tc_ctx(2, vars);
  Term v0 = tc_v(0), v1 = tc_v(1);
  Term c_v0 = tc_app(C_COIN, &v0);
  Term c_v1 = tc_app(C_COIN, &v1);
  Term l_v0 = tc_app(C_LOCK, &v0);
  Term p_01[2] = { v0, v1 };
  Term pair_01 = tc_app(C_PAIR, p_01);
  Term f_v0 = tc_app(C_FIRED, &v0);

  /* Rule R_MERGE_TWO: takes two coins COIN(x), COIN(y) |- make PAIR(x, y)@SP_OUT */
  Rule r_merge = {
    .ntake = 2,
    .take  = { { c_v0, SP_BOARD }, { c_v1, SP_BOARD } },
    .make  = { pair_01, SP_OUT },
    .fresh = -1
  };
  int R_MERGE = tc_rule(&r_merge);

  /* Rule R_GUARDED_ABSENT: keep COIN(x)@SP_BOARD, absent LOCK(x)@SP_LOCK |- make FIRED(x)@SP_OUT */
  Rule r_abs = {
    .nkeep   = 1,
    .nabsent = 1,
    .keep    = { { c_v0, SP_BOARD } },
    .absent  = { { l_v0, SP_LOCK } },
    .make    = { f_v0, SP_OUT },
    .fresh   = -1
  };
  int R_ABS = tc_rule(&r_abs);

  /* Rule R_GUARDED_COUNT: keep COIN(x)@SP_BOARD, count(COIN(x)@SP_BOARD == 2) |- make FIRED(x)@SP_OUT */
  Rule r_cnt = {
    .nkeep  = 1,
    .ncount = 1,
    .keep   = { { c_v0, SP_BOARD } },
    .count  = { { c_v0, SP_BOARD, 2 } },
    .make   = { f_v0, SP_OUT },
    .fresh  = -1
  };
  int R_CNT = tc_rule(&r_cnt);
  CHECK(R_MERGE >= 0 && R_ABS >= 0 && R_CNT >= 0, "rules installed");
  tc_seal();

  Term gold   = tc_name((uint16_t)s_val, tc_fresh_name());
  Term silver = tc_name((uint16_t)s_val, tc_fresh_name());
  Term t_coin_gold   = tc_app(C_COIN, &gold);
  Term t_coin_silver = tc_app(C_COIN, &silver);
  Term t_lock_gold   = tc_app(C_LOCK, &gold);
  Term t_fired_gold  = tc_app(C_FIRED, &gold);

  Occ o_gold   = tc_post(SP_BOARD, t_coin_gold);
  Occ o_silver = tc_post(SP_BOARD, t_coin_silver);
  Occ o_lock   = tc_post(SP_LOCK,  t_lock_gold);
  CHECK(o_gold && o_silver && o_lock, "initial occurrences posted");

  TcAdmissionProfile guard_prof = tc_admission_guard_profile(false);
  TcPreparedEffect eff;
  TcAdmittedEvent ev;
  TcAdmissionReceipt rec;
  TcRefusalReason ref;

  /* 1. Double-take refusal: passing {o_gold, o_gold} to R_MERGE */
  Occ dup_take[2] = { o_gold, o_gold };
  TcPreparedStep cand_dup = { .rule = R_MERGE, .take = dup_take };
  CHECK(tc_bridge_execute_candidate(&cand_dup, &guard_prof, &eff, &ev, &rec, &ref) == TC_BRIDGE_REFUSED,
        "double-take candidate refused");
  CHECK(ref == TC_REFUSE_DOUBLE_TAKE && !rec.admitted && tc_alive(o_gold),
        "double-take refusal reason and resource preservation");

  /* 2. Absent-resource refusal: passing non-existent occurrence 9999 */
  Occ dead_take[2] = { o_gold, 9999 };
  TcPreparedStep cand_dead = { .rule = R_MERGE, .take = dead_take };
  CHECK(tc_bridge_execute_candidate(&cand_dead, &guard_prof, &eff, &ev, &rec, &ref) == TC_BRIDGE_REFUSED,
        "absent-resource candidate refused");
  CHECK(ref == TC_REFUSE_ABSENT_RESOURCE && !rec.admitted, "absent-resource refusal reason");

  /* 3. Count-guard refusal: R_CNT requires 2 copies of COIN(gold), only 1 is present */
  Occ keep_gold[1] = { o_gold };
  TcPreparedStep cand_cnt = { .rule = R_CNT, .keep = keep_gold };
  CHECK(tc_bridge_execute_candidate(&cand_cnt, &guard_prof, &eff, &ev, &rec, &ref) == TC_BRIDGE_REFUSED,
        "count-guard candidate refused");
  CHECK(ref == TC_REFUSE_COUNT_GUARD && !rec.admitted, "count-guard refusal reason");
  CHECK(eff.prepared && eff.nmake == 1 && eff.make_terms[0] == t_fired_gold,
        "prepared effect defined BEFORE count guard is checked");

  /* 4. Reach-guard refusal: R_ABS with reachability enforced, but SP_OUT not in seeds */
  Term seeds_incomplete[1] = { tc_space_term(SP_BOARD) };
  TcPreparedStep cand_reach = {
    .rule = R_ABS, .keep = keep_gold, .nseeds = 1, .seeds = seeds_incomplete
  };
  TcAdmissionProfile reach_prof = tc_admission_guard_profile(true);
  CHECK(tc_bridge_execute_candidate(&cand_reach, &reach_prof, &eff, &ev, &rec, &ref) == TC_BRIDGE_REFUSED,
        "reach-guard candidate refused");
  CHECK(ref == TC_REFUSE_REACH_GUARD && !rec.admitted && eff.prepared,
        "reach-guard refusal reason with prepared effect intact");

  /* 5. Control 3B: Same candidate (cand_abs) with LOCK(gold) present on board:
        - Refused under guard_prof (enforce_absent = true) with TC_REFUSE_ABSENT_GUARD
        - Admitted under relaxed_prof (enforce_absent = false)
        - Both runs produce the exact same TcPreparedEffect (FIRED(gold)@SP_OUT)! */
  TcPreparedStep cand_abs = { .rule = R_ABS, .keep = keep_gold };
  TcPreparedEffect eff_strict, eff_relaxed;
  TcAdmissionReceipt rec_strict, rec_relaxed;
  TcRefusalReason ref_strict = TC_REFUSE_NONE, ref_relaxed = TC_REFUSE_NONE;

  CHECK(tc_bridge_execute_candidate(&cand_abs, &guard_prof, &eff_strict, &ev, &rec_strict, &ref_strict) == TC_BRIDGE_REFUSED,
        "strict guard profile refuses absent-violating candidate");
  CHECK(ref_strict == TC_REFUSE_ABSENT_GUARD && !rec_strict.admitted,
        "strict guard profile refusal reason is TC_REFUSE_ABSENT_GUARD");
  CHECK(eff_strict.prepared && eff_strict.make_terms[0] == t_fired_gold,
        "strict guard profile still computed prepared effect");

  TcAdmissionProfile relaxed_prof = tc_admission_custom_profile(
      "relaxedAbsentProfile", false, true, true, false, NULL, NULL);
  /* SP_OUT is protected and the store is sealed: the rule's declared absence guard belongs to the
     firing, so a relaxed profile cannot commit it into SP_OUT. */
  CHECK(tc_bridge_execute_candidate(&cand_abs, &relaxed_prof, &eff_relaxed, &ev, &rec_relaxed, &ref_relaxed) == TC_BRIDGE_REFUSED,
        "relaxed guard profile cannot commit an absent-violating firing into a protected space");
  CHECK(!rec_relaxed.admitted && ref_relaxed == TC_REFUSE_ABSENT_GUARD,
        "the refusal names the declared absence guard");
  CHECK(eff_strict.prepared == eff_relaxed.prepared &&
        eff_strict.nmake == eff_relaxed.nmake &&
        eff_strict.make_terms[0] == eff_relaxed.make_terms[0] &&
        eff_strict.make_spaces[0] == eff_relaxed.make_spaces[0],
        "identical prepared effect under guard-enforcing and guard-relaxed profiles");

  return true;
}

/* Control 4 & 5: Recorded CeTTa candidate stream + distinct outcomes
   (TC_BRIDGE_ADMITTED, TC_BRIDGE_REFUSED, TC_BRIDGE_UNRESOLVED, TC_BRIDGE_BUDGET_EXHAUSTED) */
static bool test_recorded_cetta_stream_and_outcomes(void) {
  CHECK(tc_init(1u << 16, 1u << 15), "tc_init");
  int s_name = tc_sort(SORT_PURE | SORT_FREE);
  int s_atom = tc_sort(SORT_PROVABLE);
  TcCettaIntern intern;
  CHECK(tc_cetta_intern_init(&intern, (uint16_t)s_name, (uint16_t)s_atom), "intern_init");

  /* Intern CeTTa atoms from a recorded tf:fire candidate stream:
     (coin gold), (coin silver), (coin bronze), (merged gold silver) */
  TcCettaAtomView v_gold[2]   = { { CETTA_ATOM_SYM, "coin", 0, NULL }, { CETTA_ATOM_SYM, "gold", 0, NULL } };
  TcCettaAtomView v_silver[2] = { { CETTA_ATOM_SYM, "coin", 0, NULL }, { CETTA_ATOM_SYM, "silver", 0, NULL } };
  TcCettaAtomView v_merged[3] = {
    { CETTA_ATOM_SYM, "tf:fired", 0, NULL },
    { CETTA_ATOM_SYM, "gold", 0, NULL },
    { CETTA_ATOM_SYM, "silver", 0, NULL }
  };
  TcCettaAtomView a_gold   = { CETTA_ATOM_EXPR, NULL, 2, v_gold };
  TcCettaAtomView a_silver = { CETTA_ATOM_EXPR, NULL, 2, v_silver };
  TcCettaAtomView a_merged = { CETTA_ATOM_EXPR, NULL, 3, v_merged };

  Term t_gold   = tc_cetta_intern_atom(&intern, &a_gold);
  Term t_silver = tc_cetta_intern_atom(&intern, &a_silver);
  Term t_merged = tc_cetta_intern_atom(&intern, &a_merged);
  CHECK(t_gold && t_silver && t_merged, "interned CeTTa stream atoms");

  enum { SP_SRC = 0, SP_DST = 1 };
  tc_protect(SP_DST);
  tc_ctx(0, NULL);
  Rule r_tf = {
    .ntake = 2,
    .take  = { { t_gold, SP_SRC }, { t_silver, SP_SRC } },
    .make  = { t_merged, SP_DST },
    .fresh = -1
  };
  int R_TF = tc_rule(&r_tf);
  CHECK(R_TF >= 0, "R_TF installed");
  tc_seal();

  Occ o_gold   = tc_post(SP_SRC, t_gold);
  Occ o_silver = tc_post(SP_SRC, t_silver);
  CHECK(o_gold && o_silver, "posted CeTTa source occurrences");

  /* Recorded CeTTa candidate stream:
     - Candidate 0: double-take {o_gold, o_gold} (refused: TC_REFUSE_DOUBLE_TAKE)
     - Candidate 1: wrong order {o_silver, o_gold} (refused: TC_REFUSE_SHAPE_UNIFY)
     - Candidate 2: valid {o_gold, o_silver} (admitted: TC_BRIDGE_ADMITTED) */
  Occ t_cand0[2] = { o_gold, o_gold };
  Occ t_cand1[2] = { o_silver, o_gold };
  Occ t_cand2[2] = { o_gold, o_silver };
  TcPreparedStep recorded[3] = {
    { .rule = R_TF, .take = t_cand0 },
    { .rule = R_TF, .take = t_cand1 },
    { .rule = R_TF, .take = t_cand2 }
  };

  TcAdmissionProfile prof = tc_admission_guard_profile(false);
  TcCettaRecordedStream stream;
  TcCandidateCursor cursor;
  TcAdmittedEvent ev;
  TcAdmissionReceipt rec;

  /* 1. Budget exhaustion outcome (TC_BRIDGE_BUDGET_EXHAUSTED): max_candidates = 2 stops before Candidate 2 */
  tc_cetta_stream_cursor_init(&stream, recorded, 3, &cursor);
  TcBridgeBudget budget = { .max_candidates = 2, .has_unresolved_work = true };
  TcBridgeOutcome out_budget = tc_bridge_step_cursor(&cursor, &prof, &budget, &ev, &rec);
  CHECK(out_budget == TC_BRIDGE_BUDGET_EXHAUSTED, "budget exhaustion outcome (-2)");
  CHECK(budget.candidates_inspected == 2 && !rec.admitted, "inspected 2 candidates and issued no receipt");
  CHECK(tc_alive(o_gold) && tc_alive(o_silver), "occurrences untouched after budget exhaustion");

  /* 2. Unresolved work outcome (TC_BRIDGE_UNRESOLVED): stream of only the 2 invalid candidates with has_unresolved_work = true */
  tc_cetta_stream_cursor_init(&stream, recorded, 2, &cursor);
  TcBridgeBudget budget_unres = { .max_candidates = 10, .has_unresolved_work = true };
  TcBridgeOutcome out_unres = tc_bridge_step_cursor(&cursor, &prof, &budget_unres, &ev, &rec);
  CHECK(out_unres == TC_BRIDGE_UNRESOLVED, "unresolved work outcome (-1)");
  CHECK(budget_unres.candidates_inspected == 2 && budget_unres.last_refusal == TC_REFUSE_SHAPE_UNIFY,
        "unresolved work records last refusal");

  /* 3. Pure refusal outcome (TC_BRIDGE_REFUSED): stream of 2 invalid candidates with has_unresolved_work = false */
  tc_cetta_stream_cursor_init(&stream, recorded, 2, &cursor);
  TcBridgeBudget budget_ref = { .max_candidates = 10, .has_unresolved_work = false };
  TcBridgeOutcome out_ref = tc_bridge_step_cursor(&cursor, &prof, &budget_ref, &ev, &rec);
  CHECK(out_ref == TC_BRIDGE_REFUSED, "refused outcome (0)");

  /* 4. Admitted outcome + cursor resume after budget exhaustion:
        pausing at max_candidates = 2 retains Candidate 2 for the resumed cursor call */
  tc_cetta_stream_cursor_init(&stream, recorded, 3, &cursor);
  TcBridgeBudget budget_pause = { .max_candidates = 2, .has_unresolved_work = true };
  CHECK(tc_bridge_step_cursor(&cursor, &prof, &budget_pause, &ev, &rec) == TC_BRIDGE_BUDGET_EXHAUSTED,
        "pause at max_candidates = 2 before Candidate 2");
  TcBridgeBudget budget_ok = { .max_candidates = 10, .has_unresolved_work = true };
  TcBridgeOutcome out_ok = tc_bridge_step_cursor(&cursor, &prof, &budget_ok, &ev, &rec);
  CHECK(out_ok == TC_BRIDGE_ADMITTED, "resumed cursor retains and admits Candidate 2 on recorded CeTTa stream");
  CHECK(budget_ok.candidates_inspected == 1 && rec.admitted && rec.out_term == t_merged,
        "admitted candidate 3 produced (tf:fired gold silver) receipt on resume");
  CHECK(!tc_alive(o_gold) && !tc_alive(o_silver),
        "both linear source occurrences consumed on commit");

  return true;
}

static bool inspect_retained_keep(void *ctx, const TcPreparedStep *firing,
                                  const TcPreparedEffect *effect) {
  (void)ctx;
  (void)effect;
  return firing && firing->keep && firing->keep[0] != 0;
}

static bool poison_post_state_callback(void *ctx, const TcPreparedStep *firing,
                                       const TcPreparedEffect *effect) {
  bool *called = (bool *)ctx;
  (void)firing;
  (void)effect;
  if (called) *called = true;
  return false;
}

static TcAdmittedEvent make_escaped_event_from_stack(int rule, Occ kept) {
  Occ keep[1] = { kept };
  TcPreparedStep firing = { .rule = rule, .keep = keep };
  TcAdmissionProfile profile = tc_admission_guard_profile(false);
  TcPreparedEffect effect;
  TcAdmittedEvent event;
  TcAdmissionReceipt receipt;
  TcRefusalReason refusal;
  if (tc_bridge_execute_candidate(&firing, &profile, &effect, &event,
                                  &receipt, &refusal) != TC_BRIDGE_ADMITTED) {
    memset(&event, 0, sizeof(event));
  }
  return event;
}

/* Control 6: Persistent event stack-escape lifetime safety + witnessed TcAdmissionInclusion */
static bool test_event_lifetime_and_inclusion_capability(void) {
  CHECK(tc_init(1u << 12, 1u << 10), "tc_init");
  int s_name = tc_sort(SORT_PURE | SORT_FREE);
  int s_atom = tc_sort(SORT_PROVABLE);
  Binder b1[1] = { { (uint16_t)s_name, 0, 0 } };
  int c_atom = tc_con((uint16_t)s_atom, 0, 1, b1);
  Term nm = tc_name((uint16_t)s_name, tc_fresh_name());
  Term term = tc_app(c_atom, &nm);
  tc_ctx(0, NULL);
  Rule r = { .nkeep = 1, .keep = { { term, 0 } }, .make = { term, 0 }, .fresh = -1 };
  int rid = tc_rule(&r);
  CHECK(rid >= 0, "rule installed");
  tc_seal();

  Occ kept = tc_post(0, term);
  CHECK(kept != 0, "kept posted");
  TcAdmittedEvent escaped = make_escaped_event_from_stack(rid, kept);
  volatile uint64_t clobber[64];
  for (int i = 0; i < 64; i++) clobber[i] = UINT64_C(0xDEADBEEFCAFED00D);
  CHECK(clobber[0] != 0 && escaped.receipt.admitted, "escaped event admitted after stack clobber");

  TcPreparedStep view = tc_event_firing(&escaped);
  CHECK(view.keep && view.keep[0] == kept, "tc_event_firing binds to owned keep array");

  TcAdmissionProfile target_cb = tc_admission_custom_profile(
      "reads-retained-step", true, true, true, false, NULL, inspect_retained_keep);
  TcAdmittedEvent restricted_cb;
  CHECK(tc_event_restrict(&escaped, &target_cb, &restricted_cb),
        "tc_event_restrict safely reads owned keep after stack frame return");
  CHECK(restricted_cb.firing.keep && restricted_cb.firing.keep[0] == kept,
        "restricted event rebinds firing pointers to dst owned arrays");

  /* Witnessed inclusion capability (tc_event_restrict_included) does NOT re-run callbacks */
  bool callback_invoked = false;
  TcAdmissionProfile src_prof = tc_admission_guard_profile(false);
  TcAdmissionProfile dst_custom = tc_admission_custom_profile(
      "witnessed-custom", true, true, true, false, &callback_invoked, poison_post_state_callback);
  TcAdmissionInclusion inc;
  CHECK(!tc_admission_inclusion_init(&inc, &src_prof, &dst_custom, false),
        "unwitnessed custom policy inclusion refused");
  CHECK(tc_admission_inclusion_init(&inc, &src_prof, &dst_custom, true),
        "witnessed custom policy inclusion token issued");

  TcAdmittedEvent restricted_inc;
  CHECK(tc_event_restrict_included(&escaped, &inc, &restricted_inc),
        "tc_event_restrict_included transports event via inclusion capability");
  CHECK(!callback_invoked,
        "tc_event_restrict_included does not re-run target callback in post-state");
  CHECK(restricted_inc.profile == &restricted_inc.owned_profile &&
        strcmp(restricted_inc.profile->name, "witnessed-custom") == 0,
        "restricted_inc profile bound to owned dst_profile");
  return true;
}

static bool test_missing_cursor_callback(void) {
  TcCandidateCursor cursor = {0};
  TcAdmissionReceipt receipt = {.admitted = true};
  CHECK(tc_step_cursor(&cursor, &receipt) == -1,
        "cursor without next is invalid, not exhausted");
  CHECK(!receipt.admitted, "invalid cursor clears the receipt");
  receipt.admitted = true;
  CHECK(tc_step_cursor(NULL, &receipt) == -1 && !receipt.admitted,
        "null cursor is invalid and clears the receipt");
  return true;
}

static bool test_event_view_origin(void) {
  TcPreparedStep empty = tc_event_firing(NULL);
  CHECK(!empty.take && !empty.keep && !empty.inst && !empty.seeds,
        "null event produces an empty view");
  TcAdmittedEvent original = {0};
  original.ntake = original.nkeep = original.nholes = 1;
  original.has_inst = true;
  original.firing.nseeds = 1;
  original.owned_take[0] = 11;
  original.owned_keep[0] = 13;
  original.owned_inst[0] = 17;
  original.owned_seeds[0] = 19;
  original.firing = tc_event_firing(&original);
  TcAdmittedEvent moved = original;
  TcPreparedStep view = tc_event_firing(&moved);
  CHECK(view.take == moved.owned_take && view.keep == moved.owned_keep &&
        view.inst == moved.owned_inst && view.seeds == moved.owned_seeds,
        "returned fields borrow the moved event's current storage");
  moved.owned_keep[0] = 23;
  CHECK(view.keep[0] == 23 && original.owned_keep[0] == 13,
        "view observes its referent, without copying or retaining the old event");
  moved.ntake = moved.nkeep = 0;
  moved.has_inst = false;
  moved.firing.nseeds = 0;
  view = tc_event_firing(&moved);
  CHECK(!view.take && !view.keep && !view.inst && !view.seeds,
        "empty firing components produce nullable borrowed fields");
  return true;
}

#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
static bool test_ordinary_prepared_bridge_consumer(void) {
  CHECK(tc_init(1u << 12, 64), "ordinary bridge tc_init");
  int sort = tc_sort(0);
  Binder binders[2] = { { (uint16_t)sort, 0, 0 }, { (uint16_t)sort, 0, 0 } };
  int pair = tc_con((uint16_t)sort, 0, 2, binders);
  int ca = tc_con((uint16_t)sort, 0, 0, NULL);
  int cb = tc_con((uint16_t)sort, 0, 0, NULL);
  Term ta = tc_app(ca, NULL), tb = tc_app(cb, NULL);
  CHECK(tc_ctx(2, binders), "ordinary bridge context");
  Term vx = tc_v(0);
  Rule rule = {
    .nkeep = 1, .keep = { { tc_app(pair, (Term[2]){ vx, ta }), 0 } },
    .make = { tc_app(pair, (Term[2]){ vx, tb }), 0 }, .fresh = -1
  };
  int rid = tc_rule(&rule);
  CHECK(rid >= 0, "ordinary bridge rule installed");
  tc_seal();
  Occ kept = tc_flat_put(0, 0, pair, (Term[2]){ ta, ta });
  Occ dest = tc_flat_put(0, 0, pair, (Term[2]){ tb, tb });
  CHECK(kept && dest, "ordinary bridge rows");
  TcPreparedStep candidate = { .rule = rid, .keep = &kept, .dest = dest };
  TcPreparedEffect effect;
  TcAdmittedEvent event;
  TcAdmissionReceipt receipt;
  TcRefusalReason refusal = TC_REFUSE_NONE;
  bool deny = false;
  TcAdmissionProfile denied = tc_admission_custom_profile(
      "deny-ordinary", true, true, true, false, &deny, permit_flag_cb);
  uint64_t leaves = tc_test_ordinary_flat_leaf_calls;
  uint64_t slow = tc_test_ordinary_flat_slow_calls;
  CHECK(tc_bridge_execute_candidate(&candidate, &denied, &effect, &event,
                                    &receipt, &refusal) == TC_BRIDGE_REFUSED,
        "ordinary bridge custom admission denial");
  CHECK(refusal == TC_REFUSE_PROFILE_POLICY && effect.prepared &&
        !receipt.admitted && tc_term(dest) == tc_app(pair, (Term[2]){ tb, tb }),
        "ordinary bridge denial preserves prepared effect and destination");
  CHECK(tc_test_ordinary_flat_leaf_calls == leaves &&
        tc_test_ordinary_flat_slow_calls == slow,
        "ordinary bridge denial performs no leaf or slow firing");

  TcAdmissionProfile admitted = tc_admission_guard_profile(false);
  CHECK(tc_bridge_execute_candidate(&candidate, &admitted, &effect, &event,
                                    &receipt, &refusal) == TC_BRIDGE_ADMITTED,
        "ordinary bridge prepared execution admitted");
  CHECK(receipt.admitted && receipt.out == dest &&
        receipt.out_term == tc_app(pair, (Term[2]){ ta, tb }),
        "ordinary bridge lazy receipt materialization");
  CHECK(event.firing.keep && event.firing.keep[0] == kept &&
        event.receipt.out_term == receipt.out_term,
        "ordinary bridge event owns the prepared premise and receipt");
  CHECK(tc_test_ordinary_flat_leaf_calls == leaves + 1 &&
        tc_test_ordinary_flat_leaf_fired >= 1 &&
        tc_test_ordinary_flat_slow_calls == slow,
        "ordinary bridge commit used the exact leaf without slow fallback");
  return true;
}
#endif

int main(void) {
#ifdef TC_ORDINARY_FLAT_TEST_HOOKS
  if (!test_ordinary_prepared_bridge_consumer()) return 1;
#endif
  if (!test_event_view_origin()) return 1;
  if (!test_missing_cursor_callback()) return 1;
  if (!test_presentation_fixture_and_profiles()) return 1;
  if (!test_guards_and_refusal_controls()) return 1;
  if (!test_recorded_cetta_stream_and_outcomes()) return 1;
  if (!test_event_lifetime_and_inclusion_capability()) return 1;
  printf("test_cetta_bridge: %d/%d checks passed (PreparedEffect, AdmissionProfile, AdmittedEvent, Event.restrict, 4 outcomes, recorded CeTTa stream)\n",
         g_checks, g_checks);
  return 0;
}
