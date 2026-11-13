#include "tc_cetta_bridge.h"
#include <string.h>

static TcRefusalReason map_prep_status(int st) {
  switch (st) {
    case TC_PREP_OK:              return TC_REFUSE_NONE;
    case TC_PREP_BAD_RULE:        return TC_REFUSE_BAD_RULE;
    case TC_PREP_ABSENT_RESOURCE: return TC_REFUSE_ABSENT_RESOURCE;
    case TC_PREP_DOUBLE_TAKE:     return TC_REFUSE_DOUBLE_TAKE;
    case TC_PREP_SHAPE_UNIFY:     return TC_REFUSE_SHAPE_UNIFY;
    case TC_PREP_ABSENT_GUARD:    return TC_REFUSE_ABSENT_GUARD;
    case TC_PREP_COUNT_GUARD:     return TC_REFUSE_COUNT_GUARD;
    case TC_PREP_BIRTH_GUARD:     return TC_REFUSE_BIRTH_GUARD;
    case TC_PREP_REACH_GUARD:     return TC_REFUSE_REACH_GUARD;
    default:                      return TC_REFUSE_SHAPE_UNIFY;
  }
}

TcAdmissionProfile tc_admission_guard_profile(bool enforce_reach) {
  TcAdmissionProfile p = {
    .name           = enforce_reach ? "guardAdmission+reach" : "guardAdmission",
    .enforce_absent = true,
    .enforce_count  = true,
    .enforce_birth  = true,
    .enforce_reach  = enforce_reach,
    .ctx            = NULL,
    .permit         = NULL
  };
  return p;
}

TcAdmissionProfile tc_admission_custom_profile(
    const char *name,
    bool enforce_absent, bool enforce_count,
    bool enforce_birth, bool enforce_reach,
    void *ctx,
    bool (*permit)(void *ctx, const TcPreparedStep *firing, const TcPreparedEffect *effect)) {
  TcAdmissionProfile p = {
    .name           = name ? name : "customAdmission",
    .enforce_absent = enforce_absent,
    .enforce_count  = enforce_count,
    .enforce_birth  = enforce_birth,
    .enforce_reach  = enforce_reach,
    .ctx            = ctx,
    .permit         = permit
  };
  return p;
}

bool tc_bridge_prepare(const TcPreparedStep *firing, TcPreparedEffect *out_effect,
                       TcRefusalReason *out_refusal) {
  if (out_effect) memset(out_effect, 0, sizeof(*out_effect));
  if (out_refusal) *out_refusal = TC_REFUSE_NONE;
  if (!firing) {
    if (out_refusal) *out_refusal = TC_REFUSE_BAD_RULE;
    return false;
  }
  Term mt[5] = {0}, ms[5] = {0};
  uint8_t mm[5] = {0}, nm = 0;
  int st = tc_eval_prepared_ex(firing, false, false, false, false, false,
                               mt, ms, mm, &nm, NULL);
  if (out_effect) {
    out_effect->prep_status = st;
    out_effect->rule = firing->rule;
    if (st == TC_PREP_OK) {
      out_effect->prepared = true;
      out_effect->nmake = nm;
      for (uint8_t i = 0; i < nm && i < 5; i++) {
        out_effect->make_terms[i]  = mt[i];
        out_effect->make_spaces[i] = ms[i];
        out_effect->make_marks[i]  = mm[i];
      }
    }
  }
  if (st != TC_PREP_OK) {
    if (out_refusal) *out_refusal = map_prep_status(st);
    return false;
  }
  return true;
}

bool tc_bridge_permitted(const TcPreparedStep *firing, const TcPreparedEffect *effect,
                         const TcAdmissionProfile *profile, TcRefusalReason *out_refusal) {
  if (out_refusal) *out_refusal = TC_REFUSE_NONE;
  if (!profile) {
    if (out_refusal) *out_refusal = TC_REFUSE_NO_PROFILE;
    return false;
  }
  if (!firing || !effect || !effect->prepared) {
    if (out_refusal) *out_refusal = effect ? map_prep_status(effect->prep_status) : TC_REFUSE_BAD_RULE;
    return false;
  }
  bool check_reach = profile->enforce_reach || firing->nseeds > 0;
  if (profile->enforce_absent || profile->enforce_count || profile->enforce_birth || check_reach) {
    int st = tc_eval_prepared_ex(firing,
                                 profile->enforce_absent,
                                 profile->enforce_count,
                                 profile->enforce_birth,
                                 check_reach,
                                 false, NULL, NULL, NULL, NULL, NULL);
    if (st != TC_PREP_OK) {
      if (out_refusal) *out_refusal = map_prep_status(st);
      return false;
    }
  }
  if (profile->permit && !profile->permit(profile->ctx, firing, effect)) {
    if (out_refusal) *out_refusal = TC_REFUSE_PROFILE_POLICY;
    return false;
  }
  return true;
}

#define TC_INCLUSION_MAGIC UINT64_C(0x5443494E434C5631) /* "TCINCLV1" */

static uint32_t profile_required_guards(const TcAdmissionProfile *p, int nseeds) {
  if (!p) return 0;
  uint32_t g = 0;
  if (p->enforce_absent) g |= TC_GUARD_BIT_ABSENT;
  if (p->enforce_count)  g |= TC_GUARD_BIT_COUNT;
  if (p->enforce_birth)  g |= TC_GUARD_BIT_BIRTH;
  if (p->enforce_reach || nseeds > 0) g |= TC_GUARD_BIT_REACH;
  return g;
}

static bool profiles_match(const TcAdmissionProfile *a, const TcAdmissionProfile *b) {
  if (!a || !b) return false;
  return a->enforce_absent == b->enforce_absent &&
         a->enforce_count  == b->enforce_count &&
         a->enforce_birth  == b->enforce_birth &&
         a->enforce_reach  == b->enforce_reach &&
         a->ctx            == b->ctx &&
         a->permit         == b->permit;
}

#ifndef TC_USE_CESTA_EXPORT
TcPreparedStep tc_event_firing(const TcAdmittedEvent *ev) {
  TcPreparedStep s = {0};
  if (!ev) return s;
  s.rule   = ev->firing.rule;
  s.dest   = ev->firing.dest;
  s.nseeds = ev->firing.nseeds;
  s.take   = ev->ntake > 0 ? ev->owned_take : NULL;
  s.keep   = ev->nkeep > 0 ? ev->owned_keep : NULL;
  s.inst   = ev->has_inst  ? ev->owned_inst : NULL;
  s.seeds  = ev->firing.nseeds > 0 ? ev->owned_seeds : NULL;
  return s;
}
#endif

TcBridgeOutcome tc_bridge_execute_candidate(
    const TcPreparedStep *firing,
    const TcAdmissionProfile *profile,
    TcPreparedEffect *out_effect,
    TcAdmittedEvent *out_event,
    TcAdmissionReceipt *out_receipt,
    TcRefusalReason *out_refusal) {
  if (out_event) memset(out_event, 0, sizeof(*out_event));
  if (out_receipt) memset(out_receipt, 0, sizeof(*out_receipt));
  if (out_refusal) *out_refusal = TC_REFUSE_NONE;

  /* 1. Phase 1: Prepare candidate effect BEFORE checking admission profile or guards */
  TcPreparedEffect eff;
  TcRefusalReason ref = TC_REFUSE_NONE;
  bool prep_ok = tc_bridge_prepare(firing, &eff, &ref);
  if (out_effect) *out_effect = eff;
  if (!prep_ok) {
    if (out_refusal) *out_refusal = ref;
    return TC_BRIDGE_REFUSED;
  }
  if (firing->nseeds < 0 || firing->nseeds > TC_VARS) {
    if (out_refusal) *out_refusal = TC_REFUSE_BAD_RULE;
    return TC_BRIDGE_REFUSED;
  }

  /* 2. Phase 2: Check permission under the explicit admission profile */
  if (!tc_bridge_permitted(firing, &eff, profile, &ref)) {
    if (out_refusal) *out_refusal = ref;
    return TC_BRIDGE_REFUSED;
  }

  /* Record pre-state built-in guard evidence before linear takes are consumed */
  uint32_t vguards = 0;
  if (profile->enforce_absent ||
      tc_eval_prepared_ex(firing, true, false, false, false, false, NULL, NULL, NULL, NULL, NULL) == TC_PREP_OK)
    vguards |= TC_GUARD_BIT_ABSENT;
  if (profile->enforce_count ||
      tc_eval_prepared_ex(firing, false, true, false, false, false, NULL, NULL, NULL, NULL, NULL) == TC_PREP_OK)
    vguards |= TC_GUARD_BIT_COUNT;
  if (profile->enforce_birth ||
      tc_eval_prepared_ex(firing, false, false, true, false, false, NULL, NULL, NULL, NULL, NULL) == TC_PREP_OK)
    vguards |= TC_GUARD_BIT_BIRTH;
  bool check_reach = profile->enforce_reach || firing->nseeds > 0;
  if (check_reach ||
      tc_eval_prepared_ex(firing, false, false, false, true, false, NULL, NULL, NULL, NULL, NULL) == TC_PREP_OK)
    vguards |= TC_GUARD_BIT_REACH;

  /* 3. Commit the admitted candidate to <K ; W> and issue receipt + event */
  Occ out_occ = 0;
  int st = tc_eval_prepared_ex(firing,
                               profile->enforce_absent,
                               profile->enforce_count,
                               profile->enforce_birth,
                               check_reach,
                               true, NULL, NULL, NULL, NULL, &out_occ);
  if (st != TC_PREP_OK || !out_occ) {
    if (out_refusal) *out_refusal = map_prep_status(st);
    return TC_BRIDGE_REFUSED;
  }

  TcAdmissionReceipt rec;
  memset(&rec, 0, sizeof(rec));
  rec.admitted = true;
  rec.rule     = firing->rule;
  rec.out      = out_occ;
  rec.out_term = tc_term(out_occ);
  for (int i = 0; i < 4; i++) {
    Occ ex = tc_last_extra(i);
    if (ex) rec.extra[rec.nextra++] = ex;
  }
  if (out_receipt) *out_receipt = rec;
  if (out_event) {
    uint8_t ntake = 0, nkeep = 0, nholes = 0;
    tc_rule_arity(firing->rule, &ntake, &nkeep, &nholes);
    out_event->ntake    = ntake;
    out_event->nkeep    = nkeep;
    out_event->nholes   = nholes;
    out_event->has_inst = (firing->inst != NULL);
    if (ntake > 0 && firing->take)
      memcpy(out_event->owned_take, firing->take, (size_t)ntake * sizeof(Occ));
    if (nkeep > 0 && firing->keep)
      memcpy(out_event->owned_keep, firing->keep, (size_t)nkeep * sizeof(Occ));
    if (firing->inst && nholes > 0)
      memcpy(out_event->owned_inst, firing->inst, (size_t)nholes * sizeof(Term));
    if (firing->nseeds > 0 && firing->seeds)
      memcpy(out_event->owned_seeds, firing->seeds, (size_t)firing->nseeds * sizeof(Term));
    out_event->firing.rule     = firing->rule;
    out_event->firing.dest     = firing->dest;
    out_event->firing.nseeds   = firing->nseeds;
    out_event->firing          = tc_event_firing(out_event);
    out_event->prepared        = eff;
    out_event->owned_profile   = *profile;
    out_event->profile         = profile;
    out_event->verified_guards = vguards;
    out_event->receipt         = rec;
  }
  return TC_BRIDGE_ADMITTED;
}

bool tc_admission_inclusion_init(TcAdmissionInclusion *out_inc,
                                 const TcAdmissionProfile *src_profile,
                                 const TcAdmissionProfile *dst_profile,
                                 bool policy_inclusion_witnessed) {
  if (out_inc) memset(out_inc, 0, sizeof(*out_inc));
  if (!out_inc || !src_profile || !dst_profile) return false;
  uint32_t src_g = profile_required_guards(src_profile, 0);
  uint32_t dst_g = profile_required_guards(dst_profile, 0);
  if ((src_g & dst_g) != dst_g) return false;
  if (dst_profile->permit != NULL) {
    bool same_policy = (src_profile->permit == dst_profile->permit &&
                        src_profile->ctx == dst_profile->ctx);
    if (!same_policy && !policy_inclusion_witnessed) return false;
  }
  out_inc->magic           = TC_INCLUSION_MAGIC;
  out_inc->src_profile     = *src_profile;
  out_inc->dst_profile     = *dst_profile;
  out_inc->required_guards = profile_required_guards(dst_profile, 0);
  return true;
}

bool tc_event_restrict_included(const TcAdmittedEvent *src,
                                const TcAdmissionInclusion *inc,
                                TcAdmittedEvent *dst) {
  if (!src || !src->receipt.admitted || !src->prepared.prepared || !inc || !dst)
    return false;
  if (inc->magic != TC_INCLUSION_MAGIC) return false;
  if (!profiles_match(&src->owned_profile, &inc->src_profile)) return false;
  uint32_t req = profile_required_guards(&inc->dst_profile, src->firing.nseeds);
  if ((src->verified_guards & req) != req) return false;
  *dst = *src;
  dst->owned_profile = inc->dst_profile;
  dst->profile       = &dst->owned_profile;
  dst->firing        = tc_event_firing(dst);
  return true;
}

bool tc_event_restrict(const TcAdmittedEvent *src,
                       const TcAdmissionProfile *target_profile,
                       TcAdmittedEvent *dst) {
  if (!src || !src->receipt.admitted || !src->prepared.prepared || !target_profile || !dst)
    return false;
  uint32_t req = profile_required_guards(target_profile, src->firing.nseeds);
  if ((src->verified_guards & req) != req) return false;
  TcPreparedStep step_view = tc_event_firing(src);
  bool same_policy = (src->owned_profile.permit == target_profile->permit &&
                      src->owned_profile.ctx == target_profile->ctx);
  if (target_profile->permit && !same_policy &&
      !target_profile->permit(target_profile->ctx, &step_view, &src->prepared))
    return false;
  *dst = *src;
  dst->owned_profile = *target_profile;
  dst->profile       = target_profile;
  dst->firing        = tc_event_firing(dst);
  return true;
}

TcBridgeOutcome tc_bridge_step_cursor(
    TcCandidateCursor *cursor,
    const TcAdmissionProfile *profile,
    TcBridgeBudget *budget,
    TcAdmittedEvent *out_event,
    TcAdmissionReceipt *out_receipt) {
  if (out_event) memset(out_event, 0, sizeof(*out_event));
  if (out_receipt) memset(out_receipt, 0, sizeof(*out_receipt));
  if (budget) {
    budget->candidates_inspected = 0;
    budget->last_refusal = TC_REFUSE_NONE;
  }
  if (!profile) {
    if (budget) budget->last_refusal = TC_REFUSE_NO_PROFILE;
    return TC_BRIDGE_REFUSED;
  }
  if (!cursor || !cursor->next) {
    return (budget && budget->has_unresolved_work) ? TC_BRIDGE_UNRESOLVED : TC_BRIDGE_REFUSED;
  }

  uint32_t seen = 0;
  TcRefusalReason last_ref = TC_REFUSE_NONE;
  TcPreparedStep cand;
  for (;;) {
    if (budget && budget->max_candidates > 0 && seen >= budget->max_candidates) {
      budget->candidates_inspected = seen;
      budget->last_refusal = last_ref;
      return TC_BRIDGE_BUDGET_EXHAUSTED;
    }
    if (!cursor->next(cursor->ctx, &cand)) break;
    seen++;
    TcPreparedEffect eff;
    TcRefusalReason ref = TC_REFUSE_NONE;
    TcBridgeOutcome out = tc_bridge_execute_candidate(
        &cand, profile, &eff, out_event, out_receipt, &ref);
    if (out == TC_BRIDGE_ADMITTED) {
      if (budget) {
        budget->candidates_inspected = seen;
        budget->last_refusal = TC_REFUSE_NONE;
      }
      return TC_BRIDGE_ADMITTED;
    }
    last_ref = ref;
  }
  if (budget) {
    budget->candidates_inspected = seen;
    budget->last_refusal = last_ref;
    if (budget->has_unresolved_work) return TC_BRIDGE_UNRESOLVED;
  }
  return TC_BRIDGE_REFUSED;
}

/* ---- CeTTa Atom Spine Interning & Recorded Candidate Stream Adapter ---- */
bool tc_cetta_intern_init(TcCettaIntern *tab, uint16_t sort_name, uint16_t sort_atom) {
  if (!tab) return false;
  memset(tab, 0, sizeof(*tab));
  tab->sort_atom = sort_atom;
  Binder b_nam[1]  = { { sort_name, 0, 0 } };
  Binder b_at2[2]  = { { sort_atom, 0, 0 }, { sort_atom, 0, 0 } };
  tab->con_sym  = tc_con(sort_atom, 0, 1, b_nam);
  tab->con_var  = tc_con(sort_atom, 0, 1, b_nam);
  tab->con_pair = tc_con(sort_atom, 0, 2, b_at2);
  return tab->con_sym >= 0 && tab->con_var >= 0 && tab->con_pair >= 0;
}

static Term intern_cetta_name(TcCettaIntern *tab, uint16_t sort_name, const char *s) {
  if (!s) s = "";
  for (uint32_t i = 0; i < tab->nsyms; i++) {
    if (strcmp(tab->sym_names[i], s) == 0) return tab->sym_terms[i];
  }
  if (tab->nsyms >= 256) return 0;
  uint32_t idx = tab->nsyms++;
  strncpy(tab->sym_names[idx], s, 63);
  tab->sym_names[idx][63] = '\0';
  tab->sym_terms[idx] = tc_name(sort_name, tc_fresh_name());
  return tab->sym_terms[idx];
}

Term tc_cetta_intern_atom(TcCettaIntern *tab, const TcCettaAtomView *atom) {
  if (!tab || !atom) return 0;
  uint16_t s_name = tc_sort_of(tab->nsyms ? tab->sym_terms[0] : 0);
  if (!s_name) s_name = 1; /* first registered sort S_NAME */
  if (atom->kind == CETTA_ATOM_SYM) {
    Term nm = intern_cetta_name(tab, s_name, atom->text);
    return nm ? tc_app(tab->con_sym, &nm) : 0;
  }
  if (atom->kind == CETTA_ATOM_VAR) {
    Term nm = intern_cetta_name(tab, s_name, atom->text);
    return nm ? tc_app(tab->con_var, &nm) : 0;
  }
  if (atom->kind == CETTA_ATOM_EXPR) {
    if (atom->arity == 0 || !atom->children) {
      Term nm = intern_cetta_name(tab, s_name, "()");
      return nm ? tc_app(tab->con_sym, &nm) : 0;
    }
    Term cur = tc_cetta_intern_atom(tab, &atom->children[0]);
    for (uint32_t i = 1; cur && i < atom->arity; i++) {
      Term arg = tc_cetta_intern_atom(tab, &atom->children[i]);
      if (!arg) return 0;
      Term pair[2] = { cur, arg };
      cur = tc_app(tab->con_pair, pair);
    }
    return cur;
  }
  return 0;
}

static bool recorded_stream_next(void *ctx, TcPreparedStep *out) {
  TcCettaRecordedStream *st = (TcCettaRecordedStream *)ctx;
#ifdef TC_USE_CESTA_EXPORT
  if (!st || !out || !st->candidates || st->pos >= st->len) return false;
  const TcPreparedStep *candidate = tc_cetta_cursor_advance(
      &st->candidates[st->pos], &st->pos, st->len);
  if (!candidate) return false;
  *out = *candidate;
#else
  if (!st || !out || st->pos >= st->len) return false;
  *out = st->candidates[st->pos++];
#endif
  return true;
}

void tc_cetta_stream_cursor_init(TcCettaRecordedStream *stream,
                                 const TcPreparedStep *candidates, size_t len,
                                 TcCandidateCursor *out_cursor) {
  if (!stream || !out_cursor) return;
  stream->candidates = candidates;
  stream->len = len;
  stream->pos = 0;
  out_cursor->ctx  = stream;
  out_cursor->next = recorded_stream_next;
}
