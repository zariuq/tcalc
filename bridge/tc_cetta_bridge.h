#pragma once
/* Modular tcalc <-> CeTTa transform bridge.
   This API follows the effect/admission distinction in the mathematical
   presentation; a formal C-to-calculus refinement is still required:
     Execute : if prepared(s, f, t), permitted(s, f) then (Request s f) ~> (At t);
   - EffectCore.Prepares (TcPreparedEffect): defined and computed before admission
     guards (absent, count, birth, reach) or policy predicates are checked.
   - EffectCore.Admission (TcAdmissionProfile): explicit permission predicate over
     prepared candidates; the general core has no hidden evaluation default.
   - EffectCore.Event (TcAdmittedEvent): bundles firing, prepared effect, admission
     profile, and TcAdmissionReceipt, with Event.restrict (tc_event_restrict).
   - Distinct executor outcomes (TcBridgeOutcome):
       TC_BRIDGE_ADMITTED         (1)  — prepared + permitted + committed with receipt
       TC_BRIDGE_REFUSED          (0)  — candidate refused (no receipt issued)
       TC_BRIDGE_UNRESOLVED      (-1)  — cursor exhausted with unresolved work remaining
       TC_BRIDGE_BUDGET_EXHAUSTED (-2) — candidate/step budget reached before completion */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "../tcalc.h"

typedef enum {
  TC_BRIDGE_BUDGET_EXHAUSTED = -2,
  TC_BRIDGE_UNRESOLVED       = -1,
  TC_BRIDGE_REFUSED          =  0,
  TC_BRIDGE_ADMITTED         =  1
} TcBridgeOutcome;

typedef enum {
  TC_REFUSE_NONE            = 0,
  TC_REFUSE_NO_PROFILE      = 1,
  TC_REFUSE_BAD_RULE        = 2,
  TC_REFUSE_ABSENT_RESOURCE = 3,
  TC_REFUSE_DOUBLE_TAKE     = 4,
  TC_REFUSE_SHAPE_UNIFY     = 5,
  TC_REFUSE_ABSENT_GUARD    = 6,
  TC_REFUSE_COUNT_GUARD     = 7,
  TC_REFUSE_BIRTH_GUARD     = 8,
  TC_REFUSE_REACH_GUARD     = 9,
  TC_REFUSE_PROFILE_POLICY  = 10
} TcRefusalReason;

/* EffectCore.Prepares: prepared candidate effect, computed before guards are checked. */
typedef struct {
  bool    prepared;
  int     prep_status;       /* TC_PREP_* status from tc_eval_prepared_ex */
  int     rule;
  uint8_t nmake;
  Term    make_terms[5];     /* primary make (0) + up to 4 make_extra (1..4) */
  Term    make_spaces[5];    /* target space Term for each made occurrence */
  uint8_t make_marks[5];     /* 1 iff made occurrence is a birth marker */
} TcPreparedEffect;

/* Explicit admission profile over prepared candidates.
   permit must be a pure predicate of its arguments and immutable context. It
   must not read or mutate live kernel state, advance fresh-name counters, or
   retain transient arguments. Kernel calls and preparation/admission/commit
   must be externally serialized: this API supplies no concurrent transaction
   or snapshot mechanism. Built-in state-dependent guards are handled by the
   kernel, with their pre-state results retained in verified_guards. */
typedef struct TcAdmissionProfile {
  const char *name;
  bool enforce_absent;
  bool enforce_count;
  bool enforce_birth;
  bool enforce_reach;
  void *ctx;
  bool (*permit)(void *ctx, const TcPreparedStep *firing, const TcPreparedEffect *effect);
} TcAdmissionProfile;

/* Bitmask of pre-state built-in guards verified before commit. */
enum {
  TC_GUARD_BIT_ABSENT = 1u << 0,
  TC_GUARD_BIT_COUNT  = 1u << 1,
  TC_GUARD_BIT_BIRTH  = 1u << 2,
  TC_GUARD_BIT_REACH  = 1u << 3
};

/* Admitted transition record retaining candidate, prepared effect, profile,
   and receipt. Firing arrays (take, keep, inst, seeds) and the admission
   profile descriptor are owned by value inside TcAdmittedEvent so that events
   may be safely returned or copied across stack frames without dangling slice
   pointers. Use tc_event_firing(ev) after moving/copying an event by value to
   obtain a TcPreparedStep view bound to ev's current address. */
typedef struct {
  TcPreparedStep            firing;
  TcPreparedEffect          prepared;
  const TcAdmissionProfile *profile;
  TcAdmissionProfile        owned_profile;
  uint32_t                  verified_guards;
  TcAdmissionReceipt        receipt;
  uint8_t                   ntake;
  uint8_t                   nkeep;
  uint8_t                   nholes;
  bool                      has_inst;
  Occ                       owned_take[4];
  Occ                       owned_keep[TC_HYPS];
  Term                      owned_inst[TC_VARS];
  Term                      owned_seeds[TC_VARS];
} TcAdmittedEvent;

/* Witnessed inclusion capability (Lean Event.restrict): certifies that any
   firing permitted by src_profile (with required_guards verified in pre-state)
   is permitted by dst_profile, transporting events without re-running policy
   callbacks in the post-state. */
typedef struct {
  uint64_t                  magic;
  TcAdmissionProfile        src_profile;
  TcAdmissionProfile        dst_profile;
  uint32_t                  required_guards;
} TcAdmissionInclusion;

/* Executor budget and unresolved-work tracker. */
typedef struct {
  uint32_t max_candidates;       /* 0 = unlimited; > 0 caps candidates inspected */
  uint32_t candidates_inspected; /* output: number of candidates inspected */
  bool     has_unresolved_work;  /* true iff caller has remaining obligations */
  TcRefusalReason last_refusal;  /* refusal reason of the last refused candidate */
} TcBridgeBudget;

/* Standard constructor for EffectCore.guardAdmission. */
TcAdmissionProfile tc_admission_guard_profile(bool enforce_reach);

/* Constructor for custom admission profiles (e.g. Presentation.fixture permit). */
TcAdmissionProfile tc_admission_custom_profile(
    const char *name,
    bool enforce_absent, bool enforce_count,
    bool enforce_birth, bool enforce_reach,
    void *ctx,
    bool (*permit)(void *ctx, const TcPreparedStep *firing, const TcPreparedEffect *effect));

/* Phase 1 (prepared(s, f, t)): compute the prepared effect of a firing candidate
   without mutating <K ; W> and before checking admission guards. */
bool tc_bridge_prepare(const TcPreparedStep *firing, TcPreparedEffect *out_effect,
                       TcRefusalReason *out_refusal);

/* Phase 2 (permitted(s, f)): check whether an already-prepared candidate is
   permitted by the given admission profile without mutating <K ; W>. */
bool tc_bridge_permitted(const TcPreparedStep *firing, const TcPreparedEffect *effect,
                         const TcAdmissionProfile *profile, TcRefusalReason *out_refusal);

/* Execute a single candidate under an explicit admission profile:
   populates out_effect (whenever prepared holds) and out_event + out_receipt
   (only when both prepared and permitted hold). */
TcBridgeOutcome tc_bridge_execute_candidate(
    const TcPreparedStep *firing,
    const TcAdmissionProfile *profile,
    TcPreparedEffect *out_effect,
    TcAdmittedEvent *out_event,
    TcAdmissionReceipt *out_receipt,
    TcRefusalReason *out_refusal);

/* Materialize a TcPreparedStep view pointing into ev's owned firing arrays.
   Safe even after ev has been returned or copied by value across stack frames. */
TcPreparedStep tc_event_firing(const TcAdmittedEvent *ev);

/* Issue a witnessed inclusion capability from src_profile to dst_profile.
   For built-in guard profiles (or profiles sharing the same pure callback + ctx),
   succeeds automatically; if dst_profile adds or changes a custom policy callback,
   requires policy_inclusion_witnessed == true. */
bool tc_admission_inclusion_init(TcAdmissionInclusion *out_inc,
                                 const TcAdmissionProfile *src_profile,
                                 const TcAdmissionProfile *dst_profile,
                                 bool policy_inclusion_witnessed);

/* Capability-based Event.restrict (matching Lean's Event.restrict): transports
   an admitted event from inc->src_profile to inc->dst_profile using pre-state
   guard evidence and the inclusion witness without re-running callbacks in the
   post-state. */
bool tc_event_restrict_included(const TcAdmittedEvent *src,
                                const TcAdmissionInclusion *inc,
                                TcAdmittedEvent *dst);

/* Transfer an authentic event to a target profile, preserving its source
   evidence. Built-in target requirements use recorded pre-state guard bits;
   target callbacks inspect the event's owned firing snapshot via tc_event_firing.
   Success qualifies this event, not a universal inclusion between profiles.
   A false return means this transfer is unsupported or its predicate failed. */
bool tc_event_restrict(const TcAdmittedEvent *src,
                       const TcAdmissionProfile *target_profile,
                       TcAdmittedEvent *dst);

/* Evaluate a candidate cursor under an explicit admission profile and budget,
   distinguishing TC_BRIDGE_ADMITTED, TC_BRIDGE_REFUSED, TC_BRIDGE_UNRESOLVED,
   and TC_BRIDGE_BUDGET_EXHAUSTED. */
TcBridgeOutcome tc_bridge_step_cursor(
    TcCandidateCursor *cursor,
    const TcAdmissionProfile *profile,
    TcBridgeBudget *budget,
    TcAdmittedEvent *out_event,
    TcAdmissionReceipt *out_receipt);

/* ---- CeTTa Atom Spine Interning & Recorded Candidate Stream Adapter ---- */
typedef enum {
  CETTA_ATOM_SYM  = 1,
  CETTA_ATOM_VAR  = 2,
  CETTA_ATOM_EXPR = 3
} TcCettaAtomKind;

typedef struct TcCettaAtomView {
  TcCettaAtomKind         kind;
  const char             *text;   /* symbol or variable name */
  uint32_t                arity;
  const struct TcCettaAtomView *children;
} TcCettaAtomView;

typedef struct {
  uint16_t sort_atom;
  int      con_sym;     /* unary: S_NAME -> S_ATOM */
  int      con_var;     /* unary: S_NAME -> S_ATOM */
  int      con_pair;    /* binary: (head, arg) spine application */
  uint32_t nsyms;
  char     sym_names[256][64];
  Term     sym_terms[256];
} TcCettaIntern;

bool tc_cetta_intern_init(TcCettaIntern *tab, uint16_t sort_name, uint16_t sort_atom);
Term tc_cetta_intern_atom(TcCettaIntern *tab, const TcCettaAtomView *atom);

typedef struct {
  const TcPreparedStep *candidates;
  size_t                len;
  size_t                pos;
} TcCettaRecordedStream;

/* Cesta provider: advance a bounded position and borrow the supplied candidate.
 * Position is exclusively borrowed and must not overlap the candidate or its
 * referenced inputs. The candidate and those inputs remain live while used.
 * Available in the TC_USE_CESTA_EXPORT build; the public cursor ABI is unchanged. */
const TcPreparedStep *tc_cetta_cursor_advance(const TcPreparedStep *candidate,
                                            size_t *position, size_t limit);

void tc_cetta_stream_cursor_init(TcCettaRecordedStream *stream,
                                 const TcPreparedStep *candidates, size_t len,
                                 TcCandidateCursor *out_cursor);
