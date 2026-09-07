/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Computability.RE
import Scott1976.DataTypesAsLattices.Lambda

/-!
# Scott 1976, §2 — computability and the definability theorem

Theorem 2.6: for a continuous `f`, computability (the graph is r.e.) is
equivalent both to combinatory definability of its graph and to closed
LAMBDA-definability.  The appendix proves the key converse
`IsRE u → IsCombinatory u` by realizing primitive recursion and enumerating
an arbitrary r.e. set.
-/

set_option maxHeartbeats 2000000

namespace Scott1976.DataTypesAsLattices

/-- Recursively enumerable subsets of `ω`, as elements of `Pω`. -/
def IsRE (u : Pomega) : Prop :=
  REPred fun n : ℕ => n ∈ u

/-- **Scott 1976, §2, Definition.** A continuous `k`-ary map is computable
when membership in its values on finite arguments is r.e. Unary case: -/
def IsComputable (f : Pomega → Pomega) : Prop :=
  IsScottContinuous f ∧ IsRE (graph f)

/-- Closed LAMBDA-definable elements (empty environment). -/
def IsLambdaDefinable (u : Pomega) : Prop :=
  ∃ t : Term, interp t (fun _ => botElem) = u

/-- Combinatory elements are LAMBDA-definable (converse of Theorem 2.4). -/
theorem combinatory_isLambdaDefinable {u : Pomega} (hu : IsCombinatory u) :
    IsLambdaDefinable u := by
  induction hu with
  | zero => exact ⟨.zero, rfl⟩
  | suc =>
    refine ⟨.lam 0 (.succ (.var 0)), ?_⟩
    simp [interp, sucC, envSet, Function.update]
  | pred =>
    refine ⟨.lam 0 (.pred (.var 0)), ?_⟩
    simp [interp, predC, envSet, Function.update]
  | cond =>
    refine ⟨.lam 0 (.lam 1 (.lam 2
        (.cond (.var 2) (.var 0) (.var 1)))), ?_⟩
    simp [interp, condC, envSet, Function.update]
  | K =>
    refine ⟨.lam 0 (.lam 1 (.var 0)), ?_⟩
    simp [interp, Kcomb, envSet, Function.update]
  | S =>
    refine ⟨.lam 0 (.lam 1 (.lam 2
        (.app (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2))))), ?_⟩
    simp [interp, Scomb, envSet, Function.update]
  | app _ _ iu iv =>
    obtain ⟨t, ht⟩ := iu
    obtain ⟨s, hs⟩ := iv
    exact ⟨.app t s, by simp [interp, ht, hs]⟩

/-- LAMBDA-definable maps (in one free variable) are continuous, so
clause (iii) of Theorem 2.6 lands in the setting of (i)–(ii). -/
theorem theorem_2_6_lambda_continuous (t : Term) :
    IsScottContinuous (fun v => interp t (envSet (fun _ => botElem) 0 v)) :=
  theorem_2_1 t (fun _ => botElem) 0

/-- Combinatory elements are generated from the six constants, matching
the LAMBDA-definable closed terms of Theorem 2.4. -/
theorem theorem_2_6_combinatory_zero : IsLambdaDefinable zeroC :=
  ⟨Term.zero, rfl⟩

theorem REPred.empty : REPred fun _ : ℕ => False := by
  unfold REPred
  refine (Partrec.none (α := ℕ) (σ := Unit)).of_eq fun _ => ?_
  ext
  simp [Part.assert]

theorem REPred.true {α} [Primcodable α] : REPred fun _ : α => True := by
  unfold REPred
  refine (Decidable.Partrec.const' (Part.some ())).of_eq fun _ => ?_
  ext
  simp [Part.assert]

theorem REPred.comp {α β} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : REPred p) {f : α → β} (hf : Computable f) :
    REPred fun a => p (f a) :=
  Partrec.comp hp hf

theorem REPred.and {α} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∧ q a := by
  refine (hp.bind (hq.comp Computable.fst).to₂).of_eq fun a => ?_
  ext
  simp [Part.bind_eq_bind, Part.assert]

theorem IsRE.bot : IsRE botElem :=
  REPred.empty.of_eq fun n => by simp [botElem]

theorem IsRE.top : IsRE topElem :=
  REPred.true.of_eq fun n => by simp [topElem]

/-- Named `numeral` so it does not shadow `ofNat`. -/
theorem IsRE.numeral (k : ℕ) : IsRE (ofNat k) := by
  have : ComputablePred fun n : ℕ => n = k :=
    ⟨inferInstance, (Primrec.beq.comp Primrec.id (Primrec.const k)).to_comp⟩
  exact REPred.of_eq this.to_re fun n => by simp [ofNat]

theorem IsRE.zeroC : IsRE zeroC :=
  IsRE.numeral 0

/-- **Scott 1976, Theorem 2.6, r.e. direction for numerals.** -/
theorem theorem_2_6_ofNat_isRE (n : ℕ) : IsCombinatory (ofNat n) → IsRE (ofNat n) :=
  fun _ => IsRE.numeral n

theorem primrec_twoPow : Primrec fun k : ℕ => 2 ^ k :=
  (Primrec.nat_rec' (f := id) (g := fun _ => (1 : ℕ))
    (h := fun (_ : ℕ) (p : ℕ × ℕ) => p.2 * 2)
    Primrec.id (Primrec.const 1)
    (show Primrec fun q : ℕ × ℕ × ℕ => q.2.2 * 2 from
      Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2))).of_eq
    fun k => by
      induction k with
      | zero => simp
      | succ k ih =>
        change (Nat.rec 1 (fun n IH => (n, IH).2 * 2) k) * 2 = 2 ^ (k + 1)
        have ih' : Nat.rec 1 (fun n IH => (n, IH).2 * 2) k = 2 ^ k := by
          simpa [id] using ih
        rw [ih', Nat.pow_succ, Nat.mul_comm]

theorem primrec_testBit : Primrec₂ fun n k : ℕ => n.testBit k :=
  (Primrec.eq.decide.comp
    (Primrec.nat_mod.comp
      (Primrec.nat_div.comp Primrec.fst (primrec_twoPow.comp Primrec.snd))
      (Primrec.const 2))
    (Primrec.const 1)).of_eq fun p =>
      Nat.testBit_eq_decide_div_mod_eq.symm

theorem primrec_pair : Primrec₂ pair :=
  (Primrec.nat_add.comp
    (Primrec.nat_div.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_add.comp Primrec.fst Primrec.snd)
        (Primrec.succ.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)))
      (Primrec.const 2))
    Primrec.snd).of_eq fun _ => rfl

theorem REPred.or {α} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∨ q a := by
  obtain ⟨k, hk, H⟩ := Partrec.merge' hp hq
  have hg : Computable₂ fun (_ : α) (_ : Unit) => () :=
    (Computable.const (α := α × Unit) ()).to₂
  refine Partrec.of_eq (hk.map hg) fun a => ?_
  ext
  constructor
  · intro hu
    rw [Part.mem_map_iff] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    have hx' := (H a).1 x hx
    have hpq : p a ∨ q a := by
      cases hx' with
      | inl h =>
        exact Or.inl (Part.mem_assert_iff.1 h).1
      | inr h =>
        exact Or.inr (Part.mem_assert_iff.1 h).1
    exact Part.mem_assert_iff.2 ⟨hpq, Part.mem_some_iff.2 hxu.symm⟩
  · intro hu
    have hpq : p a ∨ q a := (Part.mem_assert_iff.1 hu).1
    have hd : (k a).Dom := (H a).2.mpr <|
      hpq.imp (fun h => ⟨h, trivial⟩) (fun h => ⟨h, trivial⟩)
    rw [Part.mem_map_iff]
    exact ⟨(), ⟨hd, rfl⟩, (Part.mem_some_iff.1 (Part.mem_assert_iff.1 hu).2).symm⟩

theorem IsRE.union {u v : Pomega} (hu : IsRE u) (hv : IsRE v) : IsRE (u ∪ v) :=
  REPred.of_eq (REPred.or hu hv) fun _ => Iff.rfl

theorem IsRE.ofFinset (s : Finset ℕ) : IsRE (s : Set ℕ) := by
  induction s using Finset.induction with
  | empty =>
    simpa [botElem] using IsRE.bot
  | insert k s _hk ih =>
    have h : (insert k s : Set ℕ) = ofNat k ∪ (s : Set ℕ) := by
      ext; simp [ofNat]
    simpa [h] using IsRE.union (IsRE.numeral k) ih

/-- Finite `e j` is r.e. Named `of_e` so it does not shadow `e`. -/
theorem IsRE.of_e (j : ℕ) : IsRE (e j) := by
  let s := (Finset.range (j + 1)).filter (fun k => j.testBit k)
  have hs : (s : Set ℕ) = e j := by
    ext n
    constructor
    · intro hn
      simp [s, Finset.mem_filter] at hn
      exact mem_e.mpr hn.2
    · intro hn
      simp [s, Finset.mem_filter, Finset.mem_range, mem_e.mp hn,
        Nat.lt_succ_of_le (mem_e_le hn)]
  simpa [hs] using IsRE.ofFinset s

theorem IsRE.predSet {x : Pomega} (hx : IsRE x) : IsRE (predSet x) :=
  REPred.of_eq (hx.comp Primrec.succ.to_comp) fun _ => Iff.rfl

theorem IsRE.succSet {x : Pomega} (hx : IsRE x) : IsRE (succSet x) := by
  have heq0 : ComputablePred fun k : ℕ => k = 0 :=
    ⟨inferInstance, (Primrec.eq.decide.comp Primrec.id (Primrec.const 0)).to_comp⟩
  have hne : ComputablePred fun k : ℕ => k ≠ 0 := heq0.not
  have hand : REPred fun k : ℕ => k ≠ 0 ∧ k.pred ∈ x :=
    REPred.and hne.to_re (hx.comp Primrec.pred.to_comp)
  exact _root_.REPred.of_eq hand (fun k =>
    ⟨fun h => ⟨k.pred, h.2, (Nat.succ_pred_eq_of_ne_zero h.1).symm⟩,
     fun h => by
       obtain ⟨n, hn, hk⟩ := h
       cases k with
       | zero => cases hk
       | succ k => exact ⟨Nat.succ_ne_zero k, by cases hk; exact hn⟩⟩)

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Projection of an r.e. binary predicate, by dovetailing `Code.evaln`. -/
theorem REPred.exists {p : ℕ → ℕ → Prop}
    (hp : REPred fun q : ℕ × ℕ => p q.1 q.2) :
    REPred fun n => ∃ m, p n m := by
  have hnat : Nat.Partrec fun k : ℕ =>
      Part.bind (decode₂ (ℕ × ℕ) k) fun q : ℕ × ℕ =>
        (Part.assert (p q.1 q.2) fun _ => Part.some ()).map encode :=
    (Partrec.bind_decode₂_iff
      (f := fun q : ℕ × ℕ => Part.assert (p q.1 q.2) fun _ => Part.some ())).mp hp
  obtain ⟨c, hc⟩ := Code.exists_code.mp hnat
  have hfn : Computable₂ fun n k : ℕ =>
      (evaln k.unpair.2 c (encode (n, k.unpair.1))).map fun _ : ℕ => () := by
    refine (Primrec.option_map ?_ (Primrec.const ()).to₂).to_comp
    exact primrec_evaln.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
          (Primrec.const c))
        (Primrec.encode.comp
          (Primrec.pair Primrec.fst
            (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
  have hr : REPred fun n =>
      (Nat.rfindOpt fun k =>
        (evaln k.unpair.2 c (encode (n, k.unpair.1))).map fun _ : ℕ => ()).Dom :=
    Partrec.dom_re (Partrec.rfindOpt hfn)
  refine _root_.REPred.of_eq hr fun n => ?_
  constructor
  · intro hdom
    rw [Nat.rfindOpt_dom] at hdom
    obtain ⟨k, u, hu⟩ := hdom
    cases hopt : evaln k.unpair.2 c (encode (n, k.unpair.1)) with
    | none =>
      rw [hopt] at hu
      cases hu
    | some val =>
      have hin : val ∈ evaln k.unpair.2 c (encode (n, k.unpair.1)) := by
        rw [hopt]; rfl
      have hsound : val ∈ Code.eval c (encode (n, k.unpair.1)) :=
        evaln_sound hin
      rw [hc] at hsound
      rw [Part.mem_bind_iff] at hsound
      obtain ⟨q, hq, hv⟩ := hsound
      have hqe : decode₂ (ℕ × ℕ) (encode (n, k.unpair.1)) = some q := by
        simpa using hq
      have hq' : q = (n, k.unpair.1) :=
        Option.some_inj.mp (hqe.symm.trans (decode₂_encode (n, k.unpair.1)))
      subst hq'
      rw [Part.mem_map_iff] at hv
      obtain ⟨u, hu, _⟩ := hv
      exact ⟨k.unpair.1, (Part.mem_assert_iff.mp hu).1⟩
  · intro ⟨m, hm⟩
    have hmem : encode () ∈ Code.eval c (encode (n, m)) := by
      rw [hc, Part.mem_bind_iff]
      refine ⟨(n, m), ?_, ?_⟩
      · change (n, m) ∈ (decode₂ (ℕ × ℕ) (encode (n, m)) : Part (ℕ × ℕ))
        rw [decode₂_encode]
        exact Part.mem_some_iff.mpr rfl
      · rw [Part.mem_map_iff]
        exact ⟨(), Part.mem_assert_iff.mpr ⟨hm, Part.mem_some_iff.mpr rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := evaln_complete.mp hmem
    have hs' : evaln s c (Nat.pair n m) = some (encode ()) := hs
    refine (Nat.rfindOpt_dom (f := fun k =>
      (evaln k.unpair.2 c (encode (n, k.unpair.1))).map fun _ => ())).mpr
      ⟨Nat.pair m s, (), ?_⟩
    simp [Nat.unpair_pair, hs']

theorem IsRE.pair_mem {u : Pomega} (hu : IsRE u) :
    REPred fun q : ℕ × ℕ => pair q.1 q.2 ∈ u :=
  hu.comp primrec_pair.to_comp

theorem IsRE.hasZero {z : Pomega} (hz : IsRE z) : REPred fun _ : ℕ => 0 ∈ z :=
  hz.comp (Computable.const 0)

theorem IsRE.hasPos {z : Pomega} (hz : IsRE z) : REPred fun _ : ℕ => ∃ k, k + 1 ∈ z :=
  _root_.REPred.of_eq
    (REPred.exists (p := fun _ k => k + 1 ∈ z)
      (hz.comp (Primrec.succ.to_comp.comp Computable.snd)))
    fun _ => Iff.rfl

theorem IsRE.condSet {z x y : Pomega} (hz : IsRE z) (hx : IsRE x) (hy : IsRE y) :
    IsRE (condSet z x y) := by
  have hleft : REPred fun n => n ∈ x ∧ 0 ∈ z :=
    REPred.and hx (IsRE.hasZero hz)
  have hright : REPred fun n => n ∈ y ∧ ∃ k, k + 1 ∈ z :=
    REPred.and hy (IsRE.hasPos hz)
  exact _root_.REPred.of_eq (REPred.or hleft hright) fun n => Iff.rfl

theorem IsRE.dcondSet {z x y : Pomega} (hz : IsRE z) (hx : IsRE x) (hy : IsRE y) :
    IsRE (dcondSet z x y) :=
  IsRE.condSet hz (IsRE.condSet hz hx IsRE.top) (IsRE.condSet hz IsRE.top hy)

theorem primrecPred_bool {α} [Primcodable α] {f : α → Bool} (hf : Primrec f) :
    PrimrecPred fun a => f a = true :=
  Primrec.eq.comp hf (Primrec.const true)

theorem primrecRel_testBit : PrimrecRel fun n k : ℕ => n.testBit k = true :=
  primrecPred_bool (f := fun p : ℕ × ℕ => p.1.testBit p.2) primrec_testBit

theorem primrec_succ_sq : Primrec fun k : ℕ => (k + 1) * (k + 1) :=
  Primrec.nat_mul.comp (Primrec.succ.comp Primrec.id) (Primrec.succ.comp Primrec.id)

/-- Common-stage certificate: a finite family of r.e. facts all halt at one `evaln` bound. -/
theorem primrecPred_common_stage (c : Code) :
    PrimrecPred fun p : ℕ × ℕ =>
      ∀ k < p.1, p.1.testBit k = false ∨ (evaln p.2 c k).isSome = true := by
  have heval : Primrec fun q : ℕ × ℕ => evaln q.2 c q.1 :=
    primrec_evaln.comp <|
      Primrec.pair (Primrec.pair Primrec.snd (Primrec.const c)) Primrec.fst
  have hR : PrimrecRel fun k q : ℕ =>
      q.unpair.1.testBit k = false ∨ (evaln q.unpair.2 c k).isSome = true :=
    ((primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)).not.or
      (primrecPred_bool (Primrec.option_isSome.comp
        (primrec_evaln.comp <|
          Primrec.pair
            (Primrec.pair
              (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
              (Primrec.const c))
            Primrec.fst)))).of_eq fun p => by
      simp [Bool.not_eq_true]
  refine (hR.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simp [Nat.unpair_pair]

theorem eSubset_iff_stage {x : Pomega} {c : Code}
    (hc : Code.eval c = fun k => Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ))
    (n : ℕ) :
    e n ⊆ x ↔ ∃ s, ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true := by
  constructor
  · intro hsub
    let stage : ℕ → ℕ := fun k =>
      if h : n.testBit k = true then
        ((evaln_complete (x := 0)).1 (by
          rw [hc]
          exact Part.mem_assert_iff.mpr ⟨hsub (mem_e.mpr h), Part.mem_some_iff.mpr rfl⟩)).choose
      else 0
    refine ⟨(Finset.range n).sup stage, fun k hlt => ?_⟩
    by_cases hb : n.testBit k = true
    · refine Or.inr ?_
      have hle : stage k ≤ (Finset.range n).sup stage :=
        Finset.le_sup (Finset.mem_range.mpr hlt)
      have h0 : 0 ∈ evaln (stage k) c k := by
        simp only [stage, hb, ↓reduceDIte]
        exact ((evaln_complete (x := 0)).1 (by
          rw [hc]
          exact Part.mem_assert_iff.mpr ⟨hsub (mem_e.mpr hb), Part.mem_some_iff.mpr rfl⟩)).choose_spec
      exact (Option.isSome_of_mem (evaln_mono hle h0))
    · exact Or.inl (Bool.eq_false_iff.mpr hb)
  · intro ⟨s, hs⟩ k hk
    have hlt : k < n := mem_e_lt hk
    have hsome : (evaln s c k).isSome = true :=
      (hs k hlt).resolve_left fun hfalse => Bool.eq_false_iff.mp hfalse (mem_e.mp hk)
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hsome
    have : val ∈ Code.eval c k :=
      evaln_sound (by simpa [Option.mem_def] using hval)
    have : val ∈ (Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ)) := by
      simpa [hc] using this
    exact (Part.mem_assert_iff.mp this).1

/-- Finite inclusion `e n ⊆ x` is r.e. in `n` when `x` is, via one common `evaln` stage. -/
theorem IsRE.eSubset {x : Pomega} (hx : IsRE x) :
    REPred fun n => e n ⊆ x := by
  have hf : Partrec fun k : ℕ =>
      (Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ)) :=
    hx.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  have hex : REPred fun n =>
      ∃ s, ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true :=
    REPred.exists (p := fun n s =>
        ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true)
      (primrecPred_common_stage c).computablePred.to_re
  exact hex.of_eq fun n => (eSubset_iff_stage hc n).symm

/-- **Scott 1976, Appendix.** Application of r.e. elements is r.e. -/
theorem IsRE.funOf {u x : Pomega} (hu : IsRE u) (hx : IsRE x) : IsRE (u ⬝ x) := by
  have hand : REPred fun q : ℕ × ℕ => e q.1 ⊆ x ∧ pair q.1 q.2 ∈ u :=
    REPred.and ((IsRE.eSubset hx).comp Computable.fst) (IsRE.pair_mem hu)
  have hex : REPred fun m => ∃ n, e n ⊆ x ∧ pair n m ∈ u :=
    REPred.exists (p := fun m n => e n ⊆ x ∧ pair n m ∈ u)
      (hand.comp (Primrec.pair Primrec.snd Primrec.fst).to_comp)
  exact hex.of_eq fun _ => Iff.rfl

theorem primrecPred_eq_scott_pair :
    PrimrecPred fun t : ℕ × ℕ × ℕ => t.1 = pair t.2.1 t.2.2 :=
  Primrec.eq.comp Primrec.fst
    (primrec_pair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

/-- Encode a Scott-pair graph clause as a single `Nat.pair` search index. -/
theorem IsRE.graph_of_primrecRel {f : Pomega → Pomega}
    (hP : PrimrecRel fun n m : ℕ => m ∈ f (e n)) :
    IsRE (graph f) := by
  have hinner : PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (Nat.unpair q.2).1 (Nat.unpair q.2).2 ∧
        (Nat.unpair q.2).2 ∈ f (e (Nat.unpair q.2).1) :=
    (primrecPred_eq_scott_pair.comp
      (Primrec.pair Primrec.fst (Primrec.unpair.comp Primrec.snd))).and
      (hP.comp
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hex : REPred fun p =>
      ∃ t, p = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
        (Nat.unpair t).2 ∈ f (e (Nat.unpair t).1) :=
    REPred.exists (p := fun p t =>
        p = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
          (Nat.unpair t).2 ∈ f (e (Nat.unpair t).1))
      hinner.computablePred.to_re
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact ⟨(Nat.unpair t).1, (Nat.unpair t).2, ht, hm⟩
  · intro ⟨n, m, hm, hmem⟩
    refine ⟨Nat.pair n m, ?_, ?_⟩
    · simpa [Nat.unpair_pair] using hm
    · simpa [Nat.unpair_pair] using hmem

theorem IsRE.sucC : IsRE sucC := by
  have hp : PrimrecRel fun n m : ℕ => m ≠ 0 ∧ n.testBit m.pred = true :=
    (PrimrecPred.not (Primrec.eq.comp Primrec.snd (Primrec.const 0))).and
      (primrecPred_bool
        (Primrec₂.comp primrec_testBit Primrec.fst (Primrec.pred.comp Primrec.snd)))
  refine (IsRE.graph_of_primrecRel (f := DataTypesAsLattices.succSet)
      (hp.of_eq fun n m => ?_)).of_eq ?_
  · constructor
    · intro ⟨hm0, hbit⟩
      exact ⟨m.pred, mem_e.mpr hbit, (Nat.succ_pred_eq_of_ne_zero hm0).symm⟩
    · intro ⟨k, hk, hm⟩
      subst hm
      exact ⟨Nat.succ_ne_zero k, mem_e.mp hk⟩
  · intro p; rfl

theorem IsRE.predC : IsRE predC := by
  have hp : PrimrecRel fun n m : ℕ => n.testBit (m + 1) = true :=
    primrecPred_bool (Primrec₂.comp primrec_testBit Primrec.fst (Primrec.succ.comp Primrec.snd))
  refine (IsRE.graph_of_primrecRel (f := DataTypesAsLattices.predSet)
      (hp.of_eq fun n m => ?_)).of_eq ?_
  · constructor
    · intro h; exact mem_e.mpr h
    · intro h; exact mem_e.mp h
  · intro p; rfl

theorem eSubset_e_iff (n b : ℕ) :
    e n ⊆ e b ↔ ∀ k < n, n.testBit k = false ∨ b.testBit k = true := by
  constructor
  · intro h k hk
    by_cases hb : n.testBit k = true
    · exact Or.inr (mem_e.mp (h (mem_e.mpr hb)))
    · exact Or.inl (Bool.eq_false_iff.mpr hb)
  · intro h k hk
    have hlt : k < n := mem_e_lt hk
    exact mem_e.mpr ((h k hlt).resolve_left fun hf =>
      Bool.eq_false_iff.mp hf (mem_e.mp hk))

theorem primrecRel_eSubset : PrimrecRel fun n b : ℕ => e n ⊆ e b := by
  have hR : PrimrecRel fun k q : ℕ =>
      q.unpair.1.testBit k = false ∨ q.unpair.2.testBit k = true :=
    ((primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)).not.or
      (primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst))).of_eq
      fun _ => by simp [Bool.not_eq_true]
  refine (hR.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simpa [Nat.unpair_pair] using (eSubset_e_iff p.1 p.2).symm

theorem lt_two_pow_of_high_bits {n k : ℕ}
    (h : ∀ j, k ≤ j → n.testBit j = false) : n < 2 ^ k := by
  induction n using Nat.binaryRec generalizing k with
  | zero => simp
  | bit b n ih =>
    cases k with
    | zero =>
      have hb : b = false := by
        simpa [Nat.testBit_bit_zero] using h 0 le_rfl
      have hn0 : n = 0 := Nat.zero_of_testBit_eq_false fun j => by
        simpa [Nat.testBit_bit_succ] using h (j + 1) (Nat.zero_le (j + 1))
      simp [hb, hn0]
    | succ k =>
      have : n < 2 ^ k := ih fun j hj => by
        simpa [Nat.testBit_bit_succ] using h (j + 1) (Nat.succ_le_succ hj)
      exact Nat.bit_lt_two_pow_succ_iff.mpr this

theorem bits_subset_lt_two_pow {n b : ℕ} (h : e n ⊆ e b) : n < 2 ^ (b + 1) :=
  lt_two_pow_of_high_bits fun j hj =>
    Bool.eq_false_iff.2 fun hbit =>
      Nat.not_le.mpr hj (mem_e_le (h (mem_e.mpr hbit)))

theorem mem_funOf_e_iff (a b m : ℕ) :
    m ∈ funOf (e a) (e b) ↔
      ∃ n < 2 ^ (b + 1), e n ⊆ e b ∧ a.testBit (pair n m) := by
  constructor
  · intro ⟨n, hn, hp⟩
    exact ⟨n, bits_subset_lt_two_pow hn, hn, mem_e.mp hp⟩
  · intro ⟨n, _, hn, hbit⟩
    exact ⟨n, hn, mem_e.mpr hbit⟩

theorem pos_bit_iff (n : ℕ) :
    (∃ k, n.testBit (k + 1) = true) ↔ 2 ≤ n := by
  constructor
  · intro ⟨k, hk⟩
    exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (Nat.le_add_left 1 k) : (2 : ℕ) ^ 1 ≤ 2 ^ (k + 1)).trans
      (two_pow_le_of_testBit hk)
  · intro hn
    by_contra hex
    push_neg at hex
    have hlt : n < 2 := lt_two_pow_of_high_bits fun j hj => by
      cases j with
      | zero => exact (Nat.not_succ_le_zero 0 hj).elim
      | succ j => exact Bool.eq_false_iff.2 (hex j)
    exact Nat.not_lt.mpr hn hlt

theorem condSet_e_iff (n0 n1 n2 m : ℕ) :
    m ∈ condSet (e n2) (e n0) (e n1) ↔
      (n0.testBit m = true ∧ n2.testBit 0 = true) ∨
        (n1.testBit m = true ∧ 2 ≤ n2) := by
  constructor
  · intro h
    rcases h with ⟨hm, h0⟩ | ⟨hm, ⟨k, hk⟩⟩
    · exact Or.inl ⟨mem_e.mp hm, mem_e.mp h0⟩
    · exact Or.inr ⟨mem_e.mp hm, (pos_bit_iff n2).1 ⟨k, mem_e.mp hk⟩⟩
  · intro h
    rcases h with ⟨hm, h0⟩ | ⟨hm, hn2⟩
    · exact Or.inl ⟨mem_e.mpr hm, mem_e.mpr h0⟩
    · obtain ⟨k, hk⟩ := (pos_bit_iff n2).2 hn2
      exact Or.inr ⟨mem_e.mpr hm, k, mem_e.mpr hk⟩

theorem IsRE.graph_of_re {f : Pomega → Pomega}
    (h : REPred fun q : ℕ × ℕ => q.2 ∈ f (e q.1)) :
    IsRE (graph f) := by
  have heq : PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (Nat.unpair q.2).1 (Nat.unpair q.2).2 :=
    primrecPred_eq_scott_pair.comp
      (Primrec.pair Primrec.fst (Primrec.unpair.comp Primrec.snd))
  have hmem : REPred fun q : ℕ × ℕ =>
      (Nat.unpair q.2).2 ∈ f (e (Nat.unpair q.2).1) :=
    h.comp (Primrec.pair
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  have hex : REPred fun p =>
      ∃ t, p = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
        (Nat.unpair t).2 ∈ f (e (Nat.unpair t).1) :=
    REPred.exists (REPred.and heq.computablePred.to_re hmem)
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact ⟨(Nat.unpair t).1, (Nat.unpair t).2, ht, hm⟩
  · intro ⟨n, m, hm, hmem'⟩
    refine ⟨Nat.pair n m, ?_, ?_⟩
    · simpa [Nat.unpair_pair] using hm
    · simpa [Nat.unpair_pair] using hmem'

theorem mem_graph_const_iff (n m : ℕ) :
    m ∈ graph (fun _ => e n) ↔
      ∃ t, m = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
        n.testBit (Nat.unpair t).2 = true := by
  constructor
  · intro ⟨a, b, hm, hb⟩
    exact ⟨Nat.pair a b, by simp [Nat.unpair_pair, hm],
      by simp [Nat.unpair_pair, mem_e.mp hb]⟩
  · intro ⟨t, ht, hb⟩
    exact ⟨(Nat.unpair t).1, (Nat.unpair t).2, ht, mem_e.mpr hb⟩

theorem IsRE.Kcomb : IsRE Kcomb :=
  IsRE.graph_of_re (f := fun x => graph (fun _ => x)) <| by
    have hP : PrimrecPred fun w : ℕ × ℕ =>
        (Nat.unpair w.1).2 = pair (Nat.unpair w.2).1 (Nat.unpair w.2).2 ∧
          (Nat.unpair w.1).1.testBit (Nat.unpair w.2).2 = true :=
      (Primrec.eq.comp
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
          (primrec_pair.comp
            (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))).and
        (primrecPred_bool (Primrec₂.comp primrec_testBit
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
    have hex : REPred fun w : ℕ =>
        ∃ t, (Nat.unpair w).2 = pair (Nat.unpair t).1 (Nat.unpair t).2 ∧
          (Nat.unpair w).1.testBit (Nat.unpair t).2 = true :=
      REPred.exists hP.computablePred.to_re
    exact _root_.REPred.of_eq
      (hex.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd).to_comp)
      fun q => by
        simp only [Nat.unpair_pair]
        exact (mem_graph_const_iff q.1 q.2).symm

theorem mem_condC_iff (p : ℕ) :
    p ∈ condC ↔
      ∃ n0 n1 n2 m, p = pair n0 (pair n1 (pair n2 m)) ∧
        ((n0.testBit m = true ∧ n2.testBit 0 = true) ∨
          (n1.testBit m = true ∧ 2 ≤ n2)) := by
  constructor
  · intro ⟨n0, p1, hp, hp1⟩
    obtain ⟨n1, p2, hp1', hp2⟩ := hp1
    obtain ⟨n2, m, hp2', hm⟩ := hp2
    exact ⟨n0, n1, n2, m, by simp [hp, hp1', hp2'],
      (condSet_e_iff n0 n1 n2 m).mp hm⟩
  · intro ⟨n0, n1, n2, m, hp, hm⟩
    exact ⟨n0, pair n1 (pair n2 m), hp,
      ⟨n1, pair n2 m, rfl,
        ⟨n2, m, rfl, (condSet_e_iff n0 n1 n2 m).mpr hm⟩⟩⟩

theorem IsRE.condC : IsRE condC := by
  have heq : PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (Nat.unpair q.2).1
        (pair (Nat.unpair (Nat.unpair q.2).2).1
          (pair (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2)) :=
    Primrec.eq.comp Primrec.fst
      (primrec_pair.comp
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (primrec_pair.comp
          (Primrec.fst.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
          (primrec_pair.comp
            (Primrec.fst.comp (Primrec.unpair.comp
              (Primrec.snd.comp (Primrec.unpair.comp
                (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))))
            (Primrec.snd.comp (Primrec.unpair.comp
              (Primrec.snd.comp (Primrec.unpair.comp
                (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))))
  have hbit0 : PrimrecPred fun q : ℕ × ℕ =>
      (Nat.unpair q.2).1.testBit
          (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2 = true ∧
        (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1.testBit 0 = true :=
    (primrecPred_bool (Primrec₂.comp primrec_testBit
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))).and
      (primrecPred_bool (Primrec₂.comp primrec_testBit
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))))
        (Primrec.const 0)))
  have hbit1 : PrimrecPred fun q : ℕ × ℕ =>
      (Nat.unpair (Nat.unpair q.2).2).1.testBit
          (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2 = true ∧
        2 ≤ (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1 :=
    (primrecPred_bool (Primrec₂.comp primrec_testBit
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))).and
      (Primrec.nat_le.comp (Primrec.const 2)
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.snd.comp (Primrec.unpair.comp
            (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))
  have hinner : PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (Nat.unpair q.2).1
          (pair (Nat.unpair (Nat.unpair q.2).2).1
            (pair (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1
              (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2)) ∧
        (((Nat.unpair q.2).1.testBit
              (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2 = true ∧
            (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1.testBit 0 =
              true) ∨
          ((Nat.unpair (Nat.unpair q.2).2).1.testBit
              (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).2 = true ∧
            2 ≤ (Nat.unpair (Nat.unpair (Nat.unpair q.2).2).2).1)) :=
    heq.and (hbit0.or hbit1)
  have hex : REPred fun p =>
      ∃ t, p = pair (Nat.unpair t).1
          (pair (Nat.unpair (Nat.unpair t).2).1
            (pair (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1
              (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2)) ∧
        (((Nat.unpair t).1.testBit
              (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2 = true ∧
            (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1.testBit 0 =
              true) ∨
          ((Nat.unpair (Nat.unpair t).2).1.testBit
              (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2 = true ∧
            2 ≤ (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1)) :=
    REPred.exists hinner.computablePred.to_re
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact (mem_condC_iff p).mpr
      ⟨(Nat.unpair t).1, (Nat.unpair (Nat.unpair t).2).1,
        (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1,
        (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2, ht, hm⟩
  · intro hp
    obtain ⟨n0, n1, n2, m, ht, hm⟩ := (mem_condC_iff p).mp hp
    refine ⟨Nat.pair n0 (Nat.pair n1 (Nat.pair n2 m)), ?_, ?_⟩
    · simpa [Nat.unpair_pair] using ht
    · simpa [Nat.unpair_pair] using hm

theorem primrecRel_mem_funOf_e :
    PrimrecRel fun q m : ℕ =>
      m ∈ e (Nat.unpair q).1 ⬝ e (Nat.unpair q).2 := by
  have hinner : PrimrecRel fun n packed : ℕ =>
      e n ⊆ e (Nat.unpair (Nat.unpair packed).1).2 ∧
        (Nat.unpair (Nat.unpair packed).1).1.testBit
          (pair n (Nat.unpair packed).2) :=
    ((primrecRel_eSubset.comp Primrec.fst
        (Primrec.snd.comp (Primrec.unpair.comp
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))).and
      (primrecPred_bool (Primrec₂.comp primrec_testBit
        (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
        (primrec_pair.comp Primrec.fst
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))))
  refine (hinner.exists_lt.comp
      (primrec_twoPow.comp (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))))
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq
    fun q => ?_
  simp only [Nat.unpair_pair]
  exact (mem_funOf_e_iff q.1.unpair.1 q.1.unpair.2 q.2).symm

theorem eSubset_funOf_e_iff (k a b : ℕ) :
    e k ⊆ e a ⬝ e b ↔
      ∀ i < k, k.testBit i = false ∨ i ∈ e a ⬝ e b := by
  constructor
  · intro h i hi
    by_cases hb : k.testBit i = true
    · exact Or.inr (h (mem_e.mpr hb))
    · exact Or.inl (Bool.eq_false_iff.mpr hb)
  · intro h i hi
    have hlt : i < k := mem_e_lt hi
    exact (h i hlt).resolve_left fun hf =>
      Bool.eq_false_iff.mp hf (mem_e.mp hi)

theorem primrecRel_eSubset_funOf_e_bit :
    PrimrecRel fun i kq : ℕ =>
      (Nat.unpair kq).1.testBit i = false ∨
        i ∈ e (Nat.unpair (Nat.unpair kq).2).1 ⬝
          e (Nat.unpair (Nat.unpair kq).2).2 :=
  ((primrecPred_bool (Primrec₂.comp primrec_testBit
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).not.or
    (primrecRel_mem_funOf_e.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).of_eq fun p => by
    simp [Bool.not_eq_true]

theorem primrecRel_eSubset_funOf_e :
    PrimrecRel fun k q : ℕ =>
      e k ⊆ e (Nat.unpair q).1 ⬝ e (Nat.unpair q).2 := by
  refine (primrecRel_eSubset_funOf_e_bit.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simp only [Nat.unpair_pair]
  exact (eSubset_funOf_e_iff p.1 p.2.unpair.1 p.2.unpair.2).symm

def pack4 (n0 n1 n2 m : ℕ) : ℕ :=
  Nat.pair n0 (Nat.pair n1 (Nat.pair n2 m))

def pack4_proj1 (t : ℕ) : ℕ := (Nat.unpair t).1
def pack4_proj2 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair t).2).1
def pack4_proj3 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).1
def pack4_proj4 (t : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair t).2).2).2

theorem primrec_pack4_proj1 : Primrec pack4_proj1 :=
  Primrec.fst.comp Primrec.unpair

theorem primrec_pack4_proj2 : Primrec pack4_proj2 :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

theorem primrec_pack4_proj3 : Primrec pack4_proj3 :=
  Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))

theorem primrec_pack4_proj4 : Primrec pack4_proj4 :=
  Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))

theorem mem_Scomb_iff (p : ℕ) :
    p ∈ Scomb ↔
      ∃ n0 n1 n2 m, p = pair n0 (pair n1 (pair n2 m)) ∧
        m ∈ (e n0 ⬝ e n2) ⬝ (e n1 ⬝ e n2) := by
  constructor
  · intro ⟨n0, p1, hp, hp1⟩
    obtain ⟨n1, p2, hp1', hp2⟩ := hp1
    obtain ⟨n2, m, hp2', hm⟩ := hp2
    exact ⟨n0, n1, n2, m, by simp [hp, hp1', hp2'], hm⟩
  · intro ⟨n0, n1, n2, m, hp, hm⟩
    exact ⟨n0, pair n1 (pair n2 m), hp,
      ⟨n1, pair n2 m, rfl, ⟨n2, m, rfl, hm⟩⟩⟩

theorem primrecRel_Scomb_bit :
    PrimrecRel fun i kt : ℕ =>
      (Nat.unpair kt).1.testBit i = false ∨
        i ∈ e (pack4_proj2 (Nat.unpair kt).2) ⬝
          e (pack4_proj3 (Nat.unpair kt).2) :=
  ((primrecPred_bool (Primrec₂.comp primrec_testBit
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).not.or
    (primrecRel_mem_funOf_e.comp
      (Primrec₂.natPair.comp
        (primrec_pack4_proj2.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
        (primrec_pack4_proj3.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      Primrec.fst)).of_eq fun p => by simp [Bool.not_eq_true]

attribute [irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem primrecPred_Scomb_subset :
    PrimrecPred fun p : ℕ × ℕ =>
      ∀ i < p.1, p.1.testBit i = false ∨
        i ∈ e (pack4_proj2 p.2) ⬝ e (pack4_proj3 p.2) :=
  (primrecRel_Scomb_bit.forall_lt.comp Primrec.fst
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => by
      simp [Nat.unpair_pair]

theorem primrecRel_Scomb_app :
    PrimrecRel fun k t : ℕ =>
      e k ⊆ e (pack4_proj2 t) ⬝ e (pack4_proj3 t) ∧
        pair k (pack4_proj4 t) ∈ e (pack4_proj1 t) ⬝ e (pack4_proj3 t) := by
  have hmem : PrimrecPred fun p : ℕ × ℕ =>
      pair p.1 (pack4_proj4 p.2) ∈
        e (pack4_proj1 p.2) ⬝ e (pack4_proj3 p.2) :=
    (primrecRel_mem_funOf_e.comp
      (Primrec₂.natPair.comp (primrec_pack4_proj1.comp Primrec.snd)
        (primrec_pack4_proj3.comp Primrec.snd))
      (primrec_pair.comp Primrec.fst (primrec_pack4_proj4.comp Primrec.snd))).of_eq
      fun p => by simp [Nat.unpair_pair]
  refine (primrecPred_Scomb_subset.and hmem).of_eq fun p => ?_
  constructor
  · intro ⟨hs, hm⟩
    exact ⟨(eSubset_funOf_e_iff _ _ _).mpr hs, hm⟩
  · intro ⟨hs, hm⟩
    exact ⟨(eSubset_funOf_e_iff _ _ _).mp hs, hm⟩

theorem rePred_Scomb_nested :
    REPred fun t : ℕ =>
      pack4_proj4 t ∈
        (e (pack4_proj1 t) ⬝ e (pack4_proj3 t)) ⬝
          (e (pack4_proj2 t) ⬝ e (pack4_proj3 t)) :=
  (REPred.exists (p := fun t k =>
      e k ⊆ e (pack4_proj2 t) ⬝ e (pack4_proj3 t) ∧
        pair k (pack4_proj4 t) ∈ e (pack4_proj1 t) ⬝ e (pack4_proj3 t))
    (primrecRel_Scomb_app.swap.computablePred.to_re)).of_eq fun _ => Iff.rfl

theorem primrecPred_Scomb_eq :
    PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (pack4_proj1 q.2)
        (pair (pack4_proj2 q.2)
          (pair (pack4_proj3 q.2) (pack4_proj4 q.2))) :=
  Primrec.eq.comp Primrec.fst
    (primrec_pair.comp (primrec_pack4_proj1.comp Primrec.snd)
      (primrec_pair.comp (primrec_pack4_proj2.comp Primrec.snd)
        (primrec_pair.comp (primrec_pack4_proj3.comp Primrec.snd)
          (primrec_pack4_proj4.comp Primrec.snd))))

theorem IsRE.Scomb : IsRE Scomb := by
  have hmem : REPred fun q : ℕ × ℕ =>
      pack4_proj4 q.2 ∈
        (e (pack4_proj1 q.2) ⬝ e (pack4_proj3 q.2)) ⬝
          (e (pack4_proj2 q.2) ⬝ e (pack4_proj3 q.2)) :=
    rePred_Scomb_nested.comp Primrec.snd.to_comp
  have hex : REPred fun p =>
      ∃ t, p = pair (pack4_proj1 t)
          (pair (pack4_proj2 t) (pair (pack4_proj3 t) (pack4_proj4 t))) ∧
        pack4_proj4 t ∈
          (e (pack4_proj1 t) ⬝ e (pack4_proj3 t)) ⬝
            (e (pack4_proj2 t) ⬝ e (pack4_proj3 t)) :=
    REPred.exists (REPred.and primrecPred_Scomb_eq.computablePred.to_re hmem)
  refine hex.of_eq fun p => ?_
  constructor
  · intro ⟨t, ht, hm⟩
    exact (mem_Scomb_iff p).mpr
      ⟨pack4_proj1 t, pack4_proj2 t, pack4_proj3 t, pack4_proj4 t, ht, hm⟩
  · intro hp
    obtain ⟨n0, n1, n2, m, ht, hm⟩ := (mem_Scomb_iff p).mp hp
    refine ⟨pack4 n0 n1 n2 m, ?_, ?_⟩
    · simpa [pack4, pack4_proj1, pack4_proj2, pack4_proj3, pack4_proj4,
        Nat.unpair_pair] using ht
    · simpa [pack4, pack4_proj1, pack4_proj2, pack4_proj3, pack4_proj4,
        Nat.unpair_pair] using hm

/-- Combinatory elements are r.e. (one direction of the appendix equivalence). -/
theorem combinatory_isRE {u : Pomega} (hu : IsCombinatory u) : IsRE u := by
  induction hu with
  | zero => exact IsRE.zeroC
  | suc => exact IsRE.sucC
  | pred => exact IsRE.predC
  | cond => exact IsRE.condC
  | K => exact IsRE.Kcomb
  | S => exact IsRE.Scomb
  | app _ _ iu iv => exact IsRE.funOf iu iv

/-- **Scott 1976, (2.16).** Combinator for `λx. 0 ∪ (x+1)`. -/
def topRecTerm : Term :=
  .lam 0 (.cond (.lam 1 .zero) .zero (.succ (.var 0)))

theorem topRecTerm_interp :
    interp topRecTerm (fun _ => botElem) = graph topRec := by
  apply congrArg graph
  funext v
  simp [topRecTerm, topRec, interp, envSet, Function.update, eq_2_15]

theorem topElem_combinatory : IsCombinatory topElem := by
  have h : funOf Ycomb (interp topRecTerm (fun _ => botElem)) = topElem := by
    rw [topRecTerm_interp, theorem_2_5 topRec_isScottContinuous, eq_2_16]
  exact h ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed topRecTerm)

/-- A combinator realizes a number-theoretic function on numerals. -/
def Realizes (u : Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n, funOf u (ofNat n) = ofNat (p n)

def Realizes2 (u : Pomega) (p : ℕ → ℕ → ℕ) : Prop :=
  ∀ n m, funOf (funOf u (ofNat n)) (ofNat m) = ofNat (p n m)

def composeC (u v : Pomega) : Pomega :=
  funOf (funOf Scomb (funOf Kcomb u)) v

theorem composeC_combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (composeC u v) :=
  .app (.app .S (.app .K hu)) hv

theorem composeC_realizes {u v : Pomega} {p q : ℕ → ℕ}
    (hu : Realizes u p) (hv : Realizes v q) :
    Realizes (composeC u v) (p ∘ q) := fun n => by
  rw [composeC, Scomb_beta3, Kcomb_beta2, hv n, hu (q n)]
  rfl

def constComb (k : ℕ) : Pomega := funOf Kcomb (ofNat k)

theorem constComb_combinatory (k : ℕ) : IsCombinatory (constComb k) :=
  .app .K (ofNat_combinatory k)

theorem constComb_realizes (k : ℕ) : Realizes (constComb k) fun _ => k := fun _ => by
  simp [constComb, Kcomb_beta2]

/-- Scott (2.27) packaged as a combinator. -/
def primRecComb (a f : Pomega) : Pomega :=
  funOf dollarC
    (funOf Ycomb
      (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f))

theorem primRecComb_combinatory {a f : Pomega}
    (ha : IsCombinatory a) (hf : IsCombinatory f) :
    IsCombinatory (primRecComb a f) :=
  .app dollarC_combinatory <|
    .app Ycomb_combinatory <|
      .app (.app (theorem_2_4_closed primRecStepTerm) ha) hf

theorem primRecComb_ofNat (a f : Pomega) (n : ℕ) :
    funOf (primRecComb a f) (ofNat n) = primRecVal a f n := by
  have hgraph := primRecStep_graph_of a f
  have hfix := theorem_2_5 (primRecStep_isScottContinuous a f)
  simp only [primRecComb]
  rw [← hgraph, hfix, ← eq_2_27, primRecHat_ofNat]

def addStepC : Pomega := funOf Kcomb sucC

theorem addStepC_combinatory : IsCombinatory addStepC :=
  .app .K .suc

theorem primRecVal_add (k : ℕ) : ∀ n,
    primRecVal (ofNat k) addStepC n = ofNat (k + n)
  | 0 => rfl
  | n + 1 => by
    calc primRecVal (ofNat k) addStepC (n + 1)
        = funOf (funOf addStepC (ofNat n))
            (primRecVal (ofNat k) addStepC n) := rfl
      _ = funOf sucC (primRecVal (ofNat k) addStepC n) := by
          simp [addStepC, Kcomb_beta2]
      _ = funOf sucC (ofNat (k + n)) := by rw [primRecVal_add k n]
      _ = ofNat (k + n + 1) := by rw [sucC_app, succSet_ofNat]

/-- `λx. primRecComb x (K suc)`. -/
def addC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb (interp primRecStepTerm (fun _ => botElem)))
        (funOf Kcomb addStepC)))

theorem addC_app (x : Pomega) : funOf addC x = primRecComb x addStepC := by
  simp [addC, primRecComb, Scomb_beta3, Kcomb_beta2]

theorem addC_combinatory : IsCombinatory addC :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app (.app .S (.app .K Ycomb_combinatory))
      (.app (.app .S (theorem_2_4_closed primRecStepTerm))
        (.app .K addStepC_combinatory)))

theorem addC_realizes2 : Realizes2 addC fun n m => n + m := fun n m => by
  simp [Realizes2, addC_app, primRecComb_ofNat, primRecVal_add]

/-- `λx. x ⊃ 0, x−1`, so numerals stay numerals. -/
def safePredC : Pomega :=
  interp (.lam 0 (.cond (.var 0) .zero (.pred (.var 0)))) (fun _ => botElem)

theorem safePredC_combinatory : IsCombinatory safePredC :=
  theorem_2_4_closed _

theorem safePredC_zero : funOf safePredC (ofNat 0) = ofNat 0 := by
  simp only [safePredC]
  rw [theorem_2_2_beta]
  simp [interp, envSet, Function.update, eq_2_7_zero]

theorem safePredC_succ (n : ℕ) : funOf safePredC (ofNat (n + 1)) = ofNat n := by
  simp only [safePredC]
  rw [theorem_2_2_beta]
  simp [interp, envSet, Function.update, eq_2_7_succ, predSet_ofNat_succ]

def subStepC : Pomega := funOf Kcomb safePredC

theorem subStepC_combinatory : IsCombinatory subStepC :=
  .app .K safePredC_combinatory

theorem primRecVal_sub (k : ℕ) : ∀ n,
    primRecVal (ofNat k) subStepC n = ofNat (k - n)
  | 0 => by simp [primRecVal]
  | n + 1 => by
    calc primRecVal (ofNat k) subStepC (n + 1)
        = funOf (funOf subStepC (ofNat n))
            (primRecVal (ofNat k) subStepC n) := rfl
      _ = funOf safePredC (primRecVal (ofNat k) subStepC n) := by
          simp [subStepC, Kcomb_beta2]
      _ = funOf safePredC (ofNat (k - n)) := by rw [primRecVal_sub k n]
      _ = ofNat (k - (n + 1)) := by
          cases h : k - n with
          | zero =>
            have : k - (n + 1) = 0 := by omega
            simp [safePredC_zero, this]
          | succ k' =>
            have : k - (n + 1) = k' := by omega
            simp [safePredC_succ, this]

def subC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb (interp primRecStepTerm (fun _ => botElem)))
        (funOf Kcomb subStepC)))

theorem subC_app (x : Pomega) : funOf subC x = primRecComb x subStepC := by
  simp [subC, primRecComb, Scomb_beta3, Kcomb_beta2]

theorem subC_combinatory : IsCombinatory subC :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app (.app .S (.app .K Ycomb_combinatory))
      (.app (.app .S (theorem_2_4_closed primRecStepTerm))
        (.app .K subStepC_combinatory)))

theorem subC_realizes2 : Realizes2 subC fun n m => n - m := fun n m => by
  simp [Realizes2, subC_app, primRecComb_ofNat, primRecVal_sub]

/-- `λx. primRecComb 0 (K (addC x))`. -/
def mulC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb
          (funOf Kcomb
            (funOf (interp primRecStepTerm (fun _ => botElem)) (ofNat 0))))
        (funOf (funOf Scomb (funOf Kcomb Kcomb)) addC)))

theorem SK_comp (f g x : Pomega) :
    (Scomb ⬝ (Kcomb ⬝ f) ⬝ g) ⬝ x = f ⬝ (g ⬝ x) := by
  rw [Scomb_beta3, Kcomb_beta2]

theorem mulC_app (x : Pomega) :
    mulC ⬝ x = primRecComb (ofNat 0) (Kcomb ⬝ (addC ⬝ x)) := by
  rw [mulC, primRecComb, SK_comp, SK_comp, SK_comp, SK_comp]

theorem mulC_combinatory : IsCombinatory mulC :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app (.app .S (.app .K Ycomb_combinatory))
      (.app (.app .S
          (.app .K (.app (theorem_2_4_closed primRecStepTerm)
            (ofNat_combinatory 0))))
        (.app (.app .S (.app .K .K)) addC_combinatory)))

theorem primRecVal_mul (k : ℕ) : ∀ n,
    primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) n = ofNat (k * n)
  | 0 => by simp [primRecVal]
  | n + 1 => by
    calc primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) (n + 1)
        = funOf (funOf (funOf Kcomb (funOf addC (ofNat k))) (ofNat n))
            (primRecVal (ofNat 0) (funOf Kcomb (funOf addC (ofNat k))) n) :=
          rfl
      _ = funOf (funOf addC (ofNat k))
            (ofNat (k * n)) := by
          rw [Kcomb_beta2, primRecVal_mul k n]
      _ = ofNat (k + k * n) := addC_realizes2 k (k * n)
      _ = ofNat (k * (n + 1)) := by rw [Nat.mul_succ, Nat.add_comm]

theorem mulC_realizes2 : Realizes2 mulC fun n m => n * m := fun n m => by
  simp [Realizes2, mulC_app, primRecComb_ofNat, primRecVal_mul]

/-- `cond 1 0 n` is `1` on `0` and `0` on positive numerals. -/
def isZeroC : Pomega := funOf (funOf condC (ofNat 1)) (ofNat 0)

theorem isZeroC_combinatory : IsCombinatory isZeroC :=
  .app (.app .cond (ofNat_combinatory 1)) (ofNat_combinatory 0)

theorem isZeroC_zero : funOf isZeroC (ofNat 0) = ofNat 1 := by
  simp only [isZeroC]
  rw [condC_beta3, eq_2_7_zero]

theorem isZeroC_succ (n : ℕ) : funOf isZeroC (ofNat (n + 1)) = ofNat 0 := by
  simp only [isZeroC]
  rw [condC_beta3]
  exact eq_2_7_succ (ofNat 1) (ofNat 0) n

/-- `λn λm. isZero (n − m)`. -/
def leC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ (Scomb ⬝ (Kcomb ⬝ isZeroC))) ⬝ subC

theorem leC_combinatory : IsCombinatory leC :=
  .app (.app .S (.app .K (.app .S (.app .K isZeroC_combinatory))))
    subC_combinatory

theorem leC_realizes2 (n m : ℕ) :
    funOf (funOf leC (ofNat n)) (ofNat m) =
      ofNat (if n ≤ m then 1 else 0) := by
  unfold leC
  rw [Scomb_beta3, Kcomb_beta2, Scomb_beta3, Kcomb_beta2, subC_realizes2]
  by_cases h : n ≤ m
  · have : n - m = 0 := Nat.sub_eq_zero_of_le h
    simp [h, this, isZeroC_zero]
  · have : 0 < n - m := Nat.sub_pos_of_lt (Nat.not_le.mp h)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this.ne'
    simp [h, hk, isZeroC_succ]

/-- `λa λb. (b-a) ⊃ (a*a+a+b), (b*b+a)` with free `add, mul, sub`. -/
def pairTerm : Term :=
  .lam 3 (.lam 4
    (.cond (.app (.app (.var 2) (.var 4)) (.var 3))
      (.app (.app (.var 0)
          (.app (.app (.var 0)
              (.app (.app (.var 1) (.var 3)) (.var 3)))
            (.var 3)))
        (.var 4))
      (.app (.app (.var 0)
          (.app (.app (.var 1) (.var 4)) (.var 4)))
        (.var 3))))

def arithEnv : ℕ → Pomega
  | 0 => addC
  | 1 => mulC
  | 2 => subC
  | _ => botElem

theorem arithEnv_combinatory : ∀ i, IsCombinatory (arithEnv i)
  | 0 => addC_combinatory
  | 1 => mulC_combinatory
  | 2 => subC_combinatory
  | n + 3 => by
    have hbot : funOf predC zeroC = botElem := by
      rw [predC_app]; exact eq_2_6
    simpa [arithEnv, hbot] using
      IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

def pairComb : Pomega := interp pairTerm arithEnv

theorem pairComb_combinatory : IsCombinatory pairComb := by
  rw [pairComb, theorem_2_4_complete]
  exact ofComb_combinatory _ _ arithEnv_combinatory

theorem pairComb_app (n m : ℕ) :
    funOf (funOf pairComb (ofNat n)) (ofNat m) = ofNat (Nat.pair n m) := by
  unfold pairComb pairTerm
  rw [theorem_2_2_beta, theorem_2_2_beta]
  simp [interp, envSet, Function.update, arithEnv]
  rw [subC_realizes2, mulC_realizes2, mulC_realizes2, addC_realizes2,
    addC_realizes2, addC_realizes2]
  simp [Nat.pair]
  by_cases h : n < m
  · have : m - n ≠ 0 := Nat.sub_ne_zero_of_lt h
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
    rw [hk, eq_2_7_succ]
    simp [h]
  · have : m - n = 0 := Nat.sub_eq_zero_of_le (Nat.not_lt.mp h)
    rw [this, eq_2_7_zero]
    simp [h]

/-! ### The appendix converse: primitive-recursive realizability -/

/-- Primitive recursion with zero initial value, viewed as an operator on its step. -/
def primRecZeroC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ dollarC) ⬝
    (Scomb ⬝ (Kcomb ⬝ Ycomb) ⬝
      (interp primRecStepTerm (fun _ => botElem) ⬝ ofNat 0))

theorem primRecZeroC_combinatory : IsCombinatory primRecZeroC :=
  .app (.app .S (.app .K dollarC_combinatory))
    (.app (.app .S (.app .K Ycomb_combinatory))
      (.app (theorem_2_4_closed primRecStepTerm) (ofNat_combinatory 0)))

theorem primRecZeroC_app (f : Pomega) :
    primRecZeroC ⬝ f = primRecComb (ofNat 0) f := by
  rw [primRecZeroC, SK_comp, SK_comp]
  rfl

/-- The bounded iteration used to compute `Nat.sqrt n`. -/
def sqrtIter (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      let a := sqrtIter n k
      if (a + 1) * (a + 1) ≤ n then a + 1 else a

theorem sqrtIter_eq_min (n k : ℕ) : sqrtIter n k = min k (Nat.sqrt n) := by
  induction k with
  | zero => simp [sqrtIter]
  | succ k ih =>
    rw [sqrtIter, ih]
    by_cases h : k < Nat.sqrt n
    · have hmin : min k (Nat.sqrt n) = k := min_eq_left h.le
      have hs : (k + 1) * (k + 1) ≤ n := Nat.le_sqrt.mp h
      simp [hmin, hs, min_eq_left (Nat.succ_le_iff.mpr h)]
    · have hk : Nat.sqrt n ≤ k := Nat.le_of_not_gt h
      have hmin : min k (Nat.sqrt n) = Nat.sqrt n := min_eq_right hk
      have hs : ¬(Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ n :=
        Nat.not_le.mpr (Nat.lt_succ_sqrt n)
      simp [hmin, hs, min_eq_right (hk.trans (Nat.le_succ k))]

theorem sqrtIter_self (n : ℕ) : sqrtIter n n = Nat.sqrt n := by
  rw [sqrtIter_eq_min, min_eq_right (Nat.sqrt_le_self n)]

def sqrtEnv : ℕ → Pomega
  | 3 => leC
  | 4 => mulC
  | _ => botElem

/-- `λn _ a. if (a+1)^2 ≤ n then a+1 else a`. -/
def sqrtStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond
      (.app (.app (.var 3)
        (.app (.app (.var 4) (.succ (.var 2))) (.succ (.var 2))))
        (.var 0))
      (.var 2)
      (.succ (.var 2)))))

def sqrtStepC : Pomega := interp sqrtStepTerm sqrtEnv

theorem botElem_combinatory : IsCombinatory botElem := by
  have h : predC ⬝ zeroC = botElem := by
    rw [predC_app]
    simpa [zeroC] using eq_2_6
  exact h ▸ .app .pred .zero

theorem sqrtEnv_combinatory : ∀ i, IsCombinatory (sqrtEnv i)
  | 3 => leC_combinatory
  | 4 => mulC_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 5 => botElem_combinatory

theorem sqrtStepC_combinatory : IsCombinatory sqrtStepC := by
  rw [sqrtStepC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ sqrtEnv_combinatory

theorem sqrtStepC_app (n i a : ℕ) :
    ((sqrtStepC ⬝ ofNat n) ⬝ ofNat i) ⬝ ofNat a =
      ofNat (if (a + 1) * (a + 1) ≤ n then a + 1 else a) := by
  unfold sqrtStepC sqrtStepTerm
  rw [theorem_2_2_beta, theorem_2_2_beta, theorem_2_2_beta]
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 2),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 2), sqrtEnv]
  simp [Function.update]
  rw [succSet_ofNat, mulC_realizes2, leC_realizes2]
  by_cases h : (a + 1) * (a + 1) ≤ n
  · simp [h, eq_2_7_succ]
  · simp [h, eq_2_7_zero]

/-- A combinator realizing integer square root. -/
def sqrtC : Pomega :=
  Scomb ⬝
    (Scomb ⬝ (Kcomb ⬝ primRecZeroC) ⬝ sqrtStepC) ⬝
    (Scomb ⬝ Kcomb ⬝ Kcomb)

theorem sqrtC_combinatory : IsCombinatory sqrtC :=
  .app
    (.app .S
      (.app (.app .S (.app .K primRecZeroC_combinatory))
        sqrtStepC_combinatory))
    (.app (.app .S .K) .K)

theorem primRecVal_sqrt (n : ℕ) : ∀ k,
    primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) k = ofNat (sqrtIter n k)
  | 0 => rfl
  | k + 1 => by
      rw [show primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) (k + 1) =
        ((sqrtStepC ⬝ ofNat n) ⬝ ofNat k) ⬝
          primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) k by rfl,
        primRecVal_sqrt n k, sqrtStepC_app]
      rfl

theorem sqrtC_realizes : Realizes sqrtC Nat.sqrt := fun n => by
  rw [sqrtC, Scomb_beta3, Scomb_beta3, Scomb_beta3, Kcomb_beta2, Kcomb_beta2,
    primRecZeroC_app, primRecComb_ofNat,
    primRecVal_sqrt, sqrtIter_self]

def unpairEnv : ℕ → Pomega
  | 1 => sqrtC
  | 2 => subC
  | 3 => mulC
  | 4 => leC
  | _ => botElem

def unpairSqrtTerm : Term := .app (.var 1) (.var 0)
def unpairSquareTerm : Term :=
  .app (.app (.var 3) unpairSqrtTerm) unpairSqrtTerm
def unpairDeltaTerm : Term :=
  .app (.app (.var 2) (.var 0)) unpairSquareTerm
def unpairTestTerm : Term :=
  .app (.app (.var 4) (.succ unpairDeltaTerm)) unpairSqrtTerm

def unpairFstTerm : Term :=
  .lam 0 (.cond unpairTestTerm unpairSqrtTerm unpairDeltaTerm)

def unpairSndTerm : Term :=
  .lam 0 (.cond unpairTestTerm
    (.app (.app (.var 2) unpairDeltaTerm) unpairSqrtTerm)
    unpairSqrtTerm)

def unpairFstC : Pomega := interp unpairFstTerm unpairEnv
def unpairSndC : Pomega := interp unpairSndTerm unpairEnv

theorem unpairEnv_combinatory : ∀ i, IsCombinatory (unpairEnv i)
  | 1 => sqrtC_combinatory
  | 2 => subC_combinatory
  | 3 => mulC_combinatory
  | 4 => leC_combinatory
  | 0 => botElem_combinatory
  | _ + 5 => botElem_combinatory

theorem unpairFstC_combinatory : IsCombinatory unpairFstC := by
  rw [unpairFstC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ unpairEnv_combinatory

theorem unpairSndC_combinatory : IsCombinatory unpairSndC := by
  rw [unpairSndC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ unpairEnv_combinatory

theorem unpairFstC_realizes : Realizes unpairFstC (fun n => n.unpair.1) := fun n => by
  rw [unpairFstC, unpairFstTerm, theorem_2_2_beta]
  simp only [unpairTestTerm, unpairDeltaTerm, unpairSquareTerm, unpairSqrtTerm,
    interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (1 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0), unpairEnv]
  rw [sqrtC_realizes, mulC_realizes2, subC_realizes2, succSet_ofNat,
    leC_realizes2]
  unfold Nat.unpair
  by_cases h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
  · have hle : n - Nat.sqrt n * Nat.sqrt n + 1 ≤ Nat.sqrt n :=
      Nat.succ_le_iff.mpr h
    simp [h, hle, eq_2_7_succ]
  · have hle : ¬n - Nat.sqrt n * Nat.sqrt n + 1 ≤ Nat.sqrt n := by omega
    simp [h, hle, eq_2_7_zero]

theorem unpairSndC_realizes : Realizes unpairSndC (fun n => n.unpair.2) := fun n => by
  rw [unpairSndC, unpairSndTerm, theorem_2_2_beta]
  simp only [unpairTestTerm, unpairDeltaTerm, unpairSquareTerm, unpairSqrtTerm,
    interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (1 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (2 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0), unpairEnv]
  rw [sqrtC_realizes, mulC_realizes2, subC_realizes2, succSet_ofNat,
    leC_realizes2, subC_realizes2]
  unfold Nat.unpair
  by_cases h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n
  · have hle : n - Nat.sqrt n * Nat.sqrt n + 1 ≤ Nat.sqrt n :=
      Nat.succ_le_iff.mpr h
    simp [h, hle, eq_2_7_succ]
  · have hle : ¬n - Nat.sqrt n * Nat.sqrt n + 1 ≤ Nat.sqrt n := by omega
    simp [h, hle, eq_2_7_zero]

/-- Curried operator `λa f. primRecComb a f`. -/
def primRecOpEnv : ℕ → Pomega
  | 2 => dollarC
  | 3 => Ycomb
  | 4 => interp primRecStepTerm (fun _ => botElem)
  | _ => botElem

def primRecOpTerm : Term :=
  .lam 0 (.lam 1
    (.app (.var 2)
      (.app (.var 3) (.app (.app (.var 4) (.var 0)) (.var 1)))))

def primRecOpC : Pomega := interp primRecOpTerm primRecOpEnv

theorem primRecOpEnv_combinatory : ∀ i, IsCombinatory (primRecOpEnv i)
  | 2 => dollarC_combinatory
  | 3 => Ycomb_combinatory
  | 4 => theorem_2_4_closed primRecStepTerm
  | 0 | 1 => botElem_combinatory
  | _ + 5 => botElem_combinatory

theorem primRecOpC_combinatory : IsCombinatory primRecOpC := by
  rw [primRecOpC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ primRecOpEnv_combinatory

theorem primRecOpC_app (a f : Pomega) :
    (primRecOpC ⬝ a) ⬝ f = primRecComb a f := by
  rw [primRecOpC, primRecOpTerm, theorem_2_2_beta, theorem_2_2_beta]
  simp [interp, envSet, Function.update, primRecOpEnv, primRecComb]

def pairRealizer (u v : Pomega) : Pomega :=
  Scomb ⬝ (Scomb ⬝ (Kcomb ⬝ pairComb) ⬝ u) ⬝ v

theorem pairRealizer_combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (pairRealizer u v) :=
  .app (.app .S (.app (.app .S (.app .K pairComb_combinatory)) hu)) hv

theorem pairRealizer_realizes {u v : Pomega} {p q : ℕ → ℕ}
    (hu : Realizes u p) (hv : Realizes v q) :
    Realizes (pairRealizer u v) (fun n => Nat.pair (p n) (q n)) := fun n => by
  rw [pairRealizer, Scomb_beta3, Scomb_beta3, Kcomb_beta2,
    hu, hv, pairComb_app]

/-- Environment for the primitive-recursion constructor of `Nat.Primrec`. -/
def precEnv (f g : Pomega) : ℕ → Pomega
  | 3 => primRecOpC
  | 4 => f
  | 5 => g
  | 6 => unpairFstC
  | 7 => unpairSndC
  | 8 => pairComb
  | _ => botElem

/-- On packed input `(z,n)`, recurse from `f z` with
step `λy ih. g (pair z (pair y ih))`. -/
def precTerm : Term :=
  .lam 0
    (.app
      (.app
        (.app (.var 3) (.app (.var 4) (.app (.var 6) (.var 0))))
        (.lam 1 (.lam 2
          (.app (.var 5)
            (.app (.app (.var 8) (.app (.var 6) (.var 0)))
              (.app (.app (.var 8) (.var 1)) (.var 2)))))))
      (.app (.var 7) (.var 0)))

def precC (f g : Pomega) : Pomega := interp precTerm (precEnv f g)

theorem precEnv_combinatory {f g : Pomega}
    (hf : IsCombinatory f) (hg : IsCombinatory g) :
    ∀ i, IsCombinatory (precEnv f g i)
  | 3 => primRecOpC_combinatory
  | 4 => hf
  | 5 => hg
  | 6 => unpairFstC_combinatory
  | 7 => unpairSndC_combinatory
  | 8 => pairComb_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 9 => botElem_combinatory

theorem precC_combinatory {f g : Pomega}
    (hf : IsCombinatory f) (hg : IsCombinatory g) :
    IsCombinatory (precC f g) := by
  rw [precC, theorem_2_4_complete]
  exact ofComb_combinatory _ _ (precEnv_combinatory hf hg)

theorem precC_realizes {f g : Pomega} {p q : ℕ → ℕ}
    (hf : Realizes f p) (hg : Realizes g q) :
    Realizes (precC f g)
      (Nat.unpaired fun z n => n.rec (p z) fun y ih => q (Nat.pair z (Nat.pair y ih))) := by
  intro w
  rw [precC, precTerm, theorem_2_2_beta]
  simp only [interp, envSet, Function.update_self,
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (4 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (5 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (6 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (7 : ℕ) ≠ 0),
    Function.update_of_ne (by decide : (8 : ℕ) ≠ 0), precEnv]
  simp [Function.update]
  rw [unpairFstC_realizes, unpairSndC_realizes, hf, primRecOpC_app,
    primRecComb_ofNat]
  let z := w.unpair.1
  let step : Pomega :=
    interp (.lam 1 (.lam 2
      (.app (.var 5)
        (.app (.app (.var 8) (ofNat z |> fun _ => .app (.var 6) (.var 0)))
          (.app (.app (.var 8) (.var 1)) (.var 2))))))
      (Function.update (precEnv f g) 0 (ofNat w))
  have hstep (y ih : ℕ) :
      (step ⬝ ofNat y) ⬝ ofNat ih =
        ofNat (q (Nat.pair z (Nat.pair y ih))) := by
    dsimp [step, z]
    rw [theorem_2_2_beta, theorem_2_2_beta]
    simp [interp, envSet, Function.update, precEnv]
    rw [unpairFstC_realizes, pairComb_app, pairComb_app, hg]
  have hrec : ∀ n,
      primRecVal (ofNat (p z)) step n =
        ofNat (n.rec (p z) fun y ih => q (Nat.pair z (Nat.pair y ih))) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (step ⬝ ofNat n) ⬝ primRecVal (ofNat (p z)) step n = _
      rw [ih, hstep]
  exact hrec w.unpair.2

/-- Every unary primitive-recursive function has a combinatory realizer. -/
theorem primrec_realized {p : ℕ → ℕ} (hp : Nat.Primrec p) :
    ∃ u, IsCombinatory u ∧ Realizes u p := by
  induction hp with
  | zero =>
      exact ⟨constComb 0, constComb_combinatory 0, constComb_realizes 0⟩
  | succ =>
      exact ⟨sucC, .suc, fun n => by rw [sucC_app, succSet_ofNat]⟩
  | left =>
      exact ⟨unpairFstC, unpairFstC_combinatory, unpairFstC_realizes⟩
  | right =>
      exact ⟨unpairSndC, unpairSndC_combinatory, unpairSndC_realizes⟩
  | pair _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨pairRealizer u v, pairRealizer_combinatory hu hv,
        pairRealizer_realizes hru hrv⟩
  | comp _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨composeC u v, composeC_combinatory hu hv, composeC_realizes hru hrv⟩
  | prec _ _ ihf ihg =>
      obtain ⟨u, hu, hru⟩ := ihf
      obtain ⟨v, hv, hrv⟩ := ihg
      exact ⟨precC u v, precC_combinatory hu hv, precC_realizes hru hrv⟩

/-- Stage-bounded enumerator associated to a partial-recursive code. -/
def enumFun (c : Code) (t : ℕ) : ℕ :=
  bif (evaln t.unpair.2 c t.unpair.1).isSome
    then t.unpair.1 + 1
    else 0

theorem primrec_enumFun (c : Code) : Nat.Primrec (enumFun c) := by
  have heval : Primrec fun t : ℕ => evaln t.unpair.2 c t.unpair.1 :=
    primrec_evaln.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.unpair) (Primrec.const c))
        (Primrec.fst.comp Primrec.unpair)
  have h : Primrec fun t : ℕ =>
      bif (evaln t.unpair.2 c t.unpair.1).isSome
        then t.unpair.1 + 1 else 0 :=
    (Primrec.cond (Primrec.option_isSome.comp heval)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const 0)).of_eq fun t => by simp [Nat.succ_eq_add_one]
  exact Primrec.nat_iff.mp (h.of_eq fun _ => rfl)

def enumRangeC (r : Pomega) : Pomega :=
  (dollarC ⬝ r) ⬝ topElem

theorem enumRangeC_combinatory {r : Pomega} (hr : IsCombinatory r) :
    IsCombinatory (enumRangeC r) :=
  .app (.app dollarC_combinatory hr) topElem_combinatory

theorem enumRangeC_eq {r : Pomega} {p : ℕ → ℕ} (hr : Realizes r p) :
    enumRangeC r = ⋃ n, ofNat (p n) := by
  rw [enumRangeC, eq_2_25]
  ext k
  constructor
  · intro hk
    obtain ⟨n, _, hkn⟩ := Set.mem_iUnion₂.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [hr n] using hkn⟩
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion₂.mpr ⟨n, Set.mem_univ n, by simpa [hr n] using hkn⟩

/-- **Scott 1976, Appendix.** Every r.e. element belongs to the
combinatory closure. -/
theorem IsRE.combinatory {u : Pomega} (hu : IsRE u) : IsCombinatory u := by
  have hpart : Partrec fun k : ℕ =>
      Part.assert (k ∈ u) fun _ => Part.some (0 : ℕ) :=
    hu.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hpart)
  obtain ⟨r, hr, hreal⟩ := primrec_realized (primrec_enumFun c)
  have hrange := enumRangeC_eq hreal
  have hpred : DataTypesAsLattices.predSet (enumRangeC r) = u := by
    ext n
    constructor
    · intro hn
      rw [hrange] at hn
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hn
      have heq : enumFun c t = n + 1 := by simpa [ofNat] using ht.symm
      have hs : (evaln t.unpair.2 c t.unpair.1).isSome = true := by
        by_contra h
        have : (evaln t.unpair.2 c t.unpair.1).isSome = false :=
          Bool.eq_false_of_not_eq_true h
        simp [enumFun, this] at heq
      have hfirst : t.unpair.1 = n := by
        simp [enumFun, hs] at heq
        omega
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      have hmem : v ∈ Code.eval c t.unpair.1 :=
        evaln_sound (by simpa [Option.mem_def] using hv)
      rw [hc] at hmem
      simpa [hfirst] using (Part.mem_assert_iff.mp hmem).1
    · intro hn
      have hmem : 0 ∈ Code.eval c n := by
        rw [hc]
        exact Part.mem_assert_iff.mpr ⟨hn, Part.mem_some_iff.mpr rfl⟩
      obtain ⟨s, hs⟩ := evaln_complete.mp hmem
      rw [hrange]
      refine Set.mem_iUnion.mpr ⟨Nat.pair n s, ?_⟩
      have hsome : (evaln s c n).isSome = true := Option.isSome_of_mem hs
      simp [enumFun, Nat.unpair_pair, hsome, ofNat]
  have hcomb : IsCombinatory (DataTypesAsLattices.predC ⬝ enumRangeC r) :=
    .app .pred (enumRangeC_combinatory hr)
  rw [DataTypesAsLattices.predC_app, hpred] at hcomb
  exact hcomb

theorem IsRE.iff_combinatory {u : Pomega} : IsRE u ↔ IsCombinatory u :=
  ⟨IsRE.combinatory, combinatory_isRE⟩

/-- **Scott 1976, Theorem 2.6 (The definability theorem), unary case.**
For a continuous `f`, computability, recursive enumerability of the graph,
combinatory definability, and closed LAMBDA-definability agree. -/
theorem theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (IsComputable f ↔ IsRE (graph f)) ∧
      (IsRE (graph f) ↔ IsCombinatory (graph f)) ∧
      (IsLambdaDefinable (graph f) ↔ IsCombinatory (graph f)) := by
  refine ⟨?_, IsRE.iff_combinatory, ?_⟩
  · exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
  · exact ⟨fun ⟨t, ht⟩ => by simpa [ht] using theorem_2_4_closed t,
      combinatory_isLambdaDefinable⟩

end Scott1976.DataTypesAsLattices
