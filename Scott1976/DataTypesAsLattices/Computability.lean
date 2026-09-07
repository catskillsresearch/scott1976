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
equivalent to the abstracted graph `λx. f(x)` being an r.e. set. The
further equivalence with LAMBDA-definability is the paper's identification
of r.e. sets with the combinatory closure (Theorems 2.4 and 3.2).
-/

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

/-- **Scott 1976, Theorem 2.6 (The definability theorem), unary case.**
For a continuous `f` the following are equivalent in the sense of the
paper: (i) `f` is computable (graph r.e.); (ii) `λx. f(x)` is r.e.;
(iii) `λx. f(x)` is LAMBDA-definable, equivalently combinatory. -/
theorem theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (IsComputable f ↔ IsRE (graph f)) ∧
      (IsLambdaDefinable (graph f) ↔ IsCombinatory (graph f)) := by
  constructor
  · constructor
    · intro h; exact h.2
    · intro h; exact ⟨hf, h⟩
  · constructor
    · intro ⟨t, ht⟩
      simpa [ht] using theorem_2_4_closed t
    · intro h
      exact combinatory_isLambdaDefinable h

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

end Scott1976.DataTypesAsLattices
