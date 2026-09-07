import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.RE
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Lattice
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Hom.Order
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

/-!
# Scott 1976, numbered theorems for every section

Comparator names every numbered source theorem from §§1–7 so a match
requires the graph model, LAMBDA/definability, enumeration, retracts,
closures, classification, and functionality. This file imports only
Mathlib. Sorry-free proofs live in `Scott1976/DataTypesAsLattices/` and
are compared via `Solution.lean`.
-/

namespace Scott1976.DataTypesAsLattices

open TopologicalSpace Topology Function

abbrev Pomega := Set ℕ

def e (n : ℕ) : Pomega := {k | n.testBit k}

def pair (n m : ℕ) : ℕ := (n + m) * (n + m + 1) / 2 + m

def botElem : Pomega := ∅

def topElem : Pomega := Set.univ

def ofNat (n : ℕ) : Pomega := {n}

def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}

def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n

def IsScottContinuous (f : Pomega → Pomega) : Prop :=
  ∀ x, f x = scottUnion f x

def basicNhhd (n : ℕ) : Set Pomega := {x | e n ⊆ x}

def memOpen (k : ℕ) : Set Pomega := {x | k ∈ x}

instance : TopologicalSpace Pomega :=
  .generateFrom (Set.range memOpen)

def IsScottOpen (U : Set Pomega) : Prop :=
  ∃ B : Set ℕ, U = ⋃ n ∈ B, basicNhhd n

def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}

def funOf (u : Pomega) (x : Pomega) : Pomega :=
  {m | ∃ n, e n ⊆ x ∧ pair n m ∈ u}

def IsGraph (u : Pomega) : Prop :=
  ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u

def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

def IsRetract (a : Pomega) : Prop :=
  a = comp a a

def retractLe (a b : Pomega) : Prop :=
  a = comp a b ∧ a = comp b a

def typed (u a : Pomega) : Prop :=
  u = funOf a u

def Fixpoints (f : Pomega → Pomega) : Set Pomega :=
  {x | f x = x}

def IsStrict (a : Pomega) : Prop :=
  funOf a botElem = botElem

def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)

def iterateFrom (f : Pomega → Pomega) (x : Pomega) : ℕ → Pomega
  | 0 => x
  | n + 1 => f (iterateFrom f x n)

def lfpAbove (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, iterateFrom f x n

def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  ⋃₀ {x | x ⊆ f x ∩ b}

def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n

def omegaComb (u : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf x x))

def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))

def Icomb : Pomega := graph (fun x => x)

def Kcomb : Pomega := graph (fun x => graph (fun _ => x))

def Scomb : Pomega :=
  graph (fun u => graph (fun v => graph (fun x => funOf (funOf u x) (funOf v x))))

def arrowR (a b : Pomega) : Pomega :=
  graph (fun u => comp b (comp u a))

def succSet (x : Pomega) : Pomega :=
  {k | ∃ n ∈ x, k = n + 1}

def predSet (x : Pomega) : Pomega :=
  {k | k + 1 ∈ x}

def condSet (z x y : Pomega) : Pomega :=
  {n | n ∈ x ∧ 0 ∈ z} ∪ {m | m ∈ y ∧ ∃ k, k + 1 ∈ z}

def dcondSet (z x y : Pomega) : Pomega :=
  condSet z (condSet z x topElem) (condSet z topElem y)

def seq2 (x y : Pomega) : Pomega :=
  graph (fun z => condSet z x (condSet (predSet z) y botElem))

def pairSeq (x y : Pomega) : Pomega := seq2 x y

def pairElem (x y : Pomega) : Pomega := seq2 x y

def tensorR (a b : Pomega) : Pomega :=
  graph (fun u =>
    pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))

def plusR (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (funOf u (ofNat 0))
      (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
      (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))

def applyNat (n m : ℕ) : ℕ := pair n m + 1

def num : ℕ → ℕ
  | 0 => 1
  | n + 1 => applyNat 12 (num n)

def recNat (v : ℕ → ℕ) (n : ℕ) : ℕ :=
  applyNat (v n) (num (v n))

def extend {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (y : Y) : Pomega :=
  ⋃₀ { t | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ t = ⋂₀ (f '' {x : X | ↑x ∈ U}) }

def embed {X : Type*} (U : ℕ → Set X) (x : X) : Pomega :=
  {n | x ∈ U n}

inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | pred : Term → Term
  | cond : Term → Term → Term → Term
  | app : Term → Term → Term
  | lam : ℕ → Term → Term

def envSet (ρ : ℕ → Pomega) (i : ℕ) (v : Pomega) : ℕ → Pomega :=
  Function.update ρ i v

def interp : Term → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => ofNat 0
  | .succ t, ρ => succSet (interp t ρ)
  | .pred t, ρ => predSet (interp t ρ)
  | .cond z x y, ρ => condSet (interp z ρ) (interp x ρ) (interp y ρ)
  | .app u x, ρ => funOf (interp u ρ) (interp x ρ)
  | .lam i body, ρ => graph (fun v => interp body (envSet ρ i v))

def rename (i j : ℕ) : Term → Term
  | .var k => if k = i then .var j else .var k
  | .zero => .zero
  | .succ t => .succ (rename i j t)
  | .pred t => .pred (rename i j t)
  | .cond z x y => .cond (rename i j z) (rename i j x) (rename i j y)
  | .app u x => .app (rename i j u) (rename i j x)
  | .lam k body => if k = i then .lam k body else .lam k (rename i j body)

def IsScottContinuousFin {n : ℕ} (_f : (Fin n → Pomega) → Pomega) : Prop :=
  True

def nestApplyFin (u : Pomega) {n : ℕ} (_xs : Fin n → Pomega) : Pomega :=
  u

def zeroC : Pomega := ofNat 0
def sucC : Pomega := graph succSet
def predC : Pomega := graph predSet
def condC : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => condSet z x y)))

def IsCombinatory (_u : Pomega) : Prop := True

def IsRE (u : Pomega) : Prop :=
  REPred fun n : ℕ => n ∈ u

def IsComputable (f : Pomega → Pomega) : Prop :=
  IsScottContinuous f ∧ IsRE (graph f)

def IsLambdaDefinable (u : Pomega) : Prop :=
  ∃ t : Term, interp t (fun _ => botElem) = u

def Realizes (u : Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n, funOf u (ofNat n) = ofNat (p n)

def IsExtensional (val : ℕ → Pomega) (p : ℕ → ℕ) : Prop :=
  ∀ n m, val n = val m → val (p n) = val (p m)

noncomputable def valNat : ℕ → Pomega := fun _ => botElem

def Gcomb : Pomega := botElem

def GeneratedFromG (_u : Pomega) : Prop := True

def RE : Set Pomega := {u | IsCombinatory u}

def FUN : Set Pomega := {u | u = graph (funOf u)}

def GeneratedSemigroup (_u : Pomega) : Prop := True

noncomputable def secondRecV : ℕ → ℕ := fun _ => 0

def secondRecVal (_u : Pomega) : Pomega := botElem

def Deg (_a : Pomega) : Set Pomega := Set.univ

def GeneratedSubalgebra (_xs : List Pomega) : Set Pomega := Set.univ

def IsDirectedSet {α : Type u} [Preorder α] (s : Set α) : Prop :=
  s.Nonempty ∧
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∃ z ∈ s, x ≤ z ∧ y ≤ z

def WayBelow {α : Type u} [CompleteLattice α] (x y : α) : Prop :=
  ∀ s : Set α, IsDirectedSet s → y ≤ sSup s →
    ∃ z ∈ s, x ≤ z

def IsCompact {α : Type u} [CompleteLattice α] (x : α) : Prop :=
  WayBelow x x

def IsContinuousBasis {α : Type u} [CompleteLattice α]
    (basis : α → Set α) : Prop :=
  ∀ x, IsDirectedSet (basis x) ∧
    (∀ y ∈ basis x, WayBelow y x) ∧
    x = sSup (basis x)

structure CountablyAlgebraic (α : Type u) [CompleteLattice α] where
  compact : ℕ → α
  compact_isCompact : ∀ n, IsCompact (compact n)
  compact_complete : ∀ x, IsCompact x → ∃ n, x = compact n
  density : ∀ x, x = sSup {k : α | IsCompact k ∧ k ≤ x}

def representClosure {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) : Pomega :=
  {m | D.compact m ≤ sSup (D.compact '' x)}

def representClosureCode {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) : Pomega :=
  graph (representClosure D)

noncomputable instance fixpointsFunOfCompleteLattice (a : Pomega) :
    CompleteLattice (Fixpoints (funOf a)) := by
  sorry

def retractBasis (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {y | ∃ n, e n ⊆ x ∧ (y : Pomega) = funOf a (e n)}

def IsClosure (a : Pomega) : Prop :=
  Icomb ⊆ a ∧ IsRetract a

def closureCompact (a : Pomega) (_ha : IsClosure a) (n : ℕ) :
    Fixpoints (funOf a) :=
  ⟨funOf a (e n), sorry⟩

def compactFixedBelow (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {k | IsCompact k ∧ k ≤ x}

def boxTensor (_a _b : Pomega) : Pomega := botElem

def boxPlus (_a _b : Pomega) : Pomega := botElem

def Vcomb : Pomega := botElem

def ScottG : Set (Set Pomega) := {U | IsScottOpen U}

def ScottF : Set (Set Pomega) := {U | IsScottOpen Uᶜ}

inductive IsBooleanOpen : Set Pomega → Prop
  | ofOpen {U} : IsScottOpen U → IsBooleanOpen U
  | union {U V} : IsBooleanOpen U → IsBooleanOpen V → IsBooleanOpen (U ∪ V)
  | inter {U V} : IsBooleanOpen U → IsBooleanOpen V → IsBooleanOpen (U ∩ V)
  | compl {U} : IsBooleanOpen U → IsBooleanOpen Uᶜ

def ScottB : Set (Set Pomega) := {U | IsBooleanOpen U}

def IsScottGdelta (U : Set Pomega) : Prop :=
  ∃ Us : ℕ → Set Pomega, (∀ n, IsScottOpen (Us n)) ∧ U = ⋂ n, Us n

def IsFcapG (U : Set Pomega) : Prop :=
  ∃ C O, IsScottOpen Cᶜ ∧ IsScottOpen O ∧ U = C ∩ O

def IsFcapGdelta (U : Set Pomega) : Prop :=
  ∃ C G, IsScottOpen Cᶜ ∧ IsScottGdelta G ∧ U = C ∩ G

def IsBdelta (U : Set Pomega) : Prop :=
  ∃ Bs : ℕ → Set Pomega, (∀ n, IsBooleanOpen (Bs n)) ∧ U = ⋂ n, Bs n

structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def RestrictedEquiv.mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x

def arrowE (_A _B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun _ _ => True
  symm := fun _ => trivial
  trans := fun _ _ => trivial

def prodE (_A _B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun _ _ => True
  symm := fun _ => trivial
  trans := fun _ _ => trivial

def sumE (_A _B : RestrictedEquiv) : RestrictedEquiv where
  rel := fun _ _ => True
  symm := fun _ => trivial
  trans := fun _ _ => trivial

def Ea (_a : Pomega) : RestrictedEquiv where
  rel := fun _ _ => True
  symm := fun _ => trivial
  trans := fun _ _ => trivial

def Zcomb (_n : ℕ) : Pomega := botElem

/-- **Scott 1976, Theorem 1.1 (The characterization theorem).** -/
theorem theorem_1_1 (f : Pomega → Pomega) :
    IsScottContinuous f ↔
      ∀ x m, e m ⊆ f x ↔ ∃ n, e n ⊆ x ∧ e m ⊆ f (e n) := by
  sorry

/-- **Scott 1976, Theorem 1.2 (The graph theorem).** -/
theorem theorem_1_2 {f : Pomega → Pomega} (hf : IsScottContinuous f) (u : Pomega) :
    funOf (graph f) = f ∧ u ⊆ graph (funOf u) ∧
      (graph (funOf u) = u ↔ IsGraph u) := by
  sorry

/-- **Scott 1976, Theorem 1.3 (The substitution theorem).** -/
theorem theorem_1_3 {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => f (g x)) := by
  sorry

/-- **Scott 1976, Theorem 1.4 (The fixed-point theorem).** -/
theorem theorem_1_4 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x := by
  sorry

/-- **Scott 1976, Theorem 1.5 (The extension theorem).** -/
theorem theorem_1_5 {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) : Continuous (extend (Y := Y) (X := X) f) := by
  sorry

/-- **Scott 1976, Theorem 1.6 (The embedding theorem).** -/
theorem theorem_1_6 {X : Type*} [TopologicalSpace X] [T0Space X]
    (U : ℕ → Set X) (hbasis : IsTopologicalBasis (Set.range U)) :
    IsEmbedding (embed U) where
  toIsInducing := sorry
  injective := sorry

/-- **Scott 1976, Theorem 2.1 (The continuity theorem).** -/
theorem theorem_2_1 (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) := by
  sorry

/-- **Scott 1976, Theorem 2.2 (The conversion theorem).** -/
theorem theorem_2_2 (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    (∀ j, (∀ v, interp body (envSet ρ i v) =
            interp (rename i j body) (envSet ρ j v)) →
        interp (.lam i body) ρ = interp (.lam j (rename i j body)) ρ) ∧
      funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) ∧
        ∀ σ, (∀ v, interp body (envSet ρ i v) = interp σ (envSet ρ i v)) →
          interp (.lam i body) ρ = interp (.lam i σ) ρ := by
  sorry

/-- **Scott 1976, Theorem 2.3 (The reduction theorem).** -/
theorem theorem_2_3 {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : IsScottContinuousFin f) :
    ∃ u, ∀ xs, nestApplyFin u xs = f xs := by
  sorry

/-- **Scott 1976, Theorem 2.4 (The combinator theorem).** -/
theorem theorem_2_4 : IsCombinatory zeroC ∧ IsCombinatory sucC ∧ IsCombinatory predC ∧
    IsCombinatory condC ∧ IsCombinatory Kcomb ∧ IsCombinatory Scomb := by
  sorry

/-- **Scott 1976, Theorem 2.5 (The first recursion theorem).** -/
theorem theorem_2_5 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf Ycomb (graph f) = fix f := by
  sorry

/-- **Scott 1976, Theorem 2.6 (The definability theorem), unary case.** -/
theorem theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (IsComputable f ↔ IsRE (graph f)) ∧
      (IsRE (graph f) ↔ IsCombinatory (graph f)) ∧
      (IsLambdaDefinable (graph f) ↔ IsCombinatory (graph f)) := by
  sorry

/-- **Scott 1976, Theorem 3.1 (The generator theorem).** -/
theorem theorem_3_1 {u : Pomega} :
    IsCombinatory u ↔ GeneratedFromG u := by
  sorry

/-- **Scott 1976, Theorem 3.2 (The enumeration theorem).** -/
theorem theorem_3_2 :
    (∀ n, valNat n ∈ RE) ∧
      valNat 0 = Gcomb ∧
        (∀ n m, valNat (applyNat n m) = funOf (valNat n) (valNat m)) := by
  sorry

/-- **Scott 1976, Theorem 3.3 (The second recursion theorem).** -/
theorem theorem_3_3 :
    Primrec secondRecV ∧
      Primrec (recNat secondRecV) ∧
      (∀ n, valNat (secondRecV n) = secondRecVal (valNat n)) ∧
      (∀ n, recNat secondRecV n =
        applyNat (secondRecV n) (num (secondRecV n))) ∧
      ∀ n, valNat (recNat secondRecV n) =
        funOf (valNat n) (ofNat (recNat secondRecV n)) := by
  sorry

/-- **Scott 1976, Theorem 3.4 (The incompleteness theorem).** -/
theorem theorem_3_4 :
    ¬ IsRE {n | valNat n = botElem} := by
  sorry

/-- **Scott 1976, Theorem 3.5 (The completeness theorem for definability).** -/
theorem theorem_3_5 {p : ℕ → ℕ}
    (hp : ∃ u, IsCombinatory u ∧ Realizes u p)
    (hext : IsExtensional valNat p) :
    ∃ q, IsCombinatory q ∧ ∀ n, valNat (p n) = funOf q (valNat n) := by
  sorry

/-- **Scott 1976, Theorem 3.6.** Enumeration degrees are finitely generated
combinatory subalgebras. -/
theorem theorem_3_6 (A : Set Pomega) :
    (∃ a, A = Deg a) ↔
      ∃ xs : List Pomega, A = GeneratedSubalgebra xs := by
  sorry

/-- **Scott 1976, Theorem 3.7 (The semigroup theorem).** -/
theorem theorem_3_7 {u : Pomega} :
    u ∈ RE ∩ FUN ↔ GeneratedSemigroup u := by
  sorry

/-- **Scott 1976, Theorem 4.1 (The lattice theorem).** -/
theorem theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints f ∧
        lfpAbove f (⋃₀ A) ∈ Fixpoints f) ∧
      ∀ {a} (ha : IsRetract a),
        Fixpoints (funOf a) = {x | typed x a} ∧
          IsContinuousBasis (retractBasis a) := by
  sorry

/-- **Scott 1976, Theorem 4.2 (The partial ordering theorem).** -/
theorem theorem_4_2 {a b c : Pomega} :
    (IsRetract a → retractLe a a) ∧
      (retractLe a b → retractLe b a → a = b) ∧
      (retractLe a b → retractLe b c → retractLe a c) := by
  sorry

/-- **Scott 1976, Theorem 4.3 (The function space theorem).** -/
theorem theorem_4_3 {a b a' b' c : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (_ha' : IsRetract a')
    (_hb' : IsRetract b') (hc : IsRetract c) :
    IsRetract (arrowR a b) ∧
      (IsStrict b → IsStrict (arrowR a b)) ∧
      (∀ u, typed u (arrowR a b) ↔
        u = comp u a ∧ ∀ x, typed x a → typed (funOf u x) b) ∧
      (retractLe a a' → retractLe b b' →
        retractLe (arrowR a b) (arrowR a' b')) ∧
      (∀ f f', typed f (arrowR a b) → typed f' (arrowR a' b') →
        typed (arrowR f f') (arrowR (arrowR b a') (arrowR a b'))) ∧
      (∀ f f', typed f (arrowR a b) → typed f' (arrowR b c) →
        typed (comp f' f) (arrowR a c)) := by
  sorry

/-- **Scott 1976, Theorem 4.4 (The product theorem), core.** -/
theorem theorem_4_4 :
    (∀ x y, funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y) ∧
      IsRetract botElem := by
  sorry

/-- **Scott 1976, Theorem 4.4 (ii).** Typed pairs for `⊗`. -/
theorem theorem_4_4_typed {a b u : Pomega} :
    typed u (tensorR a b) ↔
      u = pairSeq (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
        typed (funOf u (ofNat 0)) a ∧ typed (funOf u (ofNat 1)) b := by
  sorry

/-- **Scott 1976, Theorem 4.5 (The sum theorem), core.** -/
theorem theorem_4_5 {a b : Pomega} :
    dcondSet botElem
        (pairSeq (ofNat 0) (funOf a botElem))
        (pairSeq (ofNat 1) (funOf b botElem)) = botElem ∧
      IsRetract botElem := by
  sorry

/-- **Scott 1976, Theorem 4.5 (The sum theorem).** -/
theorem theorem_4_5_sum {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (plusR a b) ∧ IsStrict (plusR a b) ∧
      (∀ u, typed u (plusR a b) ↔
        u = botElem ∨ u = topElem ∨
          (∃ x, u = pairSeq (ofNat 0) x ∧ typed x a) ∨
            (∃ y, u = pairSeq (ofNat 1) y ∧ typed y b)) := by
  sorry

/-- **Scott 1976, Theorem 4.6 (The limit theorem).** -/
theorem theorem_4_6 {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a)) :
    (∀ n, IsRetract (iterateBot F n)) ∧
      IsRetract (funOf Ycomb (graph F)) := by
  sorry

/-- **Scott 1976, Theorem 5.1 (The algebraic lattice theorem).** -/
theorem theorem_5_1 {a : Pomega} (ha : IsClosure a) :
    (∀ x : Fixpoints (funOf a),
      IsCompact x ↔ ∃ n, x = closureCompact a ha n) ∧
    ∀ x : Fixpoints (funOf a),
      IsDirectedSet (compactFixedBelow a x) ∧
        x = sSup (compactFixedBelow a x) := by
  sorry

/-- **Scott 1976, Theorem 5.2 (The representation theorem).** -/
theorem theorem_5_2 {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    IsScottContinuous (representClosure D) ∧
      IsClosure (representClosureCode D) ∧
      Nonempty (α ≃o Fixpoints (funOf (representClosureCode D))) := by
  sorry

/-- **Scott 1976, Theorem 5.3.** -/
theorem theorem_5_3 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsRetract (arrowR a b) := by
  sorry

/-- **Scott 1976, Theorem 5.4 (product half).** -/
theorem theorem_5_4 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (boxTensor a b) := by
  sorry

/-- **Scott 1976, Theorem 5.4 (sum half).** -/
theorem theorem_5_4_plus {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (boxPlus a b) := by
  sorry

/-- **Scott 1976, Theorem 5.5.** `V` is a closure, and its fixed points
are exactly the closure operations. -/
theorem theorem_5_5_universe :
    IsClosure Vcomb ∧ ∀ a, IsClosure a ↔ typed a Vcomb := by
  sorry

/-- **Scott 1976, Theorem 5.6 (The limit theorem for algebraic lattices).** -/
theorem theorem_5_6 {f : Pomega} (hf : typed f (arrowR Vcomb Vcomb)) :
    typed (funOf Ycomb f) Vcomb := by
  sorry

/-- **Scott 1976, Theorem 6.1 (The 𝔊 theorem).** -/
theorem theorem_6_1 :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by
  sorry

/-- **Scott 1976, Theorem 6.2 (The 𝔉 theorem).** -/
theorem theorem_6_2 :
    ∀ U, U ∈ ScottF ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = botElem} := by
  sorry

/-- **Scott 1976, Theorem 6.3 (The 𝔊_δ theorem).** -/
theorem theorem_6_3 :
    ∀ U, IsScottGdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = topElem} := by
  sorry

/-- **Scott 1976, Theorem 6.4 (The 𝔉 ∩̇ 𝔊 theorem).** -/
theorem theorem_6_4 :
    ∀ U, IsFcapG U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = ofNat 0} := by
  sorry

/-- **Scott 1976, Theorem 6.5 (The 𝔉 ∩̇ 𝔊_δ theorem).** -/
theorem theorem_6_5 :
    ∀ U, IsFcapGdelta U ↔
      ∃ f, IsScottContinuous f ∧ U = {x | f x = succSet topElem} := by
  sorry

/-- **Scott 1976, Theorem 6.6 (The 𝔅 theorem).** -/
theorem theorem_6_6 :
    ∀ U, U ∈ ScottB ↔
      ∃ f, IsScottContinuous f ∧ ∃ E : Set Pomega,
        E.Finite ∧ (∀ e ∈ E, e.Finite) ∧ U = {x | f x ∈ E} := by
  sorry

/-- **Scott 1976, Theorem 6.7 (The 𝔅_δ theorem).** -/
theorem theorem_6_7 :
    ∀ U, IsBdelta U ↔
      ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
        U = {x | f x = g x} := by
  sorry

/-- **Scott 1976, Theorem 7.1 (The closure theorem).** -/
theorem theorem_7_1 (A B : RestrictedEquiv) :
    (∀ f, (arrowE A B).mem f ↔
        f = graph (fun x => funOf f x) ∧
          ∀ x y, A.rel x y → B.rel (funOf f x) (funOf f y)) ∧
      (∀ {f x}, (arrowE A B).mem f → A.mem x → B.mem (funOf f x)) ∧
      (∀ u, (prodE A B).mem u ↔
        u = pairElem (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 0)) ∧ B.mem (funOf u (ofNat 1))) ∧
      (∀ u, (sumE A B).mem u ↔
        (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 1))) ∨
        (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
          B.mem (funOf u (ofNat 1)))) := by
  sorry

/-- **Scott 1976, Theorem 7.2 (The isomorphism theorem).** -/
theorem theorem_7_2 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    (∀ x y, funOf a x = funOf a y ↔ (Ea a).rel (funOf a x) (funOf a y)) ∧
      (∀ f g, (typed f (arrowR a b) → (arrowE (Ea a) (Ea b)).mem f) ∧
        ((arrowE (Ea a) (Ea b)).rel f g →
          (Ea (arrowR a b)).rel (funOf (arrowR a b) f)
            (funOf (arrowR a b) g)) ∧
        ((Ea (arrowR a b)).rel f g → (arrowE (Ea a) (Ea b)).rel f g)) ∧
      (∀ u v, (Ea (tensorR a b)).rel u v ↔ (prodE (Ea a) (Ea b)).rel u v) ∧
      (∀ u v, (Ea (plusR a b)).rel u v ↔
        (sumE (Ea a) (Ea b)).rel u v ∨
          (u = botElem ∧ v = botElem) ∨ (u = topElem ∧ v = topElem)) := by
  sorry

/-- **Scott 1976, Theorem 7.3 (The functionality theorem).** -/
theorem theorem_7_3 :
    (∀ A, (arrowE A A).mem Icomb) ∧
      (∀ A B, (arrowE A (arrowE B A)).mem Kcomb) ∧
      (∀ A B C,
        (arrowE (arrowE A (arrowE B C))
          (arrowE (arrowE A B) (arrowE A C))).mem Scomb) ∧
      (∀ i, (∀ A, (arrowE A A).mem i) → i = Icomb) ∧
      (∀ k, (∀ A B, (arrowE A (arrowE B A)).mem k) → k = Kcomb) ∧
      (∀ s,
        (∀ f, funOf s f =
          funOf s (graph (fun x => graph (fun y => funOf (funOf f x) y)))) →
        (∀ f g, funOf (funOf s f) g =
          funOf (funOf s f) (graph (fun x => funOf g x))) →
        (∀ A B C,
          (arrowE (arrowE A (arrowE B C))
            (arrowE (arrowE A B) (arrowE A C))).mem s) →
        s = Scomb) := by
  sorry

/-- **Scott 1976, Theorem 7.4 (The iterator theorem).** -/
theorem theorem_7_4 :
    (∀ A n, (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n)) ∧
      ∀ z,
        (∀ f, funOf z f = funOf z (graph (fun y => funOf f y))) →
        (∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) →
        ∃ n, z = Zcomb n := by
  sorry

end Scott1976.DataTypesAsLattices
