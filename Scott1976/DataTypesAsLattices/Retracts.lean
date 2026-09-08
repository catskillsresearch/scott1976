/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott1976.DataTypesAsLattices.FixedLattices
import Scott1976.DataTypesAsLattices.Lambda

/-!
# Scott 1976, §4 — retracts and data types

Definitions of composition, retracts, `⊑`, `∘→`, `⊗`, `⊕`, and
Theorems 4.1–4.6.
-/

namespace Scott1976.DataTypesAsLattices

/-- **Scott 1976, (4.5).** Composition `u ∘ v = λx. u(v(x))`. -/
def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

theorem comp_isScottContinuous_right (u : Pomega) :
    IsScottContinuous (fun v => comp u v) :=
  graph_const_isScottContinuous (fun v x => funOf u (funOf v x))
    (fun x => theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous_left x))

theorem comp_app (u v x : Pomega) :
    funOf (comp u v) x = funOf u (funOf v x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous v)) x

/-- **Scott 1976, §4, Definition.** `a` is a retract iff `a = a ∘ a`. -/
def IsRetract (a : Pomega) : Prop :=
  a = comp a a

/-- The range / fixed-point set of a map. -/
def Fixpoints (f : Pomega → Pomega) : Set Pomega :=
  {x | f x = x}

/-- Directedness of fixed points under subset, without a lattice instance. -/
def IsDirectedSubset {f : Pomega → Pomega} (s : Set (Fixpoints f)) : Prop :=
  s.Nonempty ∧
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∃ z ∈ s, (x : Pomega) ⊆ z ∧ (y : Pomega) ⊆ z

/-- Compactness of a fixed point under subset, without a lattice instance. -/
def IsCompactSubset {f : Pomega → Pomega} (x : Fixpoints f) : Prop :=
  ∀ s : Set (Fixpoints f),
    IsDirectedSubset s →
      (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
      ∃ z ∈ s, (x : Pomega) ⊆ z

/-- **Scott 1976, §4, Definition.** `u : a` means `u = a(u)`. -/
def typed (u a : Pomega) : Prop :=
  u = funOf a u

/-- **Scott 1976, (4.1).** The function-space retract `fun = λu λx. u(x)`. -/
def funRetract : Pomega :=
  graph (fun u => graph (fun x => funOf u x))

theorem funRetract_app (u : Pomega) :
    funOf funRetract u = graph (fun x => funOf u x) :=
  beta (graph_const_isScottContinuous (fun u x => funOf u x)
    (fun x => funOf_isScottContinuous_left x)) u

/-- **Scott 1976, (4.8).** Function space of retracts `a ∘→ b = λu. b ∘ u ∘ a`. -/
def arrowR (a b : Pomega) : Pomega :=
  graph (fun u => comp b (comp u a))

/-- **Scott 1976, (4.14)–(4.15).** Projections of a pair-as-function. -/
def fstC : Pomega := graph (fun u => funOf u (ofNat 0))
def sndC : Pomega := graph (fun u => funOf u (ofNat 1))

theorem fstC_app (u : Pomega) : funOf fstC u = funOf u (ofNat 0) :=
  beta (funOf_isScottContinuous_left (ofNat 0)) u

theorem sndC_app (u : Pomega) : funOf sndC u = funOf u (ofNat 1) :=
  beta (funOf_isScottContinuous_left (ofNat 1)) u

/-- **Scott 1976, (2.21) / (4.2).** Pairing as a distributive sequence. -/
def pairSeq (x y : Pomega) : Pomega := seq2 x y

/-- **Scott 1976, (4.9).** Product of retracts `a ⊗ b = λu. ⟨a(u₀), b(u₁)⟩`. -/
def tensorR (a b : Pomega) : Pomega :=
  graph (fun u =>
    pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))

/-- **Scott 1976, (4.10), modified.** The displayed equation writes the
ordinary McCarthy conditional `⊃`. Lean uses the doubly strict
conditional `⊐` of (4.4), as in `bool` (4.3), which (4.8)–(4.10)
generalize. Mixed tags therefore map to `⊤` rather than the union of
the two injections; that is required for `⊕` to be a retract
(Theorem 4.5). This is not a symbol-for-symbol transcription of the
displayed (4.10). -/
def plusR (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (funOf u (ofNat 0))
      (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
      (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))

/-- **Scott 1976, §4, Definition.** `a ⊑ b` iff `a = a ∘ b = b ∘ a`. -/
def retractLe (a b : Pomega) : Prop :=
  a = comp a b ∧ a = comp b a

theorem retractLe_refl {a : Pomega} (ha : IsRetract a) : retractLe a a :=
  ⟨ha, ha⟩

theorem retractLe_trans {a b c : Pomega}
    (hab : retractLe a b) (hbc : retractLe b c) :
    a = comp a c ∧ a = comp c a := by
  rcases hab with ⟨hab₁, hab₂⟩
  rcases hbc with ⟨hbc₁, hbc₂⟩
  constructor
  · -- `a ∘ c = (a ∘ b) ∘ c = a ∘ (b ∘ c) = a ∘ b = a`
    apply Eq.trans hab₁
    apply Eq.symm
    calc
      comp a c = graph (fun x => funOf a (funOf c x)) := rfl
      _ = graph (fun x => funOf (comp a b) (funOf c x)) := by simp [← hab₁]
      _ = graph (fun x => funOf a (funOf b (funOf c x))) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf (comp b c) x)) := by simp [comp_app]
      _ = graph (fun x => funOf a (funOf b x)) := by simp [← hbc₁]
      _ = comp a b := rfl
  · -- `c ∘ a = c ∘ (b ∘ a) = (c ∘ b) ∘ a = b ∘ a = a`
    apply Eq.trans hab₂
    apply Eq.symm
    calc
      comp c a = graph (fun x => funOf c (funOf a x)) := rfl
      _ = graph (fun x => funOf c (funOf (comp b a) x)) := by simp [← hab₂]
      _ = graph (fun x => funOf c (funOf b (funOf a x))) := by simp [comp_app]
      _ = graph (fun x => funOf (comp c b) (funOf a x)) := by simp [comp_app]
      _ = graph (fun x => funOf b (funOf a x)) := by
        -- `c ∘ b = b` is `hbc₂`? `retractLe b c` is `b = b ∘ c` and `b = c ∘ b`
        simp [← hbc₂]
      _ = comp b a := rfl

/-- **Scott 1976, Theorem 4.2 (The partial ordering theorem).** -/
theorem theorem_4_2 {a b c : Pomega} :
    (IsRetract a → retractLe a a) ∧
      (retractLe a b → retractLe b a → a = b) ∧
      (retractLe a b → retractLe b c → retractLe a c) := by
  refine ⟨retractLe_refl, ?_, ?_⟩
  · intro hab hba
    exact hab.1.trans (hba.2.symm)
  · intro hab hbc
    exact retractLe_trans hab hbc

/-- Directed iterates of `f` starting from `x` (Scott's sup construction). -/
def iterateFrom (f : Pomega → Pomega) (x : Pomega) : ℕ → Pomega
  | 0 => x
  | n + 1 => f (iterateFrom f x n)

/-- Least upper bound of fixed points above `x`: `⋃_n fⁿ(x)`. -/
def lfpAbove (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, iterateFrom f x n

/-- Greatest postfixed point of `z ↦ f z ∩ b` (Knaster–Tarski inf below `b`). -/
def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  ⋃₀ {x | x ⊆ f x ∩ b}

/-- The identity combinator `I = λu. u`, the largest retract. -/
def Icomb : Pomega := graph (fun x => x)

theorem Icomb_app (x : Pomega) : funOf Icomb x = x :=
  beta id_isScottContinuous x

theorem Icomb_isRetract : IsRetract Icomb := by
  change Icomb = graph (fun x => funOf Icomb (funOf Icomb x))
  have : (fun x => funOf Icomb (funOf Icomb x)) = fun x => x := by
    funext x
    simp [Icomb_app]
  rw [this]
  rfl

theorem inter_const_isScottContinuous {f : Pomega → Pomega}
    (hf : IsScottContinuous f) (b : Pomega) :
    IsScottContinuous (fun z => f z ∩ b) := by
  intro x
  ext k
  constructor
  · intro ⟨hkf, hkb⟩
    have : k ∈ scottUnion f x := by rwa [← hf x]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn, hkb⟩
  · intro hk
    obtain ⟨n, hn, hkn, hkb⟩ := mem_scottUnion.mp hk
    exact ⟨isScottContinuous_monotone hf hn hkn, hkb⟩

theorem iterateFrom_mono {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (hx : x ⊆ f x) :
    ∀ n, iterateFrom f x n ⊆ iterateFrom f x (n + 1)
  | 0 => hx
  | n + 1 => isScottContinuous_monotone hf (iterateFrom_mono hf hx n)

theorem iterateFrom_bot (f : Pomega → Pomega) (n : ℕ) :
    iterateFrom f botElem n = iterateBot f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterateFrom, iterateBot, ih]

theorem lfpAbove_bot (f : Pomega → Pomega) : lfpAbove f botElem = fix f := by
  simp [lfpAbove, fix, iterateFrom_bot]

theorem sUnion_Fixpoints_le_image {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} (hA : A ⊆ Fixpoints f) :
    ⋃₀ A ⊆ f (⋃₀ A) := by
  intro k hk
  obtain ⟨x, hxA, hkx⟩ := Set.mem_sUnion.mp hk
  have hx : f x = x := hA hxA
  have : k ∈ f x := by rwa [hx]
  exact isScottContinuous_monotone hf (Set.subset_sUnion_of_mem hxA) this

theorem lfpAbove_fixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (hx : x ⊆ f x) : f (lfpAbove f x) = lfpAbove f x := by
  have hchain := chain_lemma hf (iterateFrom f x) (iterateFrom_mono hf hx)
  unfold lfpAbove
  rw [hchain]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n + 1, hkn⟩
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    cases n with
    | zero => exact Set.mem_iUnion.mpr ⟨0, hx hkn⟩
    | succ n => exact Set.mem_iUnion.mpr ⟨n, hkn⟩

theorem lfpAbove_ub {f : Pomega → Pomega} {A : Set Pomega} :
    ∀ x ∈ A, x ⊆ lfpAbove f (⋃₀ A) := by
  intro x hx k hk
  exact Set.mem_iUnion.mpr ⟨0, Set.subset_sUnion_of_mem hx hk⟩

theorem lfpAbove_le_of_ub {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} {z : Pomega} (hz : f z = z) (hub : ∀ x ∈ A, x ⊆ z) :
    lfpAbove f (⋃₀ A) ⊆ z := by
  have h0 : ⋃₀ A ⊆ z := by
    intro k hk
    obtain ⟨x, hxA, hkx⟩ := Set.mem_sUnion.mp hk
    exact hub x hxA hkx
  have hiter : ∀ n, iterateFrom f (⋃₀ A) n ⊆ z := by
    intro n
    induction n with
    | zero => simpa [iterateFrom] using h0
    | succ n ih => simpa [iterateFrom, hz] using isScottContinuous_monotone hf ih
  intro k hk
  obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
  exact hiter n hkn

theorem lfpAbove_mem {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} (hA : A ⊆ Fixpoints f) :
    lfpAbove f (⋃₀ A) ∈ Fixpoints f :=
  lfpAbove_fixed hf (sUnion_Fixpoints_le_image hf hA)

theorem gfpBelow_le {f : Pomega → Pomega} (_hf : IsScottContinuous f) (b : Pomega)
    (_hb : f b ⊆ b) : gfpBelow f b ⊆ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  exact (hx hkx).2

theorem gfpBelow_subset (f : Pomega → Pomega) (b : Pomega) :
    gfpBelow f b ⊆ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  exact (hx hkx).2

theorem gfpBelow_postfixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (b : Pomega) : gfpBelow f b ⊆ f (gfpBelow f b) ∩ b := by
  intro k hk
  obtain ⟨x, hx, hkx⟩ := Set.mem_sUnion.mp hk
  have hxz : x ⊆ gfpBelow f b := fun _ hm => Set.mem_sUnion.mpr ⟨x, hx, hm⟩
  exact ⟨isScottContinuous_monotone hf hxz (hx hkx).1, (hx hkx).2⟩

theorem gfpBelow_fixed_inter {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (b : Pomega) : f (gfpBelow f b) ∩ b = gfpBelow f b := by
  apply subset_antisymm
  · intro k hk
    refine Set.mem_sUnion.mpr ⟨f (gfpBelow f b) ∩ b, ?_, hk⟩
    have hle : gfpBelow f b ⊆ f (gfpBelow f b) ∩ b := gfpBelow_postfixed hf b
    have : f (gfpBelow f b) ⊆ f (f (gfpBelow f b) ∩ b) :=
      isScottContinuous_monotone hf hle
    intro m hm
    exact ⟨this hm.1, hm.2⟩
  · exact gfpBelow_postfixed hf b

/-- **Scott 1976, Theorem 4.1 (The lattice theorem), complete-lattice half.**
The inf `gfpBelow f (⋂ A)` is a fixed point of `f` itself. -/
theorem theorem_4_1_complete (f : Pomega → Pomega) (hf : IsScottContinuous f)
    (A : Set Pomega) (hA : A ⊆ Fixpoints f) :
    gfpBelow f (⋂₀ A) ∈ Fixpoints f := by
  let z := gfpBelow f (⋂₀ A)
  have hinter : f z ∩ ⋂₀ A = z := gfpBelow_fixed_inter hf (⋂₀ A)
  have hzle : z ⊆ ⋂₀ A := gfpBelow_subset f (⋂₀ A)
  have hfz : f z ⊆ ⋂₀ A := by
    intro k hk y hy
    have hzy : z ⊆ y := subset_trans hzle (Set.sInter_subset_of_mem hy)
    have : k ∈ f y := isScottContinuous_monotone hf hzy hk
    have hyf : f y = y := hA hy
    rwa [hyf] at this
  have : f z ∩ ⋂₀ A = f z := Set.inter_eq_left.mpr hfz
  change f z = z
  rwa [this] at hinter

theorem gfpBelow_isGLB {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    {A : Set Pomega} (_hA : A ⊆ Fixpoints f) {z : Pomega}
    (hz : f z = z) (hlb : ∀ x ∈ A, z ⊆ x) :
    z ⊆ gfpBelow f (⋂₀ A) := by
  have hzI : z ⊆ ⋂₀ A := fun k hk y hy => hlb y hy hk
  have hpost : z ⊆ f z ∩ ⋂₀ A := fun k hk => ⟨by rwa [hz], hzI hk⟩
  exact fun k hk => Set.mem_sUnion.mpr ⟨z, hpost, hk⟩

/-- Continuous-lattice interpolation: `x = ⋃ { a(e n) | e n ⊆ x }`. -/
theorem retract_interpolation {a x : Pomega} (_ha : IsRetract a) (hx : typed x a) :
    x = ⋃ n, {k | e n ⊆ x ∧ k ∈ funOf a (e n)} := by
  have hx' : funOf a x = x := hx.symm
  have hsc := funOf_isScottContinuous a x
  apply subset_antisymm
  · intro k hk
    have : k ∈ funOf a x := by rwa [hx']
    have : k ∈ scottUnion (funOf a) x := by rwa [← hsc]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
  · intro k hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp hk
    have : k ∈ funOf a x :=
      isScottContinuous_monotone (funOf_isScottContinuous a) hn hkn
    rwa [hx'] at this

/-- Image of a set of fixed-point subtypes. -/
def Fixpoints.vals {f : Pomega → Pomega} (A : Set (Fixpoints f)) : Set Pomega :=
  Subtype.val '' A

theorem Fixpoints.vals_subset {f : Pomega → Pomega} (A : Set (Fixpoints f)) :
    Fixpoints.vals A ⊆ Fixpoints f := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

/-- Scott's complete lattice of fixed points. -/
@[instance_reducible]
def fixpointsCompleteLattice {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    CompleteLattice (Fixpoints f) :=
  letI : SupSet (Fixpoints f) :=
    ⟨fun A => ⟨lfpAbove f (⋃₀ (Fixpoints.vals A)),
      lfpAbove_mem hf (Fixpoints.vals_subset A)⟩⟩
  { completeLatticeOfSup (Fixpoints f) (fun A => by
      refine ⟨?ub, ?least⟩
      · intro x hx
        change (x : Pomega) ⊆ lfpAbove f (⋃₀ (Fixpoints.vals A))
        exact lfpAbove_ub x.val ⟨x, hx, rfl⟩
      · intro z hz
        change lfpAbove f (⋃₀ (Fixpoints.vals A)) ⊆ z
        exact lfpAbove_le_of_ub hf z.property (fun y hy => by
          obtain ⟨w, hwA, rfl⟩ := hy
          exact hz hwA)) with
    sInf := fun A => ⟨gfpBelow f (⋂₀ (Fixpoints.vals A)),
      theorem_4_1_complete f hf (Fixpoints.vals A) (Fixpoints.vals_subset A)⟩
    isGLB_sInf := fun A => by
      refine ⟨?lb, ?greatest⟩
      · intro x hx
        change gfpBelow f (⋂₀ (Fixpoints.vals A)) ⊆ x
        exact subset_trans (gfpBelow_subset f _)
          (Set.sInter_subset_of_mem ⟨x, hx, rfl⟩)
      · intro z hz
        change (z : Pomega) ⊆ gfpBelow f (⋂₀ (Fixpoints.vals A))
        exact gfpBelow_isGLB hf (Fixpoints.vals_subset A) z.property (fun y hy => by
          obtain ⟨w, hwA, rfl⟩ := hy
          exact hz hwA)
    bot := ⟨fix f, (theorem_1_4 hf).1⟩
    bot_le := fun x => (theorem_1_4 hf).2 x.val x.property }

noncomputable instance fixpointsFunOfCompleteLattice (a : Pomega) :
    CompleteLattice (Fixpoints (funOf a)) :=
  fixpointsCompleteLattice (funOf_isScottContinuous a)

theorem retract_app {a : Pomega} (ha : IsRetract a) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := congrArg (fun u => funOf u x) ha
  simpa [comp_app] using this.symm

theorem directed_finite_cover {A : Set (Fixpoints f)}
    (hA : IsDirectedSet A) {t : Pomega} (ht : t.Finite)
    (hsub : t ⊆ ⋃₀ (Fixpoints.vals A)) :
    ∃ z ∈ A, t ⊆ z := by
  classical
  have aux : ∀ s : Finset ℕ,
      (s : Set ℕ) ⊆ ⋃₀ (Fixpoints.vals A) →
        ∃ z ∈ A, (s : Set ℕ) ⊆ z := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro _
        obtain ⟨z, hz⟩ := hA.1
        exact ⟨z, hz, by simp⟩
    | insert k s hks ih =>
        intro hs
        obtain ⟨u, hu, hsu⟩ :=
          ih (fun m hm => hs (by simp [hm]))
        obtain ⟨v, hv, hkv⟩ :=
          Set.mem_sUnion.mp
            (hs (show k ∈ (insert k s : Finset ℕ) by simp))
        obtain ⟨v', hv'A, rfl⟩ := hv
        obtain ⟨z, hz, huz, hvz⟩ := hA.2 hu hv'A
        refine ⟨z, hz, ?_⟩
        intro m hm
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hm
        rcases hm with rfl | hm
        · exact hvz hkv
        · exact huz (hsu hm)
  obtain ⟨z, hzA, hz⟩ := aux ht.toFinset (by simpa using hsub)
  exact ⟨z, hzA, fun m hm => hz (by simpa using hm)⟩

theorem directed_sUnion_fixed {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set (Fixpoints f)} (hA : IsDirectedSet A) :
    ⋃₀ (Fixpoints.vals A) ∈ Fixpoints f := by
  apply subset_antisymm
  · intro k hk
    have hk' : k ∈ scottUnion f (⋃₀ (Fixpoints.vals A)) := by
      rwa [← hf (⋃₀ (Fixpoints.vals A))]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk'
    obtain ⟨z, hzA, hnz⟩ :=
      directed_finite_cover hA (e_finite n) hn
    have : k ∈ f z :=
      isScottContinuous_monotone hf hnz hkn
    rw [z.property] at this
    exact Set.mem_sUnion.mpr ⟨z, ⟨z, hzA, rfl⟩, this⟩
  · exact sUnion_Fixpoints_le_image hf (Fixpoints.vals_subset A)

theorem sSup_fixed_eq_sUnion {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set (Fixpoints f)} (hA : IsDirectedSet A) :
    ((@sSup (Fixpoints f) (fixpointsCompleteLattice hf).toSupSet A :
        Fixpoints f) : Pomega) =
      ⋃₀ (Fixpoints.vals A) := by
  letI := fixpointsCompleteLattice hf
  let u : Fixpoints f :=
    ⟨⋃₀ (Fixpoints.vals A), directed_sUnion_fixed hf hA⟩
  apply subset_antisymm
  · have hle : sSup A ≤ u := by
      apply sSup_le
      intro x hx
      exact Set.subset_sUnion_of_mem ⟨x, hx, rfl⟩
    exact hle
  · intro k hk
    obtain ⟨x, hxA, hkx⟩ := Set.mem_sUnion.mp hk
    obtain ⟨y, hyA, rfl⟩ := hxA
    exact (le_sSup hyA) hkx

/-- The canonical finite-image basis of the fixed-point lattice of a retract. -/
def retractBasis (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {y | ∃ n, e n ⊆ x ∧ (y : Pomega) = funOf a (e n)}

theorem retractBasis_directed {a : Pomega} (ha : IsRetract a)
    (x : Fixpoints (funOf a)) :
    IsDirectedSet (retractBasis a x) := by
  constructor
  · let y : Fixpoints (funOf a) :=
      ⟨funOf a (e 0), retract_app ha (e 0)⟩
    exact ⟨y, 0, by simp [e_zero], rfl⟩
  · intro y hy z hz
    obtain ⟨n, hnx, hyn⟩ := hy
    obtain ⟨m, hmx, hzm⟩ := hz
    let w : Fixpoints (funOf a) :=
      ⟨funOf a (e (n ||| m)), retract_app ha (e (n ||| m))⟩
    refine ⟨w, ⟨n ||| m, e_or_of_subset hnx hmx, rfl⟩, ?_, ?_⟩
    · change (y : Pomega) ⊆ (w : Pomega)
      rw [hyn]
      change funOf a (e n) ⊆ funOf a (e (n ||| m))
      rw [e_or]
      exact isScottContinuous_monotone (funOf_isScottContinuous a)
        Set.subset_union_left
    · change (z : Pomega) ⊆ (w : Pomega)
      rw [hzm]
      change funOf a (e m) ⊆ funOf a (e (n ||| m))
      rw [e_or]
      exact isScottContinuous_monotone (funOf_isScottContinuous a)
        Set.subset_union_right

theorem retractBasis_wayBelow {a : Pomega} (ha : IsRetract a)
    {x y : Fixpoints (funOf a)} (hy : y ∈ retractBasis a x) :
    WayBelow y x := by
  intro A hA hxA
  obtain ⟨n, hnx, hyn⟩ := hy
  have hsup :
      ((sSup A : Fixpoints (funOf a)) : Pomega) =
        ⋃₀ (Fixpoints.vals A) :=
    sSup_fixed_eq_sUnion (funOf_isScottContinuous a) hA
  have hfinite :
      e n ⊆ ⋃₀ (Fixpoints.vals A) := by
    rw [← hsup]
    exact hnx.trans hxA
  obtain ⟨z, hzA, hnz⟩ :=
    directed_finite_cover hA (e_finite n) hfinite
  refine ⟨z, hzA, ?_⟩
  change (y : Pomega) ⊆ z
  rw [hyn]
  have := isScottContinuous_monotone (funOf_isScottContinuous a) hnz
  rwa [z.property] at this

theorem retractBasis_sSup {a : Pomega} (ha : IsRetract a)
    (x : Fixpoints (funOf a)) :
    x = sSup (retractBasis a x) := by
  apply Subtype.ext
  rw [sSup_fixed_eq_sUnion (funOf_isScottContinuous a)
    (retractBasis_directed ha x)]
  have hx : typed (x : Pomega) a := x.property.symm
  rw [retract_interpolation ha hx]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hnx, hkn⟩ := Set.mem_iUnion.mp hk
    let y : Fixpoints (funOf a) :=
      ⟨funOf a (e n), retract_app ha (e n)⟩
    exact Set.mem_sUnion.mpr
      ⟨y, ⟨y, ⟨n, hnx, rfl⟩, rfl⟩, hkn⟩
  · intro hk
    obtain ⟨_, ⟨y, ⟨n, hnx, hyn⟩, rfl⟩, hky⟩ :=
      Set.mem_sUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, hnx, hyn ▸ hky⟩

theorem retractBasis_sUnion {a : Pomega} (ha : IsRetract a)
    (x : Fixpoints (funOf a)) :
    (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  have h := retractBasis_sSup ha x
  have hsu := sSup_fixed_eq_sUnion (funOf_isScottContinuous a)
    (retractBasis_directed ha x)
  have : (x : Pomega) = (sSup (retractBasis a x) : Fixpoints (funOf a)) :=
    congrArg Subtype.val h
  exact this.trans hsu

theorem retractBasis_directedSubset {a : Pomega} (ha : IsRetract a)
    (x : Fixpoints (funOf a)) :
    IsDirectedSubset (retractBasis a x) := by
  have h := retractBasis_directed ha x
  refine ⟨h.1, ?_⟩
  intro y hy z hz
  obtain ⟨w, hw, hyw, hzw⟩ := h.2 hy hz
  exact ⟨w, hw, hyw, hzw⟩

/-- **Scott 1976, Theorem 4.1, continuous-lattice half.**
The finite-image points form a directed way-below basis for every point in
the range of a retract. -/
theorem theorem_4_1_continuous {a : Pomega} (ha : IsRetract a) :
    IsContinuousBasis (retractBasis a) := by
  intro x
  exact ⟨retractBasis_directed ha x,
    fun y hy => retractBasis_wayBelow ha hy,
    retractBasis_sSup ha x⟩

/-- **Scott 1976, Theorem 4.1 (The lattice theorem).**
Fixed points of a continuous function form a complete lattice under `⊆`;
those of a retract form a continuous lattice. -/
theorem theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints f ∧
        lfpAbove f (⋃₀ A) ∈ Fixpoints f) ∧
      ∀ {a} (ha : IsRetract a),
        Fixpoints (funOf a) = {x | typed x a} ∧
          ∀ x : Fixpoints (funOf a),
            IsDirectedSubset (retractBasis a x) ∧
              (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  constructor
  · intro A hA
    exact ⟨theorem_4_1_complete f hf A hA, lfpAbove_mem hf hA⟩
  · intro a ha
    constructor
    · ext x
      simp [Fixpoints, typed, eq_comm]
    · intro x
      exact ⟨retractBasis_directedSubset ha x, retractBasis_sUnion ha x⟩

theorem graph_ext {f g : Pomega → Pomega} (h : ∀ x, f x = g x) :
    graph f = graph g := by
  simp [graph, h]

theorem funRetract_isRetract : IsRetract funRetract := by
  apply graph_ext
  intro u
  rw [funRetract_app, funRetract_app]
  apply graph_ext
  intro x
  exact (beta (funOf_isScottContinuous u) x).symm

theorem comp_right_const (a : Pomega) :
    IsScottContinuous (fun u => comp u a) :=
  graph_const_isScottContinuous (fun u x => funOf u (funOf a x))
    (fun x => funOf_isScottContinuous_left (funOf a x))

theorem arrowR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u => comp b (comp u a)) :=
  theorem_1_3 (comp_isScottContinuous_right b) (comp_right_const a)

theorem arrowR_app (a b u : Pomega) :
    funOf (arrowR a b) u = comp b (comp u a) :=
  beta (arrowR_map_isScottContinuous a b) u

/-- **Scott 1976, Theorem 4.3 (i).** On elements, `a ∘→ b` acts as `b ∘ − ∘ a`,
and that action is idempotent when `a, b` are retracts. -/
theorem theorem_4_3_i {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    funOf (arrowR a b) (funOf (arrowR a b) u) = funOf (arrowR a b) u := by
  rw [arrowR_app, arrowR_app]
  apply graph_ext
  intro x
  simp [comp_app, retract_app ha, retract_app hb]

/-- **Scott 1976, (4.11).** Action of composed function-space retracts. -/
theorem eq_4_11 (a b a' b' u : Pomega) :
    funOf (arrowR a b) (funOf (arrowR a' b') u) =
      comp b (comp (comp b' (comp u a')) a) := by
  rw [arrowR_app, arrowR_app]

/-- **Scott 1976, Theorem 4.3 (ii).** `u : a ∘→ b` means `u` is restricted
to `a` and takes values in `b`. -/
theorem theorem_4_3_ii {a b u x : Pomega}
    (hu : typed u (arrowR a b)) (hx : typed x a) :
    typed (funOf u x) b := by
  have hu' : u = comp b (comp u a) := by
    simpa [typed, arrowR_app] using hu
  have : funOf u x = funOf b (funOf u (funOf a x)) := by
    have h1 : funOf u x = funOf (comp b (comp u a)) x :=
      congrArg (fun w => funOf w x) hu'
    rw [h1, comp_app, comp_app]
  rwa [show funOf a x = x from hx.symm] at this

theorem funOf_botElem (x : Pomega) : funOf botElem x = botElem := by
  ext m
  simp [funOf, botElem]

theorem graph_const_bot : graph (fun _ => botElem) = botElem := by
  ext p
  simp [graph, botElem]

/-- Strictness: `a(⊥) = ⊥`, equivalently `⊥ ⊑ a` for retracts. -/
def IsStrict (a : Pomega) : Prop :=
  funOf a botElem = botElem

theorem typed_of_arrowR {a b u : Pomega} (hu : typed u (arrowR a b)) :
    u = comp b (comp u a) := by
  simpa [typed, arrowR_app] using hu

theorem typed_arrowR_restrict {a b u : Pomega}
    (ha : IsRetract a) (hu : typed u (arrowR a b)) :
    u = comp u a := by
  have hu' := typed_of_arrowR hu
  have h : comp (comp b (comp u a)) a = comp b (comp u a) := by
    apply graph_ext
    intro x
    simp only [comp_app]
    rw [retract_app ha]
  have : comp u a = comp (comp b (comp u a)) a := by
    conv_lhs => rw [hu']
  exact ((this.trans h).trans hu'.symm).symm

theorem typed_arrowR_range {a b u : Pomega}
    (hb : IsRetract b) (hu : typed u (arrowR a b)) :
    u = comp b u := by
  have hu' := typed_of_arrowR hu
  rw [hu']
  apply graph_ext
  intro x
  simp only [comp_app]
  rw [retract_app hb]

/-- **Scott 1976, (4.11).** Composition of function-space retracts. -/
theorem eq_4_11_comp (a b a' b' : Pomega) :
    comp (arrowR a b) (arrowR a' b') = arrowR (comp a' a) (comp b b') := by
  apply graph_ext
  intro u
  calc
    funOf (arrowR a b) (funOf (arrowR a' b') u)
        = comp b (comp (funOf (arrowR a' b') u) a) := arrowR_app _ _ _
    _ = comp b (comp (comp b' (comp u a')) a) := by rw [arrowR_app]
    _ = comp (comp b b') (comp u (comp a' a)) := by
      apply graph_ext
      intro x
      simp only [comp_app]

theorem arrowR_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (arrowR a b) := by
  change arrowR a b =
    graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha hb, arrowR_app]

theorem arrowR_isStrict {a b : Pomega} (hb : IsStrict b) :
    IsStrict (arrowR a b) := by
  change funOf (arrowR a b) botElem = botElem
  rw [arrowR_app]
  have hbot : comp botElem a = botElem := by
    unfold comp
    simp [funOf_botElem, graph_const_bot]
  rw [hbot]
  unfold comp
  simp only [funOf_botElem]
  exact (congrArg graph (funext fun _ => hb)).trans graph_const_bot

theorem typed_arrowR_iff {a b u : Pomega} (ha : IsRetract a) (_hb : IsRetract b) :
    typed u (arrowR a b) ↔
      u = comp u a ∧ ∀ x, typed x a → typed (funOf u x) b := by
  constructor
  · intro hu
    exact ⟨typed_arrowR_restrict ha hu, fun x hx => theorem_4_3_ii hu hx⟩
  · intro ⟨hrest, hval⟩
    change u = funOf (arrowR a b) u
    rw [arrowR_app]
    apply Eq.trans hrest
    apply graph_ext
    intro x
    have hx : typed (funOf a x) a := (retract_app ha x).symm
    have hbx : funOf u (funOf a x) = funOf b (funOf u (funOf a x)) :=
      hval (funOf a x) hx
    simp only [comp_app]
    exact hbx

theorem arrowR_retractLe {a b a' b' : Pomega}
    (hab : retractLe a a') (hbb : retractLe b b') :
    retractLe (arrowR a b) (arrowR a' b') := by
  constructor
  · have h : arrowR (comp a' a) (comp b b') = arrowR a b := by
      rw [← hab.2, ← hbb.1]
    exact (h.symm.trans (eq_4_11_comp a b a' b').symm)
  · have h : arrowR (comp a a') (comp b' b) = arrowR a b := by
      rw [← hab.1, ← hbb.2]
    exact (h.symm.trans (eq_4_11_comp a' b' a b).symm)

theorem arrowR_functor {a b a' b' f f' : Pomega}
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR a' b')) :
    typed (arrowR f f') (arrowR (arrowR b a') (arrowR a b')) := by
  change arrowR f f' =
    funOf (arrowR (arrowR b a') (arrowR a b')) (arrowR f f')
  rw [arrowR_app]
  have inner := eq_4_11_comp f f' b a'
  have outer := eq_4_11_comp a b' (comp b f) (comp f' a')
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  apply Eq.symm
  calc
    comp (arrowR a b') (comp (arrowR f f') (arrowR b a'))
        = comp (arrowR a b') (arrowR (comp b f) (comp f' a')) := by rw [inner]
    _ = arrowR (comp (comp b f) a) (comp b' (comp f' a')) := outer
    _ = arrowR f f' := by
      apply graph_ext
      intro u
      apply graph_ext
      intro x
      have hfx : funOf f x = funOf b (funOf f (funOf a x)) := by
        simpa [comp_app] using congrArg (fun w => funOf w x) hf1
      have hf'y : ∀ y, funOf f' y = funOf b' (funOf f' (funOf a' y)) := by
        intro y
        simpa [comp_app] using congrArg (fun w => funOf w y) hf2
      simp only [arrowR_app, comp_app]
      rw [hfx]
      exact (hf'y _).symm

theorem typed_comp {a b c f f' : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (_hc : IsRetract c)
    (hf : typed f (arrowR a b)) (hf' : typed f' (arrowR b c)) :
    typed (comp f' f) (arrowR a c) := by
  have hf1 := typed_of_arrowR hf
  have hf2 := typed_of_arrowR hf'
  change comp f' f = funOf (arrowR a c) (comp f' f)
  rw [arrowR_app]
  apply graph_ext
  intro x
  have hfx : funOf f x = funOf b (funOf f (funOf a x)) := by
    simpa [comp_app] using congrArg (fun w => funOf w x) hf1
  have hrest := typed_arrowR_restrict ha hf
  have hfa : funOf f (funOf a x) = funOf f x := by
    simpa [comp_app] using (congrArg (fun w => funOf w x) hrest).symm
  have hf'fx : funOf f' (funOf f x) =
      funOf c (funOf f' (funOf b (funOf f x))) := by
    simpa [comp_app] using congrArg (fun w => funOf w (funOf f x)) hf2
  have hrange := typed_arrowR_range hb hf
  have hbval : funOf b (funOf f (funOf a x)) = funOf f (funOf a x) := by
    simpa [comp_app] using (congrArg (fun w => funOf w (funOf a x)) hrange).symm
  simp only [comp_app]
  rw [hf'fx, ← hfa, hbval, hfa]

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
        typed (comp f' f) (arrowR a c)) :=
  ⟨arrowR_isRetract ha hb, arrowR_isStrict, fun _ => typed_arrowR_iff ha hb,
    arrowR_retractLe, fun _ _ => arrowR_functor,
    fun _ _ hf hf' => typed_comp ha hb hc hf hf'⟩

/-- **Scott 1976, (4.16).** Diagonal combinator. -/
def diagC : Pomega := graph (fun u => pairSeq u u)

/-- **Scott 1976, (4.22).** Evaluation combinator. -/
def evalC : Pomega :=
  graph (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)))

/-- **Scott 1976, (4.23).** Currying combinator. -/
def curryC : Pomega :=
  graph (fun u => graph (fun x => graph (fun y => funOf u (pairSeq x y))))

/-- **Scott 1976, (4.7).** The integer functional
`int(u) = u ⊒ 0, (int(u−1) ⊒ u, u)`. -/
def intF (f : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u))

theorem intF_map_isScottContinuous (f : Pomega) :
    IsScottContinuous (fun u =>
      dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u)) :=
  theorem_1_3_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    id_isScottContinuous
    (const_isScottContinuous (ofNat 0))
    (theorem_1_3_nary
      (fun y z => dcondSet_isScottContinuous_left y z)
      (fun x z => dcondSet_isScottContinuous_mid x z)
      (fun x y => dcondSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous f) predSet_isScottContinuous)
      id_isScottContinuous
      id_isScottContinuous)

theorem intF_isScottContinuous : IsScottContinuous intF :=
  graph_const_isScottContinuous
    (fun f u => dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u))
    (fun u =>
      theorem_1_3
        (f := fun z => dcondSet u (ofNat 0) z)
        (g := fun f => dcondSet (funOf f (predSet u)) u u)
        (dcondSet_isScottContinuous_right u (ofNat 0))
        (theorem_1_3
          (f := fun z => dcondSet z u u)
          (g := fun f => funOf f (predSet u))
          (dcondSet_isScottContinuous_left u u)
          (funOf_isScottContinuous_left (predSet u))))

theorem intF_app (f u : Pomega) :
    funOf (intF f) u =
      dcondSet u (ofNat 0) (dcondSet (funOf f (predSet u)) u u) :=
  beta (intF_map_isScottContinuous f) u

/-- **Scott 1976, (4.7).** Integer retract as the least fixed point. -/
def intR : Pomega := fix intF

theorem intR_eq_intF : intF intR = intR :=
  (theorem_1_4 intF_isScottContinuous).1

theorem intR_app (u : Pomega) :
    funOf intR u =
      dcondSet u (ofNat 0) (dcondSet (funOf intR (predSet u)) u u) := by
  have h := congrArg (fun a => funOf a u) intR_eq_intF
  simpa [intF_app] using h.symm

theorem predSet_ofNat_zero : predSet (ofNat 0) = botElem := by
  ext k
  simp [predSet, ofNat, botElem]

theorem intR_bot : funOf intR botElem = botElem := by
  rw [intR_app, dcondSet_bot]

theorem dcondSet_same_ofNat (n : ℕ) (x : Pomega) :
    dcondSet (ofNat n) x x = x :=
  match n with
  | 0 => dcondSet_ofNat_zero x x
  | n + 1 => dcondSet_ofNat_succ n x x

/-- **Scott 1976, after (4.7).** `int({n}) = {n}`. -/
theorem intR_ofNat : ∀ n, funOf intR (ofNat n) = ofNat n
  | 0 => by
    rw [intR_app, dcondSet_ofNat_zero]
  | n + 1 => by
    rw [intR_app, predSet_ofNat_succ, intR_ofNat n, dcondSet_same_ofNat,
      dcondSet_ofNat_succ]

theorem predSet_eq_ofNat_of_no_zero {u : Pomega} {k : ℕ}
    (h0 : 0 ∉ u) (hk : predSet u = ofNat k) :
    u = ofNat (k + 1) := by
  ext m
  constructor
  · intro hm
    have hm0 : m ≠ 0 := fun h => h0 (by simpa [h] using hm)
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have : t ∈ predSet u := hm
    have : t = k := by
      have : t ∈ ofNat k := by rwa [hk] at this
      simpa [ofNat] using this
    simp [ofNat, this]
  · intro hm
    simp [ofNat] at hm
    subst hm
    have : k ∈ predSet u := by
      rw [hk]; simp [ofNat]
    exact this

/-- **Scott 1976, after (4.7).** `int(u) = ⊤` when `u` is not `⊥` and not a
singleton integer. -/
theorem intR_top_of_nonsingleton :
    ∀ n u, n ∈ u → (∀ k ∈ u, n ≤ k) → u ≠ botElem → (∀ k, u ≠ ofNat k) →
      funOf intR u = topElem := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro u hn hmin hne hns
    rw [intR_app]
    by_cases h0 : 0 ∈ u
    · have hp : ∃ t, t + 1 ∈ u := by
        by_contra hp
        apply hns 0
        ext m
        constructor
        · intro hm
          have : m = 0 := by
            by_contra hm0
            obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
            exact hp ⟨t, hm⟩
          simp [ofNat, this]
        · intro hm
          simpa [ofNat] using hm.symm ▸ h0
      rw [dcondSet_of_mixed h0 hp]
    · have hn0 : n ≠ 0 := fun h => h0 (by simpa [h] using hn)
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hn' : n' ∈ predSet u := hn
      have hmin' : ∀ k ∈ predSet u, n' ≤ k := by
        intro k hk
        have : n' + 1 ≤ k + 1 := hmin (k + 1) hk
        omega
      have hne' : predSet u ≠ botElem := by
        intro hempty
        have : n' ∈ predSet u := hn'
        rw [hempty] at this
        simp [botElem] at this
      have hns' : ∀ k, predSet u ≠ ofNat k := by
        intro k hk
        exact hns (k + 1) (predSet_eq_ofNat_of_no_zero h0 hk)
      have hpred : funOf intR (predSet u) = topElem :=
        ih n' (Nat.lt_succ_self n') (predSet u) hn' hmin' hne' hns'
      rw [hpred, dcondSet_top, dcondSet_of_pos_not_zero h0 ⟨n', hn⟩]

theorem intR_top : funOf intR topElem = topElem :=
  intR_top_of_nonsingleton 0 topElem (Set.mem_univ 0)
    (fun _ _ => Nat.zero_le _)
    (by
      intro h
      have : (0 : ℕ) ∈ (botElem : Pomega) := by
        rw [← h]
        exact Set.mem_univ 0
      simp [botElem] at this)
    (fun n h => by
      have h0 : (0 : ℕ) ∈ ofNat n := by
        have : (0 : ℕ) ∈ topElem := Set.mem_univ 0
        rwa [h] at this
      have h1 : (1 : ℕ) ∈ ofNat n := by
        have : (1 : ℕ) ∈ topElem := Set.mem_univ 1
        rwa [h] at this
      simp [ofNat] at h0 h1
      omega)

theorem intR_idem (x : Pomega) : funOf intR (funOf intR x) = funOf intR x := by
  by_cases hbot : x = botElem
  · subst hbot
    rw [intR_bot, intR_bot]
  · by_cases hsing : ∃ n, x = ofNat n
    · obtain ⟨n, rfl⟩ := hsing
      rw [intR_ofNat, intR_ofNat]
    · have hx : funOf intR x = topElem := by
        have hne : x.Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          simpa [botElem] using hbot
        exact intR_top_of_nonsingleton (sInf x) x (Nat.sInf_mem hne)
          (fun k hk => Nat.sInf_le hk) hbot (fun n hn => hsing ⟨n, hn⟩)
      rw [hx, intR_top]

theorem intR_isGraph : intR = graph (funOf intR) := by
  refine intR_eq_intF.symm.trans ?_
  apply graph_ext
  intro u
  exact (intR_app u).symm

theorem intR_isRetract : IsRetract intR := by
  change intR = graph (fun x => funOf intR (funOf intR x))
  refine intR_isGraph.trans ?_
  apply graph_ext
  intro x
  exact (intR_idem x).symm

/-- **Scott 1976, Theorem 4.4 (ii), pairing form.** A pair-as-function
projects to its components. -/
theorem theorem_4_4_ii (x y : Pomega) :
    funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y :=
  ⟨seq2_app_zero x y, seq2_app_one x y⟩

/-- **Scott 1976, Theorem 4.5 (i), strictness of sums.** The zero summand
is always selected on `⊥`. -/
theorem theorem_4_5_strict (a b : Pomega) :
    dcondSet botElem
      (pairSeq (ofNat 0) (funOf a botElem))
      (pairSeq (ofNat 1) (funOf b botElem)) = botElem :=
  dcondSet_bot _ _

/-- **Scott 1976, (4.38).** The tree functor. -/
def treeF (z : Pomega) : Pomega := plusR botElem (tensorR z z)

theorem bot_isRetract : IsRetract botElem := by
  unfold IsRetract comp botElem
  ext p
  simp [graph, funOf]

theorem iterates_areRetracts {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a)) :
    ∀ n, IsRetract (iterateBot F n)
  | 0 => by simpa [iterateBot] using bot_isRetract
  | n + 1 => by simpa [iterateBot] using hret _ (iterates_areRetracts hret n)

theorem retract_isGraph {a : Pomega} (ha : IsRetract a) : graph (funOf a) = a := by
  apply subset_antisymm
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    have ha' : a = graph (fun x => funOf a (funOf a x)) := ha
    have : m ∈ funOf a (funOf a (e n)) := by
      simpa [retract_app ha] using hm
    rw [ha']
    exact ⟨n, m, rfl, this⟩
  · exact theorem_1_2_ii a

theorem iUnion_retract_isGraph {xs : ℕ → Pomega} (h : ∀ n, IsRetract (xs n)) :
    IsGraph (⋃ n, xs n) := by
  intro k m n hkm hkn
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hkm
  have hiG : IsGraph (xs i) := (theorem_1_2_iii (xs i)).mp (retract_isGraph (h i))
  exact Set.mem_iUnion.mpr ⟨i, hiG hi hkn⟩

theorem funOf_fix_idem {F : Pomega → Pomega} (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a)) (x : Pomega) :
    funOf (fix F) (funOf (fix F) x) = funOf (fix F) x := by
  have hchain : ∀ n m, n ≤ m → iterateBot F n ⊆ iterateBot F m :=
    chain_mono (iterateBot F) (iterateBot_mono hf)
  have hidem : ∀ n, funOf (iterateBot F n) (funOf (iterateBot F n) x) =
      funOf (iterateBot F n) x :=
    fun n => retract_app (iterates_areRetracts hret n) x
  have hcl : ∀ n,
      funOf (iterateBot F n) (⋃ m, funOf (iterateBot F m) x) =
        ⋃ m, funOf (iterateBot F n) (funOf (iterateBot F m) x) :=
    fun n => chain_lemma (funOf_isScottContinuous (iterateBot F n))
      (fun m => funOf (iterateBot F m) x)
      (fun m => funOf_monotone_left (iterateBot_mono hf m) x)
  apply subset_antisymm
  · intro k hk
    have hk' : k ∈ funOf (⋃ n, iterateBot F n)
        (⋃ m, funOf (iterateBot F m) x) := by
      simpa [fix, funOf_iUnion] using hk
    obtain ⟨n, hn, hp⟩ := hk'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    have : k ∈ funOf (iterateBot F i) (⋃ m, funOf (iterateBot F m) x) :=
      ⟨n, hn, hi⟩
    have : k ∈ ⋃ m, funOf (iterateBot F i) (funOf (iterateBot F m) x) := by
      rwa [hcl i] at this
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp this
    let N := max i j
    have hij : funOf (iterateBot F i) (funOf (iterateBot F j) x) ⊆
        funOf (iterateBot F N) (funOf (iterateBot F N) x) :=
      mu_law (hchain i N (le_max_left i j))
        (funOf_monotone_left (hchain j N (le_max_right i j)) x)
    have : k ∈ funOf (iterateBot F N) x := by
      have : k ∈ funOf (iterateBot F N) (funOf (iterateBot F N) x) := hij hj
      rwa [hidem N] at this
    simpa [fix, funOf_iUnion] using Set.mem_iUnion.mpr ⟨N, this⟩
  · intro k hk
    have : k ∈ ⋃ n, funOf (iterateBot F n) x := by
      simpa [fix, funOf_iUnion] using hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp this
    have : k ∈ funOf (iterateBot F n) (funOf (iterateBot F n) x) := by
      rw [hidem n]
      exact hkn
    have : k ∈ funOf (iterateBot F n) (⋃ m, funOf (iterateBot F m) x) :=
      funOf_monotone_right _ (Set.subset_iUnion (fun m => funOf (iterateBot F m) x) n) this
    have : k ∈ funOf (⋃ i, iterateBot F i) (⋃ m, funOf (iterateBot F m) x) :=
      funOf_monotone_left (Set.subset_iUnion (iterateBot F) n) _ this
    simpa [fix, funOf_iUnion] using this

/-- **Scott 1976, Theorem 4.4 (The product theorem), core.** -/
theorem theorem_4_4 :
    (∀ x y, funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y) ∧
      IsRetract botElem :=
  ⟨fun x y => theorem_4_4_ii x y, bot_isRetract⟩

/-- **Scott 1976, Theorem 4.5 (The sum theorem), core.** -/
theorem theorem_4_5 :
    dcondSet botElem
        (pairSeq (ofNat 0) (funOf a botElem))
        (pairSeq (ofNat 1) (funOf b botElem)) = botElem ∧
      IsRetract botElem :=
  ⟨theorem_4_5_strict a b, bot_isRetract⟩

/-- **Scott 1976, Theorem 4.6 (The limit theorem).**
Kleene iterates of a retract-preserving continuous `F` are retracts, and
`Y(F)` is a retract by the chain-union calculation. -/
theorem theorem_4_6 {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a)) :
    (∀ n, IsRetract (iterateBot F n)) ∧
      IsRetract (funOf Ycomb (graph F)) := by
  refine ⟨iterates_areRetracts hret, ?_⟩
  have hY : funOf Ycomb (graph F) = fix F := theorem_2_5 hf
  rw [hY]
  change fix F = graph (fun x => funOf (fix F) (funOf (fix F) x))
  have hG : IsGraph (fix F) :=
    iUnion_retract_isGraph (iterates_areRetracts hret)
  have hgr : graph (funOf (fix F)) = fix F := (theorem_1_2_iii (fix F)).mpr hG
  have hidem' : graph (fun x => funOf (fix F) (funOf (fix F) x)) =
      graph (funOf (fix F)) :=
    graph_ext (fun x => funOf_fix_idem hf hret x)
  exact (hidem'.trans hgr).symm

/-- The strict bottom retract is below every strict retract in Scott's
projection order. -/
theorem bot_retractLe {a : Pomega} (ha : IsStrict a) :
    retractLe botElem a := by
  constructor
  · unfold comp
    have h : (fun x => funOf botElem (funOf a x)) = fun _ => botElem := by
      funext x
      exact funOf_botElem (funOf a x)
    rw [h, graph_const_bot]
  · unfold comp
    have h : (fun x => funOf a (funOf botElem x)) = fun _ => botElem := by
      funext x
      rw [funOf_botElem, ha]
    rw [h, graph_const_bot]

/-- Strictness of all Kleene approximants of a strictness-preserving
retract functor. -/
theorem iterateBot_isStrict {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a)) :
    ∀ n, IsStrict (iterateBot F n)
  | 0 => by simp [iterateBot, IsStrict, funOf_botElem]
  | n + 1 =>
      hstrict _ (iterates_areRetracts hret n)
        (iterateBot_isStrict hret hstrict n)

/-- Projection-order monotonicity gives adjacent projection equations for
the Kleene chain. -/
theorem iterateBot_retractLe_succ {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    ∀ n, retractLe (iterateBot F n) (iterateBot F (n + 1))
  | 0 => by
      simpa [iterateBot] using
        (bot_retractLe (iterateBot_isStrict hret hstrict 1))
  | n + 1 => by
      simpa only [iterateBot] using
        hmono (iterates_areRetracts hret n) (iterateBot_isStrict hret hstrict n)
          (iterates_areRetracts hret (n + 1))
          (iterateBot_isStrict hret hstrict (n + 1))
          (iterateBot_retractLe_succ hret hstrict hmono n)

/-- Projection equations between arbitrary comparable Kleene stages. -/
theorem iterateBot_retractLe {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    {n m : ℕ} (hnm : n ≤ m) :
    retractLe (iterateBot F n) (iterateBot F m) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      exact retractLe_refl (iterates_areRetracts hret n)
  | succ m _ ih =>
      exact retractLe_trans ih (iterateBot_retractLe_succ hret hstrict hmono m)

/-- The inverse limit of the ranges of `Fⁿ(⊥)`: points are typed at every
stage and adjacent coordinates satisfy Scott's projection equation. -/
def RetractInverseLimit (F : Pomega → Pomega) :=
  {v : ℕ → Pomega //
    (∀ n, typed (v n) (iterateBot F n)) ∧
      ∀ n, v n = funOf (iterateBot F n) (v (n + 1))}

instance (F : Pomega → Pomega) : PartialOrder (RetractInverseLimit F) where
  le v w := ∀ n, v.1 n ⊆ w.1 n
  le_refl _ _ := subset_rfl
  le_trans _ _ _ hvw hwz n := subset_trans (hvw n) (hwz n)
  le_antisymm v w hvw hwv := by
    apply Subtype.ext
    funext n
    exact Set.Subset.antisymm (hvw n) (hwv n)

/-- A coherent inverse-limit sequence is increasing in the ambient
powerset order. -/
theorem inverseLimit_mono {F : Pomega → Pomega}
    (hf : IsScottContinuous F) (v : RetractInverseLimit F) :
    ∀ n, v.1 n ⊆ v.1 (n + 1) := by
  intro n
  rw [v.property.2 n]
  have hcode : iterateBot F n ⊆ iterateBot F (n + 1) :=
    iterateBot_mono hf n
  have h := funOf_monotone_left hcode (v.1 (n + 1))
  rw [← v.property.1 (n + 1)] at h
  exact h

theorem inverseLimit_chain {F : Pomega → Pomega}
    (hf : IsScottContinuous F) (v : RetractInverseLimit F) :
    ∀ n m, n ≤ m → v.1 n ⊆ v.1 m :=
  chain_mono v.1 (inverseLimit_mono hf v)

/-- Repeated coherence: every later coordinate projects to an earlier one. -/
theorem inverseLimit_project_later {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) {n m : ℕ} (hnm : n ≤ m) :
    funOf (iterateBot F n) (v.1 m) = v.1 n := by
  induction m, hnm using Nat.le_induction with
  | base => exact (v.property.1 n).symm
  | succ m hnm ih =>
      have hle := iterateBot_retractLe hret hstrict hmono hnm
      have happ :=
        congrArg (fun a => funOf a (v.1 (m + 1))) hle.1
      rw [comp_app, ← v.property.2 m, ih] at happ
      exact happ

/-- Earlier typed coordinates are fixed by every later projection. -/
theorem inverseLimit_project_earlier {F : Pomega → Pomega}
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) {m n : ℕ} (hmn : m ≤ n) :
    funOf (iterateBot F n) (v.1 m) = v.1 m := by
  have hle := iterateBot_retractLe hret hstrict hmono hmn
  have hm : funOf (iterateBot F m) (v.1 m) = v.1 m :=
    (v.property.1 m).symm
  have happ := congrArg (fun a => funOf a (v.1 m)) hle.2
  simpa only [comp_app, hm] using happ.symm

/-- Every stage projection of the union of a coherent sequence is its
corresponding coordinate. -/
theorem inverseLimit_project_iUnion {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) (n : ℕ) :
    funOf (iterateBot F n) (⋃ m, v.1 m) = v.1 n := by
  rw [chain_lemma (funOf_isScottContinuous (iterateBot F n)) v.1
    (inverseLimit_mono hf v)]
  apply subset_antisymm
  · intro k hk
    obtain ⟨m, hkm⟩ := Set.mem_iUnion.mp hk
    by_cases hmn : m ≤ n
    · rw [inverseLimit_project_earlier hret hstrict hmono v hmn] at hkm
      exact inverseLimit_chain hf v m n hmn hkm
    · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      rwa [inverseLimit_project_later hret hstrict hmono v hnm] at hkm
  · intro k hk
    exact Set.mem_iUnion.mpr ⟨n, by
      rw [inverseLimit_project_later hret hstrict hmono v (le_refl n)]
      exact hk⟩

/-- The union of a coherent sequence lies in the range of the least fixed
point retract. -/
theorem inverseLimit_iUnion_typed {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) :
    typed (⋃ n, v.1 n) (fix F) := by
  change (⋃ n, v.1 n) = funOf (fix F) (⋃ n, v.1 n)
  rw [fix, funOf_iUnion]
  apply Eq.symm
  congr 1
  funext n
  exact inverseLimit_project_iUnion hf hret hstrict hmono v n

/-- A point of the fixed-point range determines its sequence of finite
projections. -/
def fixedToInverseLimit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (u : Fixpoints (funOf (fix F))) : RetractInverseLimit F :=
  ⟨fun n => funOf (iterateBot F n) u.1,
    ⟨fun n => (retract_app (iterates_areRetracts hret n) u.1).symm,
      fun n => by
        have hle := iterateBot_retractLe_succ hret hstrict hmono n
        have happ := congrArg (fun a => funOf a u.1) hle.1
        simpa only [comp_app] using happ⟩⟩

/-- A coherent sequence determines a point of the least fixed-point range
by taking the union of its coordinates. -/
def inverseLimitToFixed {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) : Fixpoints (funOf (fix F)) :=
  ⟨⋃ n, v.1 n, (inverseLimit_iUnion_typed hf hret hstrict hmono v).symm⟩

/-- **Scott 1976, Theorem 4.6, inverse-limit half.** The maps
`u ↦ (Fⁿ(⊥)(u))ₙ` and `(vₙ) ↦ ⋃ₙ vₙ` are inverse order isomorphisms. -/
def theorem_4_6_inverseLimit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    Fixpoints (funOf (fix F)) ≃o RetractInverseLimit F where
  toFun := fixedToInverseLimit hf hret hstrict hmono
  invFun := inverseLimitToFixed hf hret hstrict hmono
  left_inv u := by
    apply Subtype.ext
    change (⋃ n, funOf (iterateBot F n) u.1) = u.1
    rw [← funOf_iUnion, ← fix, u.property]
  right_inv v := by
    apply Subtype.ext
    funext n
    exact inverseLimit_project_iUnion hf hret hstrict hmono v n
  map_rel_iff' := by
    intro u w
    constructor
    · intro h
      change ∀ n, funOf (iterateBot F n) u.1 ⊆
        funOf (iterateBot F n) w.1 at h
      change u.1 ⊆ w.1
      have hu : u.1 = ⋃ n, funOf (iterateBot F n) u.1 := by
        calc
          u.1 = funOf (fix F) u.1 := u.property.symm
          _ = ⋃ n, funOf (iterateBot F n) u.1 := by
            change funOf (⋃ n, iterateBot F n) u.1 = _
            rw [funOf_iUnion]
      have hw : w.1 = ⋃ n, funOf (iterateBot F n) w.1 := by
        calc
          w.1 = funOf (fix F) w.1 := w.property.symm
          _ = ⋃ n, funOf (iterateBot F n) w.1 := by
            change funOf (⋃ n, iterateBot F n) w.1 = _
            rw [funOf_iUnion]
      rw [hu, hw]
      intro k hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨n, h n hkn⟩
    · intro huw
      change u.1 ⊆ w.1 at huw
      change ∀ n, funOf (iterateBot F n) u.1 ⊆
        funOf (iterateBot F n) w.1
      intro n
      exact funOf_monotone_right (iterateBot F n) huw

def treeR : Pomega := funOf Ycomb (graph treeF)

/-- **Scott 1976, (4.3).** Boolean retract via the doubly strict conditional. -/
def boolR : Pomega :=
  graph (fun u => dcondSet u (ofNat 0) (ofNat 1))

theorem boolR_app (u : Pomega) :
    funOf boolR u = dcondSet u (ofNat 0) (ofNat 1) :=
  beta (dcondSet_isScottContinuous_left (ofNat 0) (ofNat 1)) u

/-- `bool` is idempotent: mixed tags collapse to `⊤`, a fixed point of `⊒`. -/
theorem dcondSet_bool_idem (u : Pomega) :
    dcondSet (dcondSet u (ofNat 0) (ofNat 1)) (ofNat 0) (ofNat 1) =
      dcondSet u (ofNat 0) (ofNat 1) := by
  rcases dcondSet_cases u with h | h | h | h
  · rw [dcondSet_of_zero_not_pos h.1 h.2, dcondSet_ofNat_zero]
  · rw [dcondSet_of_pos_not_zero h.1 h.2, dcondSet_ofNat_one]
  · rw [dcondSet_of_mixed h.1 h.2, dcondSet_top]
  · rw [dcondSet_of_empty h.1 h.2, dcondSet_bot]

theorem boolR_isRetract : IsRetract boolR := by
  apply graph_ext
  intro u
  rw [boolR_app, boolR_app, dcondSet_bool_idem]

/-- **Scott 1976, (4.6).** The open-set retract. -/
def openR : Pomega :=
  graph (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u})

/-- **Scott 1976, (4.39).** `lamb = int ⊕ (lamb ∘→ lamb)`. -/
def lambF (z : Pomega) : Pomega := plusR intR (arrowR z z)

def lambR : Pomega := funOf Ycomb (graph lambF)

/-- **Scott 1976, (4.40).** `env = λt. lamb ∘ seq(t)`. -/
def envR : Pomega :=
  graph (fun t => graph (fun n => funOf lambR (funOf t n)))

/-- **Scott 1976, (4.41).** Environment update `t[x/n]`. -/
def updateEnv (t x : Pomega) (n : ℕ) : Pomega :=
  graph (fun m => if m = ofNat n then x else funOf t m)

/-- **Scott 1976, Theorem 4.6**, inverse-limit half packaged with the
retract half. Under the paper's extra strictness and `⊑`-monotonicity
hypotheses, the range of `Y(F)` is order-isomorphic to the inverse
limit of the ranges of `Fⁿ(⊥)`. Stated without `≃o` so the compared
type does not mention a `CompleteLattice` instance. -/
theorem theorem_4_6_limit {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b)) :
    (∀ n, IsRetract (iterateBot F n)) ∧
      IsRetract (funOf Ycomb (graph F)) ∧
        ∃ φ : Fixpoints (funOf (fix F)) → RetractInverseLimit F,
          Function.Bijective φ ∧
            ∀ x y : Fixpoints (funOf (fix F)),
              (x : Pomega) ⊆ (y : Pomega) ↔
                ∀ n, (φ x).1 n ⊆ (φ y).1 n := by
  refine ⟨(theorem_4_6 hf hret).1, (theorem_4_6 hf hret).2, ?_⟩
  let iso := theorem_4_6_inverseLimit hf hret hstrict hmono
  refine ⟨iso, iso.bijective, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy n
    exact funOf_monotone_right (iterateBot F n) hxy
  · intro h
    have hx : (x : Pomega) = ⋃ n, funOf (iterateBot F n) (x : Pomega) := by
      calc
        (x : Pomega) = funOf (fix F) (x : Pomega) := x.property.symm
        _ = ⋃ n, funOf (iterateBot F n) (x : Pomega) := by
          change funOf (⋃ n, iterateBot F n) (x : Pomega) = _
          rw [funOf_iUnion]
    have hy : (y : Pomega) = ⋃ n, funOf (iterateBot F n) (y : Pomega) := by
      calc
        (y : Pomega) = funOf (fix F) (y : Pomega) := y.property.symm
        _ = ⋃ n, funOf (iterateBot F n) (y : Pomega) := by
          change funOf (⋃ n, iterateBot F n) (y : Pomega) = _
          rw [funOf_iUnion]
    change ∀ n, funOf (iterateBot F n) (x : Pomega) ⊆
      funOf (iterateBot F n) (y : Pomega) at h
    rw [hx, hy]
    intro k hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, h n hn⟩

/-- Tag injection `⟨i, x⟩` used by the expanded n-ary sum of (4.44). -/
def tagInj (i : ℕ) (x : Pomega) : Pomega := pairSeq (ofNat i) x

/-- Four-place sequence used by the expanded product of (4.44). -/
def seq4 (a b c d : Pomega) : Pomega :=
  graph (fun z =>
    condSet z a
      (condSet (predSet z) b
        (condSet (predSet (predSet z)) c
          (condSet (predSet (predSet (predSet z))) d botElem))))

/-- **Scott 1976, before (4.44).** Four-fold product by expanded indices,
not iterated binary `⊗`. -/
def tensor4 (a b c d : Pomega) : Pomega :=
  graph (fun u =>
    seq4 (funOf a (funOf u (ofNat 0)))
      (funOf b (funOf u (ofNat 1)))
      (funOf c (funOf u (ofNat 2)))
      (funOf d (funOf u (ofNat 3))))

/-- Body of the seven-way tagged sum of (4.44). -/
def plus7Body (a0 a1 a2 a3 a4 a5 a6 u : Pomega) : Pomega :=
  dcondSet (funOf u (ofNat 0)) (tagInj 0 (funOf a0 (funOf u (ofNat 1))))
    (dcondSet (predSet (funOf u (ofNat 0))) (tagInj 1 (funOf a1 (funOf u (ofNat 1))))
      (dcondSet (predSet (predSet (funOf u (ofNat 0))))
        (tagInj 2 (funOf a2 (funOf u (ofNat 1))))
        (dcondSet (predSet^[3] (funOf u (ofNat 0)))
          (tagInj 3 (funOf a3 (funOf u (ofNat 1))))
          (dcondSet (predSet^[4] (funOf u (ofNat 0)))
            (tagInj 4 (funOf a4 (funOf u (ofNat 1))))
            (dcondSet (predSet^[5] (funOf u (ofNat 0)))
              (tagInj 5 (funOf a5 (funOf u (ofNat 1))))
              (dcondSet (predSet^[6] (funOf u (ofNat 0)))
                (tagInj 6 (funOf a6 (funOf u (ofNat 1))))
                topElem))))))

/-- Seven-way tagged sum with indices `0,...,6`, dispatching by iterated
predecessor on the tag so mixed tags collapse to `⊤` as in (4.4). -/
def plus7 (a0 a1 a2 a3 a4 a5 a6 : Pomega) : Pomega :=
  graph (plus7Body a0 a1 a2 a3 a4 a5 a6)

/-- **Scott 1976, (4.44).** Abstract-syntax functor. -/
def expF (z : Pomega) : Pomega :=
  plus7 intR botElem z z (tensor4 z z z z) (tensorR z z) (tensorR intR z)

/-- **Scott 1976, (4.44).** `exp` as the least fixed point of the seven-tag
syntax functor. -/
def expR : Pomega := funOf Ycomb (graph expF)

end Scott1976.DataTypesAsLattices
