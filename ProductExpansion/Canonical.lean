import ProductExpansion.Basic
import ProductExpansion.Cube
import ProductExpansion.Expander

/-!
# Canonical error sets (definition `def:can`, lemmas `lem:CL`, `lem:good`)

Notation follows the part "Canonical error sets" of the proof.

## Generic cube `ι → Fin n` (matrices `H : (i : ι) → Matrix (P i) (Fin n) F`)
* `linePts Y j c` — the points of `Y` on the `j`-line through `c` (as `j`-th coordinates);
* `crossSet Z j c` — `Cr_Z(ℓ)`; `psiSet H θ Z Y j c` — `Ψ^θ_ℓ(Z, Y) = F_θ(N_j(Cr_Z(ℓ) ∪ (Y ∩ ℓ)))`;
* `stepSet H θ Z Y = Z ∪ {c ∉ Z : c ∈ Ψ^θ_ℓ(Z, Y) for all lines ℓ ∋ c}`.

## The cube `K → Fin n`, bases `B_J = {i // i ∉ J} → Fin n`
* `resPos h c = c|_{K \ J''}`, `liftSet J J'' Z = Z↑_J`;
* `badSet H θ₀ Y J = Bad_J` (well-founded recursion, downward in `|J|`; `Bad_K = ∅`; `θ₀ = τδ`);
* `canJ`, `hatJ θ` — `Can_J` and the step with threshold `θ` (`Bad_J = hatJ θ₀ J` for `J ≠ K`);
* `canSet = Can(Y)`, `hatSet θ = Ŷ^θ` (formulas of the proof in `V^K`; `hatSet_eq` identifies
  `Ŷ^θ` with the level `J = ∅`); `canonicalSet H δ ε Y = Ŷ^h` with `τ = 1/4`, `h = (1 - 2ε)δ`.

## Main results
* (L): `liftSet_badSet_subset`, `mem_badSet_of_resPos`, `outer_preimage_badSet_subset_canSet`;
* (C2) for all levels `J`: `card_linePts_canJ_hatJ_lt`, `card_linePts_badSet_lt`; for `V^K`:
  `lineCount_canSet_hatSet_lt`;
* (C3): `full_line_canSet_iff`, `full_line_hatSet_iff`, `isClosedSet_canSet`, `isClosedSet_hatSet`,
  `hatSet_ne_univ`, `canSet_ne_univ`, and for the levels `J`: `isClosedSet_canJ`,
  `isClosedSet_hatJ`, `isClosedSet_badSet`, `hatJ_ne_univ`, `badSet_ne_univ`;
* the case `|K| = 1`: `canSet_of_subsingleton`, `mem_hatSet_of_subsingleton` (`Ŷ^θ = F_θ(N(Y))`);
* lemma `good`: `exists_good_line`, `good_line_G1` … `good_line_G4`, `good_line`;
* parameters of the proof: `canonicalSet_spec`, `good_line_paper`.

The constants are `canC γ k` (`c_k`) and `canC' γ k` (`c'_k`), `γ = τ - ε`:
`c_0 = 0`, `c'_k = 1 + 2^k c_{k-1}`, `c_k = c'_k (1 + 1/γ)` (they depend
only on `k` and `γ`). The conditions on `η'` are `0 ≤ η'`, `c'_k η' ≤ γα/2` and (for (C3))
`c_k η' < 1`, `k = |K|`.
-/

open Finset

namespace ProductExpansion

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

section Generic

variable {ι : Type*} [DecidableEq ι] {P : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- Points (`j`-th coordinates) of the line in direction `j` through `c` lying in `Y`. -/
noncomputable def linePts (Y : Set (ι → Fin n)) (j : ι) (c : ι → Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun t => Function.update c j t ∈ Y

/-- `Cr_Z(ℓ)` for the line `ℓ` in direction `j` through `c`: the points of `ℓ` (identified with
their `j`-th coordinate) lying on a line of another direction contained in `Z`. -/
noncomputable def crossSet (Z : Set (ι → Fin n)) (j : ι) (c : ι → Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun t =>
    ∃ j' ≠ j, ∀ s, Function.update (Function.update c j t) j' s ∈ Z

/-- `Ψ^θ_ℓ(Z, Y) = F_θ(N_j(Cr_Z(ℓ) ∪ (Y ∩ ℓ)))` for the line `ℓ` in direction `j` through `c`;
the closure `F_θ` is taken in the graph of `H j`. -/
noncomputable def psiSet (H : (i : ι) → Matrix (P i) (Fin n) F) (θ : ℝ) (Z Y : Set (ι → Fin n))
    (j : ι) (c : ι → Fin n) : Finset (Fin n) :=
  findClosure (H j) θ (nbhd (H j) (crossSet Z j c ∪ linePts Y j c))

/-- One step of the construction: `Z ∪ {c ∉ Z : c ∈ Ψ^θ_ℓ(Z, Y) for all lines ℓ ∋ c}`
(the point `c` of the line `ℓ` of direction `j` is identified with `c j`). -/
def stepSet (H : (i : ι) → Matrix (P i) (Fin n) F) (θ : ℝ) (Z Y : Set (ι → Fin n)) :
    Set (ι → Fin n) :=
  Z ∪ {c | c ∉ Z ∧ ∀ j, c j ∈ psiSet H θ Z Y j c}

end Generic

section GenericLemmas

variable {ι : Type*} [DecidableEq ι] {P : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
variable {Y Z : Set (ι → Fin n)} {j : ι} {c : ι → Fin n}

lemma mem_linePts {t : Fin n} : t ∈ linePts Y j c ↔ Function.update c j t ∈ Y := by
  classical
  simp [linePts]

lemma mem_crossSet {t : Fin n} :
    t ∈ crossSet Z j c ↔ ∃ j' ≠ j, ∀ s, Function.update (Function.update c j t) j' s ∈ Z := by
  classical
  simp [crossSet]

lemma linePts_mono (h : Y ⊆ Z) : linePts Y j c ⊆ linePts Z j c := by
  intro t ht
  rw [mem_linePts] at ht ⊢
  exact h ht

lemma linePts_update (t : Fin n) : linePts Y j (Function.update c j t) = linePts Y j c := by
  ext s
  simp only [mem_linePts, Function.update_idem]

lemma crossSet_update (t : Fin n) : crossSet Z j (Function.update c j t) = crossSet Z j c := by
  ext s
  simp only [mem_crossSet, Function.update_idem]

lemma psiSet_update (H : (i : ι) → Matrix (P i) (Fin n) F) (θ : ℝ) (t : Fin n) :
    psiSet H θ Z Y j (Function.update c j t) = psiSet H θ Z Y j c := by
  simp only [psiSet, crossSet_update, linePts_update]

/-- Points of a line lying on full lines of `Z` of other directions lie in `Z`. -/
lemma crossSet_subset_linePts : crossSet Z j c ⊆ linePts Z j c := by
  intro t ht
  rw [mem_crossSet] at ht
  rw [mem_linePts]
  obtain ⟨j', _, h⟩ := ht
  have := h (Function.update c j t j')
  rwa [Function.update_eq_self] at this

lemma mem_stepSet {H : (i : ι) → Matrix (P i) (Fin n) F} {θ : ℝ} {x : ι → Fin n} :
    x ∈ stepSet H θ Z Y ↔ x ∈ Z ∨ (x ∉ Z ∧ ∀ j, x j ∈ psiSet H θ Z Y j x) :=
  Iff.rfl

lemma subset_stepSet (H : (i : ι) → Matrix (P i) (Fin n) F) (θ : ℝ) : Z ⊆ stepSet H θ Z Y :=
  Set.subset_union_left

/-- `ℓ ∩ step(Z) ⊆ (ℓ ∩ Z) ∪ Ψ_ℓ`. -/
lemma linePts_stepSet_subset (H : (i : ι) → Matrix (P i) (Fin n) F) (θ : ℝ) :
    linePts (stepSet H θ Z Y) j c ⊆ linePts Z j c ∪ psiSet H θ Z Y j c := by
  intro t ht
  rw [mem_linePts, mem_stepSet] at ht
  rw [mem_union, mem_linePts]
  rcases ht with ht | ⟨-, ht⟩
  · exact Or.inl ht
  · right
    have := ht j
    rwa [Function.update_self, psiSet_update] at this

/-- `Cr_Z(ℓ) ∪ (Y ∩ ℓ) ⊆ ℓ ∩ Z` if `Y ⊆ Z` on the line. -/
lemma crossSet_union_linePts_subset (hYZ : linePts Y j c ⊆ linePts Z j c) :
    crossSet Z j c ∪ linePts Y j c ⊆ linePts Z j c :=
  Finset.union_subset crossSet_subset_linePts hYZ

/-- **Size of `Ψ`** (lemma `gen-find` (a) applied on a line): if `Y ⊆ Z` on the line,
`γδ ≤ θ - εδ` and `|ℓ ∩ Z| ≤ γαn/2`, then `|Ψ^θ_ℓ(Z, Y)| ≤ |ℓ ∩ Z| / γ`. -/
theorem card_psiSet_le {H : (i : ι) → Matrix (P i) (Fin n) F} {δ Δ : ℕ} {α ε γ θ : ℝ}
    (hH : IsExpanderMatrix (H j) δ Δ α ε) (hδ : 0 < δ) (hγ : 0 < γ)
    (hθ : γ * δ ≤ θ - ε * δ) (hαn : 2 ≤ α * n) (hYZ : linePts Y j c ⊆ linePts Z j c)
    (hZ : ((linePts Z j c).card : ℝ) ≤ γ * α * n / 2) :
    ((psiSet H θ Z Y j c).card : ℝ) ≤ (linePts Z j c).card / γ := by
  set S := crossSet Z j c ∪ linePts Y j c with hS
  have hSZ : S ⊆ linePts Z j c := crossSet_union_linePts_subset hYZ
  have hScard : (S.card : ℝ) ≤ (linePts Z j c).card := by exact_mod_cast Finset.card_le_card hSZ
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hR : ((nbhd (H j) S).card : ℝ) ≤ δ * S.card := by exact_mod_cast hH.card_nbhd_le S
  have hθε : 0 < θ - ε * δ := lt_of_lt_of_le (mul_pos hγ hδ') hθ
  have hαn0 : 0 ≤ α * n := by linarith
  have hR' : ((nbhd (H j) S).card : ℝ) ≤ (θ - ε * δ) * α * n / 2 := by
    calc ((nbhd (H j) S).card : ℝ) ≤ δ * S.card := hR
      _ ≤ δ * (linePts Z j c).card := by gcongr
      _ ≤ δ * (γ * α * n / 2) := by gcongr
      _ = (γ * δ) * (α * n) / 2 := by ring
      _ ≤ (θ - ε * δ) * (α * n) / 2 := by gcongr
      _ = (θ - ε * δ) * α * n / 2 := by ring
  have hF := hH.card_findClosure_le hαn (by linarith [mul_pos hγ hδ']) hR'
  unfold psiSet
  rw [← hS]
  calc ((findClosure (H j) θ (nbhd (H j) S)).card : ℝ) ≤ (nbhd (H j) S).card / (θ - ε * δ) := hF
    _ ≤ (δ * (linePts Z j c).card) / (γ * δ) := by
        apply div_le_div₀ (by positivity) (hR.trans (by gcongr)) (mul_pos hγ hδ') hθ
    _ = (linePts Z j c).card / γ := by field_simp

/-- `|ℓ ∩ step(Z)| ≤ |ℓ ∩ Z| (1 + 1/γ)` under the conditions of `card_psiSet_le`. -/
theorem card_linePts_stepSet_le {H : (i : ι) → Matrix (P i) (Fin n) F} {δ Δ : ℕ}
    {α ε γ θ : ℝ} (hH : IsExpanderMatrix (H j) δ Δ α ε) (hδ : 0 < δ) (hγ : 0 < γ)
    (hθ : γ * δ ≤ θ - ε * δ) (hαn : 2 ≤ α * n) (hYZ : linePts Y j c ⊆ linePts Z j c)
    (hZ : ((linePts Z j c).card : ℝ) ≤ γ * α * n / 2) :
    ((linePts (stepSet H θ Z Y) j c).card : ℝ) ≤ (linePts Z j c).card * (1 + 1 / γ) := by
  have h1 : (linePts (stepSet H θ Z Y) j c).card ≤
      (linePts Z j c).card + (psiSet H θ Z Y j c).card :=
    (Finset.card_le_card (linePts_stepSet_subset H θ)).trans (Finset.card_union_le _ _)
  have h2 := card_psiSet_le hH hδ hγ hθ hαn hYZ hZ
  have h1' : ((linePts (stepSet H θ Z Y) j c).card : ℝ) ≤
      (linePts Z j c).card + (psiSet H θ Z Y j c).card := by exact_mod_cast h1
  calc ((linePts (stepSet H θ Z Y) j c).card : ℝ)
      ≤ (linePts Z j c).card + (linePts Z j c).card / γ := by linarith
    _ = (linePts Z j c).card * (1 + 1 / γ) := by ring

end GenericLemmas

section Defs

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Restriction of a position `c ∈ B_J` to the complement of `J'' ⊇ J`: `c|_{K \ J''} ∈ B_{J''}`. -/
def resPos {J J'' : Finset K} (h : J ⊆ J'') (c : {i // i ∉ J} → Fin n) : {i // i ∉ J''} → Fin n :=
  fun i => c ⟨i.1, fun hi => i.2 (h hi)⟩

/-- `Z↑_J = {c ∈ B_J : c|_{K \ J''} ∈ Z}` for `Z ⊆ B_{J''}` (empty unless `J ⊆ J''`). -/
def liftSet (J J'' : Finset K) (Z : Set ({i // i ∉ J''} → Fin n)) : Set ({i // i ∉ J} → Fin n) :=
  ⋃ h : J ⊆ J'', resPos h ⁻¹' Z

variable {P : K → Type*} [∀ k, Fintype (P k)] [∀ k, DecidableEq (P k)]

/-- The sets `Bad_J ⊆ B_J`, defined by downward recursion on `|J|`:
`Bad_K = ∅` and, for `J ≠ K`, `Bad_J = Can_J ∪ {c ∉ Can_J : c ∈ Ψ^{θ₀}_ℓ(Can_J, Y_J) ∀ ℓ ∋ c}`,
where `Can_J = Y_J ∪ ⋃_{J ⊊ J''} Bad_{J''}↑_J`. (In the proof `θ₀ = τδ`.) -/
noncomputable def badSet (H : (k : K) → Matrix (P k) (Fin n) F) (θ₀ : ℝ) (Y : Set (K → Fin n))
    (J : Finset K) : Set ({i // i ∉ J} → Fin n) :=
  if J = Finset.univ then ∅ else
    stepSet (fun j : {i // i ∉ J} => H j.1) θ₀
      (posFull Y J ∪ ⋃ (J'' : Finset K) (_ : J ⊂ J''), liftSet J J'' (badSet H θ₀ Y J''))
      (posFull Y J)
termination_by Fintype.card K - J.card
decreasing_by
  have h1 := Finset.card_lt_card ‹J ⊂ J''›
  have h2 := Finset.card_le_univ J''
  omega

end Defs

section ResPos

variable {K : Type*}

@[simp] lemma resPos_apply {J J'' : Finset K} (h : J ⊆ J'') (c : {i // i ∉ J} → Fin n)
    (i : {i // i ∉ J''}) : resPos h c i = c ⟨i.1, fun hi => i.2 (h hi)⟩ := rfl

lemma resPos_resPos {J J' J'' : Finset K} (h₁ : J ⊆ J') (h₂ : J' ⊆ J'')
    (c : {i // i ∉ J} → Fin n) : resPos h₂ (resPos h₁ c) = resPos (h₁.trans h₂) c := rfl

lemma resPos_self {J : Finset K} (h : J ⊆ J) (c : {i // i ∉ J} → Fin n) : resPos h c = c := rfl

lemma mem_liftSet {J J'' : Finset K} {Z : Set ({i // i ∉ J''} → Fin n)}
    {c : {i // i ∉ J} → Fin n} : c ∈ liftSet J J'' Z ↔ ∃ h : J ⊆ J'', resPos h c ∈ Z := by
  simp [liftSet]

/-- Every position of `B_{J''}` is a restriction of a position of `B_J` (if `n > 0`). -/
lemma exists_resPos_eq {J J'' : Finset K} (h : J ⊆ J'') (t₀ : Fin n)
    (β : {i // i ∉ J''} → Fin n) : ∃ c : {i // i ∉ J} → Fin n, resPos h c = β := by
  classical
  refine ⟨fun i => if hi : i.1 ∈ J'' then t₀ else β ⟨i.1, hi⟩, ?_⟩
  funext i
  simp [i.2]

variable [DecidableEq K]

/-- Moving along a line of direction `j ∈ J''` does not change the restriction to `K \ J''`. -/
lemma resPos_update_of_mem {J J'' : Finset K} (h : J ⊆ J'') (c : {i // i ∉ J} → Fin n)
    {j : {i // i ∉ J}} (hj : j.1 ∈ J'') (t : Fin n) :
    resPos h (Function.update c j t) = resPos h c := by
  funext i
  simp only [resPos_apply]
  rw [Function.update_of_ne]
  intro heq
  apply i.2
  rw [show i.1 = j.1 from congrArg Subtype.val heq]
  exact hj

/-- A line of direction `j ∉ J''` is mapped onto the line of direction `j` of `B_{J''}`. -/
lemma resPos_update_of_not_mem {J J'' : Finset K} (h : J ⊆ J'') (c : {i // i ∉ J} → Fin n)
    {j : {i // i ∉ J}} (hj : j.1 ∉ J'') (t : Fin n) :
    resPos h (Function.update c j t) = Function.update (resPos h c) ⟨j.1, hj⟩ t := by
  funext i
  simp only [resPos_apply, Function.update_apply]
  by_cases hi : i.1 = j.1
  · have h1 : (⟨i.1, fun hi' => i.2 (h hi')⟩ : {i // i ∉ J}) = j := Subtype.ext hi
    have h2 : i = ⟨j.1, hj⟩ := Subtype.ext hi
    simp [h2]
  · have h1 : (⟨i.1, fun hi' => i.2 (h hi')⟩ : {i // i ∉ J}) ≠ j :=
      fun h' => hi (congrArg Subtype.val h')
    have h2 : i ≠ ⟨j.1, hj⟩ := fun h' => hi (congrArg Subtype.val h')
    simp [h1, h2]

end ResPos

section DefsLemmas

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {P : K → Type*} [∀ k, Fintype (P k)] [∀ k, DecidableEq (P k)]
variable (H : (k : K) → Matrix (P k) (Fin n) F) (θ₀ : ℝ) (Y : Set (K → Fin n))

/-- `Can_J = Y_J ∪ ⋃_{J ⊊ J''} Bad_{J''}↑_J ⊆ B_J` (the term `J'' = K` is empty). -/
def canJ (J : Finset K) : Set ({i // i ∉ J} → Fin n) :=
  posFull Y J ∪ ⋃ (J'' : Finset K) (_ : J ⊂ J''), liftSet J J'' (badSet H θ₀ Y J'')

/-- `Can_J ∪ {c ∉ Can_J : c ∈ Ψ^θ_ℓ(Can_J, Y_J) ∀ ℓ ∋ c}` (lines of the base `B_J`).
For `J ≠ K` and `θ = θ₀` this is `Bad_J`; for `J = ∅` it is `Ŷ^θ` (see `hatSet_eq`). -/
def hatJ (θ : ℝ) (J : Finset K) : Set ({i // i ∉ J} → Fin n) :=
  stepSet (fun j : {i // i ∉ J} => H j.1) θ (canJ H θ₀ Y J) (posFull Y J)

/-- `Can(Y) = Y ∪ ⋃_{∅ ≠ J ⊊ K} Bad_J↑_∅ ⊆ V^K` (the term `J = K` is empty). -/
def canSet : Set (K → Fin n) :=
  Y ∪ ⋃ (J : Finset K) (_ : J.Nonempty), outer J ⁻¹' badSet H θ₀ Y J

/-- `Ŷ^θ = Can(Y) ∪ {y ∉ Can(Y) : y ∈ Ψ^θ_ℓ(Can(Y), Y) for all lines ℓ ∋ y}`;
the canonical error set is `Ŷ = Ŷ^h`, `h = (1 - 2ε)δ`. -/
def hatSet (θ : ℝ) : Set (K → Fin n) :=
  stepSet H θ (canSet H θ₀ Y) Y

variable {H θ₀ Y}

lemma badSet_of_ne_univ {J : Finset K} (hJ : J ≠ Finset.univ) :
    badSet H θ₀ Y J = hatJ H θ₀ Y θ₀ J := by
  rw [badSet, ite_eq_right hJ]
  rfl

@[simp] lemma badSet_univ : badSet H θ₀ Y (Finset.univ : Finset K) = ∅ := by
  rw [badSet, ite_eq_left rfl]

lemma posFull_subset_canJ (J : Finset K) : posFull Y J ⊆ canJ H θ₀ Y J :=
  Set.subset_union_left

lemma liftSet_subset_canJ {J J'' : Finset K} (h : J ⊂ J'') :
    liftSet J J'' (badSet H θ₀ Y J'') ⊆ canJ H θ₀ Y J :=
  fun _ hc => Or.inr (Set.mem_iUnion₂.2 ⟨J'', h, hc⟩)

lemma resPos_mem_canJ {J J'' : Finset K} (h : J ⊂ J'') {c : {i // i ∉ J} → Fin n}
    (hc : resPos h.subset c ∈ badSet H θ₀ Y J'') : c ∈ canJ H θ₀ Y J :=
  liftSet_subset_canJ h (mem_liftSet.2 ⟨h.subset, hc⟩)

lemma mem_canJ {J : Finset K} {c : {i // i ∉ J} → Fin n} :
    c ∈ canJ H θ₀ Y J ↔ c ∈ posFull Y J ∨
      ∃ J'' : Finset K, ∃ h : J ⊂ J'', resPos h.subset c ∈ badSet H θ₀ Y J'' := by
  unfold canJ
  simp only [Set.mem_union, Set.mem_iUnion, mem_liftSet]
  constructor
  · rintro (h | ⟨J'', h, h', hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨J'', h, hc⟩
  · rintro (h | ⟨J'', h, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨J'', h, h.subset, hc⟩

lemma canJ_subset_hatJ (θ : ℝ) (J : Finset K) : canJ H θ₀ Y J ⊆ hatJ H θ₀ Y θ J :=
  subset_stepSet _ _

lemma canJ_subset_badSet {J : Finset K} (hJ : J ≠ Finset.univ) :
    canJ H θ₀ Y J ⊆ badSet H θ₀ Y J := by
  rw [badSet_of_ne_univ hJ]
  exact canJ_subset_hatJ θ₀ J

/-- `Y_J ⊆ Bad_J` for `J ≠ K`. -/
lemma posFull_subset_badSet {J : Finset K} (hJ : J ≠ Finset.univ) :
    posFull Y J ⊆ badSet H θ₀ Y J :=
  (posFull_subset_canJ J).trans (canJ_subset_badSet hJ)

/-- **Lemma CL (L)**: `Bad_{J''}↑_J ⊆ Bad_J` for `J ⊊ J''`, `J ≠ K`. -/
theorem liftSet_badSet_subset {J J'' : Finset K} (hJ : J ≠ Finset.univ) (h : J ⊂ J'') :
    liftSet J J'' (badSet H θ₀ Y J'') ⊆ badSet H θ₀ Y J :=
  (liftSet_subset_canJ h).trans (canJ_subset_badSet hJ)

/-- **Lemma CL (L)**, pointwise form. -/
theorem mem_badSet_of_resPos {J J'' : Finset K} (hJ : J ≠ Finset.univ) (h : J ⊂ J'')
    {c : {i // i ∉ J} → Fin n} (hc : resPos h.subset c ∈ badSet H θ₀ Y J'') :
    c ∈ badSet H θ₀ Y J :=
  canJ_subset_badSet hJ (resPos_mem_canJ h hc)

/-- `Bad_J ⊆ hatJ θ₀ J` (with equality for `J ≠ K`, `Bad_K = ∅`). -/
lemma badSet_subset_hatJ {J : Finset K} : badSet H θ₀ Y J ⊆ hatJ H θ₀ Y θ₀ J := by
  by_cases hJ : J = Finset.univ
  · subst hJ
    simp
  · rw [badSet_of_ne_univ hJ]

lemma subset_canSet : Y ⊆ canSet H θ₀ Y := Set.subset_union_left

lemma canSet_subset_hatSet (θ : ℝ) : canSet H θ₀ Y ⊆ hatSet H θ₀ Y θ := subset_stepSet _ _

lemma subset_hatSet (θ : ℝ) : Y ⊆ hatSet H θ₀ Y θ :=
  subset_canSet.trans (canSet_subset_hatSet θ)

/-- **Lemma CL (L)**: `Bad_J↑_∅ ⊆ Can(Y)` for `J ≠ ∅`. -/
theorem outer_preimage_badSet_subset_canSet {J : Finset K} (hJ : J.Nonempty) :
    outer J ⁻¹' badSet H θ₀ Y J ⊆ canSet H θ₀ Y :=
  fun _ hy => Or.inr (Set.mem_iUnion₂.2 ⟨J, hJ, hy⟩)

lemma mem_hatSet {θ : ℝ} {y : K → Fin n} :
    y ∈ hatSet H θ₀ Y θ ↔
      y ∈ canSet H θ₀ Y ∨ (y ∉ canSet H θ₀ Y ∧ ∀ j, y j ∈ psiSet H θ (canSet H θ₀ Y) Y j y) :=
  Iff.rfl

end DefsLemmas

/-! ### Constants of lemma CL -/

section Constants

/-- `c_k`: `c_0 = 0`, `c_k = c'_k (1 + 1/γ)` for `k ≥ 1`, where `c'_k = 1 + 2^k c_{k-1}`
(see `canC'`) and `γ = τ - ε`. These constants depend only on `k` and `γ`. -/
noncomputable def canC (γ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (1 + 2 ^ (k + 1) * canC γ k) * (1 + 1 / γ)

/-- `c'_k = 1 + 2^k c_{k-1}` (so `c'_1 = 1`). -/
noncomputable def canC' (γ : ℝ) (k : ℕ) : ℝ := 1 + 2 ^ k * canC γ (k - 1)

variable {γ : ℝ}

@[simp] lemma canC_zero : canC γ 0 = 0 := rfl

lemma canC_succ (k : ℕ) : canC γ (k + 1) = canC' γ (k + 1) * (1 + 1 / γ) := by
  simp [canC, canC']

lemma canC_of_pos {k : ℕ} (hk : 0 < k) : canC γ k = canC' γ k * (1 + 1 / γ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact canC_succ m

lemma canC_nonneg (hγ : 0 < γ) : ∀ k, 0 ≤ canC γ k
  | 0 => le_rfl
  | k + 1 => by
    have := canC_nonneg hγ k
    simp only [canC]
    positivity

lemma canC_le_succ (hγ : 0 < γ) (k : ℕ) : canC γ k ≤ canC γ (k + 1) := by
  have h0 := canC_nonneg hγ k
  have h1 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 1 + 1 / γ := by
    have : 0 < 1 / γ := by positivity
    linarith
  simp only [canC]
  calc canC γ k ≤ 1 * canC γ k := by rw [one_mul]
    _ ≤ (1 + 2 ^ (k + 1) * canC γ k) * 1 := by nlinarith
    _ ≤ (1 + 2 ^ (k + 1) * canC γ k) * (1 + 1 / γ) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity

lemma canC_mono (hγ : 0 < γ) : Monotone (canC γ) :=
  monotone_nat_of_le_succ (canC_le_succ hγ)

lemma one_le_canC' (hγ : 0 < γ) (k : ℕ) : 1 ≤ canC' γ k := by
  have := canC_nonneg hγ (k - 1)
  unfold canC'
  have : 0 ≤ (2 : ℝ) ^ k * canC γ (k - 1) := by positivity
  linarith

lemma canC'_mono (hγ : 0 < γ) : Monotone (canC' γ) := by
  intro k m hkm
  unfold canC'
  have h1 : (2 : ℝ) ^ k ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hkm
  have h2 : canC γ (k - 1) ≤ canC γ (m - 1) := canC_mono hγ (by omega)
  have h3 := canC_nonneg hγ (k - 1)
  have := mul_le_mul h1 h2 h3 (by positivity)
  linarith

lemma canC'_le_canC (hγ : 0 < γ) {k : ℕ} (hk : 0 < k) : canC' γ k ≤ canC γ k := by
  rw [canC_of_pos hk]
  have h1 := one_le_canC' hγ k
  have h2 : 0 < 1 / γ := by positivity
  nlinarith

lemma one_le_canC (hγ : 0 < γ) {k : ℕ} (hk : 0 < k) : 1 ≤ canC γ k :=
  (one_le_canC' hγ k).trans (canC'_le_canC hγ hk)

/-- `c_k ≥ k` (used to bound `κ_d`). -/
lemma natCast_le_canC (hγ : 0 < γ) : ∀ k : ℕ, (k : ℝ) ≤ canC γ k
  | 0 => by simp
  | k + 1 => by
    have ih := natCast_le_canC hγ k
    have h0 := canC_nonneg hγ k
    have h1 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ 1 + 1 / γ := by
      have : 0 < 1 / γ := by positivity
      linarith
    have h3 : canC γ k ≤ 2 ^ (k + 1) * canC γ k := le_mul_of_one_le_left h0 h1
    have h4 : 0 ≤ 1 + 2 ^ (k + 1) * canC γ k := by positivity
    simp only [canC]
    push_cast
    nlinarith

end Constants

/-! ### Base cubes: `Y_J` is closed, proper, and `Y_j(Y_J) ⊆ Y_{J ∪ j}` -/

section PosFull

variable {K : Type*} [DecidableEq K]

lemma lineCount_eq_card_linePts {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Set (ι → Fin n))
    (j : ι) (c : ι → Fin n) : lineCount S j c = (linePts S j c).card := by
  classical
  unfold lineCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1

private lemma glue_update_outer_pos {J : Finset K} (z : {i // i ∈ J} → Fin n)
    (c : {i // i ∉ J} → Fin n) (j : {i // i ∉ J}) (t : Fin n) :
    glue J z (Function.update c j t) = Function.update (glue J z c) j.1 t := by
  funext i
  by_cases hi : i ∈ J
  · have hij : i ≠ j.1 := fun h => j.2 (h ▸ hi)
    simp [glue, hi, Function.update_of_ne hij]
  · by_cases hij : i = j.1
    · subst hij
      simp [glue, hi]
    · have hij' : (⟨i, hi⟩ : {i // i ∉ J}) ≠ j := fun h => hij (congrArg Subtype.val h)
      simp [glue, hi, Function.update_of_ne hij, Function.update_of_ne hij']

variable [Fintype K]

/-- (F3): `Y_J` is `η`-closed in the base `B_J` if `Y` is `η`-closed. -/
theorem isClosedSet_posFull {η : ℝ} {Y : Set (K → Fin n)} (hY : IsClosedSet η Y) (J : Finset K) :
    IsClosedSet η (posFull Y J) := by
  intro j c hcount t z
  have hle : lineCount (posFull Y J) j c ≤ lineCount Y j.1 (glue J z c) := by
    rw [lineCount_eq_card_linePts, lineCount_eq_card_linePts]
    apply Finset.card_le_card
    intro s hs
    rw [mem_linePts] at hs ⊢
    rw [← glue_update_outer_pos]
    exact hs z
  have hfull := hY j.1 (glue J z c) (hcount.trans (by exact_mod_cast hle)) t
  rwa [← glue_update_outer_pos] at hfull

/-- `Y_K = ∅` for a proper `Y` (the base `B_K` is a point). -/
lemma not_mem_posFull_of_eq_univ {Y : Set (K → Fin n)} (hYne : Y ≠ Set.univ) {J : Finset K}
    (hJ : J = Finset.univ) (β : {i // i ∉ J} → Fin n) : β ∉ posFull Y J := by
  subst hJ
  intro hβ
  apply hYne
  ext y
  simp only [Set.mem_univ, iff_true]
  have hout : outer Finset.univ y = β := funext fun i => absurd (Finset.mem_univ i.1) i.2
  have := hβ (inner Finset.univ y)
  rwa [← hout, glue_inner_outer] at this

omit [Fintype K] in
/-- `Y_J` is proper if `Y` is proper. -/
lemma posFull_ne_univ_of_ne_univ {Y : Set (K → Fin n)} (hYne : Y ≠ Set.univ) (J : Finset K) :
    posFull Y J ≠ Set.univ := by
  intro h
  apply hYne
  ext y
  simp only [Set.mem_univ, iff_true]
  have : outer J y ∈ posFull Y J := h ▸ Set.mem_univ _
  have := this (inner J y)
  rwa [glue_inner_outer] at this

omit [Fintype K] in
/-- `(YY)`: if the `j`-line of `B_J` through `c` lies in `Y_J`, then its position lies in
`Y_{J ∪ j}`. -/
lemma resPos_mem_posFull_insert {Y : Set (K → Fin n)} {J : Finset K} {j : {i // i ∉ J}}
    {c : {i // i ∉ J} → Fin n} (h : ∀ t, Function.update c j t ∈ posFull Y J) :
    resPos (Finset.subset_insert j.1 J) c ∈ posFull Y (insert j.1 J) := by
  intro z'
  set t := z' ⟨j.1, Finset.mem_insert_self _ _⟩
  set z : {i // i ∈ J} → Fin n := fun i => z' ⟨i.1, Finset.mem_insert_of_mem i.2⟩
  have key : glue (insert j.1 J) z' (resPos (Finset.subset_insert j.1 J) c) =
      glue J z (Function.update c j t) := by
    funext i
    by_cases hi : i ∈ J
    · have hi' : i ∈ insert j.1 J := Finset.mem_insert_of_mem hi
      simp [glue, hi, hi', z]
    · by_cases hij : i = j.1
      · subst hij
        simp [glue, hi, t]
      · have hi' : i ∉ insert j.1 J := by simp [hi, hij]
        have hij' : (⟨i, hi⟩ : {i // i ∉ J}) ≠ j := fun h => hij (congrArg Subtype.val h)
        simp [glue, hi, hi', Function.update_of_ne hij']
  rw [key]
  exact h t z

end PosFull

/-! ### Lemma CL: the induction over the levels `J` -/

section CL

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {P : K → Type*} [∀ k, Fintype (P k)] [∀ k, DecidableEq (P k)]
variable {H : (k : K) → Matrix (P k) (Fin n) F} {θ₀ : ℝ} {Y : Set (K → Fin n)}

omit [DecidableEq K] in
private lemma ne_univ_of_not_mem {J : Finset K} {i : K} (h : i ∉ J) : J ≠ Finset.univ :=
  fun he => h (he ▸ Finset.mem_univ i)

omit [DecidableEq K] in
private lemma ne_univ_of_ssubset {A B : Finset K} (h : A ⊂ B) : A ≠ Finset.univ :=
  Finset.ssubset_univ_iff.1 (lt_of_lt_of_le h (Finset.subset_univ B))

lemma badSet_of_eq_univ {J : Finset K} (hJ : J = Finset.univ) : badSet H θ₀ Y J = ∅ := by
  subst hJ
  exact badSet_univ

/-- Part (ii) of the proof of (C2): if the position of the `j`-line of `B_J` through `c` is not
in `Bad_{J ∪ j}`, then no face `Bad_{J''}↑_J` with `j ∈ J''` meets this line. -/
lemma resPos_not_mem_badSet_of_mem {J J'' : Finset K} {j : {i // i ∉ J}}
    {c : {i // i ∉ J} → Fin n}
    (hβ : resPos (Finset.subset_insert j.1 J) c ∉ badSet H θ₀ Y (insert j.1 J))
    (h : J ⊂ J'') (hj : j.1 ∈ J'') : resPos h.subset c ∉ badSet H θ₀ Y J'' := by
  intro hc
  have hsub : insert j.1 J ⊆ J'' := Finset.insert_subset hj h.subset
  rcases hsub.eq_or_ssubset with heq | hss
  · subst heq
    exact hβ hc
  · exact hβ (mem_badSet_of_resPos (ne_univ_of_ssubset hss) hss hc)

/-- Part (iii) of the proof of (C2): the position of the induced line `μ_{J''}` of `B_{J''}`
(`j ∉ J''`) is not in `Bad_{J'' ∪ j}`. -/
lemma resPos_insert_not_mem_badSet {J J'' : Finset K} {j : {i // i ∉ J}}
    {c : {i // i ∉ J} → Fin n}
    (hβ : resPos (Finset.subset_insert j.1 J) c ∉ badSet H θ₀ Y (insert j.1 J))
    (h : J ⊂ J'') (hj : j.1 ∉ J'') :
    resPos (Finset.subset_insert j.1 J'') (resPos h.subset c) ∉
      badSet H θ₀ Y (insert j.1 J'') := by
  intro hc
  have hss : insert j.1 J ⊂ insert j.1 J'' := by
    obtain ⟨i, hi, hiJ⟩ := Finset.exists_of_ssubset h
    rw [Finset.ssubset_iff_of_subset (Finset.insert_subset_insert _ h.subset)]
    refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun hij => hj (hij ▸ hi), hiJ⟩
  exact hβ (mem_badSet_of_resPos (ne_univ_of_ssubset hss) hss hc)

omit [Fintype K] in
lemma linePts_liftSet_eq {J J'' : Finset K} (h : J ⊆ J'') {j : {i // i ∉ J}} (hj : j.1 ∉ J'')
    (c : {i // i ∉ J} → Fin n) (Z : Set ({i // i ∉ J''} → Fin n)) :
    linePts (liftSet J J'' Z) j c = linePts Z ⟨j.1, hj⟩ (resPos h c) := by
  ext t
  rw [mem_linePts, mem_linePts, mem_liftSet, ← resPos_update_of_not_mem h c hj t]
  exact ⟨fun ⟨_, h'⟩ => h', fun h' => ⟨h, h'⟩⟩

/-- Decomposition of `μ ∩ Can_J` (parts (i)–(iii) of the proof of (C2)). -/
lemma linePts_canJ_subset {J : Finset K} {j : {i // i ∉ J}} {c : {i // i ∉ J} → Fin n}
    (hβ : resPos (Finset.subset_insert j.1 J) c ∉ badSet H θ₀ Y (insert j.1 J)) :
    linePts (canJ H θ₀ Y J) j c ⊆ linePts (posFull Y J) j c ∪
      (Finset.univ.filter fun J'' : Finset K => J ⊂ J'' ∧ j.1 ∉ J'').biUnion
        fun J'' => linePts (liftSet J J'' (badSet H θ₀ Y J'')) j c := by
  intro t ht
  rw [mem_linePts, mem_canJ] at ht
  rcases ht with ht | ⟨J'', h, hc⟩
  · exact Finset.mem_union_left _ (mem_linePts.2 ht)
  · by_cases hj : j.1 ∈ J''
    · rw [resPos_update_of_mem h.subset c hj] at hc
      exact absurd hc (resPos_not_mem_badSet_of_mem hβ h hj)
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨J'', Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hj⟩, ?_⟩
      rw [mem_linePts, mem_liftSet]
      exact ⟨h.subset, hc⟩

/-- The number of `J'' ⊋ J` is at most `2^{|K| - |J|}`. -/
lemma card_filter_ssubset_le (J : Finset K) (p : Finset K → Prop) [DecidablePred p] :
    (Finset.univ.filter fun J'' : Finset K => J ⊂ J'' ∧ p J'').card ≤
      2 ^ (Fintype.card K - J.card) := by
  calc _ ≤ (Finset.univ \ J).powerset.card := by
        apply Finset.card_le_card_of_injOn (fun J'' => J'' \ J)
        · intro J'' _
          simp only [Finset.coe_powerset, Set.mem_preimage]
          exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl
        · intro A hA B hB hAB
          simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hA hB
          have hAB' : A \ J = B \ J := hAB
          rw [← Finset.sdiff_union_of_subset hA.1.subset,
            ← Finset.sdiff_union_of_subset hB.1.subset, hAB']
    _ = 2 ^ (Fintype.card K - J.card) := by
        rw [Finset.card_powerset, Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ]

/-- **Lemma CL (C2)** at every level `J`: for the `j`-line `μ_J` of the base `B_J` through `c`,
whose position `c|_{K \ (J ∪ j)}` is not in `Bad_{J ∪ j}`,
`|μ_J ∩ Can_J| < c'_{k_J} η' n` and `|μ_J ∩ hatJ θ J| < c_{k_J} η' n` for every `θ ≥ τδ`,
where `k_J = |K| - |J|`. For `J ≠ K` the second set with `θ = θ₀` is `Bad_J`.
Proof by downward induction on `J`. -/
theorem card_linePts_canJ_hatJ_lt {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2) (J : Finset K) :
    ∀ (j : {i // i ∉ J}) (c : {i // i ∉ J} → Fin n),
      resPos (Finset.subset_insert j.1 J) c ∉ badSet H θ₀ Y (insert j.1 J) →
      ((linePts (canJ H θ₀ Y J) j c).card : ℝ) <
          canC' (τ - ε) (Fintype.card K - J.card) * η' * n ∧
        ∀ θ, τ * δ ≤ θ → ((linePts (hatJ H θ₀ Y θ J) j c).card : ℝ) <
          canC (τ - ε) (Fintype.card K - J.card) * η' * n := by
  set γ := τ - ε with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hηn : 0 ≤ η' * n := mul_nonneg hη' hn
  refine Finset.strongDownwardInduction (n := Fintype.card K)
    (p := fun J => ∀ (j : {i // i ∉ J}) (c : {i // i ∉ J} → Fin n),
      resPos (Finset.subset_insert j.1 J) c ∉ badSet H θ₀ Y (insert j.1 J) →
      ((linePts (canJ H θ₀ Y J) j c).card : ℝ) <
          canC' γ (Fintype.card K - J.card) * η' * n ∧
        ∀ θ, τ * δ ≤ θ → ((linePts (hatJ H θ₀ Y θ J) j c).card : ℝ) <
          canC γ (Fintype.card K - J.card) * η' * n) ?_ J (Finset.card_le_univ J)
  intro J ih _ j c hβ
  set k := Fintype.card K - J.card with hk
  have hJne : J ≠ Finset.univ := ne_univ_of_not_mem j.2
  have hJlt : J.card < Fintype.card K := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.2 hJne)
  have hk1 : 1 ≤ k := by omega
  -- (i) the term `Y_J`
  have hYJ : ((linePts (posFull Y J) j c).card : ℝ) < η' * n := by
    by_contra hcon
    have hfull := isClosedSet_posFull hY J j c
      (by rw [lineCount_eq_card_linePts]; exact not_lt.1 hcon)
    have hmem := resPos_mem_posFull_insert hfull
    by_cases hins : insert j.1 J = Finset.univ
    · exact not_mem_posFull_of_eq_univ hYne hins _ hmem
    · exact hβ (posFull_subset_badSet hins hmem)
  -- (ii), (iii): the faces over `Bad_{J''}`
  set S := Finset.univ.filter fun J'' : Finset K => J ⊂ J'' ∧ j.1 ∉ J'' with hS
  have hcard1 : (linePts (canJ H θ₀ Y J) j c).card ≤ (linePts (posFull Y J) j c).card +
      ∑ J'' ∈ S, (linePts (liftSet J J'' (badSet H θ₀ Y J'')) j c).card :=
    (Finset.card_le_card (linePts_canJ_subset hβ)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hterm : ∀ J'' ∈ S, ((linePts (liftSet J J'' (badSet H θ₀ Y J'')) j c).card : ℝ) ≤
      canC γ (k - 1) * η' * n := by
    intro J'' hJ''
    rw [Finset.mem_filter] at hJ''
    obtain ⟨-, h, hj⟩ := hJ''
    rw [linePts_liftSet_eq h.subset hj]
    rw [badSet_of_ne_univ (ne_univ_of_not_mem hj)]
    have hlt := (ih (Finset.card_le_univ J'') h ⟨j.1, hj⟩ (resPos h.subset c)
      (resPos_insert_not_mem_badSet hβ h hj)).2 θ₀ hθ₀
    have hcardlt : J.card < J''.card := Finset.card_lt_card h
    have hmono : canC γ (Fintype.card K - J''.card) ≤ canC γ (k - 1) :=
      canC_mono hγ (by omega)
    calc _ ≤ canC γ (Fintype.card K - J''.card) * η' * n := hlt.le
      _ ≤ canC γ (k - 1) * η' * n := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hmono hηn
  have hC0 : 0 ≤ canC γ (k - 1) * η' * n := by
    rw [mul_assoc]
    exact mul_nonneg (canC_nonneg hγ _) hηn
  have hsum : ∑ J'' ∈ S, ((linePts (liftSet J J'' (badSet H θ₀ Y J'')) j c).card : ℝ) ≤
      2 ^ k * (canC γ (k - 1) * η' * n) := by
    calc _ ≤ ∑ J'' ∈ S, canC γ (k - 1) * η' * n := Finset.sum_le_sum hterm
      _ = S.card * (canC γ (k - 1) * η' * n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ k * (canC γ (k - 1) * η' * n) := by
          apply mul_le_mul_of_nonneg_right _ hC0
          exact_mod_cast card_filter_ssubset_le J (fun J'' => j.1 ∉ J'')
  have hA : ((linePts (canJ H θ₀ Y J) j c).card : ℝ) < canC' γ k * η' * n := by
    have hcard1' : ((linePts (canJ H θ₀ Y J) j c).card : ℝ) ≤
        (linePts (posFull Y J) j c).card +
          ∑ J'' ∈ S, ((linePts (liftSet J J'' (badSet H θ₀ Y J'')) j c).card : ℝ) := by
      exact_mod_cast hcard1
    have heq : canC' γ k * η' * n = η' * n + 2 ^ k * (canC γ (k - 1) * η' * n) := by
      unfold canC'
      ring
    rw [heq]
    linarith
  refine ⟨hA, fun θ hθ => ?_⟩
  -- the step: `hatJ θ J ∩ μ ⊆ (Can_J ∩ μ) ∪ Ψ_μ`
  have hθ' : γ * δ ≤ θ - ε * δ := by
    rw [hγdef]
    nlinarith
  have hsmall : ((linePts (canJ H θ₀ Y J) j c).card : ℝ) ≤ γ * α * n / 2 := by
    have h1 : canC' γ k ≤ canC' γ (Fintype.card K) := canC'_mono hγ (by omega)
    calc _ ≤ canC' γ k * η' * n := hA.le
      _ ≤ canC' γ (Fintype.card K) * η' * n := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right h1 hηn
      _ ≤ (γ * α / 2) * n := mul_le_mul_of_nonneg_right hc' hn
      _ = γ * α * n / 2 := by ring
  have hstep := card_linePts_stepSet_le (H := fun j : {i // i ∉ J} => H j.1) (j := j)
    (hH j.1) hδ hγ hθ' hαn (linePts_mono (posFull_subset_canJ J)) hsmall
  have hck : canC γ k = canC' γ k * (1 + 1 / γ) := canC_of_pos (by omega)
  have hpos : 0 < 1 + 1 / γ := by positivity
  calc ((linePts (hatJ H θ₀ Y θ J) j c).card : ℝ)
      ≤ (linePts (canJ H θ₀ Y J) j c).card * (1 + 1 / γ) := hstep
    _ < canC' γ k * η' * n * (1 + 1 / γ) := mul_lt_mul_of_pos_right hA hpos
    _ = canC γ k * η' * n := by rw [hck]; ring


/-- `μ ∩ univ` is the whole line. -/
lemma linePts_univ {ι : Type*} [DecidableEq ι] (j : ι) (c : ι → Fin n) :
    linePts (Set.univ : Set (ι → Fin n)) j c = Finset.univ := by
  ext t
  simp [mem_linePts]

/-- **Lemma CL (C3)** at level `J`: the line through a position of `Bad_{J ∪ j}` is contained in
`Can_J`. -/
lemma update_mem_canJ_of_mem_badSet {J : Finset K} {j : {i // i ∉ J}}
    {c : {i // i ∉ J} → Fin n}
    (hβ : resPos (Finset.subset_insert j.1 J) c ∈ badSet H θ₀ Y (insert j.1 J)) (t : Fin n) :
    Function.update c j t ∈ canJ H θ₀ Y J := by
  apply resPos_mem_canJ (Finset.ssubset_insert j.2)
  rw [resPos_update_of_mem _ c (Finset.mem_insert_self _ _)]
  exact hβ

/-- **Lemma CL (C3)** at level `J`: `Can_J` is `c'_{k_J} η'`-closed in `B_J`. -/
theorem isClosedSet_canJ {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2) (J : Finset K) :
    IsClosedSet (canC' (τ - ε) (Fintype.card K - J.card) * η') (canJ H θ₀ Y J) := by
  intro j c hcount t
  by_cases hβ : resPos (Finset.subset_insert j.1 J) c ∈ badSet H θ₀ Y (insert j.1 J)
  · exact update_mem_canJ_of_mem_badSet hβ t
  · have := (card_linePts_canJ_hatJ_lt hH hδ hετ hθ₀ hαn hY hYne hη' hc' J j c hβ).1
    rw [lineCount_eq_card_linePts] at hcount
    linarith

/-- **Lemma CL (C3)** at level `J`: `hatJ θ J` (in particular `Bad_J`) is `c_{k_J} η'`-closed. -/
theorem isClosedSet_hatJ {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2) (J : Finset K) {θ : ℝ}
    (hθ : τ * δ ≤ θ) :
    IsClosedSet (canC (τ - ε) (Fintype.card K - J.card) * η') (hatJ H θ₀ Y θ J) := by
  intro j c hcount t
  by_cases hβ : resPos (Finset.subset_insert j.1 J) c ∈ badSet H θ₀ Y (insert j.1 J)
  · exact canJ_subset_hatJ θ J (update_mem_canJ_of_mem_badSet hβ t)
  · have := (card_linePts_canJ_hatJ_lt hH hδ hετ hθ₀ hαn hY hYne hη' hc' J j c hβ).2 θ hθ
    rw [lineCount_eq_card_linePts] at hcount
    linarith

/-- **Lemma CL (C3)** at level `J`: the sets `hatJ θ J` (in particular `Bad_J`) are proper
for `J ≠ K`. Downward induction on `J`. -/
theorem hatJ_ne_univ {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2)
    (hc : canC (τ - ε) (Fintype.card K) * η' < 1) (J : Finset K) (hJ : J ≠ Finset.univ)
    {θ : ℝ} (hθ : τ * δ ≤ θ) : hatJ H θ₀ Y θ J ≠ Set.univ := by
  have hγ : 0 < τ - ε := by linarith
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hαn
      linarith
    · exact h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  revert hJ θ
  refine Finset.strongDownwardInduction (n := Fintype.card K)
    (p := fun J => J ≠ Finset.univ → ∀ {θ : ℝ}, τ * δ ≤ θ → hatJ H θ₀ Y θ J ≠ Set.univ) ?_ J
    (Finset.card_le_univ J)
  intro J ih _ hJ θ hθ hfull
  obtain ⟨i, -, hi⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.2 hJ)
  set j : {i // i ∉ J} := ⟨i, hi⟩
  -- every position of `B_{J ∪ j}` lies in `Bad_{J ∪ j}`
  have hall : ∀ β, β ∈ badSet H θ₀ Y (insert j.1 J) := by
    intro β
    obtain ⟨c, rfl⟩ := exists_resPos_eq (Finset.subset_insert j.1 J) ⟨0, hn⟩ β
    by_contra hβ
    have hlt := (card_linePts_canJ_hatJ_lt hH hδ hετ hθ₀ hαn hY hYne hη' hc' J j c hβ).2 θ hθ
    rw [hfull, linePts_univ, Finset.card_univ, Fintype.card_fin] at hlt
    have hmono : canC (τ - ε) (Fintype.card K - J.card) ≤ canC (τ - ε) (Fintype.card K) :=
      canC_mono hγ (Nat.sub_le _ _)
    have h1 : canC (τ - ε) (Fintype.card K - J.card) * η' * n ≤
        canC (τ - ε) (Fintype.card K) * η' * n := by
      have := mul_le_mul_of_nonneg_right hmono hη'
      exact mul_le_mul_of_nonneg_right this hn'.le
    have h2 : canC (τ - ε) (Fintype.card K) * η' * n < 1 * n :=
      mul_lt_mul_of_pos_right hc hn'
    linarith
  by_cases hins : insert j.1 J = Finset.univ
  · have := hall (fun _ => ⟨0, hn⟩)
    rw [badSet_of_eq_univ hins] at this
    exact this
  · rw [badSet_of_ne_univ hins] at hall
    exact ih (Finset.card_le_univ _) (Finset.ssubset_insert j.2) hins hθ₀
      (Set.eq_univ_of_forall hall)

/-- `Bad_J` is proper for `J ≠ K`. -/
theorem badSet_ne_univ {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2)
    (hc : canC (τ - ε) (Fintype.card K) * η' < 1) (J : Finset K) :
    badSet H θ₀ Y J ≠ Set.univ := by
  by_cases hJ : J = Finset.univ
  · rw [badSet_of_eq_univ hJ]
    intro h
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simp at hαn
        linarith
      · exact h
    have := h ▸ Set.mem_univ (fun _ => (⟨0, hn⟩ : Fin n))
    exact this
  · rw [badSet_of_ne_univ hJ]
    exact hatJ_ne_univ hH hδ hετ hθ₀ hαn hY hYne hη' hc' hc J hJ hθ₀

/-- `Bad_J` is `c_{k_J} η'`-closed. -/
theorem isClosedSet_badSet {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2) (J : Finset K) :
    IsClosedSet (canC (τ - ε) (Fintype.card K - J.card) * η') (badSet H θ₀ Y J) := by
  by_cases hJ : J = Finset.univ
  · rw [badSet_of_eq_univ hJ]
    intro j
    exact absurd (hJ ▸ Finset.mem_univ j.1 : j.1 ∈ J) j.2
  · rw [badSet_of_ne_univ hJ]
    exact isClosedSet_hatJ hH hδ hετ hθ₀ hαn hY hYne hη' hc' J hθ₀

end CL

/-! ### The level `J = ∅`: the cube `V^K` itself -/

section Transport

variable {K : Type*} [DecidableEq K]

/-- The base `B_∅` is the cube itself; lines correspond to lines. -/
lemma outer_empty_update (y : K → Fin n) (j : K) (t : Fin n) :
    outer ∅ (Function.update y j t) =
      Function.update (outer ∅ y) ⟨j, Finset.notMem_empty j⟩ t := by
  funext i
  simp only [outer, Function.update_apply, Subtype.ext_iff]

private lemma outer_update_of_mem' {J : Finset K} (y : K → Fin n) {j : K} (hj : j ∈ J) (t : Fin n) :
    outer J (Function.update y j t) = outer J y := by
  funext i
  have : i.1 ≠ j := fun h => i.2 (h ▸ hj)
  simp only [outer, Function.update_of_ne this]

lemma linePts_preimage_outer_empty (S : Set ({i // i ∉ (∅ : Finset K)} → Fin n)) (j : K)
    (y : K → Fin n) :
    linePts (outer ∅ ⁻¹' S) j y = linePts S ⟨j, Finset.notMem_empty j⟩ (outer ∅ y) := by
  ext t
  rw [mem_linePts, mem_linePts, Set.mem_preimage, outer_empty_update]

lemma crossSet_preimage_outer_empty (Z : Set ({i // i ∉ (∅ : Finset K)} → Fin n)) (j : K)
    (y : K → Fin n) :
    crossSet (outer ∅ ⁻¹' Z) j y = crossSet Z ⟨j, Finset.notMem_empty j⟩ (outer ∅ y) := by
  ext t
  rw [mem_crossSet, mem_crossSet]
  constructor
  · rintro ⟨j', hj', h⟩
    refine ⟨⟨j', Finset.notMem_empty j'⟩, fun h' => hj' (congrArg Subtype.val h'), fun s => ?_⟩
    have := h s
    rwa [Set.mem_preimage, outer_empty_update, outer_empty_update] at this
  · rintro ⟨j', hj', h⟩
    refine ⟨j'.1, fun h' => hj' (Subtype.ext h'), fun s => ?_⟩
    rw [Set.mem_preimage, outer_empty_update, outer_empty_update]
    exact h s

variable [Fintype K]

lemma lineCount_preimage_outer_empty (S : Set ({i // i ∉ (∅ : Finset K)} → Fin n)) (j : K)
    (y : K → Fin n) :
    lineCount (outer ∅ ⁻¹' S) j y = lineCount S ⟨j, Finset.notMem_empty j⟩ (outer ∅ y) := by
  rw [lineCount_eq_card_linePts, lineCount_eq_card_linePts, linePts_preimage_outer_empty]

lemma IsClosedSet.preimage_outer_empty {η : ℝ} {S : Set ({i // i ∉ (∅ : Finset K)} → Fin n)}
    (hS : IsClosedSet η S) : IsClosedSet η (outer ∅ ⁻¹' S) := by
  intro j y hcount t
  rw [lineCount_preimage_outer_empty] at hcount
  have := hS _ _ hcount t
  rwa [Set.mem_preimage, outer_empty_update]

omit [DecidableEq K] [Fintype K] in
lemma outer_empty_surjective : Function.Surjective (outer (n := n) (∅ : Finset K)) := by
  intro c
  refine ⟨fun i => c ⟨i, Finset.notMem_empty i⟩, ?_⟩
  funext i
  rfl

omit [Fintype K] in
lemma preimage_outer_empty_posFull (Y : Set (K → Fin n)) : outer ∅ ⁻¹' posFull Y ∅ = Y := by
  ext y
  simp only [Set.mem_preimage, posFull]
  constructor
  · intro h
    have := h (inner ∅ y)
    rwa [glue_inner_outer] at this
  · intro h z
    have hz : z = inner ∅ y := funext fun i => absurd i.2 (Finset.notMem_empty _)
    rw [hz, glue_inner_outer]
    exact h

variable {P : K → Type*} [∀ k, Fintype (P k)] [∀ k, DecidableEq (P k)]
variable {H : (k : K) → Matrix (P k) (Fin n) F} {θ₀ : ℝ} {Y : Set (K → Fin n)}

omit [Fintype K] in
lemma psiSet_preimage_outer_empty (θ : ℝ) (Z Y' : Set ({i // i ∉ (∅ : Finset K)} → Fin n))
    (j : K) (y : K → Fin n) :
    psiSet H θ (outer ∅ ⁻¹' Z) (outer ∅ ⁻¹' Y') j y =
      psiSet (fun j : {i // i ∉ (∅ : Finset K)} => H j.1) θ Z Y' ⟨j, Finset.notMem_empty j⟩
        (outer ∅ y) := by
  simp only [psiSet, crossSet_preimage_outer_empty, linePts_preimage_outer_empty]

omit [Fintype K] in
lemma preimage_outer_empty_stepSet (θ : ℝ) (Z Y' : Set ({i // i ∉ (∅ : Finset K)} → Fin n)) :
    outer ∅ ⁻¹' stepSet (fun j : {i // i ∉ (∅ : Finset K)} => H j.1) θ Z Y' =
      stepSet H θ (outer ∅ ⁻¹' Z) (outer ∅ ⁻¹' Y') := by
  ext y
  rw [Set.mem_preimage, mem_stepSet, mem_stepSet, Set.mem_preimage]
  simp only [psiSet_preimage_outer_empty]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, fun j => h2 ⟨j, Finset.notMem_empty j⟩⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, fun j => h2 j.1⟩

/-- `Can(Y)` is `Can_∅` (with `B_∅ = V^K`). -/
theorem canSet_eq : canSet H θ₀ Y = outer ∅ ⁻¹' canJ H θ₀ Y ∅ := by
  ext y
  rw [Set.mem_preimage, mem_canJ, ← Set.mem_preimage, preimage_outer_empty_posFull]
  unfold canSet
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro (h | ⟨J, hJ, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨J, Finset.empty_ssubset.2 hJ, h⟩
  · rintro (h | ⟨J, hJ, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨J, Finset.empty_ssubset.1 hJ, h⟩

/-- `Ŷ^θ` is the level `J = ∅` of the construction (with `B_∅ = V^K`). -/
theorem hatSet_eq (θ : ℝ) : hatSet H θ₀ Y θ = outer ∅ ⁻¹' hatJ H θ₀ Y θ ∅ := by
  unfold hatSet hatJ
  rw [preimage_outer_empty_stepSet, ← canSet_eq, preimage_outer_empty_posFull]

lemma resPos_empty_mem_badSet_iff (j : K) (y : K → Fin n) :
    resPos (Finset.subset_insert j (∅ : Finset K)) (outer ∅ y) ∈ badSet H θ₀ Y (insert j ∅) ↔
      outer {j} y ∈ badSet H θ₀ Y {j} := by
  have key : ∀ J' : Finset K, J' = {j} → ∀ h : (∅ : Finset K) ⊆ J',
      (resPos h (outer ∅ y) ∈ badSet H θ₀ Y J' ↔ outer {j} y ∈ badSet H θ₀ Y {j}) := by
    rintro J' rfl h
    exact Iff.rfl
  exact key _ (Finset.insert_empty) _

end Transport

/-! ### Lemma CL for `Can(Y)` and `Ŷ^θ` -/

section CLMain

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {P : K → Type*} [∀ k, Fintype (P k)] [∀ k, DecidableEq (P k)]
variable {H : (k : K) → Matrix (P k) (Fin n) F} {θ₀ : ℝ} {Y : Set (K → Fin n)}

/-- **Lemma CL (C2).** Let `μ` be the `j`-line through `y`, whose position `y|_{K \ j}` is not in
`Bad_{{j}}`. Then `|μ ∩ Can(Y)| < c'_k η' n` and `|μ ∩ Ŷ^θ| < c_k η' n` for every `θ ≥ τδ`
(`k = |K|`, `γ = τ - ε`). -/
theorem lineCount_canSet_hatSet_lt {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2)
    {j : K} {y : K → Fin n} (hpos : outer {j} y ∉ badSet H θ₀ Y {j}) :
    (lineCount (canSet H θ₀ Y) j y : ℝ) < canC' (τ - ε) (Fintype.card K) * η' * n ∧
      ∀ θ, τ * δ ≤ θ →
        (lineCount (hatSet H θ₀ Y θ) j y : ℝ) < canC (τ - ε) (Fintype.card K) * η' * n := by
  have h := card_linePts_canJ_hatJ_lt hH hδ hετ hθ₀ hαn hY hYne hη' hc' ∅
    ⟨j, Finset.notMem_empty j⟩ (outer ∅ y) ((resPos_empty_mem_badSet_iff j y).not.2 hpos)
  simp only [Finset.card_empty, Nat.sub_zero] at h
  refine ⟨?_, fun θ hθ => ?_⟩
  · rw [canSet_eq, lineCount_preimage_outer_empty, lineCount_eq_card_linePts]
    exact h.1
  · rw [hatSet_eq, lineCount_preimage_outer_empty, lineCount_eq_card_linePts]
    exact h.2 θ hθ

private lemma lineCount_eq_of_full {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Set (ι → Fin n)}
    {j : ι} {y : ι → Fin n} (h : ∀ t, Function.update y j t ∈ S) : lineCount S j y = n := by
  have : linePts S j y = Finset.univ := by
    ext t
    simp [mem_linePts, h t]
  rw [lineCount_eq_card_linePts, this, Finset.card_univ, Fintype.card_fin]

/-- **Lemma CL (C3)**, full lines of `Can(Y)`: they are exactly the `j`-lines in positions from
`Bad_{{j}}`. -/
theorem full_line_canSet_iff {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2)
    (hc : canC (τ - ε) (Fintype.card K) * η' < 1) (j : K) (y : K → Fin n) :
    (∀ t, Function.update y j t ∈ canSet H θ₀ Y) ↔ outer {j} y ∈ badSet H θ₀ Y {j} := by
  constructor
  · intro hfull
    by_contra hpos
    have h := (lineCount_canSet_hatSet_lt hH hδ hετ hθ₀ hαn hY hYne hη' hc' hpos).1
    rw [lineCount_eq_of_full hfull] at h
    have hγ : 0 < τ - ε := by linarith
    have hk : 0 < Fintype.card K := Fintype.card_pos_iff.2 ⟨j⟩
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : canC' (τ - ε) (Fintype.card K) * η' * n ≤ canC (τ - ε) (Fintype.card K) * η' * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (canC'_le_canC hγ hk) hη') hn
    have h2 : canC (τ - ε) (Fintype.card K) * η' * n ≤ 1 * n :=
      mul_le_mul_of_nonneg_right hc.le hn
    linarith
  · intro hpos t
    apply outer_preimage_badSet_subset_canSet (Finset.singleton_nonempty j)
    rw [Set.mem_preimage, outer_update_of_mem' y (Finset.mem_singleton_self j)]
    exact hpos

/-- **Lemma CL (C3)**, full lines of `Ŷ^θ`: they are exactly the `j`-lines in positions from
`Bad_{{j}}`. -/
theorem full_line_hatSet_iff {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2)
    (hc : canC (τ - ε) (Fintype.card K) * η' < 1) {θ : ℝ} (hθ : τ * δ ≤ θ) (j : K)
    (y : K → Fin n) :
    (∀ t, Function.update y j t ∈ hatSet H θ₀ Y θ) ↔ outer {j} y ∈ badSet H θ₀ Y {j} := by
  constructor
  · intro hfull
    by_contra hpos
    have h := (lineCount_canSet_hatSet_lt hH hδ hετ hθ₀ hαn hY hYne hη' hc' hpos).2 θ hθ
    rw [lineCount_eq_of_full hfull] at h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : canC (τ - ε) (Fintype.card K) * η' * n ≤ 1 * n :=
      mul_le_mul_of_nonneg_right hc.le hn
    linarith
  · intro hpos t
    exact canSet_subset_hatSet θ
      ((full_line_canSet_iff hH hδ hετ hθ₀ hαn hY hYne hη' hc' hc j y).2 hpos t)

/-- **Lemma CL (C3)**: `Can(Y)` is `c'_k η'`-closed. -/
theorem isClosedSet_canSet {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2) :
    IsClosedSet (canC' (τ - ε) (Fintype.card K) * η') (canSet H θ₀ Y) := by
  have h := isClosedSet_canJ hH hδ hετ hθ₀ hαn hY hYne hη' hc' ∅
  simp only [Finset.card_empty, Nat.sub_zero] at h
  rw [canSet_eq]
  exact h.preimage_outer_empty

/-- **Lemma CL (C3)**: `Ŷ^θ` is `c_k η'`-closed for every `θ ≥ τδ`. -/
theorem isClosedSet_hatSet {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2) {θ : ℝ} (hθ : τ * δ ≤ θ) :
    IsClosedSet (canC (τ - ε) (Fintype.card K) * η') (hatSet H θ₀ Y θ) := by
  have h := isClosedSet_hatJ hH hδ hετ hθ₀ hαn hY hYne hη' hc' ∅ hθ
  simp only [Finset.card_empty, Nat.sub_zero] at h
  rw [hatSet_eq]
  exact h.preimage_outer_empty

/-- **Lemma CL (C3)**: `Ŷ^θ` is proper (for `K ≠ ∅` and `θ ≥ τδ`). -/
theorem hatSet_ne_univ [Nonempty K] {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2)
    (hc : canC (τ - ε) (Fintype.card K) * η' < 1) {θ : ℝ} (hθ : τ * δ ≤ θ) :
    hatSet H θ₀ Y θ ≠ Set.univ := by
  rw [hatSet_eq]
  intro h
  apply hatJ_ne_univ hH hδ hετ hθ₀ hαn hY hYne hη' hc' hc ∅
    (Finset.univ_nonempty (α := K)).ne_empty.symm hθ
  refine Set.eq_univ_of_forall fun c => ?_
  obtain ⟨y, rfl⟩ := outer_empty_surjective c
  have : y ∈ outer ∅ ⁻¹' hatJ H θ₀ Y θ ∅ := h ▸ Set.mem_univ y
  exact this

/-- **Lemma CL (C3)**: `Can(Y)` is proper. -/
theorem canSet_ne_univ [Nonempty K] {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2)
    (hc : canC (τ - ε) (Fintype.card K) * η' < 1) : canSet H θ₀ Y ≠ Set.univ := by
  intro h
  apply hatSet_ne_univ hH hδ hετ hθ₀ hαn hY hYne hη' hc' hc hθ₀
  exact Set.eq_univ_of_univ_subset (h ▸ canSet_subset_hatSet θ₀)


/-- **Lemma CL (C2)** for `Bad_J` itself (`J ≠ K`): for the `j`-line `μ_J` of the base `B_J`
through `c`, whose position is not in `Bad_{J ∪ j}`, `|μ_J ∩ Bad_J| < c_{k - |J|} η' n`. -/
theorem card_linePts_badSet_lt {δ Δ : ℕ} {α ε τ η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hετ : ε < τ) (hθ₀ : τ * δ ≤ θ₀)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (τ - ε) (Fintype.card K) * η' ≤ (τ - ε) * α / 2) {J : Finset K}
    (j : {i // i ∉ J}) (c : {i // i ∉ J} → Fin n)
    (hpos : resPos (Finset.subset_insert j.1 J) c ∉ badSet H θ₀ Y (insert j.1 J)) :
    (lineCount (badSet H θ₀ Y J) j c : ℝ) < canC (τ - ε) (Fintype.card K - J.card) * η' * n := by
  rw [badSet_of_ne_univ (ne_univ_of_not_mem j.2), lineCount_eq_card_linePts]
  exact (card_linePts_canJ_hatJ_lt hH hδ hετ hθ₀ hαn hY hYne hη' hc' J j c hpos).2 θ₀ hθ₀

/-- `Can_J` with the union restricted to `J ⊊ J'' ⊊ K`, as in the proof. -/
lemma mem_canJ_iff_paper {J : Finset K} {c : {i // i ∉ J} → Fin n} :
    c ∈ canJ H θ₀ Y J ↔ c ∈ posFull Y J ∨
      ∃ J'' : Finset K, ∃ h : J ⊂ J'', J'' ≠ Finset.univ ∧
        resPos h.subset c ∈ badSet H θ₀ Y J'' := by
  rw [mem_canJ]
  constructor
  · rintro (h | ⟨J'', h, hc⟩)
    · exact Or.inl h
    · refine Or.inr ⟨J'', h, fun he => ?_, hc⟩
      rw [badSet_of_eq_univ he] at hc
      exact hc
  · rintro (h | ⟨J'', h, -, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨J'', h, hc⟩

/-- `Can(Y)` with the union restricted to `∅ ≠ J ⊊ K`, as in the proof. -/
lemma mem_canSet_iff_paper {y : K → Fin n} :
    y ∈ canSet H θ₀ Y ↔ y ∈ Y ∨
      ∃ J : Finset K, J.Nonempty ∧ J ≠ Finset.univ ∧ outer J y ∈ badSet H θ₀ Y J := by
  unfold canSet
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro (h | ⟨J, hJ, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨J, hJ, fun he => ?_, h⟩
      rw [badSet_of_eq_univ he] at h
      exact h
  · rintro (h | ⟨J, hJ, -, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨J, hJ, h⟩

/-- The case `k = 1`: `Can(Y) = Y`. -/
theorem canSet_of_subsingleton [Subsingleton K] : canSet H θ₀ Y = Y := by
  ext y
  rw [mem_canSet_iff_paper]
  constructor
  · rintro (h | ⟨J, ⟨i, hi⟩, hJ, -⟩)
    · exact h
    · exact absurd (Finset.eq_univ_of_forall fun i' => Subsingleton.elim i i' ▸ hi) hJ
  · exact Or.inl

/-- The case `k = 1`: `Ŷ^θ = F_θ(N(Y))` on the (unique) line through `y`
(for `θ ≤ δ`). -/
theorem mem_hatSet_of_subsingleton [Subsingleton K] {δ Δ : ℕ} {α ε θ : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hθδ : θ ≤ δ) (j : K) (y : K → Fin n) :
    y ∈ hatSet H θ₀ Y θ ↔ y j ∈ findClosure (H j) θ (nbhd (H j) (linePts Y j y)) := by
  have hcross : crossSet Y j y = ∅ := by
    ext t
    simp only [mem_crossSet, Finset.notMem_empty, iff_false]
    rintro ⟨j', hj', -⟩
    exact hj' (Subsingleton.elim j' j)
  have hpsi : ∀ j' : K, psiSet H θ Y Y j' y =
      findClosure (H j) θ (nbhd (H j) (linePts Y j y)) := by
    intro j'
    obtain rfl := Subsingleton.elim j' j
    rw [psiSet, hcross, Finset.empty_union]
  unfold hatSet
  rw [canSet_of_subsingleton, mem_stepSet]
  simp only [hpsi]
  constructor
  · rintro (h | ⟨-, h⟩)
    · apply (hH j).subset_findClosure_nbhd hθδ
      rw [mem_linePts, Function.update_eq_self]
      exact h
    · exact h j
  · intro h
    by_cases hy : y ∈ Y
    · exact Or.inl hy
    · exact Or.inr ⟨hy, fun j' => Subsingleton.elim j j' ▸ h⟩

end CLMain

/-! ### Lemma `good` (good lines) -/

section Good

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {P : K → Type*} [∀ k, Fintype (P k)] [∀ k, DecidableEq (P k)]

/-- `Ψ_ℓ = Ψ^{θ₀}_ℓ(Can_J, Y_J)` for the line `ℓ` of the base `B_J` through `b` in direction `j`. -/
noncomputable def psiJ (H : (k : K) → Matrix (P k) (Fin n) F) (θ₀ : ℝ) (Y : Set (K → Fin n))
    (J : Finset K) (j : {i // i ∉ J}) (b : {i // i ∉ J} → Fin n) : Finset (Fin n) :=
  psiSet (fun j : {i // i ∉ J} => H j.1) θ₀ (canJ H θ₀ Y J) (posFull Y J) j b

variable {H : (k : K) → Matrix (P k) (Fin n) F} {θ₀ : ℝ} {Y : Set (K → Fin n)}

lemma psiJ_update (J : Finset K) (j : {i // i ∉ J}) (b : {i // i ∉ J} → Fin n) (t : Fin n) :
    psiJ H θ₀ Y J j (Function.update b j t) = psiJ H θ₀ Y J j b :=
  psiSet_update _ _ _

/-- **Lemma `good`, existence of the line**: if `b ∈ B_J \ Bad_J` (`J ≠ K`), then `b ∉ Can_J`
(so no line through `b` lies in `Can_J`) and `b ∉ Ψ_ℓ` for the line `ℓ` through `b` of some
direction `j ∉ J`. -/
theorem exists_good_line {J : Finset K} (hJ : J ≠ Finset.univ) {b : {i // i ∉ J} → Fin n}
    (hb : b ∉ badSet H θ₀ Y J) :
    b ∉ canJ H θ₀ Y J ∧ ∃ j : {i // i ∉ J}, b j ∉ psiJ H θ₀ Y J j b := by
  rw [badSet_of_ne_univ hJ] at hb
  unfold hatJ at hb
  rw [mem_stepSet] at hb
  have h1 : b ∉ canJ H θ₀ Y J := fun h => hb (Or.inl h)
  refine ⟨h1, ?_⟩
  by_contra h2
  exact hb (Or.inr ⟨h1, fun j => not_not.1 (not_exists.1 h2 j)⟩)

/-- Proof of (G1): `ℓ ∩ Can_J ⊆ Cr_{Can_J}(ℓ) ∪ (Y_J ∩ ℓ)` for a line `ℓ ∋ b`, `b ∉ Can_J`. -/
lemma linePts_canJ_subset_cross {J : Finset K} {b : {i // i ∉ J} → Fin n}
    (hb : b ∉ canJ H θ₀ Y J) (j : {i // i ∉ J}) :
    linePts (canJ H θ₀ Y J) j b ⊆ crossSet (canJ H θ₀ Y J) j b ∪ linePts (posFull Y J) j b := by
  intro t ht
  rw [mem_linePts, mem_canJ] at ht
  rcases ht with ht | ⟨J'', h, hc⟩
  · exact Finset.mem_union_right _ (mem_linePts.2 ht)
  · by_cases hj : j.1 ∈ J''
    · rw [resPos_update_of_mem h.subset b hj] at hc
      exact absurd (resPos_mem_canJ h hc) hb
    · apply Finset.mem_union_left
      obtain ⟨i₀, hi₀, hi₀J⟩ := Finset.exists_of_ssubset h
      rw [mem_crossSet]
      refine ⟨⟨i₀, hi₀J⟩, fun he => hj ?_, fun s => ?_⟩
      · have : i₀ = j.1 := congrArg Subtype.val he
        rw [← this]
        exact hi₀
      · apply resPos_mem_canJ h
        rw [resPos_update_of_mem h.subset _ (show (⟨i₀, hi₀J⟩ : {i // i ∉ J}).1 ∈ J'' from hi₀)]
        exact hc

/-- `ℓ ∩ Can_J ⊆ Ψ_ℓ` (uses `S ⊆ F_θ(N(S))`, `θ₀ ≤ δ`). -/
lemma linePts_canJ_subset_psiJ {δ Δ : ℕ} {α ε : ℝ} (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε)
    (hθδ : θ₀ ≤ δ) {J : Finset K} {b : {i // i ∉ J} → Fin n} (hb : b ∉ canJ H θ₀ Y J)
    (j : {i // i ∉ J}) : linePts (canJ H θ₀ Y J) j b ⊆ psiJ H θ₀ Y J j b :=
  (linePts_canJ_subset_cross hb j).trans ((hH j.1).subset_findClosure_nbhd hθδ _)

/-- **Lemma `good` (G1)**: the positions `(β, t)` of the line `ℓ` with `t ∈ G_ℓ = V \ Ψ_ℓ` are
not in `Bad_J`. -/
theorem good_line_G1 {δ Δ : ℕ} {α ε : ℝ} (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε)
    (hθδ : θ₀ ≤ δ) {J : Finset K} (hJ : J ≠ Finset.univ) {b : {i // i ∉ J} → Fin n}
    (hb : b ∉ canJ H θ₀ Y J) (j : {i // i ∉ J}) {t : Fin n} (ht : t ∉ psiJ H θ₀ Y J j b) :
    Function.update b j t ∉ badSet H θ₀ Y J := by
  rw [badSet_of_ne_univ hJ]
  unfold hatJ
  rw [mem_stepSet]
  rintro (h | ⟨-, h⟩)
  · exact ht (linePts_canJ_subset_psiJ hH hθδ hb j (mem_linePts.2 h))
  · have := h j
    rw [Function.update_self, psiSet_update] at this
    exact ht this

/-- **Lemma `good` (G2)**: every `t ∈ G_ℓ` has more than `δ - θ₀` (`= (1 - τ)δ`) good checks
`r ∈ N_j(t)`, i.e. checks with `N_j(r) ⊆ G_ℓ`. -/
theorem good_line_G2 {δ Δ : ℕ} {α ε : ℝ} (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε)
    {J : Finset K} (j : {i // i ∉ J}) (b : {i // i ∉ J} → Fin n) {t : Fin n}
    (ht : t ∉ psiJ H θ₀ Y J j b) :
    (δ : ℝ) - θ₀ < ((nbrs (H j.1) t).filter fun r =>
      vnbrs (H j.1) r ⊆ Finset.univ \ psiJ H θ₀ Y J j b).card := by
  set Ψ := psiJ H θ₀ Y J j b with hΨ
  have hclosed : IsFindClosed (H j.1) θ₀
      (nbhd (H j.1) (crossSet (canJ H θ₀ Y J) j b ∪ linePts (posFull Y J) j b)) Ψ :=
    findClosure_isFindClosed
  have h1 := hclosed t ht
  have hsub : nbrs (H j.1) t \ nbhd (H j.1) Ψ ⊆
      (nbrs (H j.1) t).filter fun r => vnbrs (H j.1) r ⊆ Finset.univ \ Ψ := by
    intro r hr
    rw [Finset.mem_sdiff] at hr
    rw [Finset.mem_filter]
    refine ⟨hr.1, fun u hu => ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, fun huΨ => hr.2 ?_⟩
    rw [mem_nbhd]
    exact ⟨u, huΨ, (mem_vnbrs _).1 hu⟩
  have h2 : (nbrs (H j.1) t \ nbhd (H j.1) Ψ).card +
      (nbrs (H j.1) t ∩ nbhd (H j.1) Ψ).card = δ := by
    rw [Finset.card_sdiff_add_card_inter, (hH j.1).card_nbrs]
  have h3 : (nbrs (H j.1) t ∩ nbhd (H j.1) Ψ).card ≤ (nbrs (H j.1) t ∩
      (nbhd (H j.1) (crossSet (canJ H θ₀ Y J) j b ∪ linePts (posFull Y J) j b) ∪
        nbhd (H j.1) Ψ)).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_right)
  have h4 := Finset.card_le_card hsub
  have h2' : ((nbrs (H j.1) t \ nbhd (H j.1) Ψ).card : ℝ) +
      (nbrs (H j.1) t ∩ nbhd (H j.1) Ψ).card = δ := by exact_mod_cast h2
  have h3' : ((nbrs (H j.1) t ∩ nbhd (H j.1) Ψ).card : ℝ) ≤ (nbrs (H j.1) t ∩
      (nbhd (H j.1) (crossSet (canJ H θ₀ Y J) j b ∪ linePts (posFull Y J) j b) ∪
        nbhd (H j.1) Ψ)).card := by exact_mod_cast h3
  have h4' : ((nbrs (H j.1) t \ nbhd (H j.1) Ψ).card : ℝ) ≤
      ((nbrs (H j.1) t).filter fun r => vnbrs (H j.1) r ⊆ Finset.univ \ Ψ).card := by
    exact_mod_cast h4
  linarith

/-- **Lemma `good` (G3)**: the position `β ∈ B_{J ∪ j}` of the line `ℓ` is not in `Bad_{J ∪ j}`. -/
theorem good_line_G3 {J : Finset K} {b : {i // i ∉ J} → Fin n} (hb : b ∉ canJ H θ₀ Y J)
    (j : {i // i ∉ J}) :
    resPos (Finset.subset_insert j.1 J) b ∉ badSet H θ₀ Y (insert j.1 J) :=
  fun h => hb (resPos_mem_canJ (Finset.ssubset_insert j.2) h)

/-- **Lemma `good` (G4)**: if `θ₀ + 2εδ ≤ δ` (i.e. `τ + 2ε ≤ 1`), then for every nonempty
`T ⊆ G_ℓ` with `|T| ≤ αn` there is a good check `r` with `N_j(r) ∩ T = {t*}`. -/
theorem good_line_G4 {δ Δ : ℕ} {α ε : ℝ} (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε)
    (hθε : θ₀ + 2 * ε * δ ≤ δ) {J : Finset K} (j : {i // i ∉ J}) (b : {i // i ∉ J} → Fin n)
    {T : Finset (Fin n)} (hTne : T.Nonempty) (hTG : T ⊆ Finset.univ \ psiJ H θ₀ Y J j b)
    (hTα : (T.card : ℝ) ≤ α * n) :
    ∃ r : P j.1, ∃ t ∈ T, vnbrs (H j.1) r ⊆ Finset.univ \ psiJ H θ₀ Y J j b ∧
      vnbrs (H j.1) r ∩ T = {t} := by
  set Ψ := psiJ H θ₀ Y J j b with hΨ
  set U := uniqueNbhd (H j.1) T with hU
  set Gd : Fin n → Finset (P j.1) := fun t =>
    (nbrs (H j.1) t).filter fun r => vnbrs (H j.1) r ⊆ Finset.univ \ Ψ with hGd
  by_contra hno
  -- for each `t ∈ T`, the unique-neighbour checks and the good checks at `t` are disjoint
  have hdisj : ∀ t ∈ T, (nbrs (H j.1) t ∩ U).card + (Gd t).card ≤ δ := by
    intro t ht
    have hd : Disjoint (nbrs (H j.1) t ∩ U) (Gd t) := by
      rw [Finset.disjoint_left]
      intro r hr1 hr2
      apply hno
      rw [Finset.mem_inter] at hr1
      rw [hGd, Finset.mem_filter] at hr2
      refine ⟨r, t, ht, hr2.2, ?_⟩
      have hr := hr1.2
      rw [hU, mem_uniqueNbhd, Finset.card_eq_one] at hr
      obtain ⟨t', ht'⟩ := hr
      have htmem : t ∈ vnbrs (H j.1) r ∩ T :=
        Finset.mem_inter.2 ⟨(mem_vnbrs _).2 ((mem_nbrs _).1 hr1.1), ht⟩
      rw [ht', Finset.mem_singleton] at htmem
      rw [ht', htmem]
    rw [← Finset.card_union_of_disjoint hd, ← (hH j.1).card_nbrs t]
    apply Finset.card_le_card
    apply Finset.union_subset Finset.inter_subset_left
    exact Finset.filter_subset _ _
  have hsum1 : ∑ t ∈ T, ((nbrs (H j.1) t ∩ U).card : ℝ) = U.card := by
    exact_mod_cast sum_card_nbrs_inter_uniqueNbhd (H j.1) T
  have hU' := (hH j.1).card_uniqueNbhd_ge hTα
  have hsum2 : ∑ t ∈ T, ((δ : ℝ) - θ₀) < ∑ t ∈ T, ((Gd t).card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hTne fun t ht =>
      good_line_G2 (Y := Y) hH j b (Finset.mem_sdiff.1 (hTG ht)).2
  have hsum3 : ∑ t ∈ T, (((nbrs (H j.1) t ∩ U).card : ℝ) + (Gd t).card) ≤ ∑ t ∈ T, (δ : ℝ) :=
    Finset.sum_le_sum fun t ht => by exact_mod_cast hdisj t ht
  rw [Finset.sum_add_distrib, hsum1] at hsum3
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum2 hsum3
  have hT0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  nlinarith


/-- **Lemma `good`** (all parts together): if `J ≠ K` and `b ∈ B_J \ Bad_J`, then there is a
direction `j ∉ J` such that, for the line `ℓ` of `B_J` through `b` in direction `j` and
`G_ℓ = V \ Ψ_ℓ`: `b j ∈ G_ℓ`, `ℓ ⊄ Can_J`, and (G1)–(G4) hold. Here `θ₀ = τδ` in the proof,
so `δ - θ₀ = (1 - τ)δ` and the condition `θ₀ + 2εδ ≤ δ` is `τ + 2ε ≤ 1`. -/
theorem good_line {δ Δ : ℕ} {α ε : ℝ} (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε)
    (hθδ : θ₀ ≤ δ) (hθε : θ₀ + 2 * ε * δ ≤ δ) {J : Finset K} (hJ : J ≠ Finset.univ)
    {b : {i // i ∉ J} → Fin n} (hb : b ∉ badSet H θ₀ Y J) :
    ∃ j : {i // i ∉ J}, b j ∉ psiJ H θ₀ Y J j b ∧
      (∃ t, Function.update b j t ∉ canJ H θ₀ Y J) ∧
      -- (G1)
      (∀ t ∉ psiJ H θ₀ Y J j b, Function.update b j t ∉ badSet H θ₀ Y J) ∧
      -- (G2)
      (∀ t ∉ psiJ H θ₀ Y J j b, (δ : ℝ) - θ₀ < ((nbrs (H j.1) t).filter fun r =>
        vnbrs (H j.1) r ⊆ Finset.univ \ psiJ H θ₀ Y J j b).card) ∧
      -- (G3)
      resPos (Finset.subset_insert j.1 J) b ∉ badSet H θ₀ Y (insert j.1 J) ∧
      -- (G4)
      (∀ T : Finset (Fin n), T.Nonempty → T ⊆ Finset.univ \ psiJ H θ₀ Y J j b →
        (T.card : ℝ) ≤ α * n → ∃ r : P j.1, ∃ t ∈ T,
          vnbrs (H j.1) r ⊆ Finset.univ \ psiJ H θ₀ Y J j b ∧ vnbrs (H j.1) r ∩ T = {t}) := by
  obtain ⟨hbC, j, hj⟩ := exists_good_line hJ hb
  refine ⟨j, hj, ⟨b j, by rw [Function.update_eq_self]; exact hbC⟩,
    fun t ht => good_line_G1 hH hθδ hJ hbC j ht, fun t ht => good_line_G2 hH j b ht,
    good_line_G3 hbC j, fun T hTne hTG hTα => good_line_G4 hH hθε j b hTne hTG hTα⟩

end Good

/-! ### The parameters of the proof: `τ = 1/4`, `ε ≤ 1/16`, `h = (1 - 2ε)δ` -/

section Paper

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {P : K → Type*} [∀ k, Fintype (P k)] [∀ k, DecidableEq (P k)]
variable {H : (k : K) → Matrix (P k) (Fin n) F} {Y : Set (K → Fin n)}

/-- The canonical error set `Ŷ = Ŷ^h` of the proof: the sets `Bad_J` are built with the
threshold `τδ`, `τ = 1/4`, and the last step uses `h = (1 - 2ε)δ`. -/
noncomputable def canonicalSet (H : (k : K) → Matrix (P k) (Fin n) F) (δ : ℕ) (ε : ℝ)
    (Y : Set (K → Fin n)) : Set (K → Fin n) :=
  hatSet H ((1 / 4 : ℝ) * δ) Y ((1 - 2 * ε) * δ)

/-- **Lemma CL with the parameters of the proof** (`τ = 1/4`, `ε ≤ 1/16`, `h = (1 - 2ε)δ`,
`αn ≥ 2`, `γ = 1/4 - ε`, `k = |K| ≥ 1`): for a proper `η'`-closed `Y` with `η' ≥ 0`,
`c'_k η' ≤ γα/2` and `c_k η' < 1`:
`Y ⊆ Can(Y) ⊆ Ŷ`; `Ŷ` is proper and `c_k η'`-closed; `Can(Y)` is `c'_k η'`-closed;
the full lines of `Can(Y)` and of `Ŷ` are exactly the `j`-lines over `Bad_{{j}}`;
every other `j`-line meets `Can(Y)` in fewer than `c'_k η' n` and `Ŷ` in fewer than `c_k η' n`
points. -/
theorem canonicalSet_spec [Nonempty K] {δ Δ : ℕ} {α ε η' : ℝ}
    (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε) (hδ : 0 < δ) (hε : ε ≤ 1 / 16)
    (hαn : 2 ≤ α * n) (hY : IsClosedSet η' Y) (hYne : Y ≠ Set.univ) (hη' : 0 ≤ η')
    (hc' : canC' (1 / 4 - ε) (Fintype.card K) * η' ≤ (1 / 4 - ε) * α / 2)
    (hc : canC (1 / 4 - ε) (Fintype.card K) * η' < 1) :
    Y ⊆ canSet H ((1 / 4 : ℝ) * δ) Y ∧
    canSet H ((1 / 4 : ℝ) * δ) Y ⊆ canonicalSet H δ ε Y ∧
    canonicalSet H δ ε Y ≠ Set.univ ∧
    IsClosedSet (canC (1 / 4 - ε) (Fintype.card K) * η') (canonicalSet H δ ε Y) ∧
    IsClosedSet (canC' (1 / 4 - ε) (Fintype.card K) * η') (canSet H ((1 / 4 : ℝ) * δ) Y) ∧
    (∀ j y, (∀ t, Function.update y j t ∈ canSet H ((1 / 4 : ℝ) * δ) Y) ↔
      outer {j} y ∈ badSet H ((1 / 4 : ℝ) * δ) Y {j}) ∧
    (∀ j y, (∀ t, Function.update y j t ∈ canonicalSet H δ ε Y) ↔
      outer {j} y ∈ badSet H ((1 / 4 : ℝ) * δ) Y {j}) ∧
    (∀ j y, outer {j} y ∉ badSet H ((1 / 4 : ℝ) * δ) Y {j} →
      (lineCount (canSet H ((1 / 4 : ℝ) * δ) Y) j y : ℝ) <
          canC' (1 / 4 - ε) (Fintype.card K) * η' * n ∧
        (lineCount (canonicalSet H δ ε Y) j y : ℝ) <
          canC (1 / 4 - ε) (Fintype.card K) * η' * n) := by
  have hετ : ε < 1 / 4 := by linarith
  have hθ₀ : (1 / 4 : ℝ) * δ ≤ (1 / 4 : ℝ) * δ := le_rfl
  have hδ' : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  have hh : (1 / 4 : ℝ) * δ ≤ (1 - 2 * ε) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ'
  refine ⟨subset_canSet, canSet_subset_hatSet _,
    hatSet_ne_univ hH hδ hετ hθ₀ hαn hY hYne hη' hc' hc hh,
    isClosedSet_hatSet hH hδ hετ hθ₀ hαn hY hYne hη' hc' hh,
    isClosedSet_canSet hH hδ hετ hθ₀ hαn hY hYne hη' hc',
    fun j y => full_line_canSet_iff hH hδ hετ hθ₀ hαn hY hYne hη' hc' hc j y,
    fun j y => full_line_hatSet_iff hH hδ hετ hθ₀ hαn hY hYne hη' hc' hc hh j y,
    fun j y hpos => ?_⟩
  have h := lineCount_canSet_hatSet_lt hH hδ hετ hθ₀ hαn hY hYne hη' hc' hpos
  exact ⟨h.1, h.2 _ hh⟩

/-- **Lemma `good` with the parameters of the proof** (`θ₀ = δ/4`, `ε ≤ 1/16`). -/
theorem good_line_paper {δ Δ : ℕ} {α ε : ℝ} (hH : ∀ k, IsExpanderMatrix (H k) δ Δ α ε)
    (hε : ε ≤ 1 / 16) {J : Finset K} (hJ : J ≠ Finset.univ) {b : {i // i ∉ J} → Fin n}
    (hb : b ∉ badSet H ((1 / 4 : ℝ) * δ) Y J) :
    ∃ j : {i // i ∉ J}, b j ∉ psiJ H ((1 / 4 : ℝ) * δ) Y J j b ∧
      (∃ t, Function.update b j t ∉ canJ H ((1 / 4 : ℝ) * δ) Y J) ∧
      (∀ t ∉ psiJ H ((1 / 4 : ℝ) * δ) Y J j b,
        Function.update b j t ∉ badSet H ((1 / 4 : ℝ) * δ) Y J) ∧
      (∀ t ∉ psiJ H ((1 / 4 : ℝ) * δ) Y J j b, (1 - 1 / 4 : ℝ) * δ <
        ((nbrs (H j.1) t).filter fun r =>
          vnbrs (H j.1) r ⊆ Finset.univ \ psiJ H ((1 / 4 : ℝ) * δ) Y J j b).card) ∧
      resPos (Finset.subset_insert j.1 J) b ∉ badSet H ((1 / 4 : ℝ) * δ) Y (insert j.1 J) ∧
      (∀ T : Finset (Fin n), T.Nonempty → T ⊆ Finset.univ \ psiJ H ((1 / 4 : ℝ) * δ) Y J j b →
        (T.card : ℝ) ≤ α * n → ∃ r : P j.1, ∃ t ∈ T,
          vnbrs (H j.1) r ⊆ Finset.univ \ psiJ H ((1 / 4 : ℝ) * δ) Y J j b ∧
            vnbrs (H j.1) r ∩ T = {t}) := by
  have hδ' : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  have hθδ : (1 / 4 : ℝ) * δ ≤ δ := by linarith
  have hθε : (1 / 4 : ℝ) * δ + 2 * ε * δ ≤ δ := by nlinarith
  obtain ⟨j, h0, h1, hG1, hG2, hG3, hG4⟩ := good_line hH hθδ hθε hJ hb
  refine ⟨j, h0, h1, hG1, fun t ht => ?_, hG3, hG4⟩
  have := hG2 t ht
  linarith

end Paper

end ProductExpansion
