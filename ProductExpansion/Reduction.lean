import ProductExpansion.Closure

/-!
# Reduction to "generated from inside" (`lem:gen-reduction`) and the trivial case `α n < 2`

* `exists_decomp_of_mem_lineSpan`: an element of `L(M)` is a sum `∑ᵢ aᵢ` with `aᵢ ∈ C^{(i)}` and
  every nonzero line of `aᵢ` (of direction `i`) contained in `M`.
* `lineWeight_mul_le_of_lines_subset`: then `|aᵢ|ᵢ · n ≤ |M|` (each point lies on exactly one line
  of direction `i`).
* `prodExpanding_of_generatedFromInside`: if every `η`-closed set (`0 < η ≤ 1`) is generated from
  inside, then `C` is `1/(m c_{m,η})`-product-expanding (`lem:gen-reduction`).
* `prodExpanding_of_mul_lt_two`: if `n α < 2` (`α ≥ 0`), then `C` is `(α/2)^m/m`-product-expanding.
* `prodExpanding_of_generatedFromInside_of_two_le`: assembly of the two cases with
  `ρ₀ = min((α/2)^m/m, 1/(m c_{m,η}))` (only `n α ≥ 2` needs the "generated from inside" property).
-/

open Finset

namespace ProductExpansion

variable {F : Type*} [Field F] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Decomposition of elements of a finite supremum of submodules -/

/-- An element of `⨆ i, p i` (finite index type) is a sum `∑ i, a i` with `a i ∈ p i`. -/
lemma exists_sum_of_mem_iSup {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    {p : ι → Submodule R V} {x : V} (hx : x ∈ ⨆ i, p i) :
    ∃ a : ι → V, (∀ i, a i ∈ p i) ∧ x = ∑ i, a i := by
  refine Submodule.iSup_induction p (motive := fun x => ∃ a : ι → V, (∀ i, a i ∈ p i) ∧
    x = ∑ i, a i) hx ?_ ?_ ?_
  · intro i x hx
    refine ⟨Pi.single i x, fun j => ?_, by simp⟩
    by_cases hj : j = i
    · subst hj
      simpa using hx
    · simp [hj]
  · exact ⟨0, fun _ => zero_mem _, by simp⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, fun i => add_mem (ha i) (hb i), by simp [Finset.sum_add_distrib]⟩

/-! ### Lines -/

omit [Fintype ι] in
@[simp] lemma restrictLine_zero (i : ι) (y : ι → Fin n) :
    restrictLine (0 : (ι → Fin n) → F) i y = 0 := rfl

omit [Fintype ι] in
lemma restrictLine_add (a b : (ι → Fin n) → F) (i : ι) (y : ι → Fin n) :
    restrictLine (a + b) i y = restrictLine a i y + restrictLine b i y := rfl

omit [Fintype ι] in
lemma restrictLine_smul (c : F) (a : (ι → Fin n) → F) (i : ι) (y : ι → Fin n) :
    restrictLine (c • a) i y = c • restrictLine a i y := rfl

omit [Fintype ι] in
/-- Two lines of direction `i` with a common point coincide (pointwise in the parametrisation). -/
lemma update_eq_update_of_eq {i : ι} {y y' : ι → Fin n} {t t' : Fin n}
    (h : Function.update y i t = Function.update y' i t') (s : Fin n) :
    Function.update y i s = Function.update y' i s := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · have := congr_fun h k
    rw [Function.update_of_ne hk, Function.update_of_ne hk] at this
    rw [Function.update_of_ne hk, Function.update_of_ne hk, this]

/-- `n` times the number of lines of direction `i` contained in `M` is at most `|M|`
(lines are counted by their points with `i`-th coordinate `0`). -/
lemma card_full_lines_mul_le (M : Finset (ι → Fin n)) (i : ι) (h0 : 0 < n) :
    (univ.filter fun y : ι → Fin n => y i = ⟨0, h0⟩ ∧ ∀ t, Function.update y i t ∈ M).card * n
      ≤ M.card := by
  have h := Finset.card_le_card_of_injOn (s := (univ.filter fun y : ι → Fin n =>
      y i = ⟨0, h0⟩ ∧ ∀ t, Function.update y i t ∈ M) ×ˢ (univ : Finset (Fin n))) (t := M)
    (fun p => Function.update p.1 i p.2) ?_ ?_
  · rwa [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hp
    exact Finset.mem_coe.mpr (hp.1.2.2 p.2)
  · rintro ⟨y, t⟩ hp ⟨y', t'⟩ hp' h
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hp hp'
    dsimp only at hp hp' h
    have ht : t = t' := by
      have := congr_fun h i
      rwa [Function.update_self, Function.update_self] at this
    subst ht
    have hy : y = y' := by
      funext k
      by_cases hk : k = i
      · subst hk
        rw [hp.1.2.1, hp'.1.2.1]
      · have := congr_fun h k
        rwa [Function.update_of_ne hk, Function.update_of_ne hk] at this
    rw [hy]

/-- If all nonzero lines of direction `i` of `a` lie in `M`, then `|a|ᵢ · n ≤ |M|`. -/
lemma lineWeight_mul_le_of_lines_subset [DecidableEq F] (a : (ι → Fin n) → F) (i : ι)
    (h0 : 0 < n) (M : Finset (ι → Fin n))
    (ha : ∀ y, restrictLine a i y ≠ 0 → ∀ t, Function.update y i t ∈ M) :
    lineWeight a i h0 * n ≤ M.card := by
  refine le_trans (Nat.mul_le_mul_right n ?_) (card_full_lines_mul_le M i h0)
  unfold lineWeight
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact ⟨hy.1, ha y hy.2⟩

/-! ### Grouping the line codewords of `L(M)` by direction -/

/-- Words of `C^{(i)}` all of whose nonzero lines (of direction `i`) lie in `M`. -/
def colCodeIn (C : ι → Submodule F (Fin n → F)) (M : Set (ι → Fin n)) (i : ι) :
    Submodule F ((ι → Fin n) → F) where
  carrier := {a | a ∈ colCode C i ∧
    ∀ y, restrictLine a i y ≠ 0 → ∀ t, Function.update y i t ∈ M}
  add_mem' := by
    rintro a b ⟨ha, haM⟩ ⟨hb, hbM⟩
    refine ⟨(colCode C i).add_mem ha hb, fun y hy => ?_⟩
    by_cases h : restrictLine a i y = 0
    · rw [restrictLine_add, h, zero_add] at hy
      exact hbM y hy
    · exact haM y h
  zero_mem' := ⟨(colCode C i).zero_mem, fun y hy => absurd (restrictLine_zero i y) hy⟩
  smul_mem' := by
    rintro c a ⟨ha, haM⟩
    refine ⟨(colCode C i).smul_mem c ha, fun y hy => haM y ?_⟩
    intro h
    rw [restrictLine_smul, h, smul_zero] at hy
    exact hy rfl

omit [Fintype ι] in
lemma mem_colCodeIn {C : ι → Submodule F (Fin n → F)} {M : Set (ι → Fin n)} {i : ι}
    {a : (ι → Fin n) → F} :
    a ∈ colCodeIn C M i ↔
      a ∈ colCode C i ∧ ∀ y, restrictLine a i y ≠ 0 → ∀ t, Function.update y i t ∈ M :=
  Iff.rfl

omit [Fintype ι] in
/-- A line codeword on a line of direction `i` contained in `M` lies in `colCodeIn C M i`. -/
lemma mem_colCodeIn_of_isLineCodeword {C : ι → Submodule F (Fin n → F)} {M : Set (ι → Fin n)}
    {a : (ι → Fin n) → F} {i : ι} {y₀ : ι → Fin n}
    (hM : ∀ t, Function.update y₀ i t ∈ M) (ha : IsLineCodeword C a i y₀) :
    a ∈ colCodeIn C M i := by
  obtain ⟨hsupp, hC⟩ := ha
  -- a nonzero value on the line through `y` forces this line to be the line through `y₀`
  have key : ∀ y t, a (Function.update y i t) ≠ 0 →
      ∀ s, Function.update y i s = Function.update y₀ i s := by
    intro y t hyt s
    obtain ⟨t', ht'⟩ := hsupp _ hyt
    exact update_eq_update_of_eq ht' s
  have hex : ∀ y, restrictLine a i y ≠ 0 → ∃ t, a (Function.update y i t) ≠ 0 := by
    intro y hy
    by_contra h
    simp only [not_exists, not_not] at h
    exact hy (funext h)
  refine ⟨fun y => ?_, fun y hy s => ?_⟩
  · by_cases hy : restrictLine a i y = 0
    · rw [hy]
      exact (C i).zero_mem
    · obtain ⟨t, ht⟩ := hex y hy
      have : restrictLine a i y = restrictLine a i y₀ := by
        funext s
        simp only [restrictLine]
        rw [key y t ht s]
      rw [this]
      exact hC
  · obtain ⟨t, ht⟩ := hex y hy
    rw [key y t ht s]
    exact hM s

omit [Fintype ι] in
lemma lineSpan_le_iSup_colCodeIn (C : ι → Submodule F (Fin n → F)) (M : Set (ι → Fin n)) :
    lineSpan C M ≤ ⨆ i, colCodeIn C M i := by
  unfold lineSpan
  rw [Submodule.span_le]
  rintro a ⟨i, y, hM, ha⟩
  exact Submodule.mem_iSup_of_mem i (mem_colCodeIn_of_isLineCodeword hM ha)

/-- An element of `L(M)` is a sum `∑ᵢ aᵢ`, `aᵢ ∈ C^{(i)}`, where every nonzero line of `aᵢ`
(of direction `i`) is contained in `M`. -/
lemma exists_decomp_of_mem_lineSpan {C : ι → Submodule F (Fin n → F)} {M : Set (ι → Fin n)}
    {x : (ι → Fin n) → F} (hx : x ∈ lineSpan C M) :
    ∃ a : ι → (ι → Fin n) → F, (∀ i, a i ∈ colCode C i) ∧
      (∀ i y, restrictLine (a i) i y ≠ 0 → ∀ t, Function.update y i t ∈ M) ∧
      x = ∑ i, a i := by
  obtain ⟨a, ha, hx⟩ := exists_sum_of_mem_iSup (lineSpan_le_iSup_colCodeIn C M hx)
  exact ⟨a, fun i => (ha i).1, fun i => (ha i).2, hx⟩

/-! ### The reduction lemma -/

/-- Core of `lem:gen-reduction`: if every `S` is contained in a set `M` generated from inside with
`|M| ≤ c |S|`, then `C` is `1/(m c)`-product-expanding (`m = |ι|`). -/
theorem prodExpanding_of_generated_superset [DecidableEq F] (C : ι → Submodule F (Fin n → F))
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ S : Finset (ι → Fin n), ∃ M : Finset (ι → Fin n), S ⊆ M ∧
      GeneratedFromInside C (M : Set (ι → Fin n)) ∧ (M.card : ℝ) ≤ c * S.card) :
    prodExpanding C (1 / (Fintype.card ι * c)) := by
  intro h0 x hx
  set S := univ.filter fun y => x y ≠ 0 with hS
  obtain ⟨M, hSM, hgenM, hMcard⟩ := h S
  have hxM : x ∈ lineSpan C (M : Set (ι → Fin n)) := by
    apply hgenM
    refine ⟨hx, fun y hy => ?_⟩
    exact Finset.mem_coe.mpr (hSM (by simp [hS, hy]))
  obtain ⟨a, haC, haM, hxa⟩ := exists_decomp_of_mem_lineSpan hxM
  refine ⟨a, haC, hxa, ?_⟩
  have hw : (weight x : ℝ) = S.card := rfl
  have hlw : ∀ i, (lineWeight (a i) i h0 : ℝ) * n ≤ M.card := fun i => by
    exact_mod_cast lineWeight_mul_le_of_lines_subset (a i) i h0 M
      (fun y hy t => Finset.mem_coe.mp (haM i y hy t))
  have hsum : (∑ i, (lineWeight (a i) i h0 : ℝ)) * n ≤ Fintype.card ι * M.card := by
    rw [Finset.sum_mul]
    calc ∑ i, (lineWeight (a i) i h0 : ℝ) * n ≤ ∑ _i : ι, (M.card : ℝ) :=
          Finset.sum_le_sum fun i _ => hlw i
      _ = Fintype.card ι * M.card := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hρ : 0 ≤ 1 / (m * c) := by positivity
  have hρmc : 1 / (m * c) * (m * c) ≤ 1 := by
    rcases eq_or_ne (m * c) 0 with h | h
    · rw [h, mul_zero]
      exact zero_le_one
    · rw [one_div_mul_cancel h]
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  calc 1 / (m * c) * n * ∑ i, (lineWeight (a i) i h0 : ℝ)
      = 1 / (m * c) * ((∑ i, (lineWeight (a i) i h0 : ℝ)) * n) := by ring
    _ ≤ 1 / (m * c) * (m * M.card) := mul_le_mul_of_nonneg_left hsum hρ
    _ ≤ 1 / (m * c) * (m * (c * S.card)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMcard hm0) hρ
    _ = (1 / (m * c) * (m * c)) * S.card := by ring
    _ ≤ 1 * S.card := mul_le_mul_of_nonneg_right hρmc hS0
    _ = weight x := by rw [one_mul, hw]

/-- **Reduction lemma** (`lem:gen-reduction`, sharp constant, any `η > 0`): if every `η`-closed
set is generated from inside, then `C` is `1/(m (1 + 2^m/η)^m)`-product-expanding. -/
theorem prodExpanding_of_generatedFromInside' [DecidableEq F] (C : ι → Submodule F (Fin n → F))
    {η : ℝ} (hη : 0 < η)
    (hgen : ∀ M : Set (ι → Fin n), IsClosedSet η M → GeneratedFromInside C M) :
    prodExpanding C
      (1 / (Fintype.card ι * (1 + 2 ^ Fintype.card ι / η) ^ Fintype.card ι)) := by
  apply prodExpanding_of_generated_superset C (by positivity)
  intro S
  obtain ⟨M, hSM, hcl, hcard⟩ := exists_closed_superset' hη S
  exact ⟨M, hSM, hgen _ hcl, hcard⟩

/-- **Reduction lemma** (`lem:gen-reduction`): if `0 < η ≤ 1` and every `η`-closed set is
generated from inside, then `C` is `1/(m c_{m,η})`-product-expanding,
`c_{m,η} = ((2^m + 1)/η)^m`, `m = |ι|`. -/
theorem prodExpanding_of_generatedFromInside [DecidableEq F] (C : ι → Submodule F (Fin n → F))
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hgen : ∀ M : Set (ι → Fin n), IsClosedSet η M → GeneratedFromInside C M) :
    prodExpanding C (1 / (Fintype.card ι * closureConst (Fintype.card ι) η)) := by
  apply prodExpanding_of_generated_superset C (by unfold closureConst; positivity)
  intro S
  obtain ⟨M, hSM, hcl, hcard⟩ := exists_closed_superset hη0 hη1 S
  exact ⟨M, hSM, hgen _ hcl, hcard⟩

/-! ### The trivial case `α n < 2` -/

/-- **Trivial case**: if `n α < 2` (`α ≥ 0`), then `C` is `(α/2)^m/m`-product-expanding:
any decomposition of a nonzero codeword works, since `|aᵢ|ᵢ ≤ n^{m-1}` and `|c| ≥ 1`. -/
theorem prodExpanding_of_mul_lt_two [DecidableEq F] (C : ι → Submodule F (Fin n → F)) {α : ℝ}
    (hα : 0 ≤ α) (hn : (n : ℝ) * α < 2) :
    prodExpanding C ((α / 2) ^ Fintype.card ι / Fintype.card ι) := by
  intro h0 c hc
  by_cases hc0 : c = 0
  · refine ⟨0, fun i => (colCode C i).zero_mem, by simp [hc0], ?_⟩
    have : ∀ i, lineWeight (0 : (ι → Fin n) → F) i h0 = 0 := by
      intro i
      unfold lineWeight
      simp
    simp only [Pi.zero_apply, this, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
    exact Nat.cast_nonneg _
  · obtain ⟨a, ha, hca⟩ := exists_sum_of_mem_iSup (p := colCode C) hc
    refine ⟨a, ha, hca, ?_⟩
    have hw : (1 : ℝ) ≤ weight c := by
      obtain ⟨y, hy⟩ : ∃ y, c y ≠ 0 := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact hc0 (funext h)
      have : 0 < weight c := Finset.card_pos.mpr ⟨y, by simp [hy]⟩
      exact_mod_cast this
    set m := Fintype.card ι with hmdef
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, Nat.cast_zero, div_zero, zero_mul, zero_mul]
      exact Nat.cast_nonneg _
    have hlw : ∀ i, (lineWeight (a i) i h0 : ℝ) * n ≤ (n : ℝ) ^ m := by
      intro i
      have := lineWeight_mul_le_of_lines_subset (a i) i h0 univ (fun _ _ _ => Finset.mem_univ _)
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at this
      exact_mod_cast this
    have hsum : (∑ i, (lineWeight (a i) i h0 : ℝ)) * n ≤ m * (n : ℝ) ^ m := by
      rw [Finset.sum_mul]
      calc ∑ i, (lineWeight (a i) i h0 : ℝ) * n ≤ ∑ _i : ι, (n : ℝ) ^ m :=
            Finset.sum_le_sum fun i _ => hlw i
        _ = m * (n : ℝ) ^ m := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hρ : 0 ≤ (α / 2) ^ m / (m : ℝ) := by positivity
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hpow : (α * n / 2) ^ m ≤ 1 := pow_le_one₀ (by positivity) (by nlinarith)
    calc (α / 2) ^ m / m * n * ∑ i, (lineWeight (a i) i h0 : ℝ)
        = (α / 2) ^ m / m * ((∑ i, (lineWeight (a i) i h0 : ℝ)) * n) := by ring
      _ ≤ (α / 2) ^ m / m * (m * (n : ℝ) ^ m) := mul_le_mul_of_nonneg_left hsum hρ
      _ = (α * n / 2) ^ m := by
          field_simp
          ring
      _ ≤ 1 := hpow
      _ ≤ weight c := hw

/-! ### Monotonicity and assembly of the two cases -/

/-- Product expansion is monotone in the constant `ρ`. -/
lemma prodExpanding.mono [DecidableEq F] {C : ι → Submodule F (Fin n → F)} {ρ ρ' : ℝ}
    (h : prodExpanding C ρ) (hle : ρ' ≤ ρ) : prodExpanding C ρ' := by
  intro h0 c hc
  obtain ⟨a, ha, hca, hineq⟩ := h h0 c hc
  refine ⟨a, ha, hca, le_trans ?_ hineq⟩
  have hnn : 0 ≤ (n : ℝ) * ∑ i, (lineWeight (a i) i h0 : ℝ) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hle hnn
  rw [← mul_assoc, ← mul_assoc] at h1
  exact h1

/-- Assembly of the two cases (end of the proof): if for `n α ≥ 2` every `η`-closed set
(`0 < η ≤ 1`) is generated from inside, then `C` is
`min((α/2)^m/m, 1/(m c_{m,η}))`-product-expanding. -/
theorem prodExpanding_of_generatedFromInside_of_two_le [DecidableEq F]
    (C : ι → Submodule F (Fin n → F)) {α η : ℝ} (hα : 0 ≤ α) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hgen : 2 ≤ (n : ℝ) * α →
      ∀ M : Set (ι → Fin n), IsClosedSet η M → GeneratedFromInside C M) :
    prodExpanding C (min ((α / 2) ^ Fintype.card ι / Fintype.card ι)
      (1 / (Fintype.card ι * closureConst (Fintype.card ι) η))) := by
  by_cases hn : (n : ℝ) * α < 2
  · exact (prodExpanding_of_mul_lt_two C hα hn).mono (min_le_left _ _)
  · exact (prodExpanding_of_generatedFromInside C hη0 hη1 (hgen (not_lt.mp hn))).mono
      (min_le_right _ _)

end ProductExpansion
