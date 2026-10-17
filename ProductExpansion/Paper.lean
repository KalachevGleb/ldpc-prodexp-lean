import ProductExpansion.Basic

/-!
# The class `ExpLDPC(δ, α, ε)` of the paper; right degrees from the rate

In the paper, `ExpLDPC(δ, α, ε)` is the set of codes `C = ker H`, where `H` is the adjacency
matrix of a `(δ, δ_R)`-biregular `(α, ε)`-expander for some `δ_R`, and theorem 1 bounds the rates
of the codes rather than their right degrees. Here we show that the rate bound gives the bound on the
right degrees used in `MainTheoremStatement`: `|P| δ_R = n δ` (double counting of the edges) and
`dim ker H ≥ n - |P|`, hence `δ_R ≤ δ / (1 - R)` if `dim ker H ≤ R n`.
-/

open Finset

namespace ProductExpansion

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

section Biregular

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The support of `H` is the adjacency matrix of a `(δ, δR)`-biregular bipartite graph. -/
structure IsBiregular (H : Matrix P (Fin n) F) (δ δR : ℕ) : Prop where
  leftDeg : ∀ u, (univ.filter fun p => H p u ≠ 0).card = δ
  rightDeg : ∀ p, (univ.filter fun u => H p u ≠ 0).card = δR

omit [DecidableEq P] in
/-- Double counting of the edges of a biregular graph: `n δ = |P| δR`. -/
lemma IsBiregular.card_mul_eq {H : Matrix P (Fin n) F} {δ δR : ℕ} (hH : IsBiregular H δ δR) :
    n * δ = Fintype.card P * δR := by
  have h1 : ∑ u : Fin n, (univ.filter fun p => H p u ≠ 0).card =
      ∑ p : P, (univ.filter fun u => H p u ≠ 0).card := by
    simp only [card_eq_sum_ones, sum_filter]
    exact Finset.sum_comm
  simp only [hH.leftDeg, hH.rightDeg, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] at h1
  exact h1

omit [DecidableEq F] [DecidableEq P] in
/-- `dim ker H ≥ n - |P|` (rank–nullity). -/
lemma le_finrank_kerCode_add_card (H : Matrix P (Fin n) F) :
    n ≤ Module.finrank F (kerCode H) + Fintype.card P := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin H)
  have h2 : Module.finrank F (LinearMap.range (Matrix.mulVecLin H)) ≤ Fintype.card P :=
    (Submodule.finrank_le _).trans (Module.finrank_fintype_fun_eq_card F).le
  rw [Module.finrank_fin_fun] at h
  unfold kerCode
  omega

omit [DecidableEq P] in
/-- **Right degrees from the rate.** If `dim ker H ≤ R n` with `R < 1` and `n > 0`, then the
right degree of a `(δ, δR)`-biregular `H` satisfies `δR ≤ δ / (1 - R)`. -/
lemma IsBiregular.rightDeg_le_of_rate {H : Matrix P (Fin n) F} {δ δR : ℕ} {R : ℝ}
    (hH : IsBiregular H δ δR) (hR : R < 1) (hn : 0 < n)
    (hrate : (Module.finrank F (kerCode H) : ℝ) ≤ R * n) :
    (δR : ℝ) ≤ δ / (1 - R) := by
  have h1R : 0 < 1 - R := by linarith
  rw [le_div_iff₀ h1R]
  have hP : (1 - R) * n ≤ Fintype.card P := by
    have : (n : ℝ) ≤ Module.finrank F (kerCode H) + Fintype.card P := by
      exact_mod_cast le_finrank_kerCode_add_card H
    linarith
  have hcm : (n : ℝ) * δ = Fintype.card P * δR := by exact_mod_cast hH.card_mul_eq
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (δR : ℝ) * ((1 - R) * n) ≤ δR * Fintype.card P :=
    mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg _)
  by_contra hlt
  push Not at hlt
  have h3 : (δ : ℝ) * n < δR * (1 - R) * n := mul_lt_mul_of_pos_right hlt hnpos
  nlinarith

end Biregular

/-- The class `ExpLDPC(δ, α, ε)` of the paper: codes `C = ker H`, where the support of `H` is a
`(δ, δR)`-biregular graph (for some `δR`) which is an `(α, ε)`-expander. (In the paper `H` is the
adjacency matrix itself; here its nonzero entries are arbitrary.) -/
def InELDPC (C : Submodule F (Fin n → F)) (δ : ℕ) (α ε : ℝ) : Prop :=
  ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (H : Matrix P (Fin n) F) (δR : ℕ),
    IsBiregular H δ δR ∧
    (∀ S : Finset (Fin n), (S.card : ℝ) ≤ α * n → (1 - ε) * δ * S.card ≤ (nbhd H S).card) ∧
    C = kerCode H

/-- A code of `ExpLDPC(δ, α, ε)` of rate at most `R < 1` is `ker H` for an `(α, ε)`-expander `H`
with left degree `δ` and right degrees at most `⌊δ / (1 - R)⌋`. -/
lemma InELDPC.exists_expander {C : Submodule F (Fin n → F)} {δ : ℕ} {α ε R : ℝ}
    (hC : InELDPC C δ α ε) (hR : R < 1) (hrate : (Module.finrank F C : ℝ) ≤ R * n) :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (H : Matrix P (Fin n) F),
      IsExpanderMatrix H δ ⌊(δ : ℝ) / (1 - R)⌋₊ α ε ∧ C = kerCode H := by
  obtain ⟨P, _, _, H, δR, hbi, hexp, rfl⟩ := hC
  refine ⟨P, inferInstance, inferInstance, H, ⟨hbi.leftDeg, fun p => ?_, hexp⟩, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [hbi.rightDeg p]
    exact Nat.le_floor (hbi.rightDeg_le_of_rate hR hn hrate)

/-- **Theorem 1 of the paper in its original form**: for all `m, δ ∈ ℕ`, rates
`R₁, …, R_m < 1`, `α > 0` and `ε ∈ [0, 1/16]` there is `ρ₀ > 0`, depending only on `m`, `α` and
`Δ = ⌊δ / (1 - max Rᵢ)⌋`, such that every collection of codes `Cᵢ ∈ ExpLDPC(δ, α, ε)` of length
`n` and rates at most `Rᵢ` is `ρ₀`-product-expanding.
That `ρ₀` depends only on `(m, Δ, α)` is expressed by a single function `ρ`; `Rmax` is any common
upper bound for the rates (e.g. `max Rᵢ`). -/
def PaperTheoremStatement : Prop :=
  ∃ ρ : ℕ → ℕ → ℝ → ℝ, (∀ m Δ α, 0 < α → 0 < ρ m Δ α) ∧
    ∀ (F : Type) [Field F] [DecidableEq F] (m δ : ℕ) (R : Fin m → ℝ) (Rmax α ε : ℝ),
      0 < δ → (∀ i, R i ≤ Rmax) → Rmax < 1 → 0 < α → 0 ≤ ε → ε ≤ 1 / 16 →
      ∀ (n : ℕ) (C : Fin m → Submodule F (Fin n → F)),
        (∀ i, InELDPC (C i) δ α ε) → (∀ i, (Module.finrank F (C i) : ℝ) ≤ R i * n) →
        prodExpanding C (ρ m ⌊(δ : ℝ) / (1 - Rmax)⌋₊ α)

end ProductExpansion
