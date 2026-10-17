import ProductExpansion.Step2
import ProductExpansion.Step3
import ProductExpansion.Step4
import ProductExpansion.Step5
import ProductExpansion.MainLemma
import ProductExpansion.Paper

/-!
# The main theorem (Theorem 1 of the paper, for all `m`)

* `mainTheoremUniform`: `ρ₀ > 0` depending only on `m`, `Δ`, `α` (uniform in the field, in `δ`,
  `ε ≤ 1/16` and in the length `n`);
* `mainTheorem`: the statement `MainTheoremStatement` of `Basic.lean`;
* `paperTheorem`: theorem 1 as stated in the paper (codes of `ExpLDPC(δ, α, ε)` with rates
  at most `Rᵢ < 1`, `ρ₀` depending only on `m`, `α` and `Δ = ⌊δ / (1 - max Rᵢ)⌋`).
-/

namespace ProductExpansion

/-- **Theorem 1**, uniform form: `ρ₀` depends only on `m`, `Δ` and `α`. -/
theorem mainTheoremUniform : MainTheoremUniformStatement :=
  mainTheoremUniform_of_steps step2 step3 step4 step5

/-- **Theorem 1** for every number `m` of codes: product expansion of collections of LDPC codes
whose check matrices are lossless expanders (see `MainTheoremStatement` in `Basic.lean`). -/
theorem mainTheorem : MainTheoremStatement :=
  mainTheorem_of_steps step2 step3 step4 step5

/-- **Theorem 1 in the form of the paper**: codes of `ExpLDPC(δ, α, ε)` of rates at
most `Rᵢ < 1`; `ρ₀ = ρ m Δ α` with `Δ = ⌊δ / (1 - Rmax)⌋`. -/
theorem paperTheorem : PaperTheoremStatement := by
  classical
  refine ⟨fun m Δ α => if hα : 0 < α then Classical.choose (mainTheoremUniform m Δ α hα) else 1,
    fun m Δ α hα => ?_, ?_⟩
  · simp only [hα, ↓reduceDIte]
    exact (Classical.choose_spec (mainTheoremUniform m Δ α hα)).1
  · intro F _ _ m δ R Rmax α ε hδ hR hRmax hα hε0 hε n C hC hrate
    simp only [hα, ↓reduceDIte]
    have hspec := (Classical.choose_spec
      (mainTheoremUniform m ⌊(δ : ℝ) / (1 - Rmax)⌋₊ α hα)).2
    have hex : ∀ i, ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (H : Matrix P (Fin n) F),
        IsExpanderMatrix H δ ⌊(δ : ℝ) / (1 - Rmax)⌋₊ α ε ∧ C i = kerCode H := fun i =>
      (hC i).exists_expander hRmax
        ((hrate i).trans (mul_le_mul_of_nonneg_right (hR i) (Nat.cast_nonneg n)))
    choose P instF instD H hH hCH using hex
    have hC' : C = fun i => kerCode (H i) := funext hCH
    rw [hC']
    exact @hspec F _ _ δ ε hδ hε0 hε n P instF instD H hH

end ProductExpansion
