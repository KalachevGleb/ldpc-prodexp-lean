import Mathlib

/-!
# Product expansion of LDPC codes: basic definitions

This file fixes the objects of the paper *Product expansion of LDPC codes*
(G. Kalachev, in Russian) and states the main theorem.

* The cube with coordinates indexed by a finite type `ι` is `ι → Fin n`;
  a word is a function `(ι → Fin n) → F`.
* The line in direction `i` through `y` is `{update y i t | t}`.
* `colCode C i` is the code `C^{(i)}` (every line in direction `i` is a codeword of `C i`),
  and `boxplus C = ∑ᵢ C^{(i)}` is the code `C₁ ⊞ ⋯ ⊞ C_m`.
* `prodExpanding C ρ` is the product-expansion property with constant `ρ`
  (normalised weights as in the paper).
-/

open Finset

namespace ProductExpansion

variable {F : Type*} [Field F]
variable {n : ℕ}

section Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The line in direction `i` through the point `y` (as a finset of points). -/
def line (i : ι) (y : ι → Fin n) : Finset (ι → Fin n) :=
  Finset.univ.image fun t => Function.update y i t

/-- Restriction of a word to the line in direction `i` through `y`,
parametrised by the `i`-th coordinate. -/
def restrictLine (a : (ι → Fin n) → F) (i : ι) (y : ι → Fin n) : Fin n → F :=
  fun t => a (Function.update y i t)

/-- The code `C^{(i)}`: all words whose restriction to every line of direction `i`
lies in `C i`. -/
def colCode (C : ι → Submodule F (Fin n → F)) (i : ι) :
    Submodule F ((ι → Fin n) → F) where
  carrier := {a | ∀ y, restrictLine a i y ∈ C i}
  add_mem' := by
    intro a b ha hb y
    have : restrictLine (a + b) i y = restrictLine a i y + restrictLine b i y := rfl
    rw [this]
    exact (C i).add_mem (ha y) (hb y)
  zero_mem' := by
    intro y
    exact (C i).zero_mem
  smul_mem' := by
    intro c a ha y
    have : restrictLine (c • a) i y = c • restrictLine a i y := rfl
    rw [this]
    exact (C i).smul_mem c (ha y)

/-- The code `C₁ ⊞ ⋯ ⊞ C_m = C^{(1)} + ⋯ + C^{(m)}`. -/
def boxplus (C : ι → Submodule F (Fin n → F)) : Submodule F ((ι → Fin n) → F) :=
  ⨆ i, colCode C i

/-- Hamming weight of a word on the cube. -/
def weight [DecidableEq F] (a : (ι → Fin n) → F) : ℕ :=
  (Finset.univ.filter fun y => a y ≠ 0).card

/-- Number `|a|_i` of lines of direction `i` on which the word `a` is nonzero. A line of
direction `i` is determined by the coordinates of its points other than the `i`-th one, so each
such line is counted once, through its point `y` with `y i = 0`. -/
def lineWeight [DecidableEq F] (a : (ι → Fin n) → F) (i : ι) (h0 : 0 < n) : ℕ :=
  (Finset.univ.filter fun y : ι → Fin n =>
      y i = ⟨0, h0⟩ ∧ restrictLine a i y ≠ 0).card

/-- Product expansion with constant `ρ` (definition from the paper, with normalised weights
`‖x‖ = |x| / n^m` and `‖a‖_i = |a|_i / n^{m-1}`): every codeword of `C₁ ⊞ ⋯ ⊞ C_m`
decomposes as `∑ᵢ aᵢ`, `aᵢ ∈ C^{(i)}`, with `ρ ∑ᵢ ‖aᵢ‖ᵢ ≤ ‖c‖`.
Multiplying by `n^m`, this is `ρ · n · ∑ᵢ |aᵢ|ᵢ ≤ |c|`. -/
def prodExpanding [DecidableEq F] (C : ι → Submodule F (Fin n → F)) (ρ : ℝ) : Prop :=
  ∀ (h0 : 0 < n), ∀ c ∈ boxplus C, ∃ a : ι → (ι → Fin n) → F,
    (∀ i, a i ∈ colCode C i) ∧ c = ∑ i, a i ∧
    ρ * n * (∑ i, (lineWeight (a i) i h0 : ℝ)) ≤ weight c

end Cube

section Expander

variable [DecidableEq F] {P : Type*} [Fintype P] [DecidableEq P]

/-- Check neighbourhood of a variable set `S` in the Tanner graph of `H`. -/
def nbhd (H : Matrix P (Fin n) F) (S : Finset (Fin n)) : Finset P :=
  S.biUnion fun u => Finset.univ.filter fun p => H p u ≠ 0

/-- `H` is the (weighted) adjacency matrix of a bipartite graph with left degrees `δ`,
right degrees at most `Δ`, which is an `(α, ε)`-expander:
every `S` with `|S| ≤ α n` has `|N(S)| ≥ (1 - ε) δ |S|`. -/
structure IsExpanderMatrix (H : Matrix P (Fin n) F) (δ Δ : ℕ) (α ε : ℝ) : Prop where
  leftDeg : ∀ u, (Finset.univ.filter fun p => H p u ≠ 0).card = δ
  rightDeg : ∀ p, (Finset.univ.filter fun u => H p u ≠ 0).card ≤ Δ
  expand : ∀ S : Finset (Fin n), (S.card : ℝ) ≤ α * n →
    (1 - ε) * δ * S.card ≤ (nbhd H S).card

/-- The code `ker H`. -/
def kerCode (H : Matrix P (Fin n) F) : Submodule F (Fin n → F) :=
  LinearMap.ker (Matrix.mulVecLin H)

end Expander

/-- **Main theorem** (theorem 1 of the paper, in the form that is actually proved):
for every number of codes `m`, left degree `δ ≥ 1`, right degree bound `Δ`, expansion
parameter `α > 0` and `ε ≤ 1/16` there is `ρ₀ > 0` such that for every length `n` and all
codes `Cᵢ = ker Hᵢ` given by `(α, ε)`-expanders with these degrees, the collection
`(C₁, …, C_m)` is `ρ₀`-product-expanding. (In the paper `Δ ≤ δ / (1 - R)` comes from the rate
bound.) -/
def MainTheoremStatement : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] (m δ Δ : ℕ) (α ε : ℝ),
    0 < δ → 0 < α → 0 ≤ ε → ε ≤ 1 / 16 →
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (n : ℕ) (P : Fin m → Type) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
        (H : ∀ i, Matrix (P i) (Fin n) F),
        (∀ i, IsExpanderMatrix (H i) δ Δ α ε) →
        prodExpanding (fun i => kerCode (H i)) ρ₀

end ProductExpansion
