import ProductExpansion.Canonical
import ProductExpansion.FaceSyn

/-!
# Interface of the main lemma `D(d)` (decoding with a defect)

This file fixes the statements shared by the modules proving lemma `lem:D`.
Each step of the proof is stated here as a `Prop`
(`Step2Statement`, …, `Step5Statement`) and proved in its own module
(`Step2.lean`, …, `Step5.lean`); the assembly (`MainLemma.lean`) only uses these `Prop`s.

Notation (proof of lemma `D`): `E` is the defect (`η'`-closed, proper), `N` is the current set
(`N''` of level `d'`, `κ`-closed), `a` is the current word (`e''`), `D_{I,b} = faceDefect N E I b`,
`η_b = η' + (d - d') κ` (in the statements: any upper bound `ηb` for it),
`γ = 1/4 - ε`, `c_k = canC γ k`, `c'_k = canC' γ k` (constants of `Canonical.lean`).

* `HypGen H η` — `P(d-1)` on the hyperplane cubes `{j // j ≠ i} → Fin n`;
* `LevelInv2 H δ E N d'` — invariant (I2) at level `d'`;
* `FaceDefectsProper H δ E N d'` — conclusion of step 2;
* `GoodFacesDecoded H δ ε E N a d'` — conclusion of step 3;
* `DecodeStatement F δ Δ α ε d κ` — the statement `D(d)` (both `E` and `N` `κ`-closed).
-/

open Finset

namespace ProductExpansion

section Defs

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- `P(d-1)` on the hyperplane cubes: every proper `η`-closed subset of a hyperplane cube
`{j // j ≠ i} → Fin n` is generated from inside (for the codes `ker H_k`, `k ≠ i`). -/
def HypGen (H : ∀ i, Matrix (P i) (Fin n) F) (η : ℝ) : Prop :=
  ∀ (i : ι) (M : Set ({j // j ≠ i} → Fin n)), IsClosedSet η M → M ≠ Set.univ →
    GeneratedFromInside (fun k : {j // j ≠ i} => kerCode (H k)) M

/-- Invariant (I2) at level `d'`: every complete `J`-face of `N` with `|J| > d'` stands over a
position of `Bad_J = badSet H (δ/4) E J`. For `J = univ` (where `Bad_J = ∅`) this says
`N ≠ univ`. -/
def LevelInv2 (H : ∀ i, Matrix (P i) (Fin n) F) (δ : ℕ) (E N : Set (ι → Fin n)) (d' : ℕ) :
    Prop :=
  ∀ J : Finset ι, d' < J.card → posFull N J ⊆ badSet H ((1 / 4 : ℝ) * δ) E J

/-- Conclusion of step 2: the defects `D_{I,b}` of the faces of type `|I| = d'` over good
positions `b ∉ Bad_I` are proper. -/
def FaceDefectsProper (H : ∀ i, Matrix (P i) (Fin n) F) (δ : ℕ) (E N : Set (ι → Fin n))
    (d' : ℕ) : Prop :=
  ∀ I : Finset ι, I.card = d' → ∀ b : {i // i ∉ I} → Fin n,
    b ∉ badSet H ((1 / 4 : ℝ) * δ) E I → faceDefect N E I b ≠ Set.univ

/-- Conclusion of step 3: every complete `I`-face (`|I| = d'`) of `N` over a good position
`b ∉ Bad_I` is decoded: `a_{I,b} ∈ W_I + F^{\hat D_{I,b}}`. -/
def GoodFacesDecoded (H : ∀ i, Matrix (P i) (Fin n) F) (δ : ℕ) (ε : ℝ)
    (E N : Set (ι → Fin n)) (a : (ι → Fin n) → F) (d' : ℕ) : Prop :=
  ∀ I : Finset ι, I.card = d' → ∀ b : {i // i ∉ I} → Fin n,
    b ∉ badSet H ((1 / 4 : ℝ) * δ) E I → b ∈ posFull N I →
      faceRestrict a I b ∈ boxplus (fun k : {k // k ∈ I} => kerCode (H k)) ⊔
        supported F (canonicalSet (fun k : {k // k ∈ I} => H k) δ ε (faceDefect N E I b))

end Defs

/-- **The main lemma `D(d)`** with closedness bound `κ`, for all cubes of dimension `d` and all
families of check matrices of the class (left degree `δ`, right degrees `≤ Δ`,
`(α,ε)`-expanders): if `a` satisfies `S(E)` for a proper `κ`-closed defect `E`, and `a = c + e`
with `c ∈ ⊞C` and `e` supported in a proper `κ`-closed set `N`, then `e ∈ L(N) + F^{\hat E}`. -/
def DecodeStatement (F : Type) [Field F] [DecidableEq F] (δ Δ : ℕ) (α ε : ℝ) (d : ℕ) (κ : ℝ) :
    Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = d →
  ∀ (P : ι → Type) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F),
    (∀ i, IsExpanderMatrix (H i) δ Δ α ε) → 2 ≤ α * n →
  ∀ E N : Set (ι → Fin n), IsClosedSet κ E → E ≠ Set.univ → IsClosedSet κ N → N ≠ Set.univ →
  ∀ a c e : (ι → Fin n) → F, SynCond H E a → a = c + e →
    c ∈ boxplus (fun i => kerCode (H i)) → SupportedIn e N →
      e ∈ lineSpan (fun i => kerCode (H i)) N ⊔ supported F (canonicalSet H δ ε E)

/-- **Step 2** of the proof of `D(d)`: for `b ∉ Bad_I` the defect `D_{I,b}` is proper.
(`D_{I,b} = E_{I,b} ∪ ⋃_{j ∉ I} Q_j`; `E_{I,b}` is proper since `Y_I(E) ⊆ Bad_I`, `Q_j` is proper
by (I2) and (L); then (F2) in the face cube, using `d' η_b ≤ 1`.) -/
def Step2Statement : Prop :=
  ∀ {F : Type} [Field F] [DecidableEq F] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F) (δ : ℕ) (η' κ ηb : ℝ) (d' : ℕ)
    (E N : Set (ι → Fin n)),
    0 < n → 1 ≤ d' → d' < Fintype.card ι →
    0 ≤ η' → 0 ≤ κ → IsClosedSet η' E → IsClosedSet κ N → LevelInv2 H δ E N d' →
    η' + ((Fintype.card ι - d' : ℕ) : ℝ) * κ ≤ ηb → (d' : ℝ) * ηb ≤ 1 →
    FaceDefectsProper H δ E N d'

/-- **Step 3** of the proof of `D(d)` (1D route along a good line, by contradiction on `T_ℓ`,
using the unique good check, the route equation `SynCond.route`, the face-syndrome lemma
`SynCond.faceSyn` and `D(d')` in the face cube). -/
def Step3Statement : Prop :=
  ∀ {F : Type} [Field F] [DecidableEq F] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F) (δ Δ : ℕ) (α ε η κD η' κ ηb : ℝ) (d' : ℕ)
    (E N : Set (ι → Fin n)) (a : (ι → Fin n) → F),
    (∀ i, IsExpanderMatrix (H i) δ Δ α ε) → 0 < δ → 0 ≤ ε → ε ≤ 1 / 16 → 2 ≤ α * n → α ≤ 1 →
    1 ≤ d' → d' < Fintype.card ι →
    DecodeStatement F δ Δ α ε d' κD → HypGen H η → η ≤ 1 →
    0 ≤ η' → 0 ≤ κ → IsClosedSet η' E → E ≠ Set.univ → IsClosedSet κ N →
    LevelInv2 H δ E N d' → FaceDefectsProper H δ E N d' →
    SynCond H E a → SupportedIn a N →
    2 * (Δ : ℝ) * max κ η' ≤ η → κ ≤ α →
    η' + ((Fintype.card ι - d' : ℕ) : ℝ) * κ ≤ ηb →
    canC' (1 / 4 - ε) d' * ηb ≤ (1 / 4 - ε) * α / 2 → canC (1 / 4 - ε) d' * ηb < 1 →
    (d' : ℝ) * (2 * Δ * (canC (1 / 4 - ε) d' * ηb)) ≤ 1 →
    ηb ≤ κD → 2 * (Δ : ℝ) * (canC (1 / 4 - ε) d' * ηb) ≤ κD →
    GoodFacesDecoded H δ ε E N a d'

/-- **Step 4** of the proof of `D(d)` (subtraction of the decoded faces of level `d'`):
produces the set `N^{(d')} ⊆ N` and the word `e^{(d')}` with invariants (I1), (I2) of the next
level. Here `N0`, `e0` are the original `N`, `e` of lemma `D` and `a = e^{(d'+1)}`. -/
def Step4Statement : Prop :=
  ∀ {F : Type} [Field F] [DecidableEq F] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F) (δ Δ : ℕ) (α ε η' κ ηb : ℝ) (d' : ℕ)
    (E N0 N : Set (ι → Fin n)) (e0 a : (ι → Fin n) → F),
    (∀ i, IsExpanderMatrix (H i) δ Δ α ε) → 0 < δ → 0 ≤ ε → ε ≤ 1 / 16 → 2 ≤ α * n → α ≤ 1 →
    1 ≤ d' → d' < Fintype.card ι →
    0 ≤ η' → 0 ≤ κ → IsClosedSet η' E → E ≠ Set.univ → IsClosedSet κ N →
    LevelInv2 H δ E N d' → FaceDefectsProper H δ E N d' →
    N ⊆ N0 → SupportedIn a N → e0 - a ∈ lineSpan (fun i => kerCode (H i)) N0 →
    GoodFacesDecoded H δ ε E N a d' →
    η' + ((Fintype.card ι - d' : ℕ) : ℝ) * κ ≤ ηb →
    canC' (1 / 4 - ε) d' * ηb ≤ (1 / 4 - ε) * α / 2 → canC (1 / 4 - ε) d' * ηb < 1 →
    ∃ (N' : Set (ι → Fin n)) (a' : (ι → Fin n) → F),
      N' ⊆ N ∧ IsClosedSet (max κ (canC (1 / 4 - ε) d' * ηb)) N' ∧ SupportedIn a' N' ∧
        e0 - a' ∈ lineSpan (fun i => kerCode (H i)) N0 ∧ LevelInv2 H δ E N' (d' - 1)

/-- **Step 5** of the proof of `D(d)` (canonization): after the last level, the remaining word
`g` is supported in the canonical set `\hat E`. (`Q = Can(E) ∪ N` is
`(c'_d η' + κ)`-closed with the same full lines as `Can(E)`; then
`SynCond.exists_of_lineSyndrome_ne_zero` and lemma `gen-find` (b) on every line.) -/
def Step5Statement : Prop :=
  ∀ {F : Type} [Field F] [DecidableEq F] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {P : ι → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F) (δ Δ : ℕ) (α ε η η' κ : ℝ)
    (E N : Set (ι → Fin n)) (g : (ι → Fin n) → F),
    (∀ i, IsExpanderMatrix (H i) δ Δ α ε) → 0 < δ → 0 ≤ ε → ε ≤ 1 / 16 → 2 ≤ α * n → α ≤ 1 →
    HypGen H η → η ≤ 1 →
    0 ≤ η' → 0 ≤ κ → IsClosedSet η' E → E ≠ Set.univ → IsClosedSet κ N →
    LevelInv2 H δ E N 0 → SynCond H E g → SupportedIn g N →
    canC' (1 / 4 - ε) (Fintype.card ι) * η' ≤ (1 / 4 - ε) * α / 2 →
    canC (1 / 4 - ε) (Fintype.card ι) * η' < 1 →
    2 * (Δ : ℝ) * max (canC' (1 / 4 - ε) (Fintype.card ι) * η' + κ) η' ≤ η →
    canC' (1 / 4 - ε) (Fintype.card ι) * η' + κ ≤ α →
    SupportedIn g (canonicalSet H δ ε E)

end ProductExpansion
