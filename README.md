# Product expansion of LDPC codes: Lean 4 formalization

[![Lean Action CI](https://github.com/KalachevGleb/ldpc-prodexp-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/KalachevGleb/ldpc-prodexp-lean/actions/workflows/lean_action_ci.yml)

**English** | [Русский](README.ru.md)

This repository contains a complete formal proof, in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4), of the main theorem of

> G. V. Kalachev. *Product expansion of LDPC codes* (Расширение произведения LDPC кодов).
> Intelligent Systems. Theory and Applications, to appear. In Russian.

The theorem says that the product expansion of any fixed number of LDPC codes whose Tanner graphs
are lossless vertex expanders is bounded below by a positive constant.

## The theorem

Let `C₁, …, C_m ⊆ F^n` be linear codes. For `i ∈ [m]`, the code `C^{(i)}` consists of the words
`x : [n]^m → F` all of whose lines in direction `i` are codewords of `Cᵢ`, and
`C₁ ⊞ ⋯ ⊞ C_m := C^{(1)} + ⋯ + C^{(m)}`. For such a word, `|x|` is its Hamming weight and `|x|ᵢ` is the
number of lines in direction `i` on which `x` is nonzero. The *product expansion* is

```text
ρ(C₁, …, C_m) := min over x ∈ C₁ ⊞ ⋯ ⊞ C_m, x ≠ 0, of  |x| / (n · min Σᵢ |aᵢ|ᵢ),
```

where the inner minimum is over all decompositions `x = Σᵢ aᵢ` with `aᵢ ∈ C^{(i)}`.

A bipartite graph with left degrees `δ` is an `(α, ε)`-expander if every set `S` of left vertices
with `|S| ≤ α·|L|` has at least `(1 − ε)·δ·|S|` neighbours. `ExpLDPC(δ, α, ε)` is the class of codes
`C = ker H`, where `H` is the adjacency matrix of a biregular `(α, ε)`-expander with left degree `δ`
(the left vertices are the columns of `H`, i.e. the positions of the code).

**Theorem 1.** For all `m, δ ≥ 1`, `R₁, …, R_m ∈ (0, 1)`, `α > 0` and `ε ∈ [0, 1/16]` there is `ρ₀ > 0`,
depending only on `m`, `α` and `Δ := ⌊δ / (1 − maxᵢ Rᵢ)⌋`, such that `ρ(C₁, …, C_m) ≥ ρ₀` for every
length `n` and all codes `Cᵢ ∈ ExpLDPC(δ, α, ε)` of length `n` and rate at most `Rᵢ`.

In Lean ([`ProductExpansion/Paper.lean`](ProductExpansion/Paper.lean),
[`ProductExpansion/Main.lean`](ProductExpansion/Main.lean)):

```lean
def PaperTheoremStatement : Prop :=
  ∃ ρ : ℕ → ℕ → ℝ → ℝ, (∀ m Δ α, 0 < α → 0 < ρ m Δ α) ∧
    ∀ (F : Type) [Field F] [DecidableEq F] (m δ : ℕ) (R : Fin m → ℝ) (Rmax α ε : ℝ),
      0 < δ → (∀ i, R i ≤ Rmax) → Rmax < 1 → 0 < α → 0 ≤ ε → ε ≤ 1 / 16 →
      ∀ (n : ℕ) (C : Fin m → Submodule F (Fin n → F)),
        (∀ i, InELDPC (C i) δ α ε) → (∀ i, (Module.finrank F (C i) : ℝ) ≤ R i * n) →
        prodExpanding C (ρ m ⌊(δ : ℝ) / (1 - Rmax)⌋₊ α)

theorem paperTheorem : PaperTheoremStatement
```

The single function `ρ m Δ α` expresses that the constant depends only on `m`, `Δ` and `α`: it
does not depend on the field, the length `n`, the left degree `δ` or `ε`. The formal statement is
slightly more general than the text: the field `F` is arbitrary (finite or not), only the support
of `H` matters (its nonzero entries are arbitrary), and `Rmax` is any common upper bound for the
rates.

The theorem is derived from a form with a bound on the right degrees instead of the rates, in which
the graphs need not be regular on the right
([`ProductExpansion/MainLemma.lean`](ProductExpansion/MainLemma.lean)):

```lean
def MainTheoremUniformStatement : Prop :=
  ∀ (m Δ : ℕ) (α : ℝ), 0 < α → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (F : Type) [Field F] [DecidableEq F] (δ : ℕ) (ε : ℝ), 0 < δ → 0 ≤ ε → ε ≤ 1 / 16 →
    ∀ (n : ℕ) (P : Fin m → Type) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
      (H : ∀ i, Matrix (P i) (Fin n) F), (∀ i, IsExpanderMatrix (H i) δ Δ α ε) →
      prodExpanding (fun i => kerCode (H i)) ρ₀

theorem mainTheoremUniform : MainTheoremUniformStatement
```

## What has to be checked by a reader

Lean checks the proofs. To trust the result, it suffices to check that the definitions used in the
statements mean what the paper says. They take about 200 lines:
[`Basic.lean`](ProductExpansion/Basic.lean), the definitions `IsBiregular`, `InELDPC` and
`PaperTheoremStatement` in [`Paper.lean`](ProductExpansion/Paper.lean), and
`MainTheoremUniformStatement` in [`MainLemma.lean`](ProductExpansion/MainLemma.lean).

| Paper | Lean |
| --- | --- |
| field `F_q` | any field `F` |
| word on the cube `[n]^m` | `(ι → Fin n) → F`, in the theorem `ι = Fin m` |
| line of direction `i` through `y`, restriction `x\|_ℓ` | `line i y`, `restrictLine x i y` |
| `C^{(i)}` | `colCode C i` |
| `C₁ ⊞ ⋯ ⊞ C_m` | `boxplus C` |
| `\|x\|`, `\|x\|ᵢ` | `weight x`, `lineWeight x i _` |
| `ρ(C₁, …, C_m) ≥ ρ₀` | `prodExpanding C ρ₀` |
| neighbourhood `N(S)` in the Tanner graph of `H` | `nbhd H S` |
| `ker H` | `kerCode H` |
| `(α, ε)`-expander, left degree `δ`, right degrees `≤ Δ` | `IsExpanderMatrix H δ Δ α ε` |
| `C ∈ ExpLDPC(δ, α, ε)` | `InELDPC C δ α ε` |
| rate of `C` at most `R` | `Module.finrank F C ≤ R * n` |

`prodExpanding C ρ₀` states that every `x ∈ C₁ ⊞ ⋯ ⊞ C_m` has a decomposition `x = Σᵢ aᵢ`,
`aᵢ ∈ C^{(i)}`, with `ρ₀ · n · Σᵢ |aᵢ|ᵢ ≤ |x|`; this is equivalent to `ρ(C₁, …, C_m) ≥ ρ₀`.

The file [`Verify.lean`](Verify.lean) checks that the theorems use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`; in particular, there is no `sorry`.

## Building

Install Lean with [elan](https://github.com/leanprover/elan) (the version is fixed by
`lean-toolchain`: Lean 4.34.1, Mathlib v4.34.1), then

```sh
git clone https://github.com/KalachevGleb/ldpc-prodexp-lean.git
cd ldpc-prodexp-lean
lake exe cache get        # precompiled Mathlib
lake build                # checks all proofs
lake env lean Verify.lean # axiom check; prints nothing on success
```

With the Mathlib cache downloaded, `lake build` takes about 3 minutes.

The same steps run in GitHub Actions on every push
([`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)).

## Structure of the proof

| Module | Content |
| --- | --- |
| `Basic` | Cube, lines, `C^{(i)}`, `⊞`, weights, product expansion, expander matrices. |
| `Expander` | Unique neighbours, distance `> αn`, greedy closure `F_θ` (lemmas `gen-unique`, `gen-find`). |
| `Cube`, `CubeLemmas` | Faces, bases `B_I`, sets `Y_I`, closed sets and their properties (F1)–(F3), `L(M)`. |
| `Closure`, `Reduction` | Small closed supersets (`gen-closure`), reduction of product expansion to `P(m)` (`gen-reduction`), the case `αn < 2`. |
| `Syndrome`, `FaceSyn` | Syndrome condition `S(E)` (`def:syn`), face-syndrome lemma (`face-syn`). |
| `Canonical` | Canonical error sets (`def:can`), lemma `CL`, good lines (`good`). |
| `MainInterface`, `Step2` … `Step5` | Statements and proofs of steps 2–5 of lemma `D(d)`. |
| `MainLemma` | Constants `κ_d`, lemma `D(d)` by induction, corollary `P(d)`, theorem 1 for collections of expander matrices. |
| `Paper`, `Main` | Right degrees from the rates; the final theorems. |

Comments in the code refer to the statements of the proof by short labels:

| Label | Statement |
| --- | --- |
| `gen-unique` | If `\|S\| ≤ αn`, then `S` has at least `(1 − 2ε)δ\|S\|` unique neighbours; the distance of `ker H` exceeds `αn`. |
| `gen-find` | Bounds for the greedy closure `F_θ(R)`: its size, and `supp e ⊆ F_h(R)` if `supp(He) ⊆ R`, `h = (1 − 2ε)δ`. |
| `gen-closure` | The smallest `η`-closed superset of `S ⊆ [n]^m` has size at most `((2^m + 1)/η)^m \|S\|` (Kalachev–Panteleev, FOCS 2025, lemma 18). |
| `gen-reduction` | If `P(m)` holds with threshold `η`, then `ρ(C₁, …, C_m) ≥ 1/(m·c_{m,η})`. |
| `P(d)` | Every proper `η`-closed set `M ⊆ [n]^d`, `η ≤ η_d`, is generated from inside: every word of `C₁ ⊞ ⋯ ⊞ C_d` supported in `M` is a sum of codewords on lines contained in `M`. |
| `def:syn` | Syndrome condition `S_d(E)` with defect `E`. |
| `face-syn` | The restriction of a word satisfying `S_d(E)` to a face satisfies the syndrome condition with an explicit defect. |
| `def:can` | Canonical error sets `Bad_J`, `Can(Y)`, `Ŷ`. |
| `CL` | Closedness and consistency of the canonical sets. |
| `good` | Existence and properties (G1)–(G4) of a good line. |
| `D(d)` | Decoding with a defect, the main lemma; proved by induction on `d` in steps 1–5. |

Without loss of generality the proof assumes `α ≤ 1` and `ε = 1/16`, since the expansion property
is monotone in these parameters.

## Use of AI tools

The formalization of the proof in Lean 4 was carried out with the help of the Claude Opus 5.5
model (Anthropic) in Claude Code.

## Citation and license

If you use this code, please cite the paper above (see also [`CITATION.cff`](CITATION.cff)).
The code is distributed under the Apache License 2.0 ([`LICENSE`](LICENSE)), the same license as
Mathlib.
