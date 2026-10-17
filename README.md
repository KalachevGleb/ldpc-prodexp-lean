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

Let $`\mathcal C_1,\dots,\mathcal C_m\subseteq\mathbb F_q^n`$ be linear codes. For $`i\in[m]`$, the code
$`\mathcal C^{(i)}`$ consists of the words $`x\colon[n]^m\to\mathbb F_q`$ all of whose lines in direction
$`i`$ are codewords of $`\mathcal C_i`$, and
$`\mathcal C_1\boxplus\dots\boxplus\mathcal C_m:=\mathcal C^{(1)}+\dots+\mathcal C^{(m)}`$. For such a word,
$`|x|`$ is its Hamming weight and $`|x|_i`$ is the number of lines in direction $`i`$
on which $`x`$ is nonzero. The *product expansion* is

```math
\rho(\mathcal C_1,\dots,\mathcal C_m):=\frac1n\min_{x\in\mathcal C_1\boxplus\dots\boxplus\mathcal C_m\setminus\{0\}}
\frac{|x|}{|x|_{\boxplus}},\qquad
|x|_{\boxplus}:=\min\Bigl\{\sum_i|a_i|_i\Bigm| x=\sum_i a_i,\ a_i\in\mathcal C^{(i)}\Bigr\}.
```

A bipartite graph with left degrees $`\delta`$ is an $`(\alpha,\varepsilon)`$-expander if every set $`S`$ of
left vertices with $`|S|\le\alpha|L|`$ has at least $`(1-\varepsilon)\delta|S|`$
neighbours. $`\mathsf{ExpLDPC}(\delta,\alpha,\varepsilon)`$ is the class of codes $`\mathcal C=\ker H`$, where
$`H`$ is the adjacency matrix of a biregular $`(\alpha,\varepsilon)`$-expander with left degree $`\delta`$
(the left vertices are the columns of $`H`$, i.e. the positions of the code).

**Theorem 1.** For all $`m,\delta\ge1`$, $`R_1,\dots,R_m\in(0,1)`$, $`\alpha>0`$ and $`\varepsilon\in[0,1/16]`$
there is $`\rho_0>0`$, depending only on $`m`$, $`\alpha`$ and $`\Delta:=\lfloor\delta/(1-\max_iR_i)\rfloor`$,
such that $`\rho(\mathcal C_1,\dots,\mathcal C_m)\ge\rho_0`$ for every length $`n`$ and all codes
$`\mathcal C_i\in\mathsf{ExpLDPC}(\delta,\alpha,\varepsilon)`$ of length $`n`$ and rate at most $`R_i`$.

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

The single function `ρ m Δ α` expresses that the constant depends only on $`m`$, $`\Delta`$ and
$`\alpha`$: it does not depend on the field, the length $`n`$, the left degree $`\delta`$ or $`\varepsilon`$.
The formal statement is slightly more general than the text: the field `F` is arbitrary (finite or
not), only the support of $`H`$ matters (its nonzero entries are arbitrary), and `Rmax` is any common
upper bound for the rates.

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
| field $`\mathbb F_q`$ | any field `F` |
| word on the cube $`[n]^m`$ | `(ι → Fin n) → F`, in the theorem `ι = Fin m` |
| line of direction $`i`$ through $`y`$, restriction $`x\|_\ell`$ | `line i y`, `restrictLine x i y` |
| $`\mathcal C^{(i)}`$ | `colCode C i` |
| $`\mathcal C_1\boxplus\dots\boxplus\mathcal C_m`$ | `boxplus C` |
| $`\|x\|`$, $`\|x\|_i`$ | `weight x`, `lineWeight x i _` |
| $`\rho(\mathcal C_1,\dots,\mathcal C_m)\ge\rho_0`$ | `prodExpanding C ρ₀` |
| neighbourhood $`N(S)`$ in the Tanner graph of $`H`$ | `nbhd H S` |
| $`\ker H`$ | `kerCode H` |
| $`(\alpha,\varepsilon)`$-expander, left degree $`\delta`$, right degrees $`\le\Delta`$ | `IsExpanderMatrix H δ Δ α ε` |
| $`\mathcal C\in\mathsf{ExpLDPC}(\delta,\alpha,\varepsilon)`$ | `InELDPC C δ α ε` |
| rate of $`\mathcal C`$ at most $`R`$ | `Module.finrank F C ≤ R * n` |

`prodExpanding C ρ₀` states that every $`x\in\mathcal C_1\boxplus\dots\boxplus\mathcal C_m`$ has a
decomposition $`x=\sum_i a_i`$, $`a_i\in\mathcal C^{(i)}`$, with $`\rho_0\,n\sum_i|a_i|_i\le|x|`$;
this is equivalent to $`\rho(\mathcal C_1,\dots,\mathcal C_m)\ge\rho_0`$.

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
| `Basic` | Cube, lines, $`\mathcal C^{(i)}`$, $`\boxplus`$, weights, product expansion, expander matrices. |
| `Expander` | Unique neighbours, distance $`>\alpha n`$, greedy closure $`F_\theta`$ (lemmas `gen-unique`, `gen-find`). |
| `Cube`, `CubeLemmas` | Faces, bases $`B_I`$, sets $`Y_I`$, closed sets and their properties (F1)–(F3), $`L(M)`$. |
| `Closure`, `Reduction` | Small closed supersets (`gen-closure`), reduction of product expansion to $`\mathrm P(m)`$ (`gen-reduction`), the case $`\alpha n<2`$. |
| `Syndrome`, `FaceSyn` | Syndrome condition $`\mathrm S(E)`$ (`def:syn`), face-syndrome lemma (`face-syn`). |
| `Canonical` | Canonical error sets (`def:can`), lemma `CL`, good lines (`good`). |
| `MainInterface`, `Step2` … `Step5` | Statements and proofs of steps 2–5 of lemma $`\mathrm D(d)`$. |
| `MainLemma` | Constants $`\kappa_d`$, lemma $`\mathrm D(d)`$ by induction, corollary $`\mathrm P(d)`$, theorem 1 for collections of expander matrices. |
| `Paper`, `Main` | Right degrees from the rates; the final theorems. |

Comments in the code refer to the statements of the proof by short labels:

| Label | Statement |
| --- | --- |
| `gen-unique` | If $`\|S\|\le\alpha n`$, then $`S`$ has at least $`(1-2\varepsilon)\delta\|S\|`$ unique neighbours; the distance of $`\ker H`$ exceeds $`\alpha n`$. |
| `gen-find` | Bounds for the greedy closure $`F_\theta(R)`$: its size, and $`\mathrm{supp}\,e\subseteq F_h(R)`$ if $`\mathrm{supp}(He)\subseteq R`$, $`h=(1-2\varepsilon)\delta`$. |
| `gen-closure` | The smallest $`\eta`$-closed superset of $`S\subseteq[n]^m`$ has size at most $`((2^m+1)/\eta)^m\|S\|`$ (Kalachev–Panteleev, FOCS 2025, lemma 18). |
| `gen-reduction` | If $`\mathrm P(m)`$ holds with threshold $`\eta`$, then $`\rho(\mathcal C_1,\dots,\mathcal C_m)\ge1/(m\,c_{m,\eta})`$. |
| `P(d)` | Every proper $`\eta`$-closed set $`M\subseteq[n]^d`$, $`\eta\le\eta_d`$, is generated from inside: every word of $`\mathcal C_1\boxplus\dots\boxplus\mathcal C_d`$ supported in $`M`$ is a sum of codewords on lines contained in $`M`$. |
| `def:syn` | Syndrome condition $`\mathrm S_d(E)`$ with defect $`E`$. |
| `face-syn` | The restriction of a word satisfying $`\mathrm S_d(E)`$ to a face satisfies the syndrome condition with an explicit defect. |
| `def:can` | Canonical error sets $`\mathrm{Bad}_J`$, $`\mathrm{Can}(Y)`$, $`\widehat Y`$. |
| `CL` | Closedness and consistency of the canonical sets. |
| `good` | Existence and properties (G1)–(G4) of a good line. |
| `D(d)` | Decoding with a defect, the main lemma; proved by induction on $`d`$ in steps 1–5. |

Without loss of generality the proof assumes $`\alpha\le1`$ and $`\varepsilon=1/16`$, since the expansion
property is monotone in these parameters.

## Use of AI tools

The formalization of the proof in Lean 4 was carried out with the help of the Claude Opus 5.5
model (Anthropic) in Claude Code.

## Citation and license

If you use this code, please cite the paper above (see also [`CITATION.cff`](CITATION.cff)).
The code is distributed under the Apache License 2.0 ([`LICENSE`](LICENSE)), the same license as
Mathlib.
