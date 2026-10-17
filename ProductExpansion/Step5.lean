import ProductExpansion.MainInterface

/-!
# Step 5 of the proof of the main lemma `D(d)`

See `MainInterface.lean` (`Step5Statement`) and the proof of lemma `lem:D`.

Notation: `Can = canSet H (δ/4) E`, `\hat E = canonicalSet H δ ε E = hatSet H (δ/4) E ((1-2ε)δ)`.

* `glue_singleton_outer`: the point of the `{j}`-face over `outer {j} y` is a point of the
  `j`-line through `y`;
* `update_mem_canSet_of_full_line` (part A of step 5): under (I2) at level `0` every full line
  of `N` lies in `Can` (it stands over `Bad_{{j}}`);
* `step5`: every point `y ∉ Can` of `supp g` lies in `Ψ^h_ℓ(Can, E)` for all lines `ℓ ∋ y`
  (`SynCond.exists_of_lineSyndrome_ne_zero` and lemma `gen-find` (b) on the line), hence in
  `\hat E`.

The auxiliary lemmas are `private` (the modules `Step2` … `Step5` are imported together by
`MainLemma`, so this avoids name clashes).

Remark: the auxiliary set `Q = Can ∪ N` is not needed here: the line-syndrome lemma
`SynCond.exists_of_lineSyndrome_ne_zero` is applied to `N` itself (it is `κ`-closed and
`2Δ max(κ, η') ≤ 2Δ max(κ_Q, η') ≤ η`), and its transversal full lines of `N` lie in `Can`
by part A. The bound `|supp g|_ℓ| ≤ |ℓ ∩ N| < κ n ≤ α n` uses `κ ≤ κ_Q ≤ α`.
-/

open Finset

namespace ProductExpansion

section Step5Aux

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

omit [Fintype ι] in
/-- The point of the `{j}`-face in position `outer {j} y` with inner coordinate `z` is the point
of the `j`-line through `y` with `j`-th coordinate `z j`. -/
private lemma glue_singleton_outer (j : ι) (z : {i // i ∈ ({j} : Finset ι)} → Fin n)
    (y : ι → Fin n) :
    glue {j} z (outer {j} y) = Function.update y j (z ⟨j, Finset.mem_singleton_self j⟩) := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [glue_apply_of_mem _ _ _ (Finset.mem_singleton_self k), Function.update_self]
  · have hk' : k ∉ ({j} : Finset ι) := by simpa using hk
    rw [glue_apply_of_not_mem _ _ _ hk', Function.update_of_ne hk]
    rfl

/-- **Step 5, part A.** Under the invariant (I2) at level `0`, every full line of `N` stands over
`Bad_{{j}}` and therefore lies in `Can(E)`. -/
private lemma update_mem_canSet_of_full_line {H : ∀ i, Matrix (P i) (Fin n) F} {δ : ℕ}
    {E N : Set (ι → Fin n)} (hI2 : LevelInv2 H δ E N 0) {j : ι} {y : ι → Fin n}
    (hfull : ∀ t, Function.update y j t ∈ N) (t : Fin n) :
    Function.update y j t ∈ canSet H ((1 / 4 : ℝ) * δ) E := by
  have hpos : outer {j} y ∈ posFull N {j} := by
    intro z
    rw [glue_singleton_outer]
    exact hfull _
  have hbad : outer {j} y ∈ badSet H ((1 / 4 : ℝ) * δ) E {j} :=
    hI2 {j} (by simp) hpos
  apply outer_preimage_badSet_subset_canSet (Finset.singleton_nonempty j)
  rw [Set.mem_preimage, outer_update_of_mem {j} y (Finset.mem_singleton_self j) t]
  exact hbad

end Step5Aux

theorem step5 : Step5Statement := by
  intro F _ _ n ι _ _ _ P _ _ H δ Δ α ε η η' κ E N g hH hδ hε0 hε hαn hα1 hgen hη1 hη' hκ hE
    hEne hN hI2 hg hgN hc' hc hpar hκQ
  have hγ : (0 : ℝ) < 1 / 4 - ε := by linarith
  have hc'1 : 1 ≤ canC' (1 / 4 - ε) (Fintype.card ι) := one_le_canC' hγ _
  have hcη : 0 ≤ canC' (1 / 4 - ε) (Fintype.card ι) * η' := mul_nonneg (by linarith) hη'
  have hκα : κ ≤ α := by linarith
  have hpar' : 2 * (Δ : ℝ) * max κ η' ≤ η := by
    refine le_trans ?_ hpar
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact max_le_max (by linarith) le_rfl
  intro y hy
  unfold canonicalSet
  by_cases hyC : y ∈ canSet H ((1 / 4 : ℝ) * δ) E
  · exact canSet_subset_hatSet _ hyC
  rw [mem_hatSet]
  refine Or.inr ⟨hyC, fun i => ?_⟩
  -- the `i`-line through `y` is not full in `N` (otherwise it lies in `Can` by part A)
  have hnotfull : ¬ ∀ t, Function.update y i t ∈ N := by
    intro hfull
    apply hyC
    have := update_mem_canSet_of_full_line hI2 hfull (y i)
    rwa [Function.update_eq_self] at this
  have hlt := hN.lineCount_lt hnotfull
  -- `|supp g|_ℓ| ≤ |ℓ ∩ N| < κ n ≤ α n`
  have hsupp_sub : (Finset.univ.filter fun u => restrictLine g i y u ≠ 0) ⊆ linePts N i y := by
    intro t ht
    rw [mem_linePts]
    rw [Finset.mem_filter] at ht
    exact hgN _ ht.2
  have hcard : ((Finset.univ.filter fun u => restrictLine g i y u ≠ 0).card : ℝ) ≤ α * n := by
    have h1 : ((Finset.univ.filter fun u => restrictLine g i y u ≠ 0).card : ℝ) ≤
        (linePts N i y).card := by
      exact_mod_cast Finset.card_le_card hsupp_sub
    rw [← lineCount_eq_card_linePts] at h1
    have h2 : κ * n ≤ α * n := mul_le_mul_of_nonneg_right hκα (Nat.cast_nonneg n)
    linarith
  -- `supp (H_i g|_ℓ) ⊆ N_i(Cr_Can(ℓ) ∪ (E ∩ ℓ))`
  have hR : (Finset.univ.filter fun p => (H i).mulVec (restrictLine g i y) p ≠ 0) ⊆
      nbhd (H i) (crossSet (canSet H ((1 / 4 : ℝ) * δ) E) i y ∪ linePts E i y) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨u, hu, hE' | ⟨j, hji, hfull⟩⟩ :=
      hg.exists_of_lineSyndrome_ne_zero (hgen i) hgN hN hE p ((hH i).rightDeg p) hpar' hη1 hp.2
    · exact (mem_nbhd (H i)).2 ⟨u, Finset.mem_union_right _ (mem_linePts.2 hE'), hu⟩
    · refine (mem_nbhd (H i)).2 ⟨u, Finset.mem_union_left _ (mem_crossSet.2 ⟨j, hji, ?_⟩), hu⟩
      exact update_mem_canSet_of_full_line hI2 hfull
  -- lemma `gen-find` (b) on the line
  have key := (hH i).supp_subset_findClosure hcard hR
  have hyi : y i ∈ Finset.univ.filter fun u => restrictLine g i y u ≠ 0 := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [restrictLine, Function.update_eq_self]
    exact hy
  exact key hyi

end ProductExpansion
