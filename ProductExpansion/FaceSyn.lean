import ProductExpansion.Syndrome

/-!
# The face-syndrome lemma (`lem:face-syn`)

Part "Syndrome condition and face syndrome" of the proof.

Throughout, `P(d-1)` is used only on the hyperplane cubes `{j // j ≠ i} → Fin n` and only for
*proper* closed sets (hypothesis `hgen`); the case `U = V^{d-1}` is covered by
`generatedFromInside_univ` (every word of `⊞ C` is a sum of line codewords).

* `mem_lineSpan_of_mem_colCode`, `boxplus_le_lineSpan_univ`, `generatedFromInside_univ`,
  `generatedFromInside_of_ne_univ`: the trivial case `M = V^d` of `P(d)`.
* `faceDefect N E I b` is the defect `D_{I,b}` of the lemma: points `z` of the `I`-face in position
  `b` with `(z,b) ∈ E` or with `(z,b)` on a full line of `N` of a direction `j ∉ I`;
  `IsClosedSet.faceDefect_closed`: it is `(η' + (d - |I|) κ)`-closed.
* Core (one direction `i`, one check `p`, `U = N^{(p)} ∪ E^{(p)}`):
  `isClosedSet_synDefect_union_of_ne_univ` (`U` is `η`-closed when proper, (F1)),
  `exists_slice_of_full_line_synDefect_union` (Dirichlet: a full line of `U` lies in one slice),
  `SynCond.checkSum_mem_lineSpan_sup` (`σ = w + f`, `w ∈ L(U)`, `supp f ⊆ E^{(p)}`),
  `SynCond.checkSum_comp_mem_sup` (restriction of `σ` to any subcube of the hyperplane).
* **Face-syndrome lemma** `SynCond.faceSyn`: `a_{I,b}` satisfies `S_{|I|}(D_{I,b})`
  (for every `I`, no fullness of the face needed).
* For the main induction: `SynCond.route` (the check sum in a direction `j ∉ I` of the faces
  `Φ_I(β,t)`, equation `eq:route` of step 3 of lemma D), `SynCond.exists_of_checkSum_ne_zero` and
  `SynCond.exists_of_lineSyndrome_ne_zero` (pointwise form, step 5 of lemma D: the syndrome of a
  line is concentrated at its points lying in `E` or on transversal full lines of `N`).
* The hypothesis `hgen` of `SynCond.faceSyn` is literally `HypGen H η` of `MainInterface.lean`
  (`P(d-1)` on the hyperplane cubes, proper closed sets only).
* `GenProp cls η d` is a packaging of `P(d)` (for all index types of cardinality `d` and all
  families of check matrices of a class `cls`, proper closed sets only); `GenProp.hyperplane`
  turns `GenProp cls η (|ι| - 1)` into `hgen`; `SynCond.faceSyn_of_genProp`,
  `SynCond.faceSyn_of_expander` are the face-syndrome lemma in this form.
-/

open Finset Function Matrix

namespace ProductExpansion

universe u v

variable {F : Type*} [Field F] {n : ℕ}

/-! ### The trivial case `M = V^d` of `P(d)` -/

section Univ

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {C : ι → Submodule F (Fin n → F)}

/-- A word of `C^{(i)}` whose nonzero points lie on lines of direction `i` contained in `M` belongs
to `L(M)`: it is the sum of its restrictions to the lines of direction `i`. -/
lemma mem_lineSpan_of_mem_colCode {M : Set (ι → Fin n)} {i : ι} {a : (ι → Fin n) → F}
    (ha : a ∈ colCode C i) (hM : ∀ y, a y ≠ 0 → ∀ t, Function.update y i t ∈ M) :
    a ∈ lineSpan C M := by
  classical
  have hdecomp : a = ∑ z : {j // j ≠ i} → Fin n,
      (fun y : ι → Fin n => if hproj i y = z then a y else 0) := by
    funext y
    rw [Finset.sum_apply]
    simp
  rw [hdecomp]
  refine Submodule.sum_mem _ fun z _ => ?_
  by_cases hz : ∃ y, hproj i y = z ∧ a y ≠ 0
  · obtain ⟨y, rfl, hy⟩ := hz
    refine IsLineCodeword.mem_lineSpan ⟨?_, ?_⟩ (hM y hy)
    · intro y' hy'
      have h1 : hproj i y' = hproj i y := by
        by_contra h
        exact hy' (by simp [h])
      exact ⟨y' i, by rw [← hglue_hproj_eq_update, ← h1, hglue_hproj]⟩
    · have : restrictLine (fun y' : ι → Fin n => if hproj i y' = hproj i y then a y' else 0) i y =
          restrictLine a i y := by
        funext t
        simp [restrictLine]
      rw [this]
      exact ha y
  · push Not at hz
    have : (fun y : ι → Fin n => if hproj i y = z then a y else 0) = 0 := by
      funext y
      split_ifs with h
      · exact hz y h
      · rfl
    rw [this]
    exact Submodule.zero_mem _

lemma colCode_le_lineSpan_univ (C : ι → Submodule F (Fin n → F)) (i : ι) :
    colCode C i ≤ lineSpan C Set.univ :=
  fun _ ha => mem_lineSpan_of_mem_colCode ha fun _ _ _ => trivial

/-- `⊞ C ⊆ L(V^d)`. -/
lemma boxplus_le_lineSpan_univ (C : ι → Submodule F (Fin n → F)) :
    boxplus C ≤ lineSpan C Set.univ :=
  iSup_le fun i => colCode_le_lineSpan_univ C i

/-- The whole cube is generated from inside (the trivial case of `P(d)`). -/
lemma generatedFromInside_univ (C : ι → Submodule F (Fin n → F)) :
    GeneratedFromInside C Set.univ :=
  fun _ ha => boxplus_le_lineSpan_univ C (Submodule.mem_inf.1 ha).1

/-- `P(d)` for proper closed sets implies `P(d)` for all closed sets. -/
lemma generatedFromInside_of_ne_univ {η : ℝ}
    (h : ∀ M : Set (ι → Fin n), IsClosedSet η M → M ≠ Set.univ → GeneratedFromInside C M)
    (M : Set (ι → Fin n)) (hM : IsClosedSet η M) : GeneratedFromInside C M := by
  by_cases hU : M = Set.univ
  · rw [hU]; exact generatedFromInside_univ C
  · exact h M hM hU

end Univ

/-! ### The defect `D_{I,b}` -/

section FaceDefect

variable {ι : Type*} [DecidableEq ι]

/-- The defect `D_{I,b}` of the face-syndrome lemma: the points `z` of the `I`-face in position `b`
such that `(z, b) ∈ E` or `(z, b)` lies on a full line of `N` of some direction `j ∉ I`. -/
def faceDefect (N E : Set (ι → Fin n)) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    Set ({i // i ∈ I} → Fin n) :=
  {z | glue I z b ∈ E ∨ ∃ j ∉ I, ∀ t, Function.update (glue I z b) j t ∈ N}

variable {N N' E E' : Set (ι → Fin n)} {I : Finset ι} {b : {i // i ∉ I} → Fin n}
  {z : {i // i ∈ I} → Fin n}

lemma mem_faceDefect : z ∈ faceDefect N E I b ↔
    glue I z b ∈ E ∨ ∃ j ∉ I, ∀ t, Function.update (glue I z b) j t ∈ N := Iff.rfl

lemma faceDefect_mono (hN : N ⊆ N') (hE : E ⊆ E') (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    faceDefect N E I b ⊆ faceDefect N' E' I b := by
  rintro z (hz | ⟨j, hj, hz⟩)
  · exact Or.inl (hE hz)
  · exact Or.inr ⟨j, hj, fun t => hN (hz t)⟩

/-- `E_{I,b} ⊆ D_{I,b}`. -/
lemma face_subset_faceDefect (N E : Set (ι → Fin n)) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    {z | glue I z b ∈ E} ⊆ faceDefect N E I b :=
  fun _ hz => Or.inl hz

/-- `D_{I,b} = E_{I,b} ∪ ⋃_{j ∉ I} Q_j`, where `Q_j` is the set of points `z` with `(z,b)` on a full
`j`-line of `N`. -/
lemma faceDefect_eq_union [Fintype ι] (N E : Set (ι → Fin n)) (I : Finset ι)
    (b : {i // i ∉ I} → Fin n) :
    faceDefect N E I b = {z | glue I z b ∈ E} ∪
      ⋃ j ∈ Iᶜ, {z | glue I z b ∈ {y | ∀ t, Function.update y j t ∈ N}} := by
  ext z
  simp [mem_faceDefect]

/-- `D_{I,b}` is `(η' + (d - |I|) κ)`-closed if `N` is `κ`-closed and `E` is `η'`-closed
(step 2 of lemma D: the union of `E_{I,b}` and of the `d - |I|` sets `Q_j`, (F1)). -/
theorem IsClosedSet.faceDefect_closed [Fintype ι] {κ η' : ℝ} (hN : IsClosedSet κ N)
    (hE : IsClosedSet η' E) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    IsClosedSet (η' + (Fintype.card ι - I.card : ℕ) * κ) (faceDefect N E I b) := by
  rw [faceDefect_eq_union, ← Finset.card_compl]
  rcases (Iᶜ : Finset ι).eq_empty_or_nonempty with h | h
  · rw [h]
    simpa using hE.face_closed I b
  · exact (hE.face_closed I b).union
      (IsClosedSet.biUnion_const h fun j _ => (hN.setOf_full_line j).face_closed I b)

end FaceDefect

/-! ### Core: one direction `i`, one check `p`, `U = N^{(p)} ∪ E^{(p)}` -/

/-- Enlarging the support set in `W + F^S`. -/
lemma mem_sup_supported_of_subset {κ : Type*} {W : Submodule F ((κ → Fin n) → F)}
    {S T : Set (κ → Fin n)} {x : (κ → Fin n) → F} (hx : x ∈ W ⊔ supported F S) (hST : S ⊆ T) :
    x ∈ W ⊔ supported F T :=
  (sup_le_sup_left (supported_mono hST) W) hx

section Core

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq F] {P : ι → Type*}
  {H : ∀ i, Matrix (P i) (Fin n) F}
  {N E : Set (ι → Fin n)} {a : (ι → Fin n) → F} {κ η' η : ℝ} {Δ : ℕ}

omit [Fintype ι] in
/-- `U = N^{(p)} ∪ E^{(p)}` is `η`-closed as soon as it is proper ((F1); the slices of `N` and `E`
at the neighbours of `p` are then proper, which forces `κ, η' > 0`). -/
theorem isClosedSet_synDefect_union_of_ne_univ (hN : IsClosedSet κ N) (hE : IsClosedSet η' E)
    {i : ι} (p : P i) (hdeg : (univ.filter fun u => H i p u ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hp : ∃ u, H i p u ≠ 0)
    (hU : synDefect H N i p ∪ synDefect H E i p ≠ Set.univ) :
    IsClosedSet η (synDefect H N i p ∪ synDefect H E i p) := by
  rcases isEmpty_or_nonempty {j // j ≠ i} with hempty | hne
  · intro k
    exact isEmptyElim k
  obtain ⟨u₀, hu₀⟩ := hp
  have hsN : sliceSet N i u₀ ≠ Set.univ := by
    intro h
    apply hU
    rw [synDefect_eq_univ_of_sliceSet hu₀ h, Set.univ_union]
  have hsE : sliceSet E i u₀ ≠ Set.univ := by
    intro h
    apply hU
    rw [synDefect_eq_univ_of_sliceSet hu₀ h, Set.union_univ]
  obtain ⟨hκ, -⟩ := (hN.sliceSet_closed i u₀).pos_of_ne_univ hsN
  obtain ⟨hη', -⟩ := (hE.sliceSet_closed i u₀).pos_of_ne_univ hsE
  have hcard : 1 ≤ (univ.filter fun u => H i p u ≠ 0).card :=
    Finset.card_pos.2 ⟨u₀, by simp [hu₀]⟩
  have hcardR : ((univ.filter fun u => H i p u ≠ 0).card : ℝ) ≤ Δ := by exact_mod_cast hdeg
  have hΔ : (1 : ℝ) ≤ Δ := by exact_mod_cast hcard.trans hdeg
  have h1 : IsClosedSet (Δ * κ) (synDefect H N i p) :=
    hN.synDefect_closed i p (mul_pos (by linarith) hκ) (mul_le_mul_of_nonneg_right hcardR hκ.le)
  have h2 : IsClosedSet (Δ * η') (synDefect H E i p) :=
    hE.synDefect_closed i p (mul_pos (by linarith) hη') (mul_le_mul_of_nonneg_right hcardR hη'.le)
  refine (h1.union h2).mono ?_
  have hmax : κ + η' ≤ 2 * max κ η' := by
    have := le_max_left κ η'
    have := le_max_right κ η'
    linarith
  calc (Δ : ℝ) * κ + Δ * η' = Δ * (κ + η') := by ring
    _ ≤ Δ * (2 * max κ η') := mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)
    _ = 2 * Δ * max κ η' := by ring
    _ ≤ η := hpar

omit [Fintype ι] in
/-- **Dirichlet for `U = N^{(p)} ∪ E^{(p)}`** ((F1)): if `2Δ max(κ, η') ≤ η ≤ 1`, every full line of
`U` (in the hyperplane cube) lies in a single slice `N|_{y_i = u}` or `E|_{y_i = u}`, `u ∈ N(p)`. -/
theorem exists_slice_of_full_line_synDefect_union (hN : IsClosedSet κ N) (hE : IsClosedSet η' E)
    {i : ι} (p : P i) (hdeg : (univ.filter fun u => H i p u ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hη1 : η ≤ 1) {j : {j // j ≠ i}}
    {z : {j // j ≠ i} → Fin n}
    (hfull : ∀ t, Function.update z j t ∈ synDefect H N i p ∪ synDefect H E i p) :
    ∃ u, H i p u ≠ 0 ∧ ((∀ t, Function.update z j t ∈ sliceSet N i u) ∨
      (∀ t, Function.update z j t ∈ sliceSet E i u)) := by
  set Np := univ.filter fun u => H i p u ≠ 0 with hNp
  have hn : 0 < n := Fin.pos (z j)
  have hcl : ∀ x ∈ Np.disjSum Np, IsClosedSet (Sum.elim (fun _ => κ) (fun _ => η') x)
      (Sum.elim (sliceSet N i) (sliceSet E i) x) := by
    rintro (u | u) -
    · exact hN.sliceSet_closed i u
    · exact hE.sliceSet_closed i u
  have hsum : ∑ x ∈ Np.disjSum Np, Sum.elim (fun _ => κ) (fun _ => η') x ≤ 1 := by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, nsmul_eq_mul]
    have hcardR : (Np.card : ℝ) ≤ Δ := by exact_mod_cast hdeg
    have hmax : κ + η' ≤ 2 * max κ η' := by
      have := le_max_left κ η'
      have := le_max_right κ η'
      linarith
    by_cases hs : κ + η' ≤ 0
    · have h0 : (0 : ℝ) ≤ Np.card := Nat.cast_nonneg _
      have : (Np.card : ℝ) * κ + Np.card * η' ≤ 0 := by
        rw [← mul_add]
        exact mul_nonpos_of_nonneg_of_nonpos h0 hs
      linarith
    · push Not at hs
      calc (Np.card : ℝ) * κ + Np.card * η' = Np.card * (κ + η') := by ring
        _ ≤ Δ * (κ + η') := mul_le_mul_of_nonneg_right hcardR hs.le
        _ ≤ Δ * (2 * max κ η') := mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)
        _ = 2 * Δ * max κ η' := by ring
        _ ≤ η := hpar
        _ ≤ 1 := hη1
  have hfull' : ∀ t, Function.update z j t ∈ ⋃ x ∈ Np.disjSum Np,
      Sum.elim (sliceSet N i) (sliceSet E i) x := by
    intro t
    rcases hfull t with ⟨u, hu, hmem⟩ | ⟨u, hu, hmem⟩
    · exact Set.mem_biUnion (Finset.inl_mem_disjSum.2 (by simp [hNp, hu])) hmem
    · exact Set.mem_biUnion (Finset.inr_mem_disjSum.2 (by simp [hNp, hu])) hmem
  obtain ⟨x, hx, hline⟩ := IsClosedSet.exists_full_line_of_biUnion hn hcl hsum hfull'
  rcases x with u | u
  · exact ⟨u, by simpa [hNp] using Finset.inl_mem_disjSum.1 hx, Or.inl hline⟩
  · exact ⟨u, by simpa [hNp] using Finset.inr_mem_disjSum.1 hx, Or.inr hline⟩

/-- **Core of the face-syndrome lemma.** Let `a` satisfy `S(E)` with `supp a ⊆ N`, and let `P(d-1)`
hold in the hyperplane cube of direction `i` for proper `η`-closed sets. Then
`σ = ∑_{u ∈ N(p)} H_i(p,u) a|_{y_i=u} = w + f` with `w ∈ L(U)`, `U = N^{(p)} ∪ E^{(p)}`, and
`supp f ⊆ E^{(p)}`. (If `U` is the whole hyperplane, `P(d-1)` is not needed.) -/
theorem SynCond.checkSum_mem_lineSpan_sup {i : ι}
    (hgen : ∀ M : Set ({j // j ≠ i} → Fin n), IsClosedSet η M → M ≠ Set.univ →
      GeneratedFromInside (fun k : {j // j ≠ i} => kerCode (H k)) M)
    (ha : SynCond H E a) (hsupp : SupportedIn a N) (hN : IsClosedSet κ N)
    (hE : IsClosedSet η' E) (p : P i) (hdeg : (univ.filter fun u => H i p u ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) :
    checkSum i (H i p) a ∈
      lineSpan (fun k : {j // j ≠ i} => kerCode (H k)) (synDefect H N i p ∪ synDefect H E i p) ⊔
        supported F (synDefect H E i p) := by
  by_cases hp : ∃ u, H i p u ≠ 0
  swap
  · push Not at hp
    have : checkSum i (H i p) a = 0 := by
      funext z
      simp [hp]
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨w, hw, f, hf, hσ⟩ := ha.exists_decomp i p
  have hwU : SupportedIn w (synDefect H N i p ∪ synDefect H E i p) := by
    intro z hz
    by_cases hfz : f z = 0
    · left
      apply supportedIn_checkSum_synDefect hsupp i p z
      rw [hσ, Pi.add_apply, hfz, add_zero]
      exact hz
    · exact Or.inr (hf z hfz)
  have hwL : w ∈ lineSpan (fun k : {j // j ≠ i} => kerCode (H k))
      (synDefect H N i p ∪ synDefect H E i p) := by
    by_cases hU : synDefect H N i p ∪ synDefect H E i p = Set.univ
    · rw [hU]
      exact boxplus_le_lineSpan_univ _ hw
    · exact hgen _ (isClosedSet_synDefect_union_of_ne_univ hN hE p hdeg hpar hp hU) hU
        (Submodule.mem_inf.2 ⟨hw, hwU⟩)
  rw [hσ]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hwL) (Submodule.mem_sup_right hf)

/-- **Restriction of the check sum to a subcube of the hyperplane.** Under the hypotheses of the
core lemma and `2Δ max(κ, η') ≤ η ≤ 1`: for any subcube `Ψ` (directions `φ`) of the hyperplane
cube of direction `i`, `σ ∘ Ψ` lies in `⊞` of the subcube plus words supported at the points `z`
such that for some `u ∈ N(p)` the point `(u, Ψ z)` lies in `E` or on a full line of `N` of a
direction outside the subcube. -/
theorem SynCond.checkSum_comp_mem_sup {i : ι}
    (hgen : ∀ M : Set ({j // j ≠ i} → Fin n), IsClosedSet η M → M ≠ Set.univ →
      GeneratedFromInside (fun k : {j // j ≠ i} => kerCode (H k)) M)
    (ha : SynCond H E a) (hsupp : SupportedIn a N) (hN : IsClosedSet κ N)
    (hE : IsClosedSet η' E) (p : P i) (hdeg : (univ.filter fun u => H i p u ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hη1 : η ≤ 1)
    {μ : Type*} [DecidableEq μ] {φ : μ → {j // j ≠ i}}
    {Ψ : (μ → Fin n) → ({j // j ≠ i} → Fin n)} (hΨ : IsSubcubeEmb φ Ψ) :
    checkSum i (H i p) a ∘ Ψ ∈ boxplus (fun k => kerCode (H (φ k))) ⊔
      supported F {z | ∃ u, H i p u ≠ 0 ∧ (hglue i u (Ψ z) ∈ E ∨
        ∃ j : {j // j ≠ i}, j ∉ Set.range φ ∧
          ∀ t, Function.update (hglue i u (Ψ z)) j.1 t ∈ N)} := by
  obtain ⟨w, hw, f, hf, hσ⟩ :=
    Submodule.mem_sup.1 (ha.checkSum_mem_lineSpan_sup hgen hsupp hN hE p hdeg hpar)
  rw [← hσ]
  change w ∘ Ψ + f ∘ Ψ ∈ _
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right ?_)
  · obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hΨ.comp_mem_lineSpan_sup hw)
    rw [← hxy]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (lineSpan_le_boxplus _ hx))
      (Submodule.mem_sup_right ?_)
    intro z hz
    obtain ⟨j, hj, hfull⟩ := hy z hz
    obtain ⟨u, hu, hline | hline⟩ :=
      exists_slice_of_full_line_synDefect_union hN hE p hdeg hpar hη1 hfull
    · refine ⟨u, hu, Or.inr ⟨j, hj, fun t => ?_⟩⟩
      have := hline t
      rwa [mem_sliceSet, hglue_update] at this
    · refine ⟨u, hu, Or.inl ?_⟩
      have := hline (Ψ z j)
      rwa [Function.update_eq_self, mem_sliceSet] at this
  · intro z hz
    obtain ⟨u, hu, hzE⟩ := hf (Ψ z) hz
    exact ⟨u, hu, Or.inl hzE⟩

end Core

/-! ### The face-syndrome lemma and its relatives -/

section FaceSyn

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq F] {P : ι → Type*}
  {H : ∀ i, Matrix (P i) (Fin n) F}
  {N E : Set (ι → Fin n)} {a : (ι → Fin n) → F} {κ η' η : ℝ} {Δ : ℕ}

/-- **Face-syndrome lemma** (`lem:face-syn`). Let `P(d-1)` hold on the hyperplane cubes
`{j // j ≠ i} → Fin n` (for proper `η`-closed sets, hypothesis `hgen`), let `N` be `κ`-closed and
`E` be `η'`-closed, let the right degrees be at most `Δ`, and `2Δ max(κ, η') ≤ η ≤ 1`.
If `a` satisfies `S(E)` and `supp a ⊆ N`, then for every `I` and every position `b` (the face need
not be full, and `I = ∅`, `I = univ` are allowed) the restriction `a_{I,b}` satisfies
`S_{|I|}(D_{I,b})`, `D_{I,b} = faceDefect N E I b`. -/
theorem SynCond.faceSyn
    (hgen : ∀ (i : ι) (M : Set ({j // j ≠ i} → Fin n)), IsClosedSet η M → M ≠ Set.univ →
      GeneratedFromInside (fun k : {j // j ≠ i} => kerCode (H k)) M)
    (ha : SynCond H E a) (hsupp : SupportedIn a N) (hN : IsClosedSet κ N)
    (hE : IsClosedSet η' E)
    (hdeg : ∀ (i : ι) (p : P i), (univ.filter fun u => H i p u ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hη1 : η ≤ 1) (I : Finset ι)
    (b : {i // i ∉ I} → Fin n) :
    SynCond (fun k : {i // i ∈ I} => H k) (faceDefect N E I b) (faceRestrict a I b) := by
  rintro ⟨i, hi⟩ p
  have h := ha.checkSum_comp_mem_sup (hgen i) hsupp hN hE p (hdeg i p) hpar hη1
    (isSubcubeEmb_faceHypPoint hi b)
  rw [checkSum_faceRestrict hi]
  refine mem_sup_supported_of_subset h ?_
  rintro z ⟨u, hu, hz⟩
  refine ⟨u, hu, ?_⟩
  rw [mem_faceDefect, ← hglue_faceHypPoint hi b u z]
  rcases hz with hz | ⟨j, hj, hfull⟩
  · exact Or.inl hz
  · exact Or.inr ⟨j.1, fun h => hj ((mem_range_faceHypEmb hi j).2 h), hfull⟩

/-- **Check sums across faces** (equation `eq:route`, step 3 of lemma D). For a direction `j ∉ I`,
a check `r ∈ P_j` and the faces `Φ_I(β, t)` along the `j`-line of the base `B_I` through `b`
(`(β, t) = update b j t`):
`∑_{t ∈ N_j(r)} H_j(r,t) a_{I,(β,t)} ∈ W_I + F^{⋃_{t ∈ N_j(r)} D_{I,(β,t)}}`.
(For `I ∪ {j} = [d]` this is just `S(E)`; the uniform proof uses `P(d-1)` in the hyperplane
`{y_j = ·}`.) -/
theorem SynCond.route {j : ι}
    (hgen : ∀ M : Set ({k // k ≠ j} → Fin n), IsClosedSet η M → M ≠ Set.univ →
      GeneratedFromInside (fun k : {k // k ≠ j} => kerCode (H k)) M)
    (ha : SynCond H E a) (hsupp : SupportedIn a N) (hN : IsClosedSet κ N)
    (hE : IsClosedSet η' E) (r : P j) (hdeg : (univ.filter fun t => H j r t ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hη1 : η ≤ 1) {I : Finset ι} (hj : j ∉ I)
    (b : {k // k ∉ I} → Fin n) :
    ∑ t, H j r t • faceRestrict a I (Function.update b ⟨j, hj⟩ t) ∈
      boxplus (fun k : {k // k ∈ I} => kerCode (H k)) ⊔
        supported F {z | ∃ t, H j r t ≠ 0 ∧
          z ∈ faceDefect N E I (Function.update b ⟨j, hj⟩ t)} := by
  have h := ha.checkSum_comp_mem_sup hgen hsupp hN hE r hdeg hpar hη1
    (isSubcubeEmb_hproj_glue hj b)
  rw [checkSum_comp_hproj_glue hj b] at h
  refine mem_sup_supported_of_subset h ?_
  rintro z ⟨t, ht, hz⟩
  refine ⟨t, ht, ?_⟩
  have key : hglue j t (hproj j (glue I z b)) = glue I z (Function.update b ⟨j, hj⟩ t) := by
    rw [hglue_hproj_eq_update, update_glue_of_not_mem I z b hj]
  rw [key] at hz
  rcases hz with hz | ⟨k, hk, hfull⟩
  · exact Or.inl hz
  · exact Or.inr ⟨k.1, fun h => hk ((mem_range_faceToHyp hj k).2 h), hfull⟩

/-- **Pointwise form** (step 5 of lemma D). If `σ = ∑_{u ∈ N(p)} H_i(p,u) a|_{y_i=u}` does not
vanish at `z`, then for some `u ∈ N(p)` the point `(u, z)` lies in `E` or on a full line of `N` of
a direction `≠ i`. -/
theorem SynCond.exists_of_checkSum_ne_zero {i : ι}
    (hgen : ∀ M : Set ({j // j ≠ i} → Fin n), IsClosedSet η M → M ≠ Set.univ →
      GeneratedFromInside (fun k : {j // j ≠ i} => kerCode (H k)) M)
    (ha : SynCond H E a) (hsupp : SupportedIn a N) (hN : IsClosedSet κ N)
    (hE : IsClosedSet η' E) (p : P i) (hdeg : (univ.filter fun u => H i p u ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hη1 : η ≤ 1) {z : {j // j ≠ i} → Fin n}
    (hz : checkSum i (H i p) a z ≠ 0) :
    ∃ u, H i p u ≠ 0 ∧ (hglue i u z ∈ E ∨
      ∃ j : {j // j ≠ i}, ∀ t, Function.update (hglue i u z) j.1 t ∈ N) := by
  obtain ⟨w, hw, f, hf, hσ⟩ :=
    Submodule.mem_sup.1 (ha.checkSum_mem_lineSpan_sup hgen hsupp hN hE p hdeg hpar)
  rw [← hσ, Pi.add_apply] at hz
  by_cases hfz : f z = 0
  · rw [hfz, add_zero] at hz
    obtain ⟨j, hfull⟩ := exists_full_line_of_mem_lineSpan hw hz
    obtain ⟨u, hu, hline | hline⟩ :=
      exists_slice_of_full_line_synDefect_union hN hE p hdeg hpar hη1 hfull
    · refine ⟨u, hu, Or.inr ⟨j, fun t => ?_⟩⟩
      have := hline t
      rwa [mem_sliceSet, hglue_update] at this
    · refine ⟨u, hu, Or.inl ?_⟩
      have := hline (z j)
      rwa [Function.update_eq_self, mem_sliceSet] at this
  · obtain ⟨u, hu, hzE⟩ := hf z hfz
    exact ⟨u, hu, Or.inl hzE⟩

/-- **Syndrome of a line** (remark after `lem:face-syn`; step 5 of lemma D). If the `p`-th check
of `H_i` does not vanish on the line of direction `i` through `y`, then some neighbour `u ∈ N(p)`
of it gives a point `y' = (y with y_i = u)` of the line lying in `E` or on a full line of `N` of
another direction. -/
theorem SynCond.exists_of_lineSyndrome_ne_zero {i : ι}
    (hgen : ∀ M : Set ({j // j ≠ i} → Fin n), IsClosedSet η M → M ≠ Set.univ →
      GeneratedFromInside (fun k : {j // j ≠ i} => kerCode (H k)) M)
    (ha : SynCond H E a) (hsupp : SupportedIn a N) (hN : IsClosedSet κ N)
    (hE : IsClosedSet η' E) (p : P i) (hdeg : (univ.filter fun u => H i p u ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hη1 : η ≤ 1) {y : ι → Fin n}
    (hy : (H i *ᵥ restrictLine a i y) p ≠ 0) :
    ∃ u, H i p u ≠ 0 ∧ (Function.update y i u ∈ E ∨
      ∃ j, j ≠ i ∧ ∀ t, Function.update (Function.update y i u) j t ∈ N) := by
  rw [← checkSum_row_apply_hproj] at hy
  obtain ⟨u, hu, h⟩ := ha.exists_of_checkSum_ne_zero hgen hsupp hN hE p hdeg hpar hη1 hy
  refine ⟨u, hu, ?_⟩
  rw [hglue_hproj_eq_update] at h
  rcases h with h | ⟨j, hj⟩
  · exact Or.inl h
  · exact Or.inr ⟨j.1, j.2, hj⟩

end FaceSyn

/-! ### `P(d)` as a hypothesis -/

section GenProp

/-- `P(d)` with threshold `η` for a class `cls` of check matrices: for every index type `K` with
`|K| = d` and every family `G` of check matrices of the class indexed by `K`, every *proper* `η`-closed set `M ⊆ K → Fin n` is generated
from inside for the codes `ker G_k`. For the main theorem `cls Q G := IsExpanderMatrix G δ Δ α ε`
(see `SynCond.faceSyn_of_expander`). Only proper sets are required: the whole cube is covered by
`generatedFromInside_univ` (see `GenProp.generatedFromInside`). The universe of `K` is the first
universe parameter: write `GenProp.{u, v}` for index types in `Type u` and `Q k : Type v`. -/
def GenProp (F : Type*) [Field F] (n : ℕ)
    (cls : ∀ (Q : Type v) [Fintype Q] [DecidableEq Q], Matrix Q (Fin n) F → Prop)
    (η : ℝ) (d : ℕ) : Prop :=
  ∀ (K : Type u) [Fintype K] [DecidableEq K], Fintype.card K = d →
    ∀ (Q : K → Type v) [∀ k, Fintype (Q k)] [∀ k, DecidableEq (Q k)]
      (G : ∀ k, Matrix (Q k) (Fin n) F), (∀ k, cls (Q k) (G k)) →
      ∀ M : Set (K → Fin n), IsClosedSet η M → M ≠ Set.univ →
        GeneratedFromInside (fun k => kerCode (G k)) M

variable {cls : ∀ (Q : Type v) [Fintype Q] [DecidableEq Q], Matrix Q (Fin n) F → Prop}
  {η η₀ : ℝ} {d : ℕ}

/-- `P(d)` with threshold `η` gives `P(d)` with every smaller threshold (`η ≤ η_d` in the proof). -/
lemma GenProp.mono (hP : GenProp.{u, v} F n cls η d) (h : η₀ ≤ η) :
    GenProp.{u, v} F n cls η₀ d :=
  fun K _ _ hK Q _ _ G hG M hM hne => hP K hK Q G hG M (hM.mono h) hne

/-- `P(d)` for all closed sets, the whole cube included. -/
lemma GenProp.generatedFromInside (hP : GenProp.{u, v} F n cls η d) {K : Type u} [Fintype K]
    [DecidableEq K] (hK : Fintype.card K = d) {Q : K → Type v} [∀ k, Fintype (Q k)]
    [∀ k, DecidableEq (Q k)] {G : ∀ k, Matrix (Q k) (Fin n) F} (hG : ∀ k, cls (Q k) (G k))
    (M : Set (K → Fin n)) (hM : IsClosedSet η M) :
    GeneratedFromInside (fun k => kerCode (G k)) M :=
  generatedFromInside_of_ne_univ (hP K hK Q G hG) M hM

variable {ι : Type u} [DecidableEq ι] [Fintype ι] {P : ι → Type v} [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (P i)] {H : ∀ i, Matrix (P i) (Fin n) F}

/-- `P(d-1)` for the class gives the hypothesis `hgen` of the lemmas above on the hyperplane cubes
`{j // j ≠ i} → Fin n` of a cube `ι → Fin n` (`|ι| = d`; the codes are `ker H_j`, `j ≠ i`). -/
lemma GenProp.hyperplane (hP : GenProp.{u, v} F n cls η (Fintype.card ι - 1))
    (hcls : ∀ i, cls (P i) (H i)) (i : ι) (M : Set ({j // j ≠ i} → Fin n))
    (hM : IsClosedSet η M) (hne : M ≠ Set.univ) :
    GeneratedFromInside (fun k : {j // j ≠ i} => kerCode (H k)) M :=
  hP {j // j ≠ i} (card_ne i) (fun k => P k) (fun k => H k) (fun k => hcls k) M hM hne

variable [DecidableEq F] {N E : Set (ι → Fin n)} {a : (ι → Fin n) → F} {κ η' : ℝ} {Δ : ℕ}

/-- **Face-syndrome lemma** with `P(d-1)` in the packaged form `GenProp`. -/
theorem SynCond.faceSyn_of_genProp (hP : GenProp.{u, v} F n cls η (Fintype.card ι - 1))
    (hcls : ∀ i, cls (P i) (H i)) (ha : SynCond H E a) (hsupp : SupportedIn a N)
    (hN : IsClosedSet κ N) (hE : IsClosedSet η' E)
    (hdeg : ∀ (i : ι) (p : P i), (univ.filter fun u => H i p u ≠ 0).card ≤ Δ)
    (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hη1 : η ≤ 1) (I : Finset ι)
    (b : {i // i ∉ I} → Fin n) :
    SynCond (fun k : {i // i ∈ I} => H k) (faceDefect N E I b) (faceRestrict a I b) :=
  ha.faceSyn (hP.hyperplane hcls) hsupp hN hE hdeg hpar hη1 I b

/-- **Face-syndrome lemma** for the class of expanders of the main theorem (the right degrees are
taken from `IsExpanderMatrix`). -/
theorem SynCond.faceSyn_of_expander {δ : ℕ} {α ε : ℝ}
    (hH : ∀ i, IsExpanderMatrix (H i) δ Δ α ε)
    (hP : GenProp.{u, v} F n (fun _ _ _ G => IsExpanderMatrix G δ Δ α ε) η
      (Fintype.card ι - 1))
    (ha : SynCond H E a) (hsupp : SupportedIn a N) (hN : IsClosedSet κ N)
    (hE : IsClosedSet η' E) (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η) (hη1 : η ≤ 1) (I : Finset ι)
    (b : {i // i ∉ I} → Fin n) :
    SynCond (fun k : {i // i ∈ I} => H k) (faceDefect N E I b) (faceRestrict a I b) :=
  ha.faceSyn_of_genProp hP hH hsupp hN hE (fun i => (hH i).rightDeg) hpar hη1 I b

end GenProp

end ProductExpansion
