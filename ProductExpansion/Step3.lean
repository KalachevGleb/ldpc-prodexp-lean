import ProductExpansion.MainInterface

/-!
# Step 3 of the proof of the main lemma `D(d)`

See `MainInterface.lean` (`Step3Statement`) and the proof of lemma `lem:D`.
-/

open Finset

namespace ProductExpansion

namespace Step3

section Lemmas

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- Step 3, bound `|T_ℓ| < κ n`: on the `j`-line of the base `B_I` through `b` whose position
`β ∈ B_{I ∪ j}` is not in `Bad_{I ∪ j}`, fewer than `κ n` of the `I`-faces are full in `N`
(otherwise, by (F3), the whole line lies in `Y_I(N)`, so `β ∈ Y_{I ∪ j}(N) ⊆ Bad_{I ∪ j}` by (I2)). -/
lemma card_linePts_posFull_lt {H : ∀ i, Matrix (P i) (Fin n) F} {δ : ℕ} {κ : ℝ} {d' : ℕ}
    {E N : Set (ι → Fin n)} (hN : IsClosedSet κ N) (hinv : LevelInv2 H δ E N d')
    {I : Finset ι} (hI : I.card = d') (j : {i // i ∉ I}) (b : {i // i ∉ I} → Fin n)
    (hG3 : resPos (Finset.subset_insert j.1 I) b ∉
      badSet H ((1 / 4 : ℝ) * δ) E (insert j.1 I)) :
    ((linePts (posFull N I) j b).card : ℝ) < κ * n := by
  by_contra hle
  push Not at hle
  have hfull : ∀ t, Function.update b j t ∈ posFull N I := by
    intro t
    refine (hN.posFull_closed I) j b ?_ t
    rw [lineCount_eq_card_linePts]
    exact hle
  apply hG3
  refine hinv (insert j.1 I) ?_ (resPos_mem_posFull_insert hfull)
  rw [Finset.card_insert_of_notMem j.2, hI]
  omega

/-- Linear algebra of step 3: if `∑_t h_t X_t ∈ W`, `h_{t₀} ≠ 0`, `h` vanishes outside `V ∋ t₀`
and `X_t ∈ W` for `t ∈ V \ {t₀}`, then `X_{t₀} ∈ W`. -/
lemma mem_of_sum_smul_mem {M : Type*} [AddCommGroup M] [Module F M] (W : Submodule F M)
    (h : Fin n → F) (X : Fin n → M) {V : Finset (Fin n)} {t₀ : Fin n} (ht₀ : t₀ ∈ V)
    (hV : ∀ t, h t ≠ 0 → t ∈ V) (h₀ : h t₀ ≠ 0) (hsum : ∑ t, h t • X t ∈ W)
    (hrest : ∀ t ∈ V.erase t₀, X t ∈ W) : X t₀ ∈ W := by
  have h1 : ∑ t, h t • X t = ∑ t ∈ V, h t • X t := by
    refine (Finset.sum_subset (Finset.subset_univ V) ?_).symm
    intro t _ ht
    have : h t = 0 := by
      by_contra hne
      exact ht (hV t hne)
    rw [this, zero_smul]
  have h2 : ∑ t ∈ V, h t • X t = h t₀ • X t₀ + ∑ t ∈ V.erase t₀, h t • X t :=
    (Finset.add_sum_erase V (fun t => h t • X t) ht₀).symm
  have h3 : ∑ t ∈ V.erase t₀, h t • X t ∈ W :=
    Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (hrest t ht)
  have h4 : h t₀ • X t₀ ∈ W := by
    have : h t₀ • X t₀ = ∑ t, h t • X t - ∑ t ∈ V.erase t₀, h t • X t := by
      rw [h1, h2, add_sub_cancel_right]
    rw [this]
    exact Submodule.sub_mem _ hsum h3
  have : X t₀ = (h t₀)⁻¹ • (h t₀ • X t₀) := by
    rw [smul_smul, inv_mul_cancel₀ h₀, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ h4

/-- (F1) + (F2) for `N_r`: the union of a nonempty family of proper `μ`-closed subsets of a cube
of dimension `≥ 1`, indexed by `s` with `|s| ≤ 2Δ`, is `2Δμ`-closed, and it is proper if
`|K| · 2Δμ ≤ 1`. -/
lemma union_closed_ne_univ {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K] {ν : Type*}
    {s : Finset ν} (hs : s.Nonempty) {S : ν → Set (K → Fin n)} {μ : ℝ} {Δ : ℕ} (hn : 0 < n)
    (hcl : ∀ x ∈ s, IsClosedSet μ (S x)) (hne : ∀ x ∈ s, S x ≠ Set.univ) (hμ : 0 ≤ μ)
    (hcard : s.card ≤ 2 * Δ) (hF2 : (Fintype.card K : ℝ) * (2 * Δ * μ) ≤ 1) :
    IsClosedSet (2 * Δ * μ) (⋃ x ∈ s, S x) ∧ (⋃ x ∈ s, S x) ≠ Set.univ := by
  have hcardR : (s.card : ℝ) ≤ 2 * Δ := by exact_mod_cast hcard
  have hsum : (s.card : ℝ) * μ ≤ 2 * Δ * μ := mul_le_mul_of_nonneg_right hcardR hμ
  refine ⟨(IsClosedSet.biUnion_const hs hcl).mono hsum, ?_⟩
  apply biUnion_ne_univ_of_isClosedSet hn (η := fun _ => μ) hcl hne
  rw [Finset.sum_const, nsmul_eq_mul]
  calc (Fintype.card K : ℝ) * (s.card * μ) ≤ Fintype.card K * (2 * Δ * μ) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ ≤ 1 := hF2

omit [Fintype ι] in
/-- Lemma CL in the face cube `{k // k ∈ I} → Fin n` (`|I| = d' ≥ 1`) for a proper `ηb`-closed
defect `D`: `D ⊆ \hat D`, and `\hat D` is proper and `c_{d'} ηb`-closed. -/
lemma face_canonical {H : ∀ i, Matrix (P i) (Fin n) F} {δ Δ : ℕ} {α ε ηb : ℝ} {d' : ℕ}
    (hH : ∀ i, IsExpanderMatrix (H i) δ Δ α ε) (hδ : 0 < δ) (hε : ε ≤ 1 / 16)
    (hαn : 2 ≤ α * n) (hd' : 1 ≤ d') (hηb : 0 ≤ ηb)
    (hc' : canC' (1 / 4 - ε) d' * ηb ≤ (1 / 4 - ε) * α / 2)
    (hc : canC (1 / 4 - ε) d' * ηb < 1) {I : Finset ι} (hI : I.card = d')
    {D : Set ({k // k ∈ I} → Fin n)} (hD : IsClosedSet ηb D) (hDne : D ≠ Set.univ) :
    D ⊆ canonicalSet (fun k : {k // k ∈ I} => H k) δ ε D ∧
      canonicalSet (fun k : {k // k ∈ I} => H k) δ ε D ≠ Set.univ ∧
      IsClosedSet (canC (1 / 4 - ε) d' * ηb)
        (canonicalSet (fun k : {k // k ∈ I} => H k) δ ε D) := by
  have hcard : Fintype.card {k // k ∈ I} = d' := by rw [Fintype.card_coe, hI]
  have : Nonempty {k // k ∈ I} := by
    rw [← Fintype.card_pos_iff, hcard]; omega
  have hspec := canonicalSet_spec (H := fun k : {k // k ∈ I} => H k) (fun k => hH k) hδ hε hαn
    hD hDne hηb (by rw [hcard]; exact hc') (by rw [hcard]; exact hc)
  rw [hcard] at hspec
  exact ⟨hspec.1.trans hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩

/-- The `I`-face of `a` in position `c` is decoded: `a_{I,c} ∈ W_I + F^{\hat D_{I,c}}`
(the conclusion of `GoodFacesDecoded`). -/
def FaceDecoded (H : ∀ i, Matrix (P i) (Fin n) F) (δ : ℕ) (ε : ℝ) (E N : Set (ι → Fin n))
    (a : (ι → Fin n) → F) (I : Finset ι) (c : {i // i ∉ I} → Fin n) : Prop :=
  faceRestrict a I c ∈ boxplus (fun k : {k // k ∈ I} => kerCode (H k)) ⊔
    supported F (canonicalSet (fun k : {k // k ∈ I} => H k) δ ε (faceDefect N E I c))

end Lemmas

section Core

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {P : ι → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- **Core of step 3** (the unique check `r` of the good line). Let `V = N_j(r)` and `t₀ ∈ V`.
Suppose the defects `D_t = D_{I,(β,t)}`, `t ∈ V`, are proper and `μ`-closed, and that sets `Z_t`,
`t ∈ V`, are proper and `μ`-closed with `X_t = a_{I,(β,t)} ∈ W_I + F^{Z_t}` for `t ∈ V \ {t₀}`.
Then the route equation `eq:route` gives `X_{t₀} ∈ W_I + F^{N_r}`, `N_r = ⋃_t D_t ∪ ⋃_t Z_t`
(proper and `2Δμ`-closed by (F1), (F2)), and `D(d')` in the face cube decodes `X_{t₀}`. -/
lemma faceDecoded_of_route {H : ∀ i, Matrix (P i) (Fin n) F} {δ Δ : ℕ}
    {α ε η κD η' κ μ : ℝ} {d' : ℕ} {E N : Set (ι → Fin n)} {a : (ι → Fin n) → F}
    (hH : ∀ i, IsExpanderMatrix (H i) δ Δ α ε) (hαn : 2 ≤ α * n) (hd' : 1 ≤ d')
    (hD : DecodeStatement F δ Δ α ε d' κD) (hgen : HypGen H η) (hη1 : η ≤ 1)
    (hE : IsClosedSet η' E) (hN : IsClosedSet κ N) (ha : SynCond H E a)
    (hsupp : SupportedIn a N) (hpar : 2 * (Δ : ℝ) * max κ η' ≤ η)
    (hμ : 0 ≤ μ) (hμF2 : (d' : ℝ) * (2 * Δ * μ) ≤ 1) (hμD : 2 * (Δ : ℝ) * μ ≤ κD)
    {I : Finset ι} (hI : I.card = d') (j : {i // i ∉ I}) (b : {i // i ∉ I} → Fin n)
    (r : P j.1) {t₀ : Fin n} (ht₀ : t₀ ∈ vnbrs (H j.1) r)
    (Z : Fin n → Set ({k // k ∈ I} → Fin n))
    (hDcl : ∀ t ∈ vnbrs (H j.1) r, IsClosedSet μ (faceDefect N E I (Function.update b j t)))
    (hDne : ∀ t ∈ vnbrs (H j.1) r, faceDefect N E I (Function.update b j t) ≠ Set.univ)
    (hDκ : IsClosedSet κD (faceDefect N E I (Function.update b j t₀)))
    (hZcl : ∀ t ∈ vnbrs (H j.1) r, IsClosedSet μ (Z t))
    (hZne : ∀ t ∈ vnbrs (H j.1) r, Z t ≠ Set.univ)
    (hX : ∀ t ∈ (vnbrs (H j.1) r).erase t₀, faceRestrict a I (Function.update b j t) ∈
      boxplus (fun k : {k // k ∈ I} => kerCode (H k)) ⊔ supported F (Z t)) :
    FaceDecoded H δ ε E N a I (Function.update b j t₀) := by
  classical
  set V := vnbrs (H j.1) r with hVdef
  set W := boxplus (fun k : {k // k ∈ I} => kerCode (H k)) with hW
  set fam : Fin n ⊕ Fin n → Set ({k // k ∈ I} → Fin n) :=
    Sum.elim (fun t => faceDefect N E I (Function.update b j t)) Z with hfam
  set s := V.disjSum V with hs
  set Nr := ⋃ x ∈ s, fam x with hNr
  have hn : 0 < n := Fin.pos t₀
  have hcard : Fintype.card {k // k ∈ I} = d' := by rw [Fintype.card_coe, hI]
  have : Nonempty {k // k ∈ I} := by
    rw [← Fintype.card_pos_iff, hcard]; omega
  have hsne : s.Nonempty := ⟨Sum.inl t₀, Finset.inl_mem_disjSum.2 ht₀⟩
  have hscard : s.card ≤ 2 * Δ := by
    have hV : V.card ≤ Δ := (hH j.1).rightDeg r
    rw [hs, Finset.card_disjSum]
    omega
  have hcl : ∀ x ∈ s, IsClosedSet μ (fam x) := by
    rintro (t | t) hx
    · exact hDcl t (Finset.inl_mem_disjSum.1 hx)
    · exact hZcl t (Finset.inr_mem_disjSum.1 hx)
  have hne : ∀ x ∈ s, fam x ≠ Set.univ := by
    rintro (t | t) hx
    · exact hDne t (Finset.inl_mem_disjSum.1 hx)
    · exact hZne t (Finset.inr_mem_disjSum.1 hx)
  obtain ⟨hNrcl, hNrne⟩ := union_closed_ne_univ hsne hn hcl hne hμ hscard
    (by rw [hcard]; exact hμF2)
  have hDsub : ∀ t ∈ V, faceDefect N E I (Function.update b j t) ⊆ Nr := fun t ht _ hz =>
    Set.mem_biUnion (Finset.inl_mem_disjSum.2 ht) hz
  have hZsub : ∀ t ∈ V, Z t ⊆ Nr := fun t ht _ hz =>
    Set.mem_biUnion (Finset.inr_mem_disjSum.2 ht) hz
  -- the route equation `eq:route`
  have hroute := ha.route (hgen j.1) hsupp hN hE r ((hH j.1).rightDeg r) hpar hη1 j.2 b
  have hroute' : ∑ t, H j.1 r t • faceRestrict a I (Function.update b j t) ∈
      W ⊔ supported F Nr := by
    refine mem_sup_supported_of_subset hroute ?_
    rintro z ⟨t, ht, hz⟩
    exact hDsub t ((mem_vnbrs _).2 ht) hz
  -- isolate `X_{t₀}`
  have hXt₀ : faceRestrict a I (Function.update b j t₀) ∈ W ⊔ supported F Nr := by
    refine mem_of_sum_smul_mem (W ⊔ supported F Nr) (fun t => H j.1 r t)
      (fun t => faceRestrict a I (Function.update b j t)) ht₀ ?_ ((mem_vnbrs _).1 ht₀) hroute' ?_
    · intro t ht; exact (mem_vnbrs _).2 ht
    · intro t ht
      exact mem_sup_supported_of_subset (hX t ht) (hZsub t (Finset.mem_of_mem_erase ht))
  -- `D(d')` in the face cube
  obtain ⟨c, hc, e, he, hce⟩ := Submodule.mem_sup.1 hXt₀
  have hsyn := ha.faceSyn hgen hsupp hN hE (fun i p => (hH i).rightDeg p) hpar hη1 I
    (Function.update b j t₀)
  have key := hD n {k // k ∈ I} hcard (fun k => P k.1) (fun k => H k.1) (fun k => hH k.1) hαn
    (faceDefect N E I (Function.update b j t₀)) Nr hDκ (hDne t₀ ht₀) (hNrcl.mono hμD) hNrne
    (faceRestrict a I (Function.update b j t₀)) c e hsyn hce.symm hc he
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 key
  unfold FaceDecoded
  rw [← hce, ← hxy, ← add_assoc]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.add_mem _ hc (lineSpan_le_boxplus _ hx)))
    (Submodule.mem_sup_right hy)

end Core

end Step3

/-- **Step 3** of the proof of `D(d)`: every complete `I`-face (`|I| = d'`) of `N` over a good
position `b ∉ Bad_I` is decoded. Route along the good line `ℓ ∋ b` of direction `j` (lemma `good`):
the set `T_ℓ` of good, complete, undecoded positions of `ℓ` has fewer than `κ n ≤ α n` points
((G3), (I2)); if it is nonempty, (G4) gives a good check `r` with `N_j(r) ∩ T_ℓ = {t*}`, and
`Step3.faceDecoded_of_route` decodes the face at `t*` — a contradiction. -/
theorem step3 : Step3Statement := by
  intro F _ _ n ι _ _ P _ _ H δ Δ α ε η κD η' κ ηb d' E N a hH hδ hε0 hε hαn hα1 hd'1 hd'ι hD
    hgen hη1 hη' hκ hE hEne hN hinv hprop ha hsupp hpar hκα hηb hc' hc hF2 hηbD hκD
    I hI b hbBad hbFull
  classical
  -- parameters
  have hγ : (0 : ℝ) < 1 / 4 - ε := by linarith
  have hc1 : 1 ≤ canC (1 / 4 - ε) d' := one_le_canC hγ hd'1
  have hk1 : (1 : ℝ) ≤ ((Fintype.card ι - d' : ℕ) : ℝ) := by
    have : 1 ≤ Fintype.card ι - d' := by omega
    exact_mod_cast this
  have hηb0 : 0 ≤ ηb := by nlinarith
  have hκηb : κ ≤ ηb := by nlinarith
  have hηbμ : ηb ≤ canC (1 / 4 - ε) d' * ηb := by nlinarith
  have hμ0 : 0 ≤ canC (1 / 4 - ε) d' * ηb := le_trans hηb0 hηbμ
  have hIne : I ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at hI
    omega
  -- the defects `D_{I,c}` are `ηb`-closed
  have hDcl : ∀ c : {i // i ∉ I} → Fin n, IsClosedSet ηb (faceDefect N E I c) := fun c =>
    (hN.faceDefect_closed hE I c).mono (by rw [hI]; exact hηb)
  show Step3.FaceDecoded H δ ε E N a I b
  by_contra hdec
  -- the good line through `b`
  obtain ⟨j, h0, -, hG1, -, hG3, hG4⟩ := good_line_paper hH hε hIne hbBad
  set Ψ := psiJ H ((1 / 4 : ℝ) * δ) E I j b with hΨ
  -- `T_ℓ`: good, complete, undecoded positions of the line
  set T := (linePts (posFull N I) j b).filter
    (fun t => t ∉ Ψ ∧ ¬ Step3.FaceDecoded H δ ε E N a I (Function.update b j t)) with hT
  have hbT : b j ∈ T := by
    rw [hT, Finset.mem_filter, mem_linePts, Function.update_eq_self]
    exact ⟨hbFull, h0, hdec⟩
  have hTcard : (T.card : ℝ) ≤ α * n := by
    have h1 := Step3.card_linePts_posFull_lt hN hinv hI j b hG3
    have h2 : (T.card : ℝ) ≤ (linePts (posFull N I) j b).card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h3 : κ * n ≤ α * n := mul_le_mul_of_nonneg_right hκα (Nat.cast_nonneg n)
    linarith
  have hTG : T ⊆ Finset.univ \ Ψ := by
    intro t ht
    rw [hT, Finset.mem_filter] at ht
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ht.2.1⟩
  -- the unique good check `r`, `N_j(r) ∩ T_ℓ = {t₀}`
  obtain ⟨r, t₀, ht₀T, hVG, hVT⟩ := hG4 T ⟨b j, hbT⟩ hTG hTcard
  have ht₀V : t₀ ∈ vnbrs (H j.1) r := by
    have : t₀ ∈ vnbrs (H j.1) r ∩ T := by rw [hVT]; exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.1 this).1
  have hgood : ∀ t ∈ vnbrs (H j.1) r, t ∉ Ψ := fun t ht => (Finset.mem_sdiff.1 (hVG ht)).2
  have hDne : ∀ t ∈ vnbrs (H j.1) r, faceDefect N E I (Function.update b j t) ≠ Set.univ :=
    fun t ht => hprop I hI _ (hG1 t (hgood t ht))
  have hcan := fun t (ht : t ∈ vnbrs (H j.1) r) =>
    Step3.face_canonical hH hδ hε hαn hd'1 hηb0 hc' hc hI (hDcl _) (hDne t ht)
  -- the sets `Z_t`
  set Z : Fin n → Set ({k // k ∈ I} → Fin n) := fun t =>
    if Function.update b j t ∈ posFull N I then
      canonicalSet (fun k : {k // k ∈ I} => H k) δ ε (faceDefect N E I (Function.update b j t))
    else {z | glue I z (Function.update b j t) ∈ N} with hZ
  have hZcl : ∀ t ∈ vnbrs (H j.1) r, IsClosedSet (canC (1 / 4 - ε) d' * ηb) (Z t) := by
    intro t ht
    by_cases hfull : Function.update b j t ∈ posFull N I
    · rw [hZ]; dsimp only; rw [ite_eq_left hfull]
      exact (hcan t ht).2.2
    · rw [hZ]; dsimp only; rw [ite_eq_right hfull]
      exact (hN.face_closed I _).mono (hκηb.trans hηbμ)
  have hZne : ∀ t ∈ vnbrs (H j.1) r, Z t ≠ Set.univ := by
    intro t ht
    by_cases hfull : Function.update b j t ∈ posFull N I
    · rw [hZ]; dsimp only; rw [ite_eq_left hfull]
      exact (hcan t ht).2.1
    · rw [hZ]; dsimp only; rw [ite_eq_right hfull]
      intro huniv
      apply hfull
      intro z
      have : z ∈ {z | glue I z (Function.update b j t) ∈ N} := by rw [huniv]; trivial
      exact this
  have hX : ∀ t ∈ (vnbrs (H j.1) r).erase t₀, faceRestrict a I (Function.update b j t) ∈
      boxplus (fun k : {k // k ∈ I} => kerCode (H k)) ⊔ supported F (Z t) := by
    intro t ht
    obtain ⟨htne, htV⟩ := Finset.mem_erase.1 ht
    by_cases hfull : Function.update b j t ∈ posFull N I
    · rw [hZ]; dsimp only; rw [ite_eq_left hfull]
      -- `t ∉ T_ℓ`, so the face is decoded
      have htT : t ∉ T := by
        intro htT
        have : t ∈ vnbrs (H j.1) r ∩ T := Finset.mem_inter.2 ⟨htV, htT⟩
        rw [hVT, Finset.mem_singleton] at this
        exact htne this
      by_contra hndec
      apply htT
      rw [hT, Finset.mem_filter, mem_linePts]
      exact ⟨hfull, hgood t htV, hndec⟩
    · rw [hZ]; dsimp only; rw [ite_eq_right hfull]
      exact Submodule.mem_sup_right (supportedIn_faceRestrict hsupp I _)
  have hdec₀ := Step3.faceDecoded_of_route hH hαn hd'1 hD hgen hη1 hE hN ha hsupp hpar hμ0 hF2
    hκD hI j b r ht₀V Z (fun t _ => (hDcl _).mono hηbμ) hDne ((hDcl _).mono hηbD) hZcl hZne hX
  rw [hT, Finset.mem_filter] at ht₀T
  exact ht₀T.2.2 hdec₀

end ProductExpansion
