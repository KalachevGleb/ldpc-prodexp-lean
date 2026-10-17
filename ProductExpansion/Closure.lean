import ProductExpansion.Cube

/-!
# Small closed supersets (`lem:gen-closure`; lemma 18 of Kalachev–Panteleev, FOCS 2025)

For `S ⊆ V^m` and `0 < ε ≤ 1` we construct an `ε`-closed set `M' ⊇ S` with
`|M'| ≤ c_{m,ε} |S|`, `c_{m,ε} = ((2^m + 1)/ε)^m` (`m = |ι|`).

Construction (with `θ = ε / 2^m`): for `I : Finset ι` let `M_I` be the union of the `I`-faces
containing at least `(θ n)^{|I|}` points of `S`, and `M' = ⋃_I M_I`. An `I`-face is described
here as the set of points agreeing with a given point `y` outside `I`
(this is `face I (outer I y)` in the notation of `Cube.lean`).

* `S ⊆ M'`: the `∅`-faces are the points.
* `M'` is `2^m θ`-closed: if a line `ℓ` of direction `j` is not contained in `M'`, then
  `|ℓ ∩ M_I| < θ n` for every `I` (if `j ∈ I`, every `I`-face meeting `ℓ` contains `ℓ`;
  if `j ∉ I`, the heavy `I`-faces meeting `ℓ` are disjoint and lie in one `(I ∪ {j})`-face,
  which would be heavy), so `|ℓ ∩ M'| < 2^m θ n`.
* `|M_I| θ^{|I|} ≤ |S|` by double counting, so `|M'| ≤ (1 + 1/θ)^m |S|`.

Main results: `exists_closed_superset` (and the sharper `exists_closed_superset'`, valid for all
`ε > 0`), and `ncard_closureOf_le` for the smallest `η`-closed superset `[S]_η = closureOf η S`.
-/

open Finset

namespace ProductExpansion

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant `c_{m,η} = ((2^m + 1)/η)^m` of `lem:gen-closure`. -/
noncomputable def closureConst (m : ℕ) (η : ℝ) : ℝ := ((2 ^ m + 1) / η) ^ m

/-- Number of points of `S` in the `I`-face through `y`, i.e. points of `S` agreeing with `y`
outside `I`. -/
def faceCount (S : Finset (ι → Fin n)) (I : Finset ι) (y : ι → Fin n) : ℕ :=
  (S.filter fun s => ∀ i, i ∉ I → s i = y i).card

/-- The `I`-face through `y` is heavy: it contains at least `(θ n)^{|I|}` points of `S`. -/
def Heavy (θ : ℝ) (S : Finset (ι → Fin n)) (I : Finset ι) (y : ι → Fin n) : Prop :=
  (θ * n) ^ I.card ≤ (faceCount S I y : ℝ)

noncomputable instance (θ : ℝ) (S : Finset (ι → Fin n)) (I : Finset ι) (y : ι → Fin n) :
    Decidable (Heavy θ S I y) :=
  inferInstanceAs (Decidable ((θ * n) ^ I.card ≤ (faceCount S I y : ℝ)))

/-- `M' = ⋃_I M_I`: the union of all heavy faces (of all dimensions). -/
noncomputable def heavyClosure (θ : ℝ) (S : Finset (ι → Fin n)) : Finset (ι → Fin n) :=
  Finset.univ.filter fun y => ∃ I : Finset ι, Heavy θ S I y

lemma mem_heavyClosure {θ : ℝ} {S : Finset (ι → Fin n)} {y : ι → Fin n} :
    y ∈ heavyClosure θ S ↔ ∃ I, Heavy θ S I y := by
  simp [heavyClosure]

/-- `lineCount` of a finset, as a `Finset.card`. -/
lemma lineCount_coe (M : Finset (ι → Fin n)) (i : ι) (y : ι → Fin n) :
    lineCount (M : Set (ι → Fin n)) i y = (univ.filter fun t => Function.update y i t ∈ M).card := by
  unfold lineCount
  simp only [Finset.mem_coe]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ### Relation with `face` from `Cube.lean` -/

lemma mem_face_iff_outer {I : Finset ι} {b : {i // i ∉ I} → Fin n} {z : ι → Fin n} :
    z ∈ face I b ↔ outer I z = b := by
  constructor
  · intro hz
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hz
    exact outer_glue I w b
  · intro hz
    exact Finset.mem_image.mpr ⟨inner I z, Finset.mem_univ _, by rw [← hz, glue_inner_outer]⟩

/-- Agreeing with `y` outside `I` means lying in the `I`-face through `y`. -/
lemma agree_outside_iff_mem_face {I : Finset ι} {y z : ι → Fin n} :
    (∀ i, i ∉ I → z i = y i) ↔ z ∈ face I (outer I y) := by
  rw [mem_face_iff_outer]
  constructor
  · intro h; funext i; exact h i.1 i.2
  · intro h i hi; exact congr_fun h ⟨i, hi⟩

lemma faceCount_eq_card_inter_face (S : Finset (ι → Fin n)) (I : Finset ι) (y : ι → Fin n) :
    faceCount S I y = (S ∩ face I (outer I y)).card := by
  unfold faceCount
  rw [← Finset.filter_mem_eq_inter]
  congr 1
  exact Finset.filter_congr fun z _ => agree_outside_iff_mem_face

/-- `heavyClosure θ S` is the union over `I` of `M_I`, the union of the `I`-faces `face I b`
containing at least `(θ n)^{|I|}` points of `S`. -/
lemma mem_heavyClosure_iff_face {θ : ℝ} {S : Finset (ι → Fin n)} {y : ι → Fin n} :
    y ∈ heavyClosure θ S ↔ ∃ (I : Finset ι) (b : {i // i ∉ I} → Fin n),
      y ∈ face I b ∧ (θ * n) ^ I.card ≤ ((S ∩ face I b).card : ℝ) := by
  rw [mem_heavyClosure]
  constructor
  · rintro ⟨I, hI⟩
    refine ⟨I, outer I y, mem_face_iff_outer.mpr rfl, ?_⟩
    unfold Heavy at hI
    rwa [faceCount_eq_card_inter_face] at hI
  · rintro ⟨I, b, hy, hI⟩
    rw [mem_face_iff_outer] at hy
    subst hy
    refine ⟨I, ?_⟩
    unfold Heavy
    rwa [faceCount_eq_card_inter_face]

/-! ### Properties of `heavyClosure` -/

/-- The face count only depends on the face. -/
lemma faceCount_congr (S : Finset (ι → Fin n)) (I : Finset ι) {y z : ι → Fin n}
    (h : ∀ i, i ∉ I → y i = z i) : faceCount S I y = faceCount S I z := by
  unfold faceCount
  congr 1
  apply Finset.filter_congr
  intro s _
  constructor
  · intro hs i hi; rw [hs i hi, h i hi]
  · intro hs i hi; rw [hs i hi, ← h i hi]

lemma one_le_faceCount_empty {S : Finset (ι → Fin n)} {y : ι → Fin n} (hy : y ∈ S) :
    1 ≤ faceCount S ∅ y := by
  unfold faceCount
  apply Finset.card_pos.mpr
  exact ⟨y, by simp [hy]⟩

/-- The `I`-faces through the points of a line of direction `j ∉ I` are disjoint and lie in one
`(insert j I)`-face. -/
lemma sum_faceCount_le (S : Finset (ι → Fin n)) {I : Finset ι} {j : ι} (hj : j ∉ I)
    (y : ι → Fin n) (t₀ : Fin n) (T : Finset (Fin n)) :
    ∑ t ∈ T, faceCount S I (Function.update y j t) ≤
      faceCount S (insert j I) (Function.update y j t₀) := by
  unfold faceCount
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hs ⊢
    obtain ⟨t, -, hsS, hst⟩ := hs
    refine ⟨hsS, fun i hi => ?_⟩
    rw [Finset.mem_insert, not_or] at hi
    rw [hst i hi.2, Function.update_of_ne hi.1, Function.update_of_ne hi.1]
  · intro t₁ _ t₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs1 hs2
    simp only [Finset.mem_filter] at hs1 hs2
    apply hne
    have h1 := hs1.2 j hj
    have h2 := hs2.2 j hj
    rw [Function.update_self] at h1 h2
    rw [← h1, ← h2]

/-- Key estimate: on a line not contained in `M'`, every `M_I` has fewer than `θ n` points. -/
lemma card_heavy_on_line_lt {θ : ℝ} (hθ : 0 < θ) (S : Finset (ι → Fin n)) (j : ι)
    (y : ι → Fin n) (t₀ : Fin n) (h₀ : Function.update y j t₀ ∉ heavyClosure θ S)
    (I : Finset ι) :
    ((univ.filter fun t => Heavy θ S I (Function.update y j t)).card : ℝ) < θ * n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos t₀
  rw [mem_heavyClosure, not_exists] at h₀
  by_cases hj : j ∈ I
  · -- every `I`-face meeting the line contains it
    have hempty : (univ.filter fun t => Heavy θ S I (Function.update y j t)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t _ ht
      apply h₀ I
      unfold Heavy at ht ⊢
      rwa [faceCount_congr S I (y := Function.update y j t₀) (z := Function.update y j t)]
      intro i hi
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rw [Function.update_of_ne hij, Function.update_of_ne hij]
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  · by_contra hcon
    replace hcon := not_lt.mp hcon
    apply h₀ (insert j I)
    unfold Heavy
    set T := univ.filter fun t => Heavy θ S I (Function.update y j t) with hT
    have hpow : (0 : ℝ) ≤ (θ * n) ^ I.card := by positivity
    rw [Finset.card_insert_of_notMem hj, pow_succ]
    calc (θ * n) ^ I.card * (θ * n) ≤ (θ * n) ^ I.card * T.card :=
          mul_le_mul_of_nonneg_left hcon hpow
      _ = ∑ _t ∈ T, (θ * n) ^ I.card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ t ∈ T, (faceCount S I (Function.update y j t) : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht
          exact (Finset.mem_filter.mp ht).2
      _ ≤ (faceCount S (insert j I) (Function.update y j t₀) : ℝ) := by
          exact_mod_cast sum_faceCount_le S hj y t₀ T

/-- `M'` is `2^m θ`-closed. -/
theorem isClosedSet_heavyClosure {θ : ℝ} (hθ : 0 < θ) (S : Finset (ι → Fin n)) :
    IsClosedSet (2 ^ Fintype.card ι * θ) (heavyClosure θ S : Set (ι → Fin n)) := by
  intro j y hcount t
  by_contra ht
  rw [Finset.mem_coe] at ht
  rw [lineCount_coe] at hcount
  have hsub : (univ.filter fun s => Function.update y j s ∈ heavyClosure θ S) ⊆
      univ.biUnion (fun I : Finset ι =>
        univ.filter fun s => Heavy θ S I (Function.update y j s)) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_heavyClosure,
      Finset.mem_biUnion] at hs ⊢
    exact hs
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : (∑ I : Finset ι,
      ((univ.filter fun s => Heavy θ S I (Function.update y j s)).card : ℝ)) <
      ∑ _I : Finset ι, θ * n :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun I _ => card_heavy_on_line_lt hθ S j y t ht I)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul] at h2
  have h1' : ((univ.filter fun s => Function.update y j s ∈ heavyClosure θ S).card : ℝ) ≤
      ∑ I : Finset ι, ((univ.filter fun s => Heavy θ S I (Function.update y j s)).card : ℝ) := by
    exact_mod_cast h1
  push_cast at h2 hcount
  linarith

/-- An `I`-face has at most `n^{|I|}` points. -/
lemma card_face_le (I : Finset ι) (b : ι → Fin n) :
    (univ.filter fun y : ι → Fin n => ∀ i, i ∉ I → b i = y i).card ≤ n ^ I.card := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun y : ι → Fin n =>
      ∀ i, i ∉ I → b i = y i) (t := (univ : Finset ({i // i ∈ I} → Fin n)))
    (fun y => inner I y) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  · rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at h
    exact h
  · intro y hy z hz hyz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy hz
    funext i
    by_cases hi : i ∈ I
    · exact congr_fun hyz ⟨i, hi⟩
    · rw [← hy i hi, ← hz i hi]

/-- Double counting: `|M_I| θ^{|I|} ≤ |S|`. -/
lemma card_heavy_mul_le (θ : ℝ) (hn : 0 < n) (S : Finset (ι → Fin n))
    (I : Finset ι) :
    ((univ.filter (Heavy θ S I)).card : ℝ) * θ ^ I.card ≤ S.card := by
  have key := Finset.card_nsmul_le_card_nsmul (R := ℝ)
    (r := fun y s => ∀ i, i ∉ I → s i = y i)
    (s := univ.filter (Heavy θ S I)) (t := S) (m := (θ * n) ^ I.card) (n := (n : ℝ) ^ I.card)
    ?hm ?hn
  · rw [nsmul_eq_mul, nsmul_eq_mul, mul_pow] at key
    have hnpos : (0 : ℝ) < (n : ℝ) ^ I.card := by positivity
    nlinarith
  · intro y hy
    exact (Finset.mem_filter.mp hy).2
  · intro s _
    have h1 : (Finset.bipartiteBelow (fun y s => ∀ i, i ∉ I → s i = y i)
        (univ.filter (Heavy θ S I)) s).card ≤
        (univ.filter fun y : ι → Fin n => ∀ i, i ∉ I → s i = y i).card := by
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_bipartiteBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      intro i hi
      exact (hy.2 i hi)
    have h2 := card_face_le I s
    exact_mod_cast h1.trans h2

/-- Summing over `I`: `|M'| ≤ (1 + 1/θ)^m |S|`. -/
theorem card_heavyClosure_le {θ : ℝ} (hθ : 0 < θ) (hn : 0 < n) (S : Finset (ι → Fin n)) :
    ((heavyClosure θ S).card : ℝ) ≤ (1 / θ + 1) ^ Fintype.card ι * S.card := by
  have hsub : heavyClosure θ S ⊆ univ.biUnion fun I : Finset ι => univ.filter (Heavy θ S I) := by
    intro y hy
    rw [mem_heavyClosure] at hy
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact hy
  have h1 : ((heavyClosure θ S).card : ℝ) ≤ ∑ I : Finset ι, ((univ.filter (Heavy θ S I)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ I : Finset ι, ((univ.filter (Heavy θ S I)).card : ℝ) ≤
      (1 / θ) ^ I.card * 1 ^ (Fintype.card ι - I.card) * S.card := by
    intro I
    have := card_heavy_mul_le θ hn S I
    have hpos : (0 : ℝ) < θ ^ I.card := by positivity
    rw [one_pow, mul_one, one_div_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
    exact this
  calc ((heavyClosure θ S).card : ℝ) ≤ ∑ I : Finset ι, ((univ.filter (Heavy θ S I)).card : ℝ) := h1
    _ ≤ ∑ I : Finset ι, (1 / θ) ^ I.card * 1 ^ (Fintype.card ι - I.card) * S.card :=
        Finset.sum_le_sum fun I _ => h2 I
    _ = (1 / θ + 1) ^ Fintype.card ι * S.card := by
        rw [← Finset.sum_mul, Fintype.sum_pow_mul_eq_add_pow]

/-- **Closed superset** (sharp form, any `ε > 0`): every `S` is contained in an `ε`-closed `M'`
with `|M'| ≤ (1 + 2^m/ε)^m |S|`. -/
theorem exists_closed_superset' {ε : ℝ} (hε : 0 < ε) (S : Finset (ι → Fin n)) :
    ∃ M : Finset (ι → Fin n), S ⊆ M ∧ IsClosedSet ε (M : Set (ι → Fin n)) ∧
      (M.card : ℝ) ≤ (1 + 2 ^ Fintype.card ι / ε) ^ Fintype.card ι * S.card := by
  have hc : (1 : ℝ) ≤ (1 + 2 ^ Fintype.card ι / ε) ^ Fintype.card ι := by
    apply one_le_pow₀
    have : (0 : ℝ) ≤ 2 ^ Fintype.card ι / ε := by positivity
    linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: there are no lines, `S` itself works
    subst hn
    refine ⟨S, Finset.Subset.refl _, ?_, ?_⟩
    · intro i y _ t
      exact t.elim0
    · have : (0 : ℝ) ≤ S.card := by positivity
      nlinarith
  · set θ := ε / 2 ^ Fintype.card ι with hθdef
    have h2pos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
    have hθ : 0 < θ := by positivity
    refine ⟨heavyClosure θ S, ?_, ?_, ?_⟩
    · intro y hy
      rw [mem_heavyClosure]
      refine ⟨∅, ?_⟩
      unfold Heavy
      rw [Finset.card_empty, pow_zero]
      exact_mod_cast one_le_faceCount_empty hy
    · have := isClosedSet_heavyClosure hθ S
      rwa [hθdef, mul_div_cancel₀ _ h2pos.ne'] at this
    · have := card_heavyClosure_le hθ hn S
      have he : 1 / θ + 1 = 1 + 2 ^ Fintype.card ι / ε := by
        rw [hθdef, one_div_div, add_comm]
      rwa [he] at this

/-- **Closed superset** (`lem:gen-closure`, KP2025 lemma 18): for `0 < ε ≤ 1` every `S` is
contained in an `ε`-closed `M'` with `|M'| ≤ c_{m,ε} |S|`, `c_{m,ε} = ((2^m + 1)/ε)^m`. -/
theorem exists_closed_superset {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (S : Finset (ι → Fin n)) :
    ∃ M : Finset (ι → Fin n), S ⊆ M ∧ IsClosedSet ε (M : Set (ι → Fin n)) ∧
      (M.card : ℝ) ≤ closureConst (Fintype.card ι) ε * S.card := by
  obtain ⟨M, hSM, hcl, hcard⟩ := exists_closed_superset' hε0 S
  refine ⟨M, hSM, hcl, hcard.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold closureConst
  apply pow_le_pow_left₀ (by positivity)
  have h1 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
  rw [add_div]
  linarith

/-! ### The smallest closed superset `[S]_η` -/

omit [Fintype ι] in
lemma lineCount_mono {S T : Set (ι → Fin n)} (h : S ⊆ T) (i : ι) (y : ι → Fin n) :
    lineCount S i y ≤ lineCount T i y :=
  Nat.card_le_card_of_injective (fun t => ⟨t.1, h t.2⟩)
    (fun _ _ hab => Subtype.ext (Subtype.mk.inj hab))

/-- `[S]_η`: the smallest `η`-closed set containing `S` (intersection of all of them). -/
def closureOf (η : ℝ) (S : Set (ι → Fin n)) : Set (ι → Fin n) :=
  ⋂₀ {M | S ⊆ M ∧ IsClosedSet η M}

omit [Fintype ι] in
lemma subset_closureOf (η : ℝ) (S : Set (ι → Fin n)) : S ⊆ closureOf η S :=
  Set.subset_sInter fun _ hM => hM.1

omit [Fintype ι] in
lemma closureOf_subset {η : ℝ} {S M : Set (ι → Fin n)} (hSM : S ⊆ M) (hM : IsClosedSet η M) :
    closureOf η S ⊆ M :=
  Set.sInter_subset_of_mem ⟨hSM, hM⟩

omit [Fintype ι] in
/-- An intersection of `η`-closed sets is `η`-closed (F1), so `[S]_η` is `η`-closed. -/
lemma isClosedSet_closureOf (η : ℝ) (S : Set (ι → Fin n)) : IsClosedSet η (closureOf η S) := by
  intro i y hcount t
  refine Set.mem_sInter.mpr fun M hM => hM.2 i y ?_ t
  exact hcount.trans (by exact_mod_cast lineCount_mono (Set.sInter_subset_of_mem hM) i y)

/-- `lem:gen-closure` in the form used in the proof: `|[S]_η| ≤ c_{m,η} |S|` for `0 < η ≤ 1`. -/
theorem ncard_closureOf_le {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (S : Finset (ι → Fin n)) :
    ((closureOf η (S : Set (ι → Fin n))).ncard : ℝ) ≤
      closureConst (Fintype.card ι) η * S.card := by
  obtain ⟨M, hSM, hcl, hcard⟩ := exists_closed_superset hη0 hη1 S
  have h := Set.ncard_le_ncard (closureOf_subset (Finset.coe_subset.mpr hSM) hcl) M.finite_toSet
  rw [Set.ncard_coe_finset] at h
  exact le_trans (by exact_mod_cast h) hcard

end ProductExpansion
