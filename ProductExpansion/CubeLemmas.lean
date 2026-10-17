import ProductExpansion.Cube

/-!
# Cube lemmas: faces, lines, hyperplane slices, closed sets (F1)–(F3)

Notation follows the conventions of the proof.

* `glue`/`inner`/`outer`/`face`: interaction with `Function.update` and with lines
  (`line_subset_face`: a line of direction `i ∈ I` through a point of an `I`-face lies in it;
  `eq_of_update_mem_face`, `card_line_inter_face_le_one`: a line of direction `j ∉ I` meets an
  `I`-face in at most one point).
* `lineCount` via `Set.ncard`: `lineCount_eq_ncard`, `lineCount_union_le`, `lineCount_eq_iff`.
* (F1) `IsClosedSet.inter`, `IsClosedSet.iInter`, `IsClosedSet.union`, `IsClosedSet.biUnion`
  (`∑ ηⱼ`), `IsClosedSet.biUnion_const` (`k η`); Dirichlet: `IsClosedSet.full_line_of_union`,
  `IsClosedSet.exists_full_line_of_biUnion` (`∑ ηⱼ ≤ 1`),
  `IsClosedSet.exists_full_line_of_biUnion'` (`k ηⱼ ≤ 1`).
* Hyperplanes: `hglue i u z` is the point with `y_i = u` and the other coordinates
  `z : {j // j ≠ i} → Fin n`; `hproj i y`; `sliceSet S i u = S|_{y_i = u}`;
  `IsClosedSet.sliceSet_closed`.
* (F2) `IsClosedSet.ncard_le` (`|S| ≤ d η n^d`), `IsClosedSet.ncard_lt` (`|S| < d η n^d` for
  `d ≥ 1`), and the form in which it is used: `biUnion_ne_univ_of_isClosedSet`.
* (F3) `IsClosedSet.posFull_closed`, `posFull_ne_univ`.
* Restriction of words to faces: `faceRestrictLin`, `faceRestrict_mem_colCode`, line codewords
  (`IsLineCodeword.mem_colCode`, `IsLineCodeword.faceRestrict_of_mem`, ...), `lineSpan_le_boxplus`,
  and `faceRestrict_mem_lineSpan_sup`: the restriction of `w ∈ L(M)` to a face.
* Subcube embeddings `IsSubcubeEmb φ Ψ` (faces, hyperplanes, faces of hyperplanes, ...) with the
  general restriction lemma `IsSubcubeEmb.comp_mem_lineSpan_sup`.
* `IsClosedSet.setOf_full_line`: the points on full `j`-lines of a closed set form a closed set.
-/

open Finset Function

namespace ProductExpansion

variable {n : ℕ} {ι : Type*} [DecidableEq ι]

/-! ### `glue`, `inner`, `outer` and `Function.update` -/

section Glue

variable (I : Finset ι)

@[simp] lemma glue_apply_of_mem (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n)
    {i : ι} (hi : i ∈ I) : glue I z b i = z ⟨i, hi⟩ := by
  simp [glue, hi]

@[simp] lemma glue_apply_of_not_mem (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n)
    {i : ι} (hi : i ∉ I) : glue I z b i = b ⟨i, hi⟩ := by
  simp [glue, hi]

lemma glue_apply_val_mem (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n)
    (i : {i // i ∈ I}) : glue I z b i.1 = z i :=
  glue_apply_of_mem I z b i.2

lemma glue_apply_val_not_mem (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n)
    (i : {i // i ∉ I}) : glue I z b i.1 = b i :=
  glue_apply_of_not_mem I z b i.2

omit [DecidableEq ι] in
@[simp] lemma inner_apply (y : ι → Fin n) (i : {i // i ∈ I}) : inner I y i = y i.1 := rfl

omit [DecidableEq ι] in
@[simp] lemma outer_apply (y : ι → Fin n) (i : {i // i ∉ I}) : outer I y i = y i.1 := rfl

/-! Versions of `inner_glue`, `outer_glue`, `glue_inner_outer` without `[Fintype ι]`. -/

@[simp] lemma inner_glue' (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n) :
    inner I (glue I z b) = z := by
  funext i; simp [glue, inner, i.2]

@[simp] lemma outer_glue' (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n) :
    outer I (glue I z b) = b := by
  funext i; simp [glue, outer, i.2]

@[simp] lemma glue_inner_outer' (y : ι → Fin n) : glue I (inner I y) (outer I y) = y := by
  funext i; by_cases h : i ∈ I <;> simp [glue, inner, outer, h]

lemma glue_injective_left (b : {i // i ∉ I} → Fin n) :
    Function.Injective fun z : {i // i ∈ I} → Fin n => glue I z b := by
  intro z z' h
  have := congrArg (inner I) h
  simpa using this

lemma glue_inj {z z' : {i // i ∈ I} → Fin n} {b b' : {i // i ∉ I} → Fin n} :
    glue I z b = glue I z' b' ↔ z = z' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (inner I) h, by simpa using congrArg (outer I) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma eq_glue_iff {y : ι → Fin n} {z : {i // i ∈ I} → Fin n} {b : {i // i ∉ I} → Fin n} :
    y = glue I z b ↔ inner I y = z ∧ outer I y = b := by
  constructor
  · rintro rfl; simp
  · rintro ⟨rfl, rfl⟩; simp

/-- Updating an inner coordinate of a glued point. -/
lemma glue_update_inner (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n)
    (j : {i // i ∈ I}) (t : Fin n) :
    glue I (Function.update z j t) b = Function.update (glue I z b) j.1 t := by
  funext k
  by_cases hk : k ∈ I
  · rw [glue_apply_of_mem I _ _ hk]
    by_cases hkj : k = j.1
    · subst hkj; simp
    · rw [Function.update_of_ne hkj, Function.update_of_ne (fun h => hkj (congrArg Subtype.val h)),
        glue_apply_of_mem I _ _ hk]
  · have hkj : k ≠ j.1 := fun h => hk (h ▸ j.2)
    rw [glue_apply_of_not_mem I _ _ hk, Function.update_of_ne hkj, glue_apply_of_not_mem I _ _ hk]

/-- Updating an outer coordinate of a glued point. -/
lemma glue_update_outer (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n)
    (j : {i // i ∉ I}) (t : Fin n) :
    glue I z (Function.update b j t) = Function.update (glue I z b) j.1 t := by
  funext k
  by_cases hk : k ∈ I
  · have hkj : k ≠ j.1 := fun h => j.2 (h ▸ hk)
    rw [glue_apply_of_mem I _ _ hk, Function.update_of_ne hkj, glue_apply_of_mem I _ _ hk]
  · rw [glue_apply_of_not_mem I _ _ hk]
    by_cases hkj : k = j.1
    · subst hkj; simp
    · rw [Function.update_of_ne hkj, Function.update_of_ne (fun h => hkj (congrArg Subtype.val h)),
        glue_apply_of_not_mem I _ _ hk]

lemma update_glue_of_mem (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n)
    {i : ι} (hi : i ∈ I) (t : Fin n) :
    Function.update (glue I z b) i t = glue I (Function.update z ⟨i, hi⟩ t) b :=
  (glue_update_inner I z b ⟨i, hi⟩ t).symm

lemma update_glue_of_not_mem (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n)
    {i : ι} (hi : i ∉ I) (t : Fin n) :
    Function.update (glue I z b) i t = glue I z (Function.update b ⟨i, hi⟩ t) :=
  (glue_update_outer I z b ⟨i, hi⟩ t).symm

lemma outer_update_of_mem (y : ι → Fin n) {i : ι} (hi : i ∈ I) (t : Fin n) :
    outer I (Function.update y i t) = outer I y := by
  funext k
  have : k.1 ≠ i := fun h => k.2 (h ▸ hi)
  simp [outer, Function.update_of_ne this]

lemma inner_update_of_not_mem (y : ι → Fin n) {i : ι} (hi : i ∉ I) (t : Fin n) :
    inner I (Function.update y i t) = inner I y := by
  funext k
  have : k.1 ≠ i := fun h => hi (h ▸ k.2)
  simp [inner, Function.update_of_ne this]

lemma inner_update_of_mem (y : ι → Fin n) {i : ι} (hi : i ∈ I) (t : Fin n) :
    inner I (Function.update y i t) = Function.update (inner I y) ⟨i, hi⟩ t := by
  conv_lhs => rw [← glue_inner_outer' I y, update_glue_of_mem I _ _ hi]
  simp

lemma outer_update_of_not_mem (y : ι → Fin n) {i : ι} (hi : i ∉ I) (t : Fin n) :
    outer I (Function.update y i t) = Function.update (outer I y) ⟨i, hi⟩ t := by
  conv_lhs => rw [← glue_inner_outer' I y, update_glue_of_not_mem I _ _ hi]
  simp

end Glue

/-! ### Faces and lines -/

section FaceLine

variable [Fintype ι]

lemma mem_line_iff {i : ι} {y x : ι → Fin n} : x ∈ line i y ↔ ∃ t, Function.update y i t = x := by
  simp [line]

lemma update_mem_line (i : ι) (y : ι → Fin n) (t : Fin n) : Function.update y i t ∈ line i y :=
  mem_line_iff.2 ⟨t, rfl⟩

lemma mem_line_self (i : ι) (y : ι → Fin n) : y ∈ line i y :=
  mem_line_iff.2 ⟨y i, by simp⟩

lemma mem_face_iff {I : Finset ι} {b : {i // i ∉ I} → Fin n} {y : ι → Fin n} :
    y ∈ face I b ↔ outer I y = b := by
  simp only [face, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, rfl⟩; simp
  · rintro rfl; exact ⟨inner I y, by simp⟩

lemma glue_mem_face (I : Finset ι) (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n) :
    glue I z b ∈ face I b :=
  mem_face_iff.2 (by simp)

/-- A line of direction `i ∈ I` through a point of an `I`-face lies in that face. -/
lemma update_mem_face_of_mem {I : Finset ι} {b : {i // i ∉ I} → Fin n} {y : ι → Fin n}
    (hy : y ∈ face I b) {i : ι} (hi : i ∈ I) (t : Fin n) : Function.update y i t ∈ face I b := by
  rw [mem_face_iff] at hy ⊢
  rw [outer_update_of_mem I y hi, hy]

lemma line_subset_face {I : Finset ι} {b : {i // i ∉ I} → Fin n} {y : ι → Fin n}
    (hy : y ∈ face I b) {i : ι} (hi : i ∈ I) : line i y ⊆ face I b := by
  intro x hx
  obtain ⟨t, rfl⟩ := mem_line_iff.1 hx
  exact update_mem_face_of_mem hy hi t

/-- A line of direction `j ∉ I` meets an `I`-face in at most one point. -/
lemma eq_of_update_mem_face {I : Finset ι} {b : {i // i ∉ I} → Fin n} {y : ι → Fin n}
    {j : ι} (hj : j ∉ I) {t t' : Fin n} (ht : Function.update y j t ∈ face I b)
    (ht' : Function.update y j t' ∈ face I b) : t = t' := by
  rw [mem_face_iff] at ht ht'
  have h1 := congrFun ht ⟨j, hj⟩
  have h2 := congrFun ht' ⟨j, hj⟩
  simp only [outer_apply, Function.update_self] at h1 h2
  rw [h1, h2]

lemma card_line_inter_face_le_one {I : Finset ι} (b : {i // i ∉ I} → Fin n) (y : ι → Fin n)
    {j : ι} (hj : j ∉ I) : (line j y ∩ face I b).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx x' hx'
  rw [Finset.mem_inter] at hx hx'
  obtain ⟨t, rfl⟩ := mem_line_iff.1 hx.1
  obtain ⟨t', rfl⟩ := mem_line_iff.1 hx'.1
  rw [eq_of_update_mem_face hj hx.2 hx'.2]

end FaceLine

/-! ### Line counts -/

section LineCount

lemma lineCount_eq_ncard (S : Set (ι → Fin n)) (i : ι) (y : ι → Fin n) :
    lineCount S i y = {t : Fin n | Function.update y i t ∈ S}.ncard := rfl

lemma lineCount_le (S : Set (ι → Fin n)) (i : ι) (y : ι → Fin n) : lineCount S i y ≤ n := by
  rw [lineCount_eq_ncard]
  simpa using Set.ncard_le_card {t : Fin n | Function.update y i t ∈ S}

lemma lineCount_le_of_subset {S T : Set (ι → Fin n)} (h : S ⊆ T) (i : ι) (y : ι → Fin n) :
    lineCount S i y ≤ lineCount T i y := by
  rw [lineCount_eq_ncard, lineCount_eq_ncard]
  exact Set.ncard_le_ncard (fun t ht => h ht)

lemma lineCount_union_le (S T : Set (ι → Fin n)) (i : ι) (y : ι → Fin n) :
    lineCount (S ∪ T) i y ≤ lineCount S i y + lineCount T i y := by
  rw [lineCount_eq_ncard, lineCount_eq_ncard, lineCount_eq_ncard]
  exact Set.ncard_union_le _ _

lemma lineCount_biUnion_le {κ : Type*} (s : Finset κ) (S : κ → Set (ι → Fin n)) (i : ι)
    (y : ι → Fin n) :
    lineCount (⋃ j ∈ s, S j) i y ≤ ∑ j ∈ s, lineCount (S j) i y := by
  rw [lineCount_eq_ncard]
  have : {t : Fin n | Function.update y i t ∈ ⋃ j ∈ s, S j} =
      ⋃ j ∈ s, {t : Fin n | Function.update y i t ∈ S j} := by
    ext t; simp
  rw [this]
  exact Finset.set_ncard_biUnion_le s _

/-- A line is full in `S` iff it has `n` points of `S`. -/
lemma lineCount_eq_iff (S : Set (ι → Fin n)) (i : ι) (y : ι → Fin n) :
    lineCount S i y = n ↔ ∀ t, Function.update y i t ∈ S := by
  rw [lineCount_eq_ncard]
  have h := Set.eq_univ_iff_ncard {t : Fin n | Function.update y i t ∈ S}
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  rw [← h, Set.eq_univ_iff_forall]
  simp

lemma lineCount_of_full {S : Set (ι → Fin n)} {i : ι} {y : ι → Fin n}
    (h : ∀ t, Function.update y i t ∈ S) : lineCount S i y = n :=
  (lineCount_eq_iff S i y).2 h

@[simp] lemma lineCount_update_self (S : Set (ι → Fin n)) (i : ι) (y : ι → Fin n) (t : Fin n) :
    lineCount S i (Function.update y i t) = lineCount S i y := by
  simp [lineCount]

end LineCount

/-! ### Closed sets: (F1) -/

section Closed

variable {η η₁ η₂ η' : ℝ} {S T : Set (ι → Fin n)}

lemma IsClosedSet.full {S : Set (ι → Fin n)} (hS : IsClosedSet η S) {i : ι} {y : ι → Fin n}
    (h : η * n ≤ lineCount S i y) (t : Fin n) : Function.update y i t ∈ S :=
  hS i y h t

/-- A line not contained in an `η`-closed set has fewer than `η n` of its points. -/
lemma IsClosedSet.lineCount_lt (hS : IsClosedSet η S) {i : ι} {y : ι → Fin n}
    (h : ¬ ∀ t, Function.update y i t ∈ S) : (lineCount S i y : ℝ) < η * n := by
  by_contra h'
  exact h (hS i y (not_lt.1 h'))

lemma IsClosedSet.mono (hS : IsClosedSet η S) (h : η ≤ η') : IsClosedSet η' S :=
  fun i y hy => hS i y (le_trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n)) hy)

lemma isClosedSet_univ (η : ℝ) : IsClosedSet η (Set.univ : Set (ι → Fin n)) :=
  fun _ _ _ _ => trivial

lemma isClosedSet_empty (hη : 0 < η) : IsClosedSet η (∅ : Set (ι → Fin n)) := by
  intro i y hy t
  have h0 : lineCount (∅ : Set (ι → Fin n)) i y = 0 := by
    rw [lineCount_eq_ncard]; simp
  rw [h0, Nat.cast_zero] at hy
  have hn : (n : ℝ) ≤ 0 := by
    by_contra h; push Not at h; linarith [mul_pos hη h]
  have : n = 0 := by exact_mod_cast le_antisymm hn (Nat.cast_nonneg n)
  subst this
  exact t.elim0

/-- (F1) The intersection of two `η`-closed sets is `η`-closed. -/
lemma IsClosedSet.inter (hS : IsClosedSet η S) (hT : IsClosedSet η T) :
    IsClosedSet η (S ∩ T) := by
  intro i y hy t
  exact ⟨hS i y (hy.trans (by exact_mod_cast lineCount_le_of_subset Set.inter_subset_left i y)) t,
    hT i y (hy.trans (by exact_mod_cast lineCount_le_of_subset Set.inter_subset_right i y)) t⟩

/-- (F1) The intersection of any family of `η`-closed sets is `η`-closed. -/
lemma IsClosedSet.iInter {κ : Sort*} {S : κ → Set (ι → Fin n)} (h : ∀ k, IsClosedSet η (S k)) :
    IsClosedSet η (⋂ k, S k) := by
  intro i y hy t
  rw [Set.mem_iInter]
  intro k
  exact h k i y (hy.trans (by exact_mod_cast lineCount_le_of_subset (Set.iInter_subset S k) i y)) t

/-- (F1) The intersection of a (finite or not) indexed family of `η`-closed sets. -/
lemma IsClosedSet.biInter {κ : Type*} {s : Set κ} {S : κ → Set (ι → Fin n)}
    (h : ∀ k ∈ s, IsClosedSet η (S k)) : IsClosedSet η (⋂ k ∈ s, S k) :=
  IsClosedSet.iInter fun k => IsClosedSet.iInter fun hk => h k hk

/-- (F1) The union of an `η₁`-closed and an `η₂`-closed set is `(η₁ + η₂)`-closed. -/
lemma IsClosedSet.union (hS : IsClosedSet η₁ S) (hT : IsClosedSet η₂ T) :
    IsClosedSet (η₁ + η₂) (S ∪ T) := by
  intro i y hy
  by_cases h1 : ∀ t, Function.update y i t ∈ S
  · exact fun t => Or.inl (h1 t)
  by_cases h2 : ∀ t, Function.update y i t ∈ T
  · exact fun t => Or.inr (h2 t)
  exfalso
  have l1 := hS.lineCount_lt h1
  have l2 := hT.lineCount_lt h2
  have l3 : (lineCount (S ∪ T) i y : ℝ) ≤ lineCount S i y + lineCount T i y := by
    exact_mod_cast lineCount_union_le S T i y
  nlinarith

/-- (F1) The union of a nonempty finite family of `ηⱼ`-closed sets is `(∑ ηⱼ)`-closed. -/
lemma IsClosedSet.biUnion {κ : Type*} {s : Finset κ} (hs : s.Nonempty) {η : κ → ℝ}
    {S : κ → Set (ι → Fin n)} (h : ∀ j ∈ s, IsClosedSet (η j) (S j)) :
    IsClosedSet (∑ j ∈ s, η j) (⋃ j ∈ s, S j) := by
  intro i y hy
  by_cases hfull : ∃ j ∈ s, ∀ t, Function.update y i t ∈ S j
  · obtain ⟨j, hj, hjt⟩ := hfull
    intro t
    exact Set.mem_biUnion hj (hjt t)
  exfalso
  push Not at hfull
  have hlt : ∀ j ∈ s, (lineCount (S j) i y : ℝ) < η j * n := by
    intro j hj
    exact (h j hj).lineCount_lt (by
      obtain ⟨t, ht⟩ := hfull j hj
      exact fun h' => ht (h' t))
  have h1 : (lineCount (⋃ j ∈ s, S j) i y : ℝ) ≤ ∑ j ∈ s, (lineCount (S j) i y : ℝ) := by
    exact_mod_cast lineCount_biUnion_le s S i y
  have h2 : ∑ j ∈ s, (lineCount (S j) i y : ℝ) < ∑ j ∈ s, η j * n :=
    Finset.sum_lt_sum_of_nonempty hs hlt
  rw [← Finset.sum_mul] at h2
  linarith

/-- (F1), version allowing an empty family: the union is `η'`-closed for any `η' > 0`
with `∑ ηⱼ ≤ η'`. -/
lemma IsClosedSet.biUnion_of_le {κ : Type*} {s : Finset κ} {η : κ → ℝ}
    {S : κ → Set (ι → Fin n)} (h : ∀ j ∈ s, IsClosedSet (η j) (S j)) (hpos : 0 < η')
    (hsum : ∑ j ∈ s, η j ≤ η') : IsClosedSet η' (⋃ j ∈ s, S j) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using isClosedSet_empty (ι := ι) (n := n) hpos
  · exact (IsClosedSet.biUnion hs h).mono hsum

/-- (F1) The union of a nonempty finite family of `η`-closed sets is `(k η)`-closed. -/
lemma IsClosedSet.biUnion_const {κ : Type*} {s : Finset κ} (hs : s.Nonempty)
    {S : κ → Set (ι → Fin n)} (h : ∀ j ∈ s, IsClosedSet η (S j)) :
    IsClosedSet (s.card * η) (⋃ j ∈ s, S j) := by
  have := IsClosedSet.biUnion hs (η := fun _ => η) h
  simpa [Finset.sum_const, nsmul_eq_mul] using this

/-- (F1, Dirichlet) If `S` is `η₁`-closed, `T` is `η₂`-closed and `η₁ + η₂ ≤ 1`, then every
full line of `S ∪ T` lies in `S` or in `T`. -/
lemma IsClosedSet.full_line_of_union (hS : IsClosedSet η₁ S) (hT : IsClosedSet η₂ T)
    (h : η₁ + η₂ ≤ 1) {i : ι} {y : ι → Fin n} (hfull : ∀ t, Function.update y i t ∈ S ∪ T) :
    (∀ t, Function.update y i t ∈ S) ∨ (∀ t, Function.update y i t ∈ T) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩⟩ := hc
  have l1 := hS.lineCount_lt (fun h' => ht1 (h' t1))
  have l2 := hT.lineCount_lt (fun h' => ht2 (h' t2))
  have l3 : (lineCount (S ∪ T) i y : ℝ) ≤ lineCount S i y + lineCount T i y := by
    exact_mod_cast lineCount_union_le S T i y
  have l4 : (lineCount (S ∪ T) i y : ℝ) = n := by exact_mod_cast lineCount_of_full hfull
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- (F1, Dirichlet) If `Sⱼ` is `ηⱼ`-closed (`j ∈ s`) and `∑ ηⱼ ≤ 1`, then every full line of
`⋃ Sⱼ` lies in one of the `Sⱼ`. -/
lemma IsClosedSet.exists_full_line_of_biUnion (hn : 0 < n) {κ : Type*} {s : Finset κ}
    {η : κ → ℝ} {S : κ → Set (ι → Fin n)} (h : ∀ j ∈ s, IsClosedSet (η j) (S j))
    (hsum : ∑ j ∈ s, η j ≤ 1) {i : ι} {y : ι → Fin n}
    (hfull : ∀ t, Function.update y i t ∈ ⋃ j ∈ s, S j) :
    ∃ j ∈ s, ∀ t, Function.update y i t ∈ S j := by
  by_contra hc
  push Not at hc
  have hlt : ∀ j ∈ s, (lineCount (S j) i y : ℝ) < η j * n := by
    intro j hj
    exact (h j hj).lineCount_lt (by
      obtain ⟨t, ht⟩ := hc j hj
      exact fun h' => ht (h' t))
  have h1 : (lineCount (⋃ j ∈ s, S j) i y : ℝ) ≤ ∑ j ∈ s, (lineCount (S j) i y : ℝ) := by
    exact_mod_cast lineCount_biUnion_le s S i y
  have h3 : (lineCount (⋃ j ∈ s, S j) i y : ℝ) = n := by exact_mod_cast lineCount_of_full hfull
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact absurd (hfull ⟨0, hn⟩) (by simp)
  · have h2 : ∑ j ∈ s, (lineCount (S j) i y : ℝ) < ∑ j ∈ s, η j * n :=
      Finset.sum_lt_sum_of_nonempty hs hlt
    rw [← Finset.sum_mul] at h2
    nlinarith

/-- (F1, by the pigeonhole principle) If `Sⱼ` is `ηⱼ`-closed (`j ∈ s`, `|s| = k`) and
`ηⱼ ≤ 1/k` for all `j`, then every full line of `⋃ Sⱼ` lies in one of the `Sⱼ`. -/
lemma IsClosedSet.exists_full_line_of_biUnion' (hn : 0 < n) {κ : Type*} {s : Finset κ}
    {η : κ → ℝ} {S : κ → Set (ι → Fin n)} (h : ∀ j ∈ s, IsClosedSet (η j) (S j))
    (hmax : ∀ j ∈ s, (s.card : ℝ) * η j ≤ 1) {i : ι} {y : ι → Fin n}
    (hfull : ∀ t, Function.update y i t ∈ ⋃ j ∈ s, S j) :
    ∃ j ∈ s, ∀ t, Function.update y i t ∈ S j := by
  refine IsClosedSet.exists_full_line_of_biUnion hn h ?_ hfull
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have hk : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
    calc ∑ j ∈ s, η j ≤ ∑ _j ∈ s, (1 / (s.card : ℝ)) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [le_div_iff₀ hk]; linarith [hmax j hj]
      _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp

/-- The set of points lying on a full line of direction `j` of an `η`-closed set is
`η`-closed. -/
lemma IsClosedSet.setOf_full_line (hS : IsClosedSet η S) (j : ι) :
    IsClosedSet η {y | ∀ t, Function.update y j t ∈ S} := by
  intro k y hy s t
  by_cases hηn : η * n ≤ 0
  · -- then every point lies in `S`
    have hall : ∀ x : ι → Fin n, x ∈ S := fun x => by
      have := hS j x (le_trans hηn (Nat.cast_nonneg _)) (x j)
      simpa using this
    exact hall _
  push Not at hηn
  by_cases hkj : k = j
  · subst hkj
    -- some point of the line lies on a full `k`-line, which is the line itself
    have hpos : 0 < lineCount {y | ∀ t, Function.update y k t ∈ S} k y := by
      have : (0 : ℝ) < lineCount {y | ∀ t, Function.update y k t ∈ S} k y := lt_of_lt_of_le hηn hy
      exact_mod_cast this
    rw [lineCount_eq_ncard] at hpos
    obtain ⟨s₀, hs₀⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.1 hpos)
    simp only [Set.mem_ofPred_eq, Function.update_idem] at hs₀
    rw [Function.update_idem]
    exact hs₀ t
  · -- every `k`-line through `update y j t` has at least `η n` points of `S`
    have hcount : (lineCount {y | ∀ t, Function.update y j t ∈ S} k y : ℝ) ≤
        lineCount S k (Function.update y j t) := by
      have : lineCount {y | ∀ t, Function.update y j t ∈ S} k y ≤
          lineCount S k (Function.update y j t) := by
        rw [lineCount_eq_ncard, lineCount_eq_ncard]
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        intro s' hs'
        simp only [Set.mem_ofPred_eq] at hs' ⊢
        rw [Function.update_comm (Ne.symm hkj)]
        exact hs' t
      exact_mod_cast this
    have := hS k _ (hy.trans hcount) s
    rwa [Function.update_comm (Ne.symm hkj)] at this

end Closed

/-! ### Hyperplanes `{y_i = u}` and slices -/

section Hyperplane

/-- The point of the cube with `i`-th coordinate `u` and remaining coordinates `z`
(`z` is a point of the cube `{j // j ≠ i} → Fin n` of the hyperplane). -/
def hglue (i : ι) (u : Fin n) (z : {j // j ≠ i} → Fin n) : ι → Fin n :=
  fun j => if h : j = i then u else z ⟨j, h⟩

/-- The coordinates of `y` other than the `i`-th one. -/
def hproj (i : ι) (y : ι → Fin n) : {j // j ≠ i} → Fin n := fun j => y j.1

/-- `S|_{y_i = u}`: the slice of a set by the hyperplane `{y_i = u}`, as a subset of the
cube `{j // j ≠ i} → Fin n`. -/
def sliceSet (S : Set (ι → Fin n)) (i : ι) (u : Fin n) : Set ({j // j ≠ i} → Fin n) :=
  {z | hglue i u z ∈ S}

variable {i : ι} {u : Fin n} {z : {j // j ≠ i} → Fin n}

@[simp] lemma hglue_apply_self : hglue i u z i = u := by simp [hglue]

@[simp] lemma hglue_apply_val (j : {j // j ≠ i}) : hglue i u z j.1 = z j := by
  simp [hglue, j.2]

lemma hglue_apply_of_ne {j : ι} (h : j ≠ i) : hglue i u z j = z ⟨j, h⟩ := by
  simp [hglue, h]

omit [DecidableEq ι] in
@[simp] lemma hproj_apply (y : ι → Fin n) (j : {j // j ≠ i}) : hproj i y j = y j.1 := rfl

@[simp] lemma hproj_hglue : hproj i (hglue i u z) = z := by
  funext j; simp

@[simp] lemma hglue_hproj (y : ι → Fin n) : hglue i (y i) (hproj i y) = y := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [hglue_apply_of_ne h]

lemma hglue_hproj_eq_update (y : ι → Fin n) (t : Fin n) :
    hglue i t (hproj i y) = Function.update y i t := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [hglue_apply_of_ne h, Function.update_of_ne h]

lemma eq_hglue_iff {y : ι → Fin n} : y = hglue i u z ↔ y i = u ∧ hproj i y = z := by
  constructor
  · rintro rfl; simp
  · rintro ⟨rfl, rfl⟩; simp

lemma hglue_inj {u' : Fin n} {z' : {j // j ≠ i} → Fin n} :
    hglue i u z = hglue i u' z' ↔ u = u' ∧ z = z' := by
  rw [eq_hglue_iff]; simp

@[simp] lemma update_hglue_self (t : Fin n) :
    Function.update (hglue i u z) i t = hglue i t z := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [hglue_apply_of_ne h, Function.update_of_ne h]

lemma hglue_update (j : {j // j ≠ i}) (t : Fin n) :
    hglue i u (Function.update z j t) = Function.update (hglue i u z) j.1 t := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [hglue_apply_self, Function.update_of_ne (Ne.symm j.2), hglue_apply_self]
  · rw [hglue_apply_of_ne hk]
    by_cases hkj : k = j.1
    · subst hkj; simp
    · rw [Function.update_of_ne (fun h => hkj (congrArg Subtype.val h)),
        Function.update_of_ne hkj, hglue_apply_of_ne hk]

lemma update_hglue (j : {j // j ≠ i}) (t : Fin n) :
    Function.update (hglue i u z) j.1 t = hglue i u (Function.update z j t) :=
  (hglue_update j t).symm

@[simp] lemma hproj_update_self (y : ι → Fin n) (t : Fin n) :
    hproj i (Function.update y i t) = hproj i y := by
  funext j; simp [Function.update_of_ne j.2]

lemma hproj_update (y : ι → Fin n) (j : {j // j ≠ i}) (t : Fin n) :
    hproj i (Function.update y j.1 t) = Function.update (hproj i y) j t := by
  conv_lhs => rw [← hglue_hproj (i := i) y, update_hglue]
  simp

@[simp] lemma mem_sliceSet {S : Set (ι → Fin n)} : z ∈ sliceSet S i u ↔ hglue i u z ∈ S :=
  Iff.rfl

lemma sliceSet_mono {S T : Set (ι → Fin n)} (h : S ⊆ T) (i : ι) (u : Fin n) :
    sliceSet S i u ⊆ sliceSet T i u := fun _ hz => h hz

@[simp] lemma sliceSet_univ (i : ι) (u : Fin n) :
    sliceSet (Set.univ : Set (ι → Fin n)) i u = Set.univ := rfl

@[simp] lemma sliceSet_empty (i : ι) (u : Fin n) :
    sliceSet (∅ : Set (ι → Fin n)) i u = ∅ := rfl

lemma sliceSet_union (S T : Set (ι → Fin n)) (i : ι) (u : Fin n) :
    sliceSet (S ∪ T) i u = sliceSet S i u ∪ sliceSet T i u := rfl

lemma sliceSet_inter (S T : Set (ι → Fin n)) (i : ι) (u : Fin n) :
    sliceSet (S ∩ T) i u = sliceSet S i u ∩ sliceSet T i u := rfl

/-- Lines of the hyperplane are lines of the cube. -/
lemma lineCount_sliceSet (S : Set (ι → Fin n)) (j : {j // j ≠ i}) :
    lineCount (sliceSet S i u) j z = lineCount S j.1 (hglue i u z) := by
  simp only [lineCount, mem_sliceSet, hglue_update]

/-- A slice of an `η`-closed set is `η`-closed. -/
lemma IsClosedSet.sliceSet_closed {η : ℝ} {S : Set (ι → Fin n)} (hS : IsClosedSet η S) (i : ι)
    (u : Fin n) : IsClosedSet η (sliceSet S i u) := by
  intro j z hz t
  rw [lineCount_sliceSet] at hz
  rw [mem_sliceSet, hglue_update]
  exact hS j.1 _ hz t

end Hyperplane

/-! ### (F2): proper closed sets are small -/

section Small

variable [Fintype ι]

omit [DecidableEq ι] in
lemma card_cube : Nat.card (ι → Fin n) = n ^ Fintype.card ι := by
  simp [Nat.card_fun]

lemma card_ne (i : ι) : Fintype.card {j // j ≠ i} = Fintype.card ι - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [Fintype ι] in
/-- A proper `η`-closed set in a cube of positive dimension forces `η > 0` and `n > 0`. -/
lemma IsClosedSet.pos_of_ne_univ [Nonempty ι] {η : ℝ} {S : Set (ι → Fin n)}
    (hS : IsClosedSet η S) (hne : S ≠ Set.univ) : 0 < η ∧ 0 < n := by
  have key : 0 < η * n := by
    by_contra hle
    push Not at hle
    apply hne
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := hS i y (le_trans hle (Nat.cast_nonneg _)) (y i)
    simpa using this
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at key
    · exact h
  refine ⟨?_, hn⟩
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact pos_of_mul_pos_left key this.le

/-- `|S| ≤ ∑_u |S|_{y_i = u}|`. -/
lemma ncard_le_sum_sliceSet (S : Set (ι → Fin n)) (i : ι) :
    S.ncard ≤ ∑ u : Fin n, (sliceSet S i u).ncard := by
  have hsub : S ⊆ ⋃ u ∈ (Finset.univ : Finset (Fin n)), hglue i u '' sliceSet S i u := by
    intro y hy
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_image, mem_sliceSet]
    exact ⟨y i, hproj i y, by simpa using hy, by simp⟩
  calc S.ncard ≤ (⋃ u ∈ (Finset.univ : Finset (Fin n)), hglue i u '' sliceSet S i u).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ ∑ u : Fin n, (hglue i u '' sliceSet S i u).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ u : Fin n, (sliceSet S i u).ncard :=
        Finset.sum_le_sum fun u _ => Set.ncard_image_le

/-- The slicing step of (F2): if all proper slices of a proper `η`-closed set `S` have at most
`B` points, then `|S| < η n · n^{d-1} + n B`. -/
lemma IsClosedSet.ncard_lt_of_slices {η : ℝ} {S : Set (ι → Fin n)} (hS : IsClosedSet η S)
    (hne : S ≠ Set.univ) (i : ι) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u, sliceSet S i u ≠ Set.univ → ((sliceSet S i u).ncard : ℝ) ≤ B) :
    (S.ncard : ℝ) < η * n * (n : ℝ) ^ (Fintype.card ι - 1) + n * B := by
  classical
  have : Nonempty ι := ⟨i⟩
  obtain ⟨hη, hn⟩ := hS.pos_of_ne_univ hne
  -- the set of full slices
  set Fu : Finset (Fin n) := Finset.univ.filter fun u => sliceSet S i u = Set.univ with hFu
  -- fewer than `η n` slices are full
  have hF : (Fu.card : ℝ) < η * n := by
    by_contra hle
    push Not at hle
    apply hne
    rw [Set.eq_univ_iff_forall]
    intro y
    have hcount : (Fu.card : ℝ) ≤ lineCount S i y := by
      have : Fu.card ≤ lineCount S i y := by
        rw [lineCount_eq_ncard, ← Set.ncard_coe_finset]
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        intro u hu
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hFu] at hu
        simp only [Set.mem_ofPred_eq]
        have : hproj i y ∈ sliceSet S i u := by rw [hu]; trivial
        simpa [hglue_hproj_eq_update] using this
      exact_mod_cast this
    have := hS i y (hle.trans hcount) (y i)
    simpa using this
  -- size of a full slice
  have hfull : ∀ u ∈ Fu, ((sliceSet S i u).ncard : ℝ) = (n : ℝ) ^ (Fintype.card ι - 1) := by
    intro u hu
    simp only [hFu, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [hu, Set.ncard_univ, card_cube, card_ne]
    push_cast; ring
  have hsum : (S.ncard : ℝ) ≤ ∑ u : Fin n, ((sliceSet S i u).ncard : ℝ) := by
    exact_mod_cast ncard_le_sum_sliceSet S i
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun u => sliceSet S i u = Set.univ)] at hsum
  have h1 : ∑ u ∈ Finset.univ.filter (fun u => sliceSet S i u = Set.univ),
      ((sliceSet S i u).ncard : ℝ) = Fu.card * (n : ℝ) ^ (Fintype.card ι - 1) := by
    rw [← hFu, Finset.sum_congr rfl hfull, Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ u ∈ Finset.univ.filter (fun u => ¬ sliceSet S i u = Set.univ),
      ((sliceSet S i u).ncard : ℝ) ≤ n * B := by
    calc ∑ u ∈ Finset.univ.filter (fun u => ¬ sliceSet S i u = Set.univ),
          ((sliceSet S i u).ncard : ℝ)
        ≤ ∑ _u ∈ Finset.univ.filter (fun u => ¬ sliceSet S i u = Set.univ), B := by
          apply Finset.sum_le_sum
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          exact hB u hu
      _ ≤ ∑ _u : Fin n, B :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hB0)
      _ = n * B := by simp
  have hpow : (0 : ℝ) < (n : ℝ) ^ (Fintype.card ι - 1) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h3 : (Fu.card : ℝ) * (n : ℝ) ^ (Fintype.card ι - 1) <
      η * n * (n : ℝ) ^ (Fintype.card ι - 1) :=
    mul_lt_mul_of_pos_right hF hpow
  linarith

end Small

/-- Auxiliary statement for (F2), by induction on the dimension. -/
theorem IsClosedSet.ncard_le_aux (η : ℝ) (n : ℕ) :
    ∀ (d : ℕ) (κ : Type _) [Fintype κ] [DecidableEq κ], Fintype.card κ = d →
      ∀ S : Set (κ → Fin n), IsClosedSet η S → S ≠ Set.univ →
        (S.ncard : ℝ) ≤ d * η * (n : ℝ) ^ d := by
  intro d
  induction d with
  | zero =>
    intro κ _ _ hκ S _ hne
    have hlt := Set.ncard_lt_card hne
    rw [card_cube, hκ, pow_zero] at hlt
    have : S.ncard = 0 := by omega
    simp [this]
  | succ d ih =>
    intro κ _ _ hκ S hS hne
    have : Nonempty κ := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i⟩ := this
    have : Nonempty κ := ⟨i⟩
    obtain ⟨hη, hn⟩ := hS.pos_of_ne_univ hne
    have hcard : Fintype.card {j // j ≠ i} = d := by rw [card_ne, hκ]; rfl
    have hB0 : (0 : ℝ) ≤ d * η * (n : ℝ) ^ d := by positivity
    have := hS.ncard_lt_of_slices hne i hB0 (fun u hu =>
      ih {j // j ≠ i} hcard (sliceSet S i u) (hS.sliceSet_closed i u) hu)
    rw [hκ, Nat.add_sub_cancel] at this
    push_cast
    have : (S.ncard : ℝ) < (d + 1) * η * (n : ℝ) ^ (d + 1) := by
      calc (S.ncard : ℝ) < η * n * (n : ℝ) ^ d + n * (d * η * (n : ℝ) ^ d) := this
        _ = (d + 1) * η * (n : ℝ) ^ (d + 1) := by ring
    exact this.le

/-- (F2) A proper `η`-closed subset of the cube `V^d` has at most `d η n^d` points. -/
theorem IsClosedSet.ncard_le [Fintype ι] {η : ℝ} {S : Set (ι → Fin n)} (hS : IsClosedSet η S)
    (hne : S ≠ Set.univ) :
    (S.ncard : ℝ) ≤ Fintype.card ι * η * (n : ℝ) ^ Fintype.card ι :=
  IsClosedSet.ncard_le_aux η n _ ι rfl S hS hne

/-- (F2) A proper `η`-closed subset of the cube `V^d`, `d ≥ 1`, has fewer than `d η n^d`
points. -/
theorem IsClosedSet.ncard_lt [Fintype ι] [Nonempty ι] {η : ℝ} {S : Set (ι → Fin n)}
    (hS : IsClosedSet η S) (hne : S ≠ Set.univ) :
    (S.ncard : ℝ) < Fintype.card ι * η * (n : ℝ) ^ Fintype.card ι := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨hη, hn⟩ := hS.pos_of_ne_univ hne
  have hd : 0 < Fintype.card ι := Fintype.card_pos
  have hB0 : (0 : ℝ) ≤ (Fintype.card ι - 1 : ℕ) * η * (n : ℝ) ^ (Fintype.card ι - 1) := by
    positivity
  have := hS.ncard_lt_of_slices hne i hB0 (fun u hu =>
    IsClosedSet.ncard_le_aux η n _ {j // j ≠ i} (card_ne i) (sliceSet S i u) (hS.sliceSet_closed i u) hu)
  calc (S.ncard : ℝ) < η * n * (n : ℝ) ^ (Fintype.card ι - 1) +
        n * ((Fintype.card ι - 1 : ℕ) * η * (n : ℝ) ^ (Fintype.card ι - 1)) := this
    _ = Fintype.card ι * η * (n : ℝ) ^ Fintype.card ι := by
        obtain ⟨d, hd'⟩ : ∃ d, Fintype.card ι = d + 1 := ⟨Fintype.card ι - 1, by omega⟩
        rw [hd', Nat.add_sub_cancel]
        push_cast; ring

/-- (F2), the way it is used: the union of proper `ηⱼ`-closed sets with `d ∑ ηⱼ ≤ 1` is
proper (`d = |ι| ≥ 1`, `n ≥ 1`). -/
theorem biUnion_ne_univ_of_isClosedSet [Fintype ι] [Nonempty ι] (hn : 0 < n) {κ : Type*}
    {s : Finset κ} {η : κ → ℝ} {S : κ → Set (ι → Fin n)}
    (h : ∀ j ∈ s, IsClosedSet (η j) (S j)) (hne : ∀ j ∈ s, S j ≠ Set.univ)
    (hsum : Fintype.card ι * ∑ j ∈ s, η j ≤ 1) : (⋃ j ∈ s, S j) ≠ Set.univ := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    intro h'
    have : (fun _ => (⟨0, hn⟩ : Fin n)) ∈ (∅ : Set (ι → Fin n)) := by rw [h']; trivial
    exact this
  intro hU
  have hcard : ((⋃ j ∈ s, S j).ncard : ℝ) = (n : ℝ) ^ Fintype.card ι := by
    rw [hU, Set.ncard_univ, card_cube]; push_cast; rfl
  have h1 : ((⋃ j ∈ s, S j).ncard : ℝ) ≤ ∑ j ∈ s, ((S j).ncard : ℝ) := by
    exact_mod_cast Finset.set_ncard_biUnion_le s S
  have h2 : ∑ j ∈ s, ((S j).ncard : ℝ) <
      ∑ j ∈ s, Fintype.card ι * η j * (n : ℝ) ^ Fintype.card ι :=
    Finset.sum_lt_sum_of_nonempty hs fun j hj => (h j hj).ncard_lt (hne j hj)
  have h3 : ∑ j ∈ s, Fintype.card ι * η j * (n : ℝ) ^ Fintype.card ι =
      (Fintype.card ι * ∑ j ∈ s, η j) * (n : ℝ) ^ Fintype.card ι := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hpow : (0 : ℝ) < (n : ℝ) ^ Fintype.card ι := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h4 : (Fintype.card ι * ∑ j ∈ s, η j) * (n : ℝ) ^ Fintype.card ι ≤
      (n : ℝ) ^ Fintype.card ι := by
    nlinarith
  linarith

/-! ### (F3): positions of full faces -/

section PosFull

variable {η : ℝ} {S : Set (ι → Fin n)}

lemma mem_posFull_iff {I : Finset ι} {b : {i // i ∉ I} → Fin n} :
    b ∈ posFull S I ↔ ∀ z, glue I z b ∈ S := Iff.rfl

/-- A line of the base `B_I` through `b` has at most as many points of `Y_I(S)` as the
corresponding line of the cube through any point of the face `Φ_I(b)` has points of `S`. -/
lemma lineCount_posFull_le (S : Set (ι → Fin n)) (I : Finset ι) (j : {i // i ∉ I})
    (b : {i // i ∉ I} → Fin n) (z : {i // i ∈ I} → Fin n) :
    lineCount (posFull S I) j b ≤ lineCount S j.1 (glue I z b) := by
  rw [lineCount_eq_ncard, lineCount_eq_ncard]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro t ht
  simp only [Set.mem_ofPred_eq, mem_posFull_iff] at ht ⊢
  rw [← glue_update_outer]
  exact ht z

/-- (F3) If `S` is `η`-closed, then `Y_I(S)` is `η`-closed in the base `B_I`. -/
theorem IsClosedSet.posFull_closed (hS : IsClosedSet η S) (I : Finset ι) :
    IsClosedSet η (posFull S I) := by
  intro j b hb t z
  rw [glue_update_outer]
  exact hS j.1 (glue I z b) (hb.trans (by exact_mod_cast lineCount_posFull_le S I j b z)) t

/-- (F3) If `S` is proper, then `Y_I(S)` is proper. -/
theorem posFull_ne_univ (hS : S ≠ Set.univ) (I : Finset ι) : posFull S I ≠ Set.univ := by
  intro h
  apply hS
  rw [Set.eq_univ_iff_forall]
  intro y
  have : outer I y ∈ posFull S I := by rw [h]; trivial
  simpa using this (inner I y)

lemma posFull_mono {S T : Set (ι → Fin n)} (h : S ⊆ T) (I : Finset ι) :
    posFull S I ⊆ posFull T I := fun _ hb z => h (hb z)

@[simp] lemma posFull_univ (I : Finset ι) :
    posFull (Set.univ : Set (ι → Fin n)) I = Set.univ := by
  ext b; simp [mem_posFull_iff]

lemma posFull_inter (S T : Set (ι → Fin n)) (I : Finset ι) :
    posFull (S ∩ T) I = posFull S I ∩ posFull T I := by
  ext b; simp only [mem_posFull_iff, Set.mem_inter_iff]; exact forall_and

/-- `Y_∅`-like statement for a single direction: `b ∈ Y_{{i}}(S)` iff the line is full. -/
lemma glue_mem_of_mem_posFull {I : Finset ι} {b : {i // i ∉ I} → Fin n} (hb : b ∈ posFull S I)
    (z : {i // i ∈ I} → Fin n) : glue I z b ∈ S := hb z

end PosFull

/-! ### Restricting words to faces -/

section FaceRestrict

variable {F : Type*} [Field F]

/-- `a ↦ a_{I,b}` as a linear map. -/
def faceRestrictLin (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    ((ι → Fin n) → F) →ₗ[F] (({i // i ∈ I} → Fin n) → F) :=
  LinearMap.funLeft F F (fun z => glue I z b)

@[simp] lemma faceRestrictLin_apply (I : Finset ι) (b : {i // i ∉ I} → Fin n)
    (a : (ι → Fin n) → F) : faceRestrictLin I b a = faceRestrict a I b := rfl

omit [Field F] in
@[simp] lemma faceRestrict_apply (a : (ι → Fin n) → F) (I : Finset ι)
    (b : {i // i ∉ I} → Fin n) (z : {i // i ∈ I} → Fin n) :
    faceRestrict a I b z = a (glue I z b) := rfl

lemma faceRestrict_add (a a' : (ι → Fin n) → F) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    faceRestrict (a + a') I b = faceRestrict a I b + faceRestrict a' I b := rfl

lemma faceRestrict_sub (a a' : (ι → Fin n) → F) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    faceRestrict (a - a') I b = faceRestrict a I b - faceRestrict a' I b := rfl

lemma faceRestrict_smul (c : F) (a : (ι → Fin n) → F) (I : Finset ι)
    (b : {i // i ∉ I} → Fin n) : faceRestrict (c • a) I b = c • faceRestrict a I b := rfl

@[simp] lemma faceRestrict_zero (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    faceRestrict (0 : (ι → Fin n) → F) I b = 0 := rfl

omit [Field F] in
lemma restrictLine_faceRestrict (a : (ι → Fin n) → F) (I : Finset ι) (b : {i // i ∉ I} → Fin n)
    (i : {i // i ∈ I}) (z : {i // i ∈ I} → Fin n) :
    restrictLine (faceRestrict a I b) i z = restrictLine a i.1 (glue I z b) := by
  funext t
  simp [restrictLine, glue_update_inner]

/-- The restriction of a word of `C^{(i)}`, `i ∈ I`, to an `I`-face lies in `C^{(i)}` of the
face. -/
lemma faceRestrict_mem_colCode {C : ι → Submodule F (Fin n → F)} {I : Finset ι} {i : ι}
    (hi : i ∈ I) {a : (ι → Fin n) → F} (ha : a ∈ colCode C i) (b : {i // i ∉ I} → Fin n) :
    faceRestrict a I b ∈ colCode (fun k : {k // k ∈ I} => C k) ⟨i, hi⟩ := by
  intro z
  rw [restrictLine_faceRestrict]
  exact ha _

lemma supportedIn_faceRestrict {a : (ι → Fin n) → F} {S : Set (ι → Fin n)}
    (ha : SupportedIn a S) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    SupportedIn (faceRestrict a I b) {z | glue I z b ∈ S} :=
  fun _ hz => ha _ hz

omit [DecidableEq ι] in
lemma SupportedIn.mono {a : (ι → Fin n) → F} {S T : Set (ι → Fin n)} (ha : SupportedIn a S)
    (h : S ⊆ T) : SupportedIn a T := fun y hy => h (ha y hy)

omit [DecidableEq ι] in
lemma mem_supported_iff {a : (ι → Fin n) → F} {S : Set (ι → Fin n)} :
    a ∈ supported F S ↔ ∀ y, a y ≠ 0 → y ∈ S := Iff.rfl

omit [DecidableEq ι] in
lemma supported_mono {S T : Set (ι → Fin n)} (h : S ⊆ T) :
    supported F S ≤ supported F T := fun _ ha => SupportedIn.mono ha h

/-! #### Line codewords -/

variable {C : ι → Submodule F (Fin n → F)}

/-- Points of the line in direction `i` through `y`, as used in `IsLineCodeword`. -/
lemma update_eq_update_iff {i : ι} {y y' : ι → Fin n} {t t' : Fin n} :
    Function.update y' i t' = Function.update y i t ↔ t' = t ∧ hproj i y' = hproj i y := by
  constructor
  · intro h
    refine ⟨by simpa using congrFun h i, ?_⟩
    have := congrArg (hproj i) h
    simpa using this
  · rintro ⟨rfl, h⟩
    rw [← hglue_hproj_eq_update, h, hglue_hproj_eq_update]

/-- A line codeword of direction `i` lies in `C^{(i)}`. -/
lemma IsLineCodeword.mem_colCode {x : (ι → Fin n) → F} {i : ι} {y : ι → Fin n}
    (hx : IsLineCodeword C x i y) : x ∈ colCode C i := by
  intro y'
  by_cases h : hproj i y' = hproj i y
  · have : restrictLine x i y' = restrictLine x i y := by
      funext t
      simp only [restrictLine]
      rw [(update_eq_update_iff (t' := t) (t := t)).2 ⟨rfl, h⟩]
    rw [this]; exact hx.2
  · have : restrictLine x i y' = 0 := by
      funext t
      simp only [restrictLine, Pi.zero_apply]
      by_contra hne
      obtain ⟨s, hs⟩ := hx.1 _ hne
      exact h ((update_eq_update_iff.1 hs).2)
    rw [this]; exact (C i).zero_mem

lemma lineSpan_mono {M M' : Set (ι → Fin n)} (h : M ⊆ M') : lineSpan C M ≤ lineSpan C M' := by
  apply Submodule.span_mono
  rintro x ⟨i, y, hM, hx⟩
  exact ⟨i, y, fun t => h (hM t), hx⟩

/-- `L(M) ⊆ ⊞ C`. -/
lemma lineSpan_le_boxplus (M : Set (ι → Fin n)) : lineSpan C M ≤ boxplus C := by
  rw [lineSpan, Submodule.span_le]
  rintro x ⟨i, y, -, hx⟩
  exact (le_iSup (colCode C) i : colCode C i ≤ boxplus C) hx.mem_colCode

/-- `L(M) ⊆ F^M`. -/
lemma lineSpan_le_supported (M : Set (ι → Fin n)) : lineSpan C M ≤ supported F M := by
  rw [lineSpan, Submodule.span_le]
  rintro x ⟨i, y, hM, hx⟩ y' hy'
  obtain ⟨t, rfl⟩ := hx.1 y' hy'
  exact hM t

lemma IsLineCodeword.mem_lineSpan {M : Set (ι → Fin n)} {x : (ι → Fin n) → F} {i : ι}
    {y : ι → Fin n} (hx : IsLineCodeword C x i y) (hM : ∀ t, Function.update y i t ∈ M) :
    x ∈ lineSpan C M :=
  Submodule.subset_span ⟨i, y, hM, hx⟩

/-- A line codeword of direction `i ∈ I` restricted to an `I`-face containing its line is a
line codeword of the face. -/
lemma IsLineCodeword.faceRestrict_of_mem {x : (ι → Fin n) → F} {i : ι} {y : ι → Fin n}
    (hx : IsLineCodeword C x i y) {I : Finset ι} (hi : i ∈ I) {b : {i // i ∉ I} → Fin n}
    (hb : outer I y = b) :
    IsLineCodeword (fun k : {k // k ∈ I} => C k) (faceRestrict x I b) ⟨i, hi⟩ (inner I y) := by
  subst hb
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht⟩ := hx.1 _ hz
    refine ⟨t, ?_⟩
    have := congrArg (inner I) ht
    rwa [inner_glue', inner_update_of_mem I y hi] at this
  · rw [restrictLine_faceRestrict, glue_inner_outer']
    exact hx.2

/-- A line codeword of direction `i ∈ I` vanishes on `I`-faces not containing its line. -/
lemma IsLineCodeword.faceRestrict_eq_zero {x : (ι → Fin n) → F} {i : ι} {y : ι → Fin n}
    (hx : IsLineCodeword C x i y) {I : Finset ι} (hi : i ∈ I) {b : {i // i ∉ I} → Fin n}
    (hb : outer I y ≠ b) : faceRestrict x I b = 0 := by
  funext z
  simp only [faceRestrict_apply, Pi.zero_apply]
  by_contra hne
  obtain ⟨t, ht⟩ := hx.1 _ hne
  apply hb
  have := congrArg (outer I) ht
  rw [outer_glue', outer_update_of_mem I y hi] at this
  exact this.symm

/-- A word supported on the line of direction `j ∉ I` through `y` restricts to an `I`-face as a
word supported in at most one point: the intersection of the line with the face. -/
lemma faceRestrict_supportedIn_of_not_mem {x : (ι → Fin n) → F} {j : ι} {y : ι → Fin n}
    (hx : SupportedIn x {z | ∃ t, z = Function.update y j t}) {I : Finset ι} (hj : j ∉ I)
    (b : {i // i ∉ I} → Fin n) :
    SupportedIn (faceRestrict x I b)
      {z | z = inner I y ∧ ∃ t, glue I z b = Function.update y j t} := by
  intro z hz
  obtain ⟨t, ht⟩ := hx _ hz
  refine ⟨?_, t, ht⟩
  have := congrArg (inner I) ht
  rwa [inner_glue', inner_update_of_not_mem I y hj] at this

/-- **Restriction of `L(M)` to a face.** If `w ∈ L(M)`, then its restriction to the `I`-face in
position `b` is the sum of a word of `L(M_{I,b})` (lines of the face lying in `M`) and a word
supported at points of the face lying on full lines of `M` of directions `j ∉ I`. -/
theorem faceRestrict_mem_lineSpan_sup {M : Set (ι → Fin n)} {w : (ι → Fin n) → F}
    (hw : w ∈ lineSpan C M) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    faceRestrict w I b ∈ lineSpan (fun k : {k // k ∈ I} => C k) {z | glue I z b ∈ M} ⊔
      supported F {z | ∃ j, j ∉ I ∧ ∀ t, Function.update (glue I z b) j t ∈ M} := by
  have key : lineSpan C M ≤ Submodule.comap (faceRestrictLin I b)
      (lineSpan (fun k : {k // k ∈ I} => C k) {z | glue I z b ∈ M} ⊔
        supported F {z | ∃ j, j ∉ I ∧ ∀ t, Function.update (glue I z b) j t ∈ M}) := by
    rw [lineSpan, Submodule.span_le]
    rintro x ⟨i, y, hM, hx⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, faceRestrictLin_apply]
    by_cases hi : i ∈ I
    · by_cases hb : outer I y = b
      · apply Submodule.mem_sup_left
        apply (hx.faceRestrict_of_mem hi hb).mem_lineSpan
        intro t
        simp only [Set.mem_ofPred_eq]
        rw [glue_update_inner, ← hb, glue_inner_outer']
        exact hM t
      · rw [hx.faceRestrict_eq_zero hi hb]
        exact Submodule.zero_mem _
    · apply Submodule.mem_sup_right
      intro z hz
      obtain ⟨-, t, ht⟩ := faceRestrict_supportedIn_of_not_mem hx.1 hi b z hz
      refine ⟨i, hi, fun s => ?_⟩
      rw [ht, Function.update_idem]
      exact hM s
  exact key hw

/-- Restriction of `L(M)` to a face, coarse form: the restriction lies in `⊞` of the face
plus words supported at points on full lines of `M` of directions `j ∉ I`. -/
theorem faceRestrict_mem_boxplus_sup {M : Set (ι → Fin n)} {w : (ι → Fin n) → F}
    (hw : w ∈ lineSpan C M) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    faceRestrict w I b ∈ boxplus (fun k : {k // k ∈ I} => C k) ⊔
      supported F {z | ∃ j, j ∉ I ∧ ∀ t, Function.update (glue I z b) j t ∈ M} := by
  have h1 := faceRestrict_mem_lineSpan_sup hw I b
  have h2 : lineSpan (fun k : {k // k ∈ I} => C k) {z | glue I z b ∈ M} ⊔
      supported F {z | ∃ j, j ∉ I ∧ ∀ t, Function.update (glue I z b) j t ∈ M} ≤
      boxplus (fun k : {k // k ∈ I} => C k) ⊔
      supported F {z | ∃ j, j ∉ I ∧ ∀ t, Function.update (glue I z b) j t ∈ M} :=
    sup_le_sup_right (lineSpan_le_boxplus _) _
  exact h2 h1

end FaceRestrict

/-! ### Subcube embeddings

A uniform treatment of faces, hyperplanes, faces of hyperplanes etc.: `Ψ : (κ → Fin n) → (ι → Fin n)`
embeds the cube `κ → Fin n` as the subcube of `ι → Fin n` spanned by the directions `φ k`
(the coordinates outside the range of `φ` are fixed). Examples: `glue I · b` (faces, with
`φ = Subtype.val`), `hglue i u` (hyperplanes, with `φ = Subtype.val`). -/

section Subcube

variable {κ : Type*}

/-- `Ψ` embeds the cube `κ → Fin n` into `ι → Fin n` as the subcube spanned by the directions
`φ k`: coordinate `φ k` of `Ψ z` is `z k`, the other coordinates do not depend on `z`. -/
structure IsSubcubeEmb (φ : κ → ι) (Ψ : (κ → Fin n) → (ι → Fin n)) : Prop where
  injective : Function.Injective φ
  apply_map : ∀ z k, Ψ z (φ k) = z k
  apply_out : ∀ z z' j, j ∉ Set.range φ → Ψ z j = Ψ z' j

namespace IsSubcubeEmb

variable {φ : κ → ι} {Ψ : (κ → Fin n) → (ι → Fin n)}

omit [DecidableEq ι] in
lemma comp_eq (hΨ : IsSubcubeEmb φ Ψ) (z : κ → Fin n) : Ψ z ∘ φ = z :=
  funext fun k => hΨ.apply_map z k

omit [DecidableEq ι] in
lemma injective_emb (hΨ : IsSubcubeEmb φ Ψ) : Function.Injective Ψ := by
  intro z z' h
  rw [← hΨ.comp_eq z, ← hΨ.comp_eq z', h]

omit [DecidableEq ι] in
/-- A point of the cube lies in the subcube iff its coordinates outside the range of `φ` are
those of the subcube. -/
lemma eq_emb_iff (hΨ : IsSubcubeEmb φ Ψ) (z : κ → Fin n) (y : ι → Fin n) :
    Ψ z = y ↔ z = y ∘ φ ∧ ∀ j, j ∉ Set.range φ → Ψ z j = y j := by
  constructor
  · rintro rfl; exact ⟨(hΨ.comp_eq z).symm, fun _ _ => rfl⟩
  · rintro ⟨rfl, hout⟩
    funext j
    by_cases hj : j ∈ Set.range φ
    · obtain ⟨k, rfl⟩ := hj
      exact hΨ.apply_map _ k
    · exact hout j hj

omit [DecidableEq ι] in
lemma mem_range_iff (hΨ : IsSubcubeEmb φ Ψ) (z₀ : κ → Fin n) (y : ι → Fin n) :
    y ∈ Set.range Ψ ↔ ∀ j, j ∉ Set.range φ → Ψ z₀ j = y j := by
  constructor
  · rintro ⟨z, rfl⟩ j hj
    exact hΨ.apply_out z₀ z j hj
  · intro h
    refine ⟨y ∘ φ, (hΨ.eq_emb_iff _ y).2 ⟨rfl, fun j hj => ?_⟩⟩
    rw [hΨ.apply_out (y ∘ φ) z₀ j hj]
    exact h j hj

variable [DecidableEq κ]

lemma update_emb (hΨ : IsSubcubeEmb φ Ψ) (z : κ → Fin n) (k : κ) (t : Fin n) :
    Ψ (Function.update z k t) = Function.update (Ψ z) (φ k) t := by
  funext j
  by_cases hj : j ∈ Set.range φ
  · obtain ⟨k', rfl⟩ := hj
    rw [hΨ.apply_map]
    by_cases hk : k' = k
    · subst hk; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne (hΨ.injective.ne hk), hΨ.apply_map]
  · have hjk : j ≠ φ k := fun h => hj ⟨k, h.symm⟩
    rw [Function.update_of_ne hjk]
    exact hΨ.apply_out _ _ j hj

lemma lineCount_preimage (hΨ : IsSubcubeEmb φ Ψ) (S : Set (ι → Fin n)) (k : κ)
    (z : κ → Fin n) : lineCount (Ψ ⁻¹' S) k z = lineCount S (φ k) (Ψ z) := by
  simp only [lineCount, Set.mem_preimage, hΨ.update_emb]

/-- The trace of an `η`-closed set on a subcube is `η`-closed. -/
lemma isClosedSet_preimage (hΨ : IsSubcubeEmb φ Ψ) {η : ℝ} {S : Set (ι → Fin n)}
    (hS : IsClosedSet η S) : IsClosedSet η (Ψ ⁻¹' S) := by
  intro k z hz t
  rw [hΨ.lineCount_preimage] at hz
  rw [Set.mem_preimage, hΨ.update_emb]
  exact hS _ _ hz t

end IsSubcubeEmb

lemma isSubcubeEmb_glue (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    IsSubcubeEmb (Subtype.val : {i // i ∈ I} → ι) (fun z => glue I z b) where
  injective := Subtype.val_injective
  apply_map z k := glue_apply_val_mem I z b k
  apply_out z z' j hj := by
    have hjI : j ∉ I := fun h => hj ⟨⟨j, h⟩, rfl⟩
    rw [glue_apply_of_not_mem I _ _ hjI, glue_apply_of_not_mem I _ _ hjI]

lemma isSubcubeEmb_hglue (i : ι) (u : Fin n) :
    IsSubcubeEmb (Subtype.val : {j // j ≠ i} → ι) (hglue i u) where
  injective := Subtype.val_injective
  apply_map z k := hglue_apply_val k
  apply_out z z' j hj := by
    have hji : j = i := by
      by_contra h; exact hj ⟨⟨j, h⟩, rfl⟩
    subst hji
    simp

/-- The trace `S_{I,b} = {z | (z, b) ∈ S}` of an `η`-closed set on a face is `η`-closed. -/
lemma IsClosedSet.face_closed {η : ℝ} {S : Set (ι → Fin n)} (hS : IsClosedSet η S)
    (I : Finset ι) (b : {i // i ∉ I} → Fin n) : IsClosedSet η {z | glue I z b ∈ S} :=
  (isSubcubeEmb_glue I b).isClosedSet_preimage hS

end Subcube

section SubcubeWords

variable {F : Type*} [Field F] {κ : Type*} [DecidableEq κ]
variable {φ : κ → ι} {Ψ : (κ → Fin n) → (ι → Fin n)} {C : ι → Submodule F (Fin n → F)}

namespace IsSubcubeEmb

omit [Field F] in
lemma restrictLine_comp (hΨ : IsSubcubeEmb φ Ψ) (a : (ι → Fin n) → F) (k : κ) (z : κ → Fin n) :
    restrictLine (a ∘ Ψ) k z = restrictLine a (φ k) (Ψ z) := by
  funext t
  simp [restrictLine, hΨ.update_emb]

/-- The restriction of a word of `C^{(φ k)}` to the subcube is a word of `C^{(k)}` there. -/
lemma comp_mem_colCode (hΨ : IsSubcubeEmb φ Ψ) {k : κ} {a : (ι → Fin n) → F}
    (ha : a ∈ colCode C (φ k)) : a ∘ Ψ ∈ colCode (fun k => C (φ k)) k := by
  intro z
  rw [hΨ.restrictLine_comp]
  exact ha _

omit [DecidableEq κ] [DecidableEq ι] in
lemma supportedIn_comp (hΨ : IsSubcubeEmb φ Ψ) {a : (ι → Fin n) → F} {S : Set (ι → Fin n)}
    (ha : SupportedIn a S) : SupportedIn (a ∘ Ψ) (Ψ ⁻¹' S) := by
  have := hΨ
  exact fun _ hz => ha _ hz

/-- A line codeword of direction `φ k` whose line meets the subcube restricts to a line codeword
of the subcube. -/
lemma isLineCodeword_comp (hΨ : IsSubcubeEmb φ Ψ) {x : (ι → Fin n) → F} {k : κ}
    {y : ι → Fin n} (hx : IsLineCodeword C x (φ k) y) (z₀ : κ → Fin n) (hy : Ψ z₀ = y) :
    IsLineCodeword (fun k => C (φ k)) (x ∘ Ψ) k z₀ := by
  subst hy
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht⟩ := hx.1 _ hz
    refine ⟨t, ?_⟩
    rw [← hΨ.update_emb] at ht
    exact hΨ.injective_emb ht
  · rw [hΨ.restrictLine_comp]
    exact hx.2

/-- A line codeword of direction `φ k` whose line does not meet the subcube vanishes on it. -/
lemma comp_eq_zero_of_isLineCodeword (hΨ : IsSubcubeEmb φ Ψ) {x : (ι → Fin n) → F} {k : κ}
    {y : ι → Fin n} (hx : IsLineCodeword C x (φ k) y) (hy : y ∉ Set.range Ψ) : x ∘ Ψ = 0 := by
  funext z
  simp only [Function.comp_apply, Pi.zero_apply]
  by_contra hne
  obtain ⟨t, ht⟩ := hx.1 _ hne
  apply hy
  refine ⟨Function.update z k (y (φ k)), ?_⟩
  rw [hΨ.update_emb, ht, Function.update_idem, Function.update_eq_self]

omit [DecidableEq κ] in
/-- A word supported on a line of direction `j ∉ range φ` restricts to the subcube as a word
supported at points `z` with `Ψ z` on that line (at most one point). -/
lemma comp_supportedIn_of_not_mem_range (hΨ : IsSubcubeEmb φ Ψ) {x : (ι → Fin n) → F}
    {j : ι} {y : ι → Fin n} (hx : SupportedIn x {z | ∃ t, z = Function.update y j t})
    (hj : j ∉ Set.range φ) :
    SupportedIn (x ∘ Ψ) {z | ∃ t, Ψ z = Function.update y j t} := by
  have := hj
  have := hΨ
  intro z hz
  exact hx _ hz

/-- **Restriction of `L(M)` to a subcube.** If `w ∈ L(M)`, then `w ∘ Ψ` is the sum of a word of
`L(Ψ⁻¹ M)` (in the subcube, for the codes `C ∘ φ`) and a word supported at points `z` such that
`Ψ z` lies on a full line of `M` of a direction outside the subcube. -/
theorem comp_mem_lineSpan_sup (hΨ : IsSubcubeEmb φ Ψ) {M : Set (ι → Fin n)}
    {w : (ι → Fin n) → F} (hw : w ∈ lineSpan C M) :
    w ∘ Ψ ∈ lineSpan (fun k => C (φ k)) (Ψ ⁻¹' M) ⊔
      supported F {z | ∃ j, j ∉ Set.range φ ∧ ∀ t, Function.update (Ψ z) j t ∈ M} := by
  have key : lineSpan C M ≤ Submodule.comap (LinearMap.funLeft F F Ψ)
      (lineSpan (fun k => C (φ k)) (Ψ ⁻¹' M) ⊔
        supported F {z | ∃ j, j ∉ Set.range φ ∧ ∀ t, Function.update (Ψ z) j t ∈ M}) := by
    rw [lineSpan, Submodule.span_le]
    rintro x ⟨i, y, hM, hx⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    change x ∘ Ψ ∈ _
    by_cases hi : i ∈ Set.range φ
    · obtain ⟨k, rfl⟩ := hi
      by_cases hy : y ∈ Set.range Ψ
      · obtain ⟨z₀, hz₀⟩ := hy
        apply Submodule.mem_sup_left
        apply (hΨ.isLineCodeword_comp hx z₀ hz₀).mem_lineSpan
        intro t
        rw [Set.mem_preimage, hΨ.update_emb, hz₀]
        exact hM t
      · rw [hΨ.comp_eq_zero_of_isLineCodeword hx hy]
        exact Submodule.zero_mem _
    · apply Submodule.mem_sup_right
      intro z hz
      obtain ⟨t, ht⟩ := hΨ.comp_supportedIn_of_not_mem_range hx.1 hi z hz
      refine ⟨i, hi, fun s => ?_⟩
      rw [ht, Function.update_idem]
      exact hM s
  exact key hw

/-- Coarse form of `comp_mem_lineSpan_sup`, with `⊞` of the subcube. -/
theorem comp_mem_boxplus_sup (hΨ : IsSubcubeEmb φ Ψ) {M : Set (ι → Fin n)}
    {w : (ι → Fin n) → F} (hw : w ∈ lineSpan C M) :
    w ∘ Ψ ∈ boxplus (fun k => C (φ k)) ⊔
      supported F {z | ∃ j, j ∉ Set.range φ ∧ ∀ t, Function.update (Ψ z) j t ∈ M} := by
  have h1 := hΨ.comp_mem_lineSpan_sup hw
  have h2 : lineSpan (fun k => C (φ k)) (Ψ ⁻¹' M) ⊔
      supported F {z | ∃ j, j ∉ Set.range φ ∧ ∀ t, Function.update (Ψ z) j t ∈ M} ≤
      boxplus (fun k => C (φ k)) ⊔
      supported F {z | ∃ j, j ∉ Set.range φ ∧ ∀ t, Function.update (Ψ z) j t ∈ M} :=
    sup_le_sup_right (lineSpan_le_boxplus _) _
  exact h2 h1

end IsSubcubeEmb

/-- A word of `L(M)` vanishes outside the union of the full lines of `M`. -/
lemma exists_full_line_of_mem_lineSpan {M : Set (ι → Fin n)} {w : (ι → Fin n) → F}
    (hw : w ∈ lineSpan C M) {y : ι → Fin n} (hy : w y ≠ 0) :
    ∃ j, ∀ t, Function.update y j t ∈ M := by
  have key : lineSpan C M ≤ supported F {y | ∃ j, ∀ t, Function.update y j t ∈ M} := by
    rw [lineSpan, Submodule.span_le]
    rintro x ⟨i, y', hM, hx⟩ z hz
    obtain ⟨t, rfl⟩ := hx.1 z hz
    exact ⟨i, fun s => by rw [Function.update_idem]; exact hM s⟩
  exact key hw y hy

end SubcubeWords

end ProductExpansion
