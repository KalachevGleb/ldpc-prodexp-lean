import ProductExpansion.CubeLemmas

/-!
# Slices, check sums and the syndrome condition `S(E)`

Part "Syndrome condition and face syndrome" of the proof (definition `def:syn`),
without the face-syndrome lemma.

* `slice a i u = a|_{y_i = u}`: a word on the cube `{j // j ≠ i} → Fin n` of the hyperplane
  (via `hglue`).
* `checkSum i h a = ∑_u h(u) • a|_{y_i = u}` (a linear map); for a check `p` of `H_i` we use
  `h = H i p` (the row of `H_i`), so that `checkSum i (H i p) a = ∑_{u ∈ N(p)} H_i(p,u) a|_{y_i=u}`.
* **Light direction** (`checkSum_mem_boxplus`, `checkSum_row_mem_boxplus`): for `a ∈ ⊞ C` and any
  `h` orthogonal to `C i` (e.g. a row of `H_i` with `C i ≤ ker H_i`),
  `checkSum i h a ∈ ⊞_{j ≠ i} C_j`; on `C^{(i)}` the check sum vanishes
  (`checkSum_eq_zero_of_mem_colCode`), on `C^{(j)}`, `j ≠ i`, it lands in `C^{(j)}` of the
  hyperplane (`checkSum_mem_colCode_of_ne`).
* `synDefect H E i p = E^{(p)} = ⋃_{u ∈ N(p)} E|_{y_i = u}` and `SynCond H E a` is `S(E)`:
  for all `i`, `p ∈ P_i`, `∑_u H_i(p,u) a|_{y_i=u} ∈ W_{[d]∖i} + F^{E^{(p)}}`, where
  `W_{[d]∖i} = ⊞_{j ≠ i} ker H_j` (for `d = 1` this is `{0}`, see `synCond_iff_of_forall_eq`).
* Properties: (i) `synCond_of_mem_boxplus` / `synCond_empty_of_mem_boxplus`,
  (ii) `SynCond.add_boxplus`, `synCond_add_boxplus_iff`, (iii) `SynCond.mono`, and more.
* Faces vs hyperplanes (for the face-syndrome lemma and step 3 of lemma D):
  `checkSum_faceRestrict` with the subcube embedding `faceHypPoint`, and
  `checkSum_comp_hproj_glue` with the subcube embedding `fun z => hproj j (glue I z p)`.
-/

open Finset Function Matrix

namespace ProductExpansion

variable {F : Type*} [Field F] {n : ℕ} {ι : Type*} [DecidableEq ι]

/-! ### Slices of words -/

section Slice

/-- `a|_{y_i = u}`: the restriction of a word to the hyperplane `{y_i = u}`, as a word on the
cube `{j // j ≠ i} → Fin n`. -/
def slice (a : (ι → Fin n) → F) (i : ι) (u : Fin n) : ({j // j ≠ i} → Fin n) → F :=
  fun z => a (hglue i u z)

/-- `a ↦ a|_{y_i = u}` as a linear map. -/
def sliceLin (i : ι) (u : Fin n) : ((ι → Fin n) → F) →ₗ[F] (({j // j ≠ i} → Fin n) → F) :=
  LinearMap.funLeft F F (hglue i u)

variable {i : ι} {u : Fin n}

omit [Field F] in
@[simp] lemma slice_apply (a : (ι → Fin n) → F) (z : {j // j ≠ i} → Fin n) :
    slice a i u z = a (hglue i u z) := rfl

@[simp] lemma sliceLin_apply (a : (ι → Fin n) → F) : sliceLin i u a = slice a i u := rfl

lemma slice_add (a a' : (ι → Fin n) → F) : slice (a + a') i u = slice a i u + slice a' i u := rfl

lemma slice_sub (a a' : (ι → Fin n) → F) : slice (a - a') i u = slice a i u - slice a' i u := rfl

lemma slice_smul (c : F) (a : (ι → Fin n) → F) : slice (c • a) i u = c • slice a i u := rfl

@[simp] lemma slice_zero : slice (0 : (ι → Fin n) → F) i u = 0 := rfl

omit [Field F] in
lemma restrictLine_slice (a : (ι → Fin n) → F) (j : {j // j ≠ i}) (z : {j // j ≠ i} → Fin n) :
    restrictLine (slice a i u) j z = restrictLine a j.1 (hglue i u z) := by
  funext t
  simp [restrictLine, hglue_update]

/-- A slice of a word of `C^{(j)}`, `j ≠ i`, by a hyperplane `{y_i = u}` is a word of `C^{(j)}`
of the hyperplane. -/
lemma slice_mem_colCode {C : ι → Submodule F (Fin n → F)} {j : ι} (hj : j ≠ i)
    {a : (ι → Fin n) → F} (ha : a ∈ colCode C j) (u : Fin n) :
    slice a i u ∈ colCode (fun k : {k // k ≠ i} => C k) ⟨j, hj⟩ := by
  intro z
  rw [restrictLine_slice]
  exact ha _

lemma supportedIn_slice {a : (ι → Fin n) → F} {S : Set (ι → Fin n)} (ha : SupportedIn a S)
    (i : ι) (u : Fin n) : SupportedIn (slice a i u) (sliceSet S i u) :=
  fun _ hz => ha _ hz

lemma slice_mem_supported {a : (ι → Fin n) → F} {S : Set (ι → Fin n)} (ha : a ∈ supported F S)
    (i : ι) (u : Fin n) : slice a i u ∈ supported F (sliceSet S i u) :=
  supportedIn_slice ha i u

end Slice

/-! ### Check sums `∑_u h(u) a|_{y_i = u}` -/

section CheckSum

/-- `checkSum i h a = ∑_u h(u) • a|_{y_i = u}`, a word on the cube `{j // j ≠ i} → Fin n`.
For a check `p` of `H_i` (`h = H i p`) this is `∑_{u ∈ N(p)} H_i(p,u) a|_{y_i = u}`. -/
def checkSum (i : ι) (h : Fin n → F) :
    ((ι → Fin n) → F) →ₗ[F] (({j // j ≠ i} → Fin n) → F) where
  toFun a z := ∑ u, h u * a (hglue i u z)
  map_add' a a' := by
    funext z
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring

variable {i : ι} {h : Fin n → F}

@[simp] lemma checkSum_apply (a : (ι → Fin n) → F) (z : {j // j ≠ i} → Fin n) :
    checkSum i h a z = ∑ u, h u * a (hglue i u z) := rfl

lemma checkSum_eq_sum_smul_slice (a : (ι → Fin n) → F) :
    checkSum i h a = ∑ u, h u • slice a i u := by
  funext z
  simp [Finset.sum_apply]

/-- The value of a check sum at the trace `z = y|_{[d]∖i}` of a line of direction `i` is the
`h`-check of the restriction of `a` to that line. -/
lemma checkSum_apply_hproj (a : (ι → Fin n) → F) (y : ι → Fin n) :
    checkSum i h a (hproj i y) = ∑ u, h u * restrictLine a i y u := by
  simp [restrictLine, hglue_hproj_eq_update]

lemma checkSum_apply_hproj_eq_dotProduct (a : (ι → Fin n) → F) (y : ι → Fin n) :
    checkSum i h a (hproj i y) = h ⬝ᵥ restrictLine a i y := by
  rw [checkSum_apply_hproj]; rfl

/-- For a row of a matrix `H`: `(∑_u H(p,u) a|_{y_i=u})(z) = (H · a|_ℓ)_p`, where `ℓ` is the line
of direction `i` through any `y` with `y|_{[d]∖i} = z`. -/
lemma checkSum_row_apply_hproj {P : Type*} (H : Matrix P (Fin n) F) (p : P)
    (a : (ι → Fin n) → F) (y : ι → Fin n) :
    checkSum i (H p) a (hproj i y) = (H *ᵥ restrictLine a i y) p := by
  rw [checkSum_apply_hproj_eq_dotProduct]; rfl

lemma mem_kerCode_iff_forall_row {P : Type*} (H : Matrix P (Fin n) F) (c : Fin n → F) :
    c ∈ kerCode H ↔ ∀ p, ∑ u, H p u * c u = 0 := by
  simp only [kerCode, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hc p
    have := congrFun hc p
    simpa [Matrix.mulVec, dotProduct] using this
  · intro hc
    funext p
    simpa [Matrix.mulVec, dotProduct] using hc p

/-- Light direction, the direction `i` itself: if `h` is orthogonal to `C i`, then the check
sum of any word of `C^{(i)}` vanishes. -/
lemma checkSum_eq_zero_of_mem_colCode {C : ι → Submodule F (Fin n → F)}
    (hh : ∀ c ∈ C i, ∑ u, h u * c u = 0) {a : (ι → Fin n) → F} (ha : a ∈ colCode C i) :
    checkSum i h a = 0 := by
  funext z
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨u₀⟩⟩
  · simp
  · have := hh _ (ha (hglue i u₀ z))
    simpa [restrictLine] using this

/-- Light direction, the other directions: for `j ≠ i` the check sum maps `C^{(j)}` to `C^{(j)}`
of the hyperplane cube. -/
lemma checkSum_mem_colCode_of_ne {C : ι → Submodule F (Fin n → F)} {j : ι} (hj : j ≠ i)
    {a : (ι → Fin n) → F} (ha : a ∈ colCode C j) :
    checkSum i h a ∈ colCode (fun k : {k // k ≠ i} => C k) ⟨j, hj⟩ := by
  rw [checkSum_eq_sum_smul_slice]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (slice_mem_colCode hj ha u)

/-- **Light direction.** If `a ∈ ⊞ C` and `h` is orthogonal to `C i`, then
`∑_u h(u) a|_{y_i = u} ∈ ⊞_{j ≠ i} C_j` (on the cube `{j // j ≠ i} → Fin n`). -/
theorem checkSum_mem_boxplus {C : ι → Submodule F (Fin n → F)}
    (hh : ∀ c ∈ C i, ∑ u, h u * c u = 0) {a : (ι → Fin n) → F} (ha : a ∈ boxplus C) :
    checkSum i h a ∈ boxplus (fun k : {k // k ≠ i} => C k) := by
  have key : boxplus C ≤ Submodule.comap (checkSum i h) (boxplus (fun k : {k // k ≠ i} => C k)) := by
    refine iSup_le fun j => ?_
    intro a ha
    rw [Submodule.mem_comap]
    by_cases hj : j = i
    · subst hj
      rw [checkSum_eq_zero_of_mem_colCode hh ha]
      exact Submodule.zero_mem _
    · exact (le_iSup (colCode (fun k : {k // k ≠ i} => C k)) ⟨j, hj⟩ :
        colCode (fun k : {k // k ≠ i} => C k) ⟨j, hj⟩ ≤ boxplus _)
        (checkSum_mem_colCode_of_ne hj ha)
  exact key ha

/-- **Light direction** for a check `p` of a matrix `H` with `C i ≤ ker H`. -/
theorem checkSum_row_mem_boxplus {C : ι → Submodule F (Fin n → F)} {P : Type*}
    (H : Matrix P (Fin n) F) (hC : C i ≤ kerCode H) (p : P) {a : (ι → Fin n) → F}
    (ha : a ∈ boxplus C) :
    checkSum i (H p) a ∈ boxplus (fun k : {k // k ≠ i} => C k) :=
  checkSum_mem_boxplus (fun c hc => (mem_kerCode_iff_forall_row H c).1 (hC hc) p) ha

/-- Support of a check sum: it is contained in `⋃_{u : h(u) ≠ 0} S|_{y_i = u}`. -/
lemma supportedIn_checkSum {a : (ι → Fin n) → F} {S : Set (ι → Fin n)} (ha : SupportedIn a S)
    (i : ι) (h : Fin n → F) :
    SupportedIn (checkSum i h a) {z | ∃ u, h u ≠ 0 ∧ hglue i u z ∈ S} := by
  intro z hz
  by_contra hcon
  rw [Set.mem_ofPred_eq] at hcon
  push Not at hcon
  apply hz
  rw [checkSum_apply]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : h u = 0
  · simp [hu]
  · have : a (hglue i u z) = 0 := by
      by_contra ha0
      exact hcon u hu (ha _ ha0)
    simp [this]

lemma checkSum_mem_supported {a : (ι → Fin n) → F} {S : Set (ι → Fin n)}
    (ha : a ∈ supported F S) (i : ι) (h : Fin n → F) :
    checkSum i h a ∈ supported F {z | ∃ u, h u ≠ 0 ∧ hglue i u z ∈ S} :=
  supportedIn_checkSum ha i h

end CheckSum

/-! ### The syndrome condition `S(E)` -/

section Syndrome

variable {P : ι → Type*}

/-- `E^{(p)} = ⋃_{u ∈ N(p)} E|_{y_i = u}` for a check `p ∈ P_i`, a subset of the hyperplane cube
`{j // j ≠ i} → Fin n`. -/
def synDefect (H : ∀ i, Matrix (P i) (Fin n) F) (E : Set (ι → Fin n)) (i : ι) (p : P i) :
    Set ({j // j ≠ i} → Fin n) :=
  {z | ∃ u, H i p u ≠ 0 ∧ hglue i u z ∈ E}

/-- **Syndrome condition with defect `E`** (`S_d(E)`, definition `def:syn`): for every direction
`i` and every check `p ∈ P_i`,
`∑_{u ∈ N(p)} H_i(p,u) a|_{y_i=u} ∈ W_{[d]∖i} + F^{E^{(p)}}`,
where `W_{[d]∖i} = ⊞_{j ≠ i} ker H_j` on the cube `{j // j ≠ i} → Fin n`. -/
def SynCond (H : ∀ i, Matrix (P i) (Fin n) F) (E : Set (ι → Fin n)) (a : (ι → Fin n) → F) :
    Prop :=
  ∀ (i : ι) (p : P i), checkSum i (H i p) a ∈
    boxplus (fun j : {j // j ≠ i} => kerCode (H j)) ⊔ supported F (synDefect H E i p)

variable {H : ∀ i, Matrix (P i) (Fin n) F} {E E' : Set (ι → Fin n)} {a b : (ι → Fin n) → F}

lemma mem_synDefect {i : ι} {p : P i} {z : {j // j ≠ i} → Fin n} :
    z ∈ synDefect H E i p ↔ ∃ u, H i p u ≠ 0 ∧ hglue i u z ∈ E := Iff.rfl

lemma synDefect_mono (hE : E ⊆ E') (i : ι) (p : P i) :
    synDefect H E i p ⊆ synDefect H E' i p := by
  rintro z ⟨u, hu, hz⟩
  exact ⟨u, hu, hE hz⟩

@[simp] lemma synDefect_empty (i : ι) (p : P i) :
    synDefect H (∅ : Set (ι → Fin n)) i p = ∅ := by
  ext z; simp [synDefect]

lemma synDefect_union (E E' : Set (ι → Fin n)) (i : ι) (p : P i) :
    synDefect H (E ∪ E') i p = synDefect H E i p ∪ synDefect H E' i p := by
  ext z
  simp only [synDefect, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hu, hE | hE⟩
    · exact Or.inl ⟨u, hu, hE⟩
    · exact Or.inr ⟨u, hu, hE⟩
  · rintro (⟨u, hu, hE⟩ | ⟨u, hu, hE⟩)
    · exact ⟨u, hu, Or.inl hE⟩
    · exact ⟨u, hu, Or.inr hE⟩

/-- `E^{(p)}` is the union of the slices `E|_{y_i = u}` over the neighbours `u ∈ N(p)`. -/
lemma synDefect_eq_iUnion (E : Set (ι → Fin n)) (i : ι) (p : P i) :
    synDefect H E i p = ⋃ (u : Fin n) (_ : H i p u ≠ 0), sliceSet E i u := by
  ext z
  simp [synDefect]

/-- `E^{(p)}` is the union of the slices `E|_{y_i = u}` over the neighbours `u ∈ N(p)`
(indexed by a `Finset`, for (F1)). -/
lemma synDefect_eq_biUnion [DecidableEq F] (E : Set (ι → Fin n)) (i : ι) (p : P i) :
    synDefect H E i p = ⋃ u ∈ Finset.univ.filter (fun u => H i p u ≠ 0), sliceSet E i u := by
  ext z
  simp [synDefect]

/-- If some neighbour `u ∈ N(p)` has a full slice `E|_{y_i = u}`, then `E^{(p)}` is everything. -/
lemma synDefect_eq_univ_of_sliceSet {i : ι} {p : P i} {u : Fin n} (hu : H i p u ≠ 0)
    (hE : sliceSet E i u = Set.univ) : synDefect H E i p = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro z
  refine ⟨u, hu, ?_⟩
  have : z ∈ sliceSet E i u := by rw [hE]; trivial
  exact this

/-- `E^{(p)}` is closed if `E` is: it is a union of at most `|N(p)|` closed slices (F1). -/
lemma IsClosedSet.synDefect_closed [DecidableEq F] {η η' : ℝ} (hE : IsClosedSet η E) (i : ι)
    (p : P i) (hpos : 0 < η')
    (hsum : ((Finset.univ.filter fun u => H i p u ≠ 0).card : ℝ) * η ≤ η') :
    IsClosedSet η' (synDefect H E i p) := by
  rw [synDefect_eq_biUnion]
  refine IsClosedSet.biUnion_of_le (η := fun _ => η) (fun u _ => hE.sliceSet_closed i u) hpos ?_
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum

/-- The check sum of a word supported in `S` is supported in `S^{(p)}`. -/
lemma supportedIn_checkSum_synDefect {S : Set (ι → Fin n)} (ha : SupportedIn a S) (i : ι)
    (p : P i) : SupportedIn (checkSum i (H i p) a) (synDefect H S i p) :=
  supportedIn_checkSum ha i (H i p)

lemma synCond_iff : SynCond H E a ↔ ∀ (i : ι) (p : P i), checkSum i (H i p) a ∈
    boxplus (fun j : {j // j ≠ i} => kerCode (H j)) ⊔ supported F (synDefect H E i p) := Iff.rfl

/-- The decomposition `σ = w + f` given by `S(E)`. -/
lemma SynCond.exists_decomp (ha : SynCond H E a) (i : ι) (p : P i) :
    ∃ w ∈ boxplus (fun j : {j // j ≠ i} => kerCode (H j)),
      ∃ f, SupportedIn f (synDefect H E i p) ∧ checkSum i (H i p) a = w + f := by
  obtain ⟨w, hw, f, hf, hwf⟩ := Submodule.mem_sup.1 (ha i p)
  exact ⟨w, hw, f, hf, hwf.symm⟩

lemma synCond_of_decomp
    (h : ∀ (i : ι) (p : P i), ∃ w ∈ boxplus (fun j : {j // j ≠ i} => kerCode (H j)),
      ∃ f, SupportedIn f (synDefect H E i p) ∧ checkSum i (H i p) a = w + f) :
    SynCond H E a := by
  intro i p
  obtain ⟨w, hw, f, hf, hwf⟩ := h i p
  exact Submodule.mem_sup.2 ⟨w, hw, f, hf, hwf.symm⟩

/-- (iii) `S(E)` is monotone in `E`. -/
lemma SynCond.mono (ha : SynCond H E a) (hE : E ⊆ E') : SynCond H E' a := by
  intro i p
  have hle : boxplus (fun j : {j // j ≠ i} => kerCode (H j)) ⊔ supported F (synDefect H E i p) ≤
      boxplus (fun j : {j // j ≠ i} => kerCode (H j)) ⊔ supported F (synDefect H E' i p) :=
    sup_le_sup_left (supported_mono (synDefect_mono hE i p)) _
  exact hle (ha i p)

/-- (i) Every word of `⊞ ker H_i` satisfies `S(E)` for any `E`, in particular `S(∅)`. -/
lemma synCond_of_mem_boxplus (ha : a ∈ boxplus (fun i => kerCode (H i))) (E : Set (ι → Fin n)) :
    SynCond H E a := by
  intro i p
  exact Submodule.mem_sup_left
    (checkSum_row_mem_boxplus (C := fun i => kerCode (H i)) (H i) le_rfl p ha)

/-- (i) Every word of `⊞ ker H_i` satisfies `S(∅)`. -/
lemma synCond_empty_of_mem_boxplus (ha : a ∈ boxplus (fun i => kerCode (H i))) :
    SynCond H ∅ a :=
  synCond_of_mem_boxplus ha ∅

/-- Every word supported in `E` satisfies `S(E)`. -/
lemma synCond_of_supportedIn (ha : SupportedIn a E) : SynCond H E a := by
  intro i p
  exact Submodule.mem_sup_right (supportedIn_checkSum ha i (H i p))

lemma synCond_zero (E : Set (ι → Fin n)) : SynCond H E (0 : (ι → Fin n) → F) := by
  intro i p
  rw [map_zero]
  exact Submodule.zero_mem _

/-- Sums: `S(E)` and `S(E')` give `S(E ∪ E')` for the sum. -/
lemma SynCond.add_union (ha : SynCond H E a) (hb : SynCond H E' b) :
    SynCond H (E ∪ E') (a + b) := by
  intro i p
  rw [map_add]
  exact Submodule.add_mem _ ((ha.mono Set.subset_union_left) i p)
    ((hb.mono Set.subset_union_right) i p)

lemma SynCond.add (ha : SynCond H E a) (hb : SynCond H E b) : SynCond H E (a + b) := by
  simpa using ha.add_union hb

lemma SynCond.smul (ha : SynCond H E a) (c : F) : SynCond H E (c • a) := by
  intro i p
  rw [map_smul]
  exact Submodule.smul_mem _ c (ha i p)

lemma SynCond.neg (ha : SynCond H E a) : SynCond H E (-a) := by
  intro i p
  rw [map_neg]
  exact Submodule.neg_mem _ (ha i p)

lemma SynCond.sub (ha : SynCond H E a) (hb : SynCond H E b) : SynCond H E (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

/-- (ii) `S(E)` is preserved by adding words of `⊞ ker H_i`. -/
lemma SynCond.add_boxplus (ha : SynCond H E a) (hb : b ∈ boxplus (fun i => kerCode (H i))) :
    SynCond H E (a + b) :=
  ha.add (synCond_of_mem_boxplus hb E)

/-- (ii) `S(E)` is preserved by subtracting words of `⊞ ker H_i`. -/
lemma SynCond.sub_boxplus (ha : SynCond H E a) (hb : b ∈ boxplus (fun i => kerCode (H i))) :
    SynCond H E (a - b) :=
  ha.sub (synCond_of_mem_boxplus hb E)

/-- (ii) `S(E)` only depends on the class of `a` modulo `⊞ ker H_i`. -/
lemma synCond_add_boxplus_iff (hb : b ∈ boxplus (fun i => kerCode (H i))) :
    SynCond H E (a + b) ↔ SynCond H E a := by
  constructor
  · intro h
    simpa using h.sub_boxplus hb
  · intro h
    exact h.add_boxplus hb

/-- `S(E)` for `a` and `a = c + e` with `c ∈ ⊞ ker H_i` gives `S(E)` for `e`. -/
lemma SynCond.of_eq_add (ha : SynCond H E a) {c e : (ι → Fin n) → F}
    (hc : c ∈ boxplus (fun i => kerCode (H i))) (hace : a = c + e) : SynCond H E e := by
  have : e = a - c := by rw [hace]; abel
  rw [this]
  exact ha.sub_boxplus hc

/-- `d = 1`: if all directions coincide with `i`, then `S(E)` means `supp(H_i a) ⊆ N_i(E)`. -/
lemma synCond_iff_of_forall_eq {i : ι} (hι : ∀ j : ι, j = i) :
    SynCond H E a ↔ ∀ p : P i, (∑ u, H i p u * a (fun _ => u)) ≠ 0 →
      ∃ u, H i p u ≠ 0 ∧ (fun _ => u) ∈ E := by
  have hconst : ∀ (u : Fin n) (z : {j // j ≠ i} → Fin n), hglue i u z = fun _ => u := by
    intro u z
    funext j
    rw [hι j, hglue_apply_self]
  have hempty : IsEmpty {j // j ≠ i} := ⟨fun j => j.2 (hι j.1)⟩
  have hbot : boxplus (fun j : {j // j ≠ i} => kerCode (H j)) = ⊥ := by
    rw [boxplus]; exact iSup_of_empty _
  constructor
  · intro h p hp
    have := h i p
    rw [hbot, bot_sup_eq] at this
    obtain ⟨u, hu, hE⟩ := this (isEmptyElim) (by simpa [hconst] using hp)
    exact ⟨u, hu, by simpa [hconst] using hE⟩
  · intro h i' p
    obtain rfl := hι i'
    rw [hbot, bot_sup_eq]
    intro z hz
    obtain ⟨u, hu, hE⟩ := h p (by simpa [hconst] using hz)
    exact ⟨u, hu, by simpa [hconst] using hE⟩

end Syndrome

/-! ### Faces and hyperplanes

Two ways a face and a hyperplane interact; both are subcube embeddings (`IsSubcubeEmb`), so
`IsSubcubeEmb.comp_mem_lineSpan_sup` applies to them.

* The hyperplane `{z_i = u}` of an `I`-face (`i ∈ I`) lies in the hyperplane `{y_i = u}` of the
  cube: `faceHypPoint`, `checkSum_faceRestrict` (used in the face-syndrome lemma).
* An `I`-face with `j ∉ I` lies in hyperplanes `{y_j = t}`: `checkSum_comp_hproj_glue`
  (`(∑_t h(t) a|_{y_j=t})_{I,β} = ∑_t h(t) a_{I,(β,t)}`, used in step 3 of lemma D). -/

section FaceHyperplane

variable {I : Finset ι} {i : ι}

/-- Directions of the hyperplane cube of the face cube `{j // j ∈ I}` (for `i ∈ I`) as directions
of the hyperplane cube `{j // j ≠ i}` of the whole cube. -/
def faceHypEmb (hi : i ∈ I) : {j' : {j // j ∈ I} // j' ≠ ⟨i, hi⟩} → {j // j ≠ i} :=
  fun j' => ⟨j'.1.1, fun h => j'.2 (Subtype.ext h)⟩

/-- The point of the hyperplane cube `{j // j ≠ i} → Fin n` corresponding to the point `z` of the
hyperplane cube of the face `Φ_I(b)`: coordinates in `I ∖ {i}` are taken from `z`, the others
from `b`. -/
def faceHypPoint (hi : i ∈ I) (b : {j // j ∉ I} → Fin n)
    (z : {j' : {j // j ∈ I} // j' ≠ ⟨i, hi⟩} → Fin n) : {j // j ≠ i} → Fin n :=
  fun j => if h : j.1 ∈ I then z ⟨⟨j.1, h⟩, fun h' => j.2 (congrArg Subtype.val h')⟩
    else b ⟨j.1, h⟩

omit [DecidableEq ι] in
@[simp] lemma faceHypEmb_val (hi : i ∈ I) (j' : {j' : {j // j ∈ I} // j' ≠ ⟨i, hi⟩}) :
    (faceHypEmb hi j').1 = j'.1.1 := rfl

omit [DecidableEq ι] in
lemma mem_range_faceHypEmb (hi : i ∈ I) (j : {j // j ≠ i}) :
    j ∈ Set.range (faceHypEmb hi) ↔ j.1 ∈ I := by
  constructor
  · rintro ⟨j', rfl⟩; exact j'.1.2
  · intro h
    exact ⟨⟨⟨j.1, h⟩, fun h' => j.2 (congrArg Subtype.val h')⟩, rfl⟩

lemma isSubcubeEmb_faceHypPoint (hi : i ∈ I) (b : {j // j ∉ I} → Fin n) :
    IsSubcubeEmb (faceHypEmb hi) (faceHypPoint hi b) where
  injective := by
    intro j₁ j₂ h
    have h' := congrArg Subtype.val h
    apply Subtype.ext; apply Subtype.ext
    exact h'
  apply_map z j' := by
    unfold faceHypPoint
    exact dite_eq_left_of_eq_true (eq_true (show (faceHypEmb hi j').1 ∈ I from j'.1.2))
  apply_out z z' j hj := by
    have hjI : j.1 ∉ I := fun h => hj ((mem_range_faceHypEmb hi j).2 h)
    simp only [faceHypPoint, hjI, dite_false]

/-- `(y_i = u, faceHypPoint z) = (glue (z_i = u) b)`: the two ways of building a point of the
cube from a point of the hyperplane of the face. -/
lemma hglue_faceHypPoint (hi : i ∈ I) (b : {j // j ∉ I} → Fin n) (u : Fin n)
    (z : {j' : {j // j ∈ I} // j' ≠ ⟨i, hi⟩} → Fin n) :
    hglue i u (faceHypPoint hi b z) = glue I (hglue ⟨i, hi⟩ u z) b := by
  funext j
  by_cases hji : j = i
  · subst hji
    rw [hglue_apply_self, glue_apply_of_mem I _ _ hi, hglue_apply_self]
  · rw [hglue_apply_of_ne hji]
    by_cases hj : j ∈ I
    · have hne : (⟨j, hj⟩ : {j // j ∈ I}) ≠ ⟨i, hi⟩ := fun h => hji (congrArg Subtype.val h)
      rw [glue_apply_of_mem I _ _ hj, hglue_apply_of_ne hne]
      simp [faceHypPoint, hj]
    · rw [glue_apply_of_not_mem I _ _ hj]
      simp [faceHypPoint, hj]

/-- **Check sums commute with restriction to faces**: the check sum (direction `i ∈ I`) of
`a_{I,b}` is the restriction of the check sum of `a` to the face of the hyperplane cube given by
`faceHypPoint`. -/
lemma checkSum_faceRestrict (hi : i ∈ I) (h : Fin n → F) (a : (ι → Fin n) → F)
    (b : {j // j ∉ I} → Fin n) :
    checkSum ⟨i, hi⟩ h (faceRestrict a I b) = checkSum i h a ∘ faceHypPoint hi b := by
  funext z
  simp only [checkSum_apply, faceRestrict_apply, Function.comp_apply, hglue_faceHypPoint]

/-- The defect `E^{(p)}` restricted to the face of the hyperplane cube is `(E_{I,b})^{(p)}`. -/
lemma preimage_synDefect_faceHypPoint {P : ι → Type*} (H : ∀ i, Matrix (P i) (Fin n) F)
    (E : Set (ι → Fin n)) (hi : i ∈ I) (p : P i) (b : {j // j ∉ I} → Fin n) :
    faceHypPoint hi b ⁻¹' synDefect H E i p =
      synDefect (fun j : {j // j ∈ I} => H j) {z | glue I z b ∈ E} ⟨i, hi⟩ p := by
  ext z
  simp only [Set.mem_preimage, mem_synDefect, hglue_faceHypPoint, Set.mem_ofPred_eq]

variable {j : ι}

/-- Directions of an `I`-face, `j ∉ I`, as directions of the hyperplane cube `{k // k ≠ j}`. -/
def faceToHyp (hj : j ∉ I) : {k // k ∈ I} → {k // k ≠ j} :=
  fun k => ⟨k.1, fun h => hj (h ▸ k.2)⟩

omit [DecidableEq ι] in
@[simp] lemma faceToHyp_val (hj : j ∉ I) (k : {k // k ∈ I}) : (faceToHyp hj k).1 = k.1 := rfl

omit [DecidableEq ι] in
lemma mem_range_faceToHyp (hj : j ∉ I) (k : {k // k ≠ j}) :
    k ∈ Set.range (faceToHyp hj) ↔ k.1 ∈ I := by
  constructor
  · rintro ⟨k', rfl⟩; exact k'.2
  · intro h; exact ⟨⟨k.1, h⟩, rfl⟩

/-- An `I`-face with `j ∉ I` sits in the hyperplane cube `{k // k ≠ j}`. -/
lemma isSubcubeEmb_hproj_glue (hj : j ∉ I) (p : {k // k ∉ I} → Fin n) :
    IsSubcubeEmb (faceToHyp hj) (fun z => hproj j (glue I z p)) where
  injective := by
    intro k₁ k₂ h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  apply_map z k := by
    simp only [hproj_apply, faceToHyp_val]
    exact glue_apply_val_mem I z p k
  apply_out z z' k hk := by
    have hkI : k.1 ∉ I := fun h => hk ((mem_range_faceToHyp hj k).2 h)
    simp only [hproj_apply, glue_apply_of_not_mem I _ _ hkI]

/-- `(∑_t h(t) a|_{y_j = t})_{I,β} = ∑_t h(t) a_{I,(β,t)}` for `j ∉ I`, where the face of the
hyperplane cube is embedded by `z ↦ hproj j (glue I z p)` and `(β,t) = update p j t`. -/
lemma checkSum_comp_hproj_glue (hj : j ∉ I) (p : {k // k ∉ I} → Fin n) (h : Fin n → F)
    (a : (ι → Fin n) → F) :
    checkSum j h a ∘ (fun z => hproj j (glue I z p)) =
      ∑ t, h t • faceRestrict a I (Function.update p ⟨j, hj⟩ t) := by
  funext z
  simp only [Function.comp_apply, checkSum_apply, hglue_hproj_eq_update, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, faceRestrict_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [update_glue_of_not_mem I z p hj]

end FaceHyperplane

end ProductExpansion
