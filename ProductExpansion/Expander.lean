import ProductExpansion.Basic

/-!
# Expander lemmas: unique neighbours, distance, greedy closure `F_θ`

Formalisation of the auxiliary statements of the proof
(lemmas `gen-unique` and `gen-find`).

* `nbrs H u` — the checks adjacent to the variable `u` (`N(u)`);
* `vnbrs H p` — the variables adjacent to the check `p` (`N(p)`);
* `uniqueNbhd H S` — the unique neighbours `U(S)` of `S` (checks with exactly one neighbour
  in `S`);
* `IsFindClosed H θ R L` — every `u ∉ L` has fewer than `θ` neighbours in `R ∪ N(L)`;
* `findClosure H θ R` — `F_θ(R)`, the intersection of all `L` with `IsFindClosed H θ R L`
  (it is itself `θ`-closed, hence the smallest such set);
* `GreedyReach H θ R L` — `L` is obtained from `∅` by steps of the greedy procedure.
-/

open Finset

namespace ProductExpansion

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

section Defs

/-- `N(u)`: the checks adjacent to the variable `u`. -/
def nbrs (H : Matrix P (Fin n) F) (u : Fin n) : Finset P :=
  Finset.univ.filter fun p => H p u ≠ 0

/-- `N(p)`: the variables adjacent to the check `p`. -/
def vnbrs (H : Matrix P (Fin n) F) (p : P) : Finset (Fin n) :=
  Finset.univ.filter fun u => H p u ≠ 0

/-- `U(S)`: the unique neighbours of `S`, i.e. the checks having exactly one neighbour in `S`. -/
def uniqueNbhd (H : Matrix P (Fin n) F) (S : Finset (Fin n)) : Finset P :=
  Finset.univ.filter fun p => (vnbrs H p ∩ S).card = 1

end Defs

section API

variable (H : Matrix P (Fin n) F)

omit [DecidableEq P] in
@[simp] lemma mem_nbrs {u : Fin n} {p : P} : p ∈ nbrs H u ↔ H p u ≠ 0 := by
  simp [nbrs]

omit [Fintype P] [DecidableEq P] in
@[simp] lemma mem_vnbrs {u : Fin n} {p : P} : u ∈ vnbrs H p ↔ H p u ≠ 0 := by
  simp [vnbrs]

omit [DecidableEq P] in
lemma mem_vnbrs_iff_mem_nbrs {u : Fin n} {p : P} : u ∈ vnbrs H p ↔ p ∈ nbrs H u := by
  simp

lemma nbhd_eq_biUnion (S : Finset (Fin n)) : nbhd H S = S.biUnion (nbrs H) := rfl

lemma mem_nbhd {S : Finset (Fin n)} {p : P} : p ∈ nbhd H S ↔ ∃ u ∈ S, H p u ≠ 0 := by
  simp [nbhd]

lemma mem_nbhd_iff_nonempty {S : Finset (Fin n)} {p : P} :
    p ∈ nbhd H S ↔ (vnbrs H p ∩ S).Nonempty := by
  rw [mem_nbhd]
  constructor
  · rintro ⟨u, hu, hpu⟩
    exact ⟨u, mem_inter.2 ⟨(mem_vnbrs H).2 hpu, hu⟩⟩
  · rintro ⟨u, hu⟩
    rw [mem_inter, mem_vnbrs] at hu
    exact ⟨u, hu.2, hu.1⟩

lemma nbrs_subset_nbhd {S : Finset (Fin n)} {u : Fin n} (hu : u ∈ S) : nbrs H u ⊆ nbhd H S := by
  intro p hp
  exact (mem_nbhd H).2 ⟨u, hu, (mem_nbrs H).1 hp⟩

lemma nbhd_mono {S T : Finset (Fin n)} (h : S ⊆ T) : nbhd H S ⊆ nbhd H T :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

@[simp] lemma nbhd_empty : nbhd H (∅ : Finset (Fin n)) = ∅ := by
  simp [nbhd]

lemma nbhd_insert (S : Finset (Fin n)) (u : Fin n) :
    nbhd H (insert u S) = nbrs H u ∪ nbhd H S := by
  simp only [nbhd_eq_biUnion, Finset.biUnion_insert]

omit [DecidableEq P] in
@[simp] lemma mem_uniqueNbhd {S : Finset (Fin n)} {p : P} :
    p ∈ uniqueNbhd H S ↔ (vnbrs H p ∩ S).card = 1 := by
  simp [uniqueNbhd]

lemma uniqueNbhd_subset_nbhd (S : Finset (Fin n)) : uniqueNbhd H S ⊆ nbhd H S := by
  intro p hp
  rw [mem_uniqueNbhd] at hp
  rw [mem_nbhd_iff_nonempty, ← Finset.card_pos, hp]
  exact Nat.one_pos

/-- **Double counting** of the edges between `S ⊆ V` and `T ⊆ P`. -/
lemma sum_card_nbrs_inter_eq (S : Finset (Fin n)) (T : Finset P) :
    ∑ u ∈ S, (nbrs H u ∩ T).card = ∑ p ∈ T, (vnbrs H p ∩ S).card := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (u : Fin n) (p : P) => H p u ≠ 0) (s := S) (t := T)
  convert h using 2 with u _ p _
  · congr 1
    ext p
    simp [Finset.bipartiteAbove, and_comm]
  · congr 1
    ext u
    simp [Finset.bipartiteBelow, and_comm]

/-- `δ|S| = ∑_{p ∈ N(S)} |N(p) ∩ S|` (in the form `∑_{u ∈ S} |N(u)|`). -/
lemma sum_card_vnbrs_inter_nbhd (S : Finset (Fin n)) :
    ∑ p ∈ nbhd H S, (vnbrs H p ∩ S).card = ∑ u ∈ S, (nbrs H u).card := by
  rw [← sum_card_nbrs_inter_eq]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.inter_eq_left.2 (nbrs_subset_nbhd H hu)]

/-- Every unique neighbour of `S` is joined to `S` by exactly one edge, so the number of edges
between `S` and `U(S)` is `|U(S)|`. -/
lemma sum_card_nbrs_inter_uniqueNbhd (S : Finset (Fin n)) :
    ∑ u ∈ S, (nbrs H u ∩ uniqueNbhd H S).card = (uniqueNbhd H S).card := by
  rw [sum_card_nbrs_inter_eq, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact (mem_uniqueNbhd H).1 hp

end API

/-! ### Lemma `gen-unique`: unique neighbours -/

section Unique

variable {H : Matrix P (Fin n) F} {δ Δ : ℕ} {α ε : ℝ}

lemma IsExpanderMatrix.card_nbrs (hH : IsExpanderMatrix H δ Δ α ε) (u : Fin n) :
    (nbrs H u).card = δ :=
  hH.leftDeg u

lemma IsExpanderMatrix.card_vnbrs_le (hH : IsExpanderMatrix H δ Δ α ε) (p : P) :
    (vnbrs H p).card ≤ Δ :=
  hH.rightDeg p

lemma IsExpanderMatrix.sum_card_nbrs (hH : IsExpanderMatrix H δ Δ α ε) (S : Finset (Fin n)) :
    ∑ u ∈ S, (nbrs H u).card = δ * S.card := by
  simp [hH.card_nbrs, mul_comm]

/-- `|N(S)| ≤ δ|S|`. -/
lemma IsExpanderMatrix.card_nbhd_le (hH : IsExpanderMatrix H δ Δ α ε) (S : Finset (Fin n)) :
    (nbhd H S).card ≤ δ * S.card := by
  rw [nbhd_eq_biUnion, ← hH.sum_card_nbrs]
  exact Finset.card_biUnion_le

/-- `δ|S| = ∑_{p ∈ N(S) \ U(S)} |N(p) ∩ S| + |U(S)|`. -/
lemma IsExpanderMatrix.sum_nonunique_add_card_uniqueNbhd (hH : IsExpanderMatrix H δ Δ α ε)
    (S : Finset (Fin n)) :
    ∑ p ∈ nbhd H S \ uniqueNbhd H S, (vnbrs H p ∩ S).card + (uniqueNbhd H S).card =
      δ * S.card := by
  have h1 := Finset.sum_sdiff (f := fun p => (vnbrs H p ∩ S).card) (uniqueNbhd_subset_nbhd H S)
  have h2 : ∑ p ∈ uniqueNbhd H S, (vnbrs H p ∩ S).card = (uniqueNbhd H S).card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun p hp => (mem_uniqueNbhd H).1 hp
  rw [← h2, h1, sum_card_vnbrs_inter_nbhd, hH.sum_card_nbrs]

/-- Every check of `N(S) \ U(S)` has at least two neighbours in `S`. -/
lemma two_mul_card_le_sum_nonunique (H : Matrix P (Fin n) F) (S : Finset (Fin n)) :
    2 * (nbhd H S \ uniqueNbhd H S).card ≤
      ∑ p ∈ nbhd H S \ uniqueNbhd H S, (vnbrs H p ∩ S).card := by
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [mem_sdiff, mem_nbhd_iff_nonempty, mem_uniqueNbhd] at hp
  have := hp.1.card_pos
  omega

/-- Real-valued form of the counting identities behind lemma `gen-unique`. -/
private lemma IsExpanderMatrix.unique_aux (hH : IsExpanderMatrix H δ Δ α ε)
    (S : Finset (Fin n)) :
    (∑ p ∈ nbhd H S \ uniqueNbhd H S, ((vnbrs H p ∩ S).card : ℝ)) +
        (uniqueNbhd H S).card = δ * S.card ∧
      2 * ((nbhd H S \ uniqueNbhd H S).card : ℝ) ≤
        ∑ p ∈ nbhd H S \ uniqueNbhd H S, ((vnbrs H p ∩ S).card : ℝ) ∧
      ((nbhd H S \ uniqueNbhd H S).card : ℝ) + (uniqueNbhd H S).card = (nbhd H S).card := by
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hH.sum_nonunique_add_card_uniqueNbhd S
  · exact_mod_cast two_mul_card_le_sum_nonunique H S
  · exact_mod_cast Finset.card_sdiff_add_card_eq_card (uniqueNbhd_subset_nbhd H S)

/-- **Lemma `gen-unique`, part 1.** If `|S| ≤ αn`, then `|U(S)| ≥ (1 - 2ε) δ |S|`. -/
theorem IsExpanderMatrix.card_uniqueNbhd_ge (hH : IsExpanderMatrix H δ Δ α ε)
    {S : Finset (Fin n)} (hS : (S.card : ℝ) ≤ α * n) :
    (1 - 2 * ε) * δ * S.card ≤ (uniqueNbhd H S).card := by
  have hexp := hH.expand S hS
  obtain ⟨h1, h2, h3⟩ := hH.unique_aux S
  linarith

/-- **Lemma `gen-unique`, part 2.** If `|S| ≤ αn`, then the number of edges between `S` and
`N(S) \ U(S)` is at most `2εδ|S|` (edges counted from the check side). -/
theorem IsExpanderMatrix.sum_card_nonunique_le (hH : IsExpanderMatrix H δ Δ α ε)
    {S : Finset (Fin n)} (hS : (S.card : ℝ) ≤ α * n) :
    (∑ p ∈ nbhd H S \ uniqueNbhd H S, ((vnbrs H p ∩ S).card : ℝ)) ≤ 2 * ε * δ * S.card := by
  have h := hH.card_uniqueNbhd_ge hS
  obtain ⟨h1, -, -⟩ := hH.unique_aux S
  linarith

/-- **Lemma `gen-unique`, part 2** (edges counted from the variable side): if `|S| ≤ αn`, then
`∑_{u ∈ S} |N(u) \ U(S)| ≤ 2εδ|S|`. -/
theorem IsExpanderMatrix.sum_card_nbrs_sdiff_uniqueNbhd_le (hH : IsExpanderMatrix H δ Δ α ε)
    {S : Finset (Fin n)} (hS : (S.card : ℝ) ≤ α * n) :
    (∑ u ∈ S, ((nbrs H u \ uniqueNbhd H S).card : ℝ)) ≤ 2 * ε * δ * S.card := by
  have h := hH.card_uniqueNbhd_ge hS
  have h1 : ∑ u ∈ S, (nbrs H u \ uniqueNbhd H S).card + (uniqueNbhd H S).card = δ * S.card := by
    rw [← sum_card_nbrs_inter_uniqueNbhd, ← Finset.sum_add_distrib, ← hH.sum_card_nbrs]
    exact Finset.sum_congr rfl fun u _ => Finset.card_sdiff_add_card_inter _ _
  have h1' : (∑ u ∈ S, ((nbrs H u \ uniqueNbhd H S).card : ℝ)) + (uniqueNbhd H S).card =
      δ * S.card := by
    exact_mod_cast h1
  linarith

end Unique

/-! ### Syndrome at a unique neighbour and the distance bound -/

section Distance

omit [Fintype P] [DecidableEq P] in
/-- If `u` is the only variable adjacent to `p` in the support of `e`, then
`(He)_p = H p u · e u`. -/
lemma mulVec_apply_eq_of_unique (H : Matrix P (Fin n) F) {e : Fin n → F} {p : P} {u : Fin n}
    (h : ∀ v, H p v ≠ 0 → e v ≠ 0 → v = u) : H.mulVec e p = H p u * e u := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_single u (fun v _ hv => ?_) (fun hu => absurd (mem_univ u) hu)
  by_contra hne
  exact hv (h v (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))

omit [Fintype P] [DecidableEq P] in
/-- If `u` is the unique neighbour of `p` in the support of `e`, then `(He)_p ≠ 0`. -/
lemma mulVec_apply_ne_zero_of_unique (H : Matrix P (Fin n) F) {e : Fin n → F} {p : P}
    {u : Fin n} (hpu : H p u ≠ 0) (heu : e u ≠ 0) (h : ∀ v, H p v ≠ 0 → e v ≠ 0 → v = u) :
    H.mulVec e p ≠ 0 := by
  rw [mulVec_apply_eq_of_unique H h]
  exact mul_ne_zero hpu heu

omit [DecidableEq F] [Fintype P] [DecidableEq P] in
lemma mem_kerCode_iff (H : Matrix P (Fin n) F) {c : Fin n → F} :
    c ∈ kerCode H ↔ H.mulVec c = 0 := by
  simp [kerCode, LinearMap.mem_ker]

variable {H : Matrix P (Fin n) F} {δ Δ : ℕ} {α ε : ℝ}

/-- **Lemma `gen-unique`, part 3** (contrapositive form): a codeword of `ker H` with support of
size at most `αn` is zero (if `δ > 0` and `ε < 1/2`). -/
theorem IsExpanderMatrix.eq_zero_of_mem_kerCode (hH : IsExpanderMatrix H δ Δ α ε)
    (hδ : 0 < δ) (hε : ε < 1 / 2) {c : Fin n → F} (hc : c ∈ kerCode H)
    (hcard : ((Finset.univ.filter fun u => c u ≠ 0).card : ℝ) ≤ α * n) : c = 0 := by
  set S := Finset.univ.filter fun u => c u ≠ 0
  by_contra hc0
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hc0
    funext u
    by_contra hu
    have : u ∈ S := by simpa [S] using hu
    rw [h] at this
    simp at this
  have hU := hH.card_uniqueNbhd_ge hcard
  have hpos : 0 < (1 - 2 * ε) * δ * S.card := by
    have h1 : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
    have h2 : (0 : ℝ) < δ := by exact_mod_cast hδ
    have h3 : 0 < 1 - 2 * ε := by linarith
    exact mul_pos (mul_pos h3 h2) h1
  have hUne : (uniqueNbhd H S).Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hpos.trans_le hU
  obtain ⟨p, hp⟩ := hUne
  rw [mem_uniqueNbhd, Finset.card_eq_one] at hp
  obtain ⟨u, hu⟩ := hp
  have huS : u ∈ vnbrs H p ∩ S := by rw [hu]; exact mem_singleton_self u
  rw [mem_inter, mem_vnbrs] at huS
  have hcu : c u ≠ 0 := by simpa [S] using huS.2
  have hker : H.mulVec c = 0 := (mem_kerCode_iff H).1 hc
  refine mulVec_apply_ne_zero_of_unique H huS.1 hcu ?_ (congrFun hker p)
  intro v hpv hcv
  have hv : v ∈ vnbrs H p ∩ S := by simp [S, hpv, hcv]
  rw [hu] at hv
  exact mem_singleton.1 hv

/-- **Lemma `gen-unique`, part 3.** The minimum distance of `ker H` is greater than `αn`:
every nonzero codeword has more than `αn` nonzero coordinates (if `δ > 0` and `ε < 1/2`). -/
theorem IsExpanderMatrix.lt_card_supp_of_mem_kerCode (hH : IsExpanderMatrix H δ Δ α ε)
    (hδ : 0 < δ) (hε : ε < 1 / 2) {c : Fin n → F} (hc : c ∈ kerCode H) (hc0 : c ≠ 0) :
    α * n < ((Finset.univ.filter fun u => c u ≠ 0).card : ℝ) := by
  by_contra h
  exact hc0 (hH.eq_zero_of_mem_kerCode hδ hε hc (not_lt.1 h))

end Distance

/-! ### The closure `F_θ(R)` -/

section Closure

/-- `L` is `θ`-closed relative to `R ⊆ P`: every variable `u ∉ L` has fewer than `θ` neighbours
in `R ∪ N(L)`. -/
def IsFindClosed (H : Matrix P (Fin n) F) (θ : ℝ) (R : Finset P) (L : Finset (Fin n)) : Prop :=
  ∀ u ∉ L, ((nbrs H u ∩ (R ∪ nbhd H L)).card : ℝ) < θ

/-- `F_θ(R)`: the intersection of all `θ`-closed sets `L` (relative to `R`). By
`findClosure_isFindClosed` and `findClosure_subset` it is the smallest `θ`-closed set. -/
noncomputable def findClosure (H : Matrix P (Fin n) F) (θ : ℝ) (R : Finset P) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun u => ∀ L : Finset (Fin n), IsFindClosed H θ R L → u ∈ L

variable {H : Matrix P (Fin n) F} {θ θ' : ℝ} {R R' : Finset P} {L L₁ L₂ : Finset (Fin n)}

lemma mem_findClosure {u : Fin n} :
    u ∈ findClosure H θ R ↔ ∀ L, IsFindClosed H θ R L → u ∈ L := by
  classical
  simp [findClosure]

lemma isFindClosed_univ : IsFindClosed H θ R Finset.univ :=
  fun u hu => absurd (mem_univ u) hu

/-- Criterion: `L` is `θ`-closed if every `u ∉ L` lies outside some `θ`-closed superset of `L`.
In particular, the intersection of any family of `θ`-closed sets is `θ`-closed. -/
lemma isFindClosed_of_forall (h : ∀ u ∉ L, ∃ M, IsFindClosed H θ R M ∧ L ⊆ M ∧ u ∉ M) :
    IsFindClosed H θ R L := by
  intro u hu
  obtain ⟨M, hM, hLM, huM⟩ := h u hu
  refine lt_of_le_of_lt ?_ (hM u huM)
  exact_mod_cast Finset.card_le_card
    (Finset.inter_subset_inter_left (Finset.union_subset_union_right (nbhd_mono H hLM)))

/-- `θ`-closed sets are closed under intersection. -/
lemma IsFindClosed.inter (h₁ : IsFindClosed H θ R L₁) (h₂ : IsFindClosed H θ R L₂) :
    IsFindClosed H θ R (L₁ ∩ L₂) := by
  refine isFindClosed_of_forall fun u hu => ?_
  rw [mem_inter, not_and_or] at hu
  rcases hu with hu | hu
  · exact ⟨L₁, h₁, inter_subset_left, hu⟩
  · exact ⟨L₂, h₂, inter_subset_right, hu⟩

/-- `F_θ(R)` is contained in every `θ`-closed set. -/
theorem findClosure_subset (hL : IsFindClosed H θ R L) : findClosure H θ R ⊆ L :=
  fun _ hu => mem_findClosure.1 hu L hL

/-- `F_θ(R)` is itself `θ`-closed: every `u ∉ F_θ(R)` has fewer than `θ` neighbours in
`R ∪ N(F_θ(R))`. -/
theorem findClosure_isFindClosed : IsFindClosed H θ R (findClosure H θ R) := by
  refine isFindClosed_of_forall fun u hu => ?_
  rw [mem_findClosure] at hu
  push Not at hu
  obtain ⟨L, hL, huL⟩ := hu
  exact ⟨L, hL, findClosure_subset hL, huL⟩

/-- `F_θ(R)` is the smallest `θ`-closed set. -/
theorem isLeast_findClosure : IsLeast {L | IsFindClosed H θ R L} (findClosure H θ R) :=
  ⟨findClosure_isFindClosed, fun _ hL => findClosure_subset hL⟩

lemma IsFindClosed.mono_right (h : R ⊆ R') (hL : IsFindClosed H θ R' L) :
    IsFindClosed H θ R L := by
  intro u hu
  refine lt_of_le_of_lt ?_ (hL u hu)
  exact_mod_cast Finset.card_le_card
    (Finset.inter_subset_inter_left (Finset.union_subset_union_left h))

lemma IsFindClosed.mono_threshold (h : θ ≤ θ') (hL : IsFindClosed H θ R L) :
    IsFindClosed H θ' R L :=
  fun u hu => (hL u hu).trans_le h

/-- `F_θ` is monotone in `R`. -/
theorem findClosure_mono (h : R ⊆ R') : findClosure H θ R ⊆ findClosure H θ R' :=
  findClosure_subset (findClosure_isFindClosed.mono_right h)

/-- `F_θ` is antitone in the threshold `θ`. -/
theorem findClosure_anti_threshold (h : θ ≤ θ') : findClosure H θ' R ⊆ findClosure H θ R :=
  findClosure_subset (findClosure_isFindClosed.mono_threshold h)

/-- Every variable with at least `θ` neighbours in `R` lies in `F_θ(R)`. -/
theorem mem_findClosure_of_le {u : Fin n} (hu : θ ≤ ((nbrs H u ∩ R).card : ℝ)) :
    u ∈ findClosure H θ R := by
  rw [mem_findClosure]
  intro L hL
  by_contra huL
  have h1 := hL u huL
  have h2 : ((nbrs H u ∩ R).card : ℝ) ≤ (nbrs H u ∩ (R ∪ nbhd H L)).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left Finset.subset_union_left)
  linarith

/-- `S ⊆ F_θ(N(S))` for `θ ≤ δ`. -/
theorem IsExpanderMatrix.subset_findClosure_nbhd {δ Δ : ℕ} {α ε : ℝ}
    (hH : IsExpanderMatrix H δ Δ α ε) (hθ : θ ≤ δ) (S : Finset (Fin n)) :
    S ⊆ findClosure H θ (nbhd H S) := by
  intro u hu
  apply mem_findClosure_of_le
  rw [Finset.inter_eq_left.2 (nbrs_subset_nbhd H hu), hH.card_nbrs]
  exact hθ

end Closure

/-! ### The greedy procedure -/

section Greedy

/-- The sets produced by the greedy procedure computing `F_θ(R)`: starting from `∅`, repeatedly
add a variable `u ∉ L` having at least `θ` neighbours in `R ∪ N(L)`. -/
inductive GreedyReach (H : Matrix P (Fin n) F) (θ : ℝ) (R : Finset P) : Finset (Fin n) → Prop
  | empty : GreedyReach H θ R ∅
  | step {L : Finset (Fin n)} {u : Fin n} : GreedyReach H θ R L → u ∉ L →
      θ ≤ ((nbrs H u ∩ (R ∪ nbhd H L)).card : ℝ) → GreedyReach H θ R (insert u L)

variable {H : Matrix P (Fin n) F} {θ : ℝ} {R : Finset P} {L M : Finset (Fin n)}

/-- Every greedily reachable set is contained in every `θ`-closed set. -/
theorem GreedyReach.subset_of_isFindClosed (hL : GreedyReach H θ R L)
    (hM : IsFindClosed H θ R M) : L ⊆ M := by
  induction hL with
  | empty => exact Finset.empty_subset _
  | @step L u _ _ hθu ih =>
    intro v hv
    rw [mem_insert] at hv
    rcases hv with rfl | hv
    · by_contra hvM
      have h1 := hM v hvM
      have h2 : ((nbrs H v ∩ (R ∪ nbhd H L)).card : ℝ) ≤ (nbrs H v ∩ (R ∪ nbhd H M)).card := by
        exact_mod_cast Finset.card_le_card
          (Finset.inter_subset_inter_left (Finset.union_subset_union_right (nbhd_mono H ih)))
      linarith
    · exact ih hv

theorem GreedyReach.subset_findClosure (hL : GreedyReach H θ R L) : L ⊆ findClosure H θ R :=
  fun _ hu => mem_findClosure.2 fun _ hM => hL.subset_of_isFindClosed hM hu

/-- The greedy procedure terminates with a `θ`-closed set. -/
theorem exists_greedyReach_isFindClosed :
    ∃ L, GreedyReach H θ R L ∧ IsFindClosed H θ R L := by
  classical
  obtain ⟨L, hL, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (GreedyReach H θ R))
    Finset.card ⟨∅, by simp [GreedyReach.empty]⟩
  rw [mem_filter] at hL
  refine ⟨L, hL.2, fun u hu => ?_⟩
  by_contra hθu
  push Not at hθu
  have h := hmax (insert u L) (mem_filter.2 ⟨mem_univ _, hL.2.step hu hθu⟩)
  rw [card_insert_of_notMem hu] at h
  omega

/-- The result of the greedy procedure does not depend on the order of steps: every terminal
(i.e. `θ`-closed) greedily reachable set equals `F_θ(R)`. -/
theorem GreedyReach.eq_findClosure (hL : GreedyReach H θ R L) (hc : IsFindClosed H θ R L) :
    L = findClosure H θ R :=
  Subset.antisymm hL.subset_findClosure (findClosure_subset hc)

/-- `F_θ(R)` is produced by the greedy procedure. -/
theorem greedyReach_findClosure : GreedyReach H θ R (findClosure H θ R) := by
  obtain ⟨L, hL, hc⟩ := exists_greedyReach_isFindClosed (H := H) (θ := θ) (R := R)
  rw [← hL.eq_findClosure hc]
  exact hL

variable {δ Δ : ℕ} {α ε : ℝ}

/-- Along the greedy procedure, `|R ∪ N(L)| ≤ |R| + (δ - θ)|L|`. -/
theorem IsExpanderMatrix.card_union_nbhd_le_of_greedyReach (hH : IsExpanderMatrix H δ Δ α ε)
    (hL : GreedyReach H θ R L) :
    ((R ∪ nbhd H L).card : ℝ) ≤ R.card + (δ - θ) * L.card := by
  induction hL with
  | empty => simp
  | @step L u _ hu hθu ih =>
    have h1 : R ∪ nbhd H (insert u L) = (R ∪ nbhd H L) ∪ (nbrs H u \ (R ∪ nbhd H L)) := by
      rw [nbhd_insert, Finset.union_sdiff_self_eq_union]
      ext p
      simp only [mem_union]
      tauto
    have h2 : (R ∪ nbhd H (insert u L)).card ≤
        (R ∪ nbhd H L).card + (nbrs H u \ (R ∪ nbhd H L)).card := by
      rw [h1]
      exact Finset.card_union_le _ _
    have h3 : (nbrs H u \ (R ∪ nbhd H L)).card + (nbrs H u ∩ (R ∪ nbhd H L)).card = δ := by
      rw [Finset.card_sdiff_add_card_inter, hH.card_nbrs]
    have h2' : ((R ∪ nbhd H (insert u L)).card : ℝ) ≤
        (R ∪ nbhd H L).card + (nbrs H u \ (R ∪ nbhd H L)).card := by
      exact_mod_cast h2
    have h3' : ((nbrs H u \ (R ∪ nbhd H L)).card : ℝ) + (nbrs H u ∩ (R ∪ nbhd H L)).card =
        δ := by
      exact_mod_cast h3
    rw [card_insert_of_notMem hu]
    push_cast
    linarith

/-- Size bound along the greedy procedure (proof of lemma `gen-find` (a)): while the procedure
runs, `(1 - ε)δ|L| ≤ |N(L)| ≤ |R| + (δ - θ)|L|`, so `|L| ≤ |R| / (θ - εδ) ≤ αn/2`, and the
condition `|L| ≤ αn` needed for expansion is preserved since `αn ≥ 2`. -/
theorem IsExpanderMatrix.card_le_of_greedyReach (hH : IsExpanderMatrix H δ Δ α ε)
    (hαn : 2 ≤ α * n) (hθ : ε * δ < θ) (hR : (R.card : ℝ) ≤ (θ - ε * δ) * α * n / 2)
    (hL : GreedyReach H θ R L) :
    (L.card : ℝ) ≤ R.card / (θ - ε * δ) := by
  have hpos : 0 < θ - ε * δ := by linarith
  induction hL with
  | empty =>
    simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (Nat.cast_nonneg _) hpos.le
  | @step L u hL' hu hθu ih =>
    have hR' : (R.card : ℝ) / (θ - ε * δ) ≤ α * n / 2 := by
      rw [div_le_iff₀ hpos]
      linarith
    have hcard : ((insert u L).card : ℝ) ≤ α * n := by
      rw [card_insert_of_notMem hu]
      push_cast
      linarith
    have hexp := hH.expand _ hcard
    have hN := hH.card_union_nbhd_le_of_greedyReach (hL'.step hu hθu)
    have hsub : ((nbhd H (insert u L)).card : ℝ) ≤ (R ∪ nbhd H (insert u L)).card := by
      exact_mod_cast Finset.card_le_card Finset.subset_union_right
    rw [le_div_iff₀ hpos]
    linarith

/-- **Lemma `gen-find` (a).** If `αn ≥ 2`, `εδ < θ` and `|R| ≤ (θ - εδ)αn/2`, then
`|F_θ(R)| ≤ |R| / (θ - εδ)`. (The condition `θ ≤ δ` is not needed.) -/
theorem IsExpanderMatrix.card_findClosure_le (hH : IsExpanderMatrix H δ Δ α ε)
    (hαn : 2 ≤ α * n) (hθ : ε * δ < θ) (hR : (R.card : ℝ) ≤ (θ - ε * δ) * α * n / 2) :
    ((findClosure H θ R).card : ℝ) ≤ R.card / (θ - ε * δ) :=
  hH.card_le_of_greedyReach hαn hθ hR greedyReach_findClosure

end Greedy

/-! ### Lemma `gen-find` (b) -/

section FindB

variable {H : Matrix P (Fin n) F} {δ Δ : ℕ} {α ε : ℝ}

/-- **Lemma `gen-find` (b).** Let `h = (1 - 2ε)δ`. If `|supp e| ≤ αn` and `supp (He) ⊆ R`,
then `supp e ⊆ F_h(R)`. -/
theorem IsExpanderMatrix.supp_subset_findClosure (hH : IsExpanderMatrix H δ Δ α ε)
    {R : Finset P} {e : Fin n → F}
    (he : ((Finset.univ.filter fun u => e u ≠ 0).card : ℝ) ≤ α * n)
    (hR : (Finset.univ.filter fun p => H.mulVec e p ≠ 0) ⊆ R) :
    (Finset.univ.filter fun u => e u ≠ 0) ⊆ findClosure H ((1 - 2 * ε) * δ) R := by
  set L := findClosure H ((1 - 2 * ε) * δ) R
  set S := Finset.univ.filter fun u => e u ≠ 0
  have hLc : IsFindClosed H ((1 - 2 * ε) * δ) R L := findClosure_isFindClosed
  by_contra hsub
  set E' := S \ L
  have hE'ne : E'.Nonempty := Finset.sdiff_nonempty.2 hsub
  have hE'card : (E'.card : ℝ) ≤ α * n :=
    le_trans (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset) he
  -- every unique neighbour of `E'` lies in `R ∪ N(L)`
  have hU : uniqueNbhd H E' ⊆ R ∪ nbhd H L := by
    intro p hp
    rw [mem_uniqueNbhd, Finset.card_eq_one] at hp
    obtain ⟨u, hu⟩ := hp
    have huE : u ∈ vnbrs H p ∩ E' := by rw [hu]; exact mem_singleton_self u
    rw [mem_inter, mem_vnbrs] at huE
    by_cases hpL : p ∈ nbhd H L
    · exact mem_union_right _ hpL
    · apply mem_union_left
      apply hR
      rw [mem_filter]
      refine ⟨mem_univ _, mulVec_apply_ne_zero_of_unique H huE.1 ?_ ?_⟩
      · have huS := (mem_sdiff.1 huE.2).1
        simpa [S] using huS
      · intro v hpv hev
        have hvS : v ∈ S := by simpa [S] using hev
        have hvL : v ∉ L := fun hvL => hpL ((mem_nbhd H).2 ⟨v, hvL, hpv⟩)
        have hv : v ∈ vnbrs H p ∩ E' :=
          mem_inter.2 ⟨(mem_vnbrs H).2 hpv, mem_sdiff.2 ⟨hvS, hvL⟩⟩
        rw [hu] at hv
        exact mem_singleton.1 hv
  -- counting: `∑_{u ∈ E'} |N(u) ∩ U(E')| = |U(E')| ≥ h|E'|`, but each term is `< h`
  have hcount := hH.card_uniqueNbhd_ge hE'card
  have hsum : ∑ u ∈ E', ((nbrs H u ∩ uniqueNbhd H E').card : ℝ) = (uniqueNbhd H E').card := by
    exact_mod_cast sum_card_nbrs_inter_uniqueNbhd H E'
  have hlt : ∑ u ∈ E', ((nbrs H u ∩ uniqueNbhd H E').card : ℝ) <
      ∑ _u ∈ E', (1 - 2 * ε) * (δ : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hE'ne fun u hu => ?_
    have huL : u ∉ L := (mem_sdiff.1 hu).2
    refine lt_of_le_of_lt ?_ (hLc u huL)
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hU)
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  linarith

end FindB

end ProductExpansion
