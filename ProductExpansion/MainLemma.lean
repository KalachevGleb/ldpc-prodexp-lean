import ProductExpansion.MainInterface
import ProductExpansion.Reduction

/-!
# Assembly: the main lemma `D(d)` by induction on `d`, `P(d)`, and the main theorem

Uses only the statements `Step2Statement` … `Step5Statement` of `MainInterface.lean`
(they are proved in `Step2.lean` … `Step5.lean`; see `Main.lean`).
Contains lemma `lem:D`, corollary `cor:Pd` and the end of the proof of theorem 1.

## Constants (`γ = 1/4 - ε`, `c_d = canC γ d`)
* `decM ε d = M_d = (d + 1) c_d`, `decW Δ ε d = W_d = 4 (Δ + 1) (d + 1)^2 M_d^(d+1)`;
* `decKappa Δ α ε d = κ_d`: `κ_0 = min(γα/2, 1/2)`, `κ_{d+1} = κ_d / W_{d+1}`;
* `rhoConst m Δ α = ρ₀ = min((α'/2)^m/m, 1/(m c_{m,κ_m}))`, `α' = min α 1`, `κ_m` for `ε = 1/16`.

## Results
* `decode_of_steps`: `D(d)` (`DecodeStatement … d κ_d`) for all `d ≥ 1`, `0 < α ≤ 1`,
  `0 ≤ ε ≤ 1/16`; the parameter conditions of the steps are `Assembly.level_numeric`,
  `Assembly.final_numeric`;
* `generatedFromInside_of_steps`: `P(d)` with `η_d = κ_d` (via `Assembly.generatedFromInside_of_decode`,
  which uses `\hat ∅ = ∅`, `Assembly.canonicalSet_empty`);
* `prodExpanding_rhoConst`, `MainTheoremUniformStatement`, `mainTheoremUniform_of_steps`
  (`ρ₀` depends only on `m`, `Δ`, `α`) and `mainTheorem_of_steps`.
-/

open Finset

namespace ProductExpansion

/-! The auxiliary lemmas live in the namespace `ProductExpansion.Assembly` (to avoid clashes with
the modules `Step2` … `Step5`, which are imported together with this file by `Main.lean`). -/

namespace Assembly

/-! ### Small lemmas -/

section Small

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- Expanders are monotone in `α`. -/
lemma isExpanderMatrix_mono_alpha {P : Type*} [Fintype P] [DecidableEq P]
    {H : Matrix P (Fin n) F} {δ Δ : ℕ} {α α' ε : ℝ} (hH : IsExpanderMatrix H δ Δ α ε)
    (h : α' ≤ α) : IsExpanderMatrix H δ Δ α' ε where
  leftDeg := hH.leftDeg
  rightDeg := hH.rightDeg
  expand S hS := hH.expand S (hS.trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n)))

/-- Expanders are monotone in `ε`. -/
lemma isExpanderMatrix_mono_eps {P : Type*} [Fintype P] [DecidableEq P]
    {H : Matrix P (Fin n) F} {δ Δ : ℕ} {α ε ε' : ℝ} (hH : IsExpanderMatrix H δ Δ α ε)
    (h : ε ≤ ε') : IsExpanderMatrix H δ Δ α ε' where
  leftDeg := hH.leftDeg
  rightDeg := hH.rightDeg
  expand S hS := by
    refine le_trans ?_ (hH.expand S hS)
    have h1 : (1 - ε') * δ ≤ (1 - ε) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg δ)
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)

omit [DecidableEq F] in
/-- `F^∅ = 0`. -/
lemma supported_empty {ι : Type*} : supported F (∅ : Set (ι → Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext y
  by_contra h
  exact hx y h

omit [DecidableEq F] in
/-- For an empty index type, `⊞ C = 0`, so every set is generated from inside. -/
lemma generatedFromInside_of_isEmpty {κ : Type*} [Fintype κ] [DecidableEq κ] [IsEmpty κ]
    (C : κ → Submodule F (Fin n → F)) (M : Set (κ → Fin n)) : GeneratedFromInside C M := by
  intro x hx
  have hb : x ∈ boxplus C := (Submodule.mem_inf.1 hx).1
  rw [boxplus, iSup_of_empty, Submodule.mem_bot] at hb
  rw [hb]
  exact Submodule.zero_mem _

end Small

/-! ### The canonical set of the empty defect is empty -/

section EmptyDefect

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- One step of the construction from `Z = Y = ∅` gives `∅` (positive threshold, nonempty index
type): all the sets `Ψ^θ_ℓ(∅, ∅) = F_θ(∅)` are empty. -/
lemma stepSet_empty_empty {ι : Type*} [DecidableEq ι] [Nonempty ι] {P : ι → Type*}
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] (H : (i : ι) → Matrix (P i) (Fin n) F)
    {θ : ℝ} (hθ : 0 < θ) : stepSet H θ (∅ : Set (ι → Fin n)) ∅ = ∅ := by
  have hpsi : ∀ j c, psiSet H θ (∅ : Set (ι → Fin n)) ∅ j c = ∅ := by
    intro j c
    have h1 : crossSet (∅ : Set (ι → Fin n)) j c = ∅ := by
      ext t
      simp only [mem_crossSet, Set.mem_empty_iff_false, Finset.notMem_empty, iff_false]
      rintro ⟨j', -, h⟩
      exact h t
    have h2 : linePts (∅ : Set (ι → Fin n)) j c = ∅ := by
      ext t
      simp [mem_linePts]
    rw [psiSet, h1, h2, Finset.empty_union, nbhd_empty]
    apply Finset.subset_empty.1
    apply findClosure_subset
    intro u _
    simp [hθ]
  ext c
  simp only [stepSet, Set.mem_union, Set.mem_empty_iff_false, Set.mem_ofPred_eq, false_or,
    iff_false, not_and]
  intro _ h
  obtain ⟨j⟩ := ‹Nonempty ι›
  have := h j
  rw [hpsi] at this
  simp at this

omit [DecidableEq F] in
lemma posFull_empty_of_pos (hn : 0 < n) {ι : Type*} [DecidableEq ι] (I : Finset ι) :
    posFull (∅ : Set (ι → Fin n)) I = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  exact h (fun _ => ⟨0, hn⟩)

variable {K : Type*} [Fintype K] [DecidableEq K] {P : K → Type*} [∀ k, Fintype (P k)]
  [∀ k, DecidableEq (P k)] {H : (k : K) → Matrix (P k) (Fin n) F} {θ₀ : ℝ}

/-- `Bad_J(∅) = ∅` for all `J` (downward induction on `|J|`). -/
lemma badSet_empty_defect (hn : 0 < n) (hθ₀ : 0 < θ₀) (J : Finset K) :
    badSet H θ₀ (∅ : Set (K → Fin n)) J = ∅ := by
  suffices h : ∀ m, ∀ J : Finset K, Fintype.card K - J.card = m →
      badSet H θ₀ (∅ : Set (K → Fin n)) J = ∅ from h _ J rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro J hm
    by_cases hJ : J = Finset.univ
    · exact badSet_of_eq_univ hJ
    · rw [badSet_of_ne_univ hJ]
      have hcan : canJ H θ₀ (∅ : Set (K → Fin n)) J = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        rw [mem_canJ]
        rintro (h | ⟨J'', h, hc⟩)
        · rw [posFull_empty_of_pos hn] at h
          exact h
        · have hlt : Fintype.card K - J''.card < m := by
            have h1 := Finset.card_lt_card h
            have h2 := Finset.card_le_univ J''
            omega
          rw [ih _ hlt J'' rfl] at hc
          exact hc
      have : Nonempty {i // i ∉ J} := by
        by_contra h
        apply hJ
        rw [Finset.eq_univ_iff_forall]
        intro i
        by_contra hi
        exact h ⟨⟨i, hi⟩⟩
      rw [hatJ, hcan, posFull_empty_of_pos hn]
      exact stepSet_empty_empty _ hθ₀

/-- `Can(∅) = ∅`. -/
lemma canSet_empty_defect (hn : 0 < n) (hθ₀ : 0 < θ₀) :
    canSet H θ₀ (∅ : Set (K → Fin n)) = ∅ := by
  ext y
  simp only [canSet, Set.mem_union, Set.mem_empty_iff_false, Set.mem_iUnion, Set.mem_preimage,
    false_or, iff_false, not_exists]
  intro J _ h
  rw [badSet_empty_defect hn hθ₀] at h
  exact h

/-- `\hat ∅ = ∅` (remark after definition `def:can`). -/
lemma canonicalSet_empty [Nonempty K] {δ : ℕ} {ε : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    (hε : ε < 1 / 2) : canonicalSet H δ ε (∅ : Set (K → Fin n)) = ∅ := by
  have hδ' : (0 : ℝ) < δ := Nat.cast_pos.2 hδ
  rw [canonicalSet, hatSet, canSet_empty_defect hn (by positivity)]
  exact stepSet_empty_empty H (mul_pos (by linarith) hδ')

end EmptyDefect

/-! ### The top level, `P(d)` from `D(d)`, `HypGen` -/

section Gen

/-- `α n ≥ 2` forces `n > 0`. -/
lemma pos_of_two_le_mul {α : ℝ} {n : ℕ} (h : 2 ≤ α * n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    norm_num at h
  · exact h0

/-- The invariant (I2) at the top level `d - 1`: it only concerns `J = K`, where `Bad_K = ∅`
and `Y_K(N) = ∅` for a proper `N`. -/
lemma levelInv2_top {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {P : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F) (δ : ℕ) (E : Set (ι → Fin n)) {N : Set (ι → Fin n)}
    (hN : N ≠ Set.univ) : LevelInv2 H δ E N (Fintype.card ι - 1) := by
  intro J hJ b hb
  have hJu : J = Finset.univ := by
    apply Finset.eq_univ_of_card
    have := Finset.card_le_univ J
    omega
  exact absurd hb (not_mem_posFull_of_eq_univ hN hJu b)

/-- **Corollary `cor:Pd`**: `D(d)` implies `P(d)` (with the same closedness bound): apply `D(d)`
with `E = ∅`, `a = e = x`, `c = 0`, and use `\hat ∅ = ∅`. -/
theorem generatedFromInside_of_decode {F : Type} [Field F] [DecidableEq F] {δ Δ : ℕ}
    {α ε κ : ℝ} {d : ℕ} (hD : DecodeStatement F δ Δ α ε d κ) (hδ : 0 < δ) (hε : ε < 1 / 2)
    (hκ : 0 < κ) {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : Fintype.card ι = d) {P : ι → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F) (hH : ∀ i, IsExpanderMatrix (H i) δ Δ α ε)
    (hαn : 2 ≤ α * n) (M : Set (ι → Fin n)) (hM : IsClosedSet κ M) (hMne : M ≠ Set.univ) :
    GeneratedFromInside (fun i => kerCode (H i)) M := by
  have hn : 0 < n := pos_of_two_le_mul hαn
  intro x hx
  obtain ⟨hxb, hxs⟩ := Submodule.mem_inf.1 hx
  have hEne : (∅ : Set (ι → Fin n)) ≠ Set.univ := by
    intro h
    have : (fun _ => (⟨0, hn⟩ : Fin n)) ∈ (∅ : Set (ι → Fin n)) := by
      rw [h]
      trivial
    exact this
  have key := hD n ι hcard P H hH hαn ∅ M (isClosedSet_empty hκ) hEne hM hMne x 0 x
    (synCond_empty_of_mem_boxplus hxb) (zero_add x).symm (Submodule.zero_mem _) hxs
  rwa [canonicalSet_empty hn hδ hε, supported_empty, sup_bot_eq] at key

/-- `P(d)` (from `D(d)`) gives the hypothesis `HypGen` (`P(d)` on the hyperplane cubes) in a cube of
dimension `d + 1`. -/
theorem hypGen_of_decode {F : Type} [Field F] [DecidableEq F] {δ Δ : ℕ} {α ε κ : ℝ} {d : ℕ}
    (hD : DecodeStatement F δ Δ α ε d κ) (hd : 1 ≤ d) (hδ : 0 < δ) (hε : ε < 1 / 2)
    (hκ : 0 < κ) {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (hcard : Fintype.card ι = d + 1)
    {P : ι → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F) (hH : ∀ i, IsExpanderMatrix (H i) δ Δ α ε)
    (hαn : 2 ≤ α * n) : HypGen H κ := by
  intro i M hM hMne
  have hc : Fintype.card {j // j ≠ i} = d := by
    rw [card_ne, hcard]
    omega
  have : Nonempty {j // j ≠ i} := Fintype.card_pos_iff.1 (by omega)
  exact generatedFromInside_of_decode hD hδ hε hκ hc (fun k => H k) (fun k => hH k) hαn M hM hMne

/-- `HypGen` in dimension `1`: the hyperplane cubes have no directions, so `⊞ = 0`. -/
theorem hypGen_of_card_one {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hcard : Fintype.card ι = 1) {P : ι → Type*}
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] (H : ∀ i, Matrix (P i) (Fin n) F) (η : ℝ) :
    HypGen H η := by
  intro i M _ _
  have : IsEmpty {j // j ≠ i} := by
    rw [← Fintype.card_eq_zero_iff, card_ne, hcard]
  exact generatedFromInside_of_isEmpty _ M

end Gen

end Assembly

/-! ### Constants -/

section Constants

/-- `M_d = (d + 1) c_d`, where `c_d = canC γ d`, `γ = 1/4 - ε`. -/
noncomputable def decM (ε : ℝ) (d : ℕ) : ℝ := (d + 1) * canC (1 / 4 - ε) d

/-- `W_d = 4 (Δ + 1) (d + 1)^2 M_d^(d+1)`: all the factors appearing in the parameter
conditions of the proof of `D(d)` are at most `W_d` (see `le_decW`). -/
noncomputable def decW (Δ : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  4 * (Δ + 1) * (d + 1) ^ 2 * decM ε d ^ (d + 1)

/-- The closedness bounds `κ_d` of lemma `D(d)`: `κ_0 = min(γα/2, 1/2)`,
`κ_{d+1} = κ_d / W_{d+1}`. They depend only on `d`, `Δ`, `α`, `ε`. -/
noncomputable def decKappa (Δ : ℕ) (α ε : ℝ) : ℕ → ℝ
  | 0 => min ((1 / 4 - ε) * α / 2) (1 / 2)
  | d + 1 => decKappa Δ α ε d / decW Δ ε (d + 1)

variable {Δ d : ℕ} {α ε : ℝ}

lemma one_le_decM (hε : ε < 1 / 4) (hd : 1 ≤ d) : 1 ≤ decM ε d := by
  unfold decM
  have h1 : 1 ≤ canC (1 / 4 - ε) d := one_le_canC (by linarith) hd
  have h2 : (1 : ℝ) ≤ d + 1 := by
    have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (d + 1) * canC (1 / 4 - ε) d := mul_le_mul h2 h1 (by norm_num) (by linarith)

/-- The basic estimate: `a b M_d^j ≤ W_d` for `a ≤ 4(Δ+1)`, `b ≤ (d+1)^2`, `j ≤ d+1`. -/
lemma le_decW {j : ℕ} {a b : ℝ} (hM : 1 ≤ decM ε d) (ha : a ≤ 4 * (Δ + 1))
    (hb0 : 0 ≤ b) (hb : b ≤ (d + 1) ^ 2) (hj : j ≤ d + 1) :
    a * b * decM ε d ^ j ≤ decW Δ ε d := by
  unfold decW
  have h1 : decM ε d ^ j ≤ decM ε d ^ (d + 1) := pow_le_pow_right₀ hM hj
  have h2 : a * b ≤ 4 * (Δ + 1) * (d + 1) ^ 2 := mul_le_mul ha hb hb0 (by positivity)
  exact mul_le_mul h2 h1 (by positivity) (by positivity)

lemma one_le_decW (hε : ε < 1 / 4) (hd : 1 ≤ d) : 1 ≤ decW Δ ε d := by
  have h := le_decW (Δ := Δ) (j := 0) (a := 1) (b := 1) (one_le_decM hε hd)
    (by have := (Nat.cast_nonneg Δ : (0 : ℝ) ≤ Δ); linarith) zero_le_one
    (by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); nlinarith) (Nat.zero_le _)
  simpa using h

lemma decKappa_pos (hα : 0 < α) (hε : ε < 1 / 4) : ∀ d, 0 < decKappa Δ α ε d
  | 0 => by
    have hγ : 0 < 1 / 4 - ε := by linarith
    simp only [decKappa]
    exact lt_min (by positivity) (by norm_num)
  | d + 1 => by
    simp only [decKappa]
    exact div_pos (decKappa_pos hα hε d)
      (lt_of_lt_of_le one_pos (one_le_decW hε (Nat.succ_pos d)))

lemma decKappa_succ_le (hα : 0 < α) (hε : ε < 1 / 4) (d : ℕ) :
    decKappa Δ α ε (d + 1) ≤ decKappa Δ α ε d := by
  rw [decKappa]
  exact div_le_self (decKappa_pos hα hε d).le (one_le_decW hε (Nat.succ_pos d))

lemma decKappa_anti (hα : 0 < α) (hε : ε < 1 / 4) : Antitone (decKappa Δ α ε) :=
  antitone_nat_of_succ_le (decKappa_succ_le hα hε)

lemma decKappa_le_gamma (hα : 0 < α) (hε : ε < 1 / 4) (d : ℕ) :
    decKappa Δ α ε d ≤ (1 / 4 - ε) * α / 2 := by
  have h := decKappa_anti (Δ := Δ) hα hε (Nat.zero_le d)
  rw [decKappa] at h
  exact h.trans (min_le_left _ _)

lemma decKappa_le_half (hα : 0 < α) (hε : ε < 1 / 4) (d : ℕ) :
    decKappa Δ α ε d ≤ 1 / 2 := by
  have h := decKappa_anti (Δ := Δ) hα hε (Nat.zero_le d)
  rw [decKappa] at h
  exact h.trans (min_le_right _ _)

lemma decW_mul_decKappa (hε : ε < 1 / 4) (hd : 1 ≤ d) :
    decW Δ ε d * decKappa Δ α ε d = decKappa Δ α ε (d - 1) := by
  obtain ⟨d₀, rfl⟩ : ∃ d₀, d = d₀ + 1 := ⟨d - 1, by omega⟩
  rw [decKappa, Nat.add_sub_cancel]
  have hW : decW Δ ε (d₀ + 1) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_decW hε (Nat.succ_pos d₀))).ne'
  field_simp

end Constants

namespace Assembly

/-! ### Parameter conditions of the steps -/

section Numeric

/-- The parameter conditions of steps 2–4 at the level `d' = d - 1 - k` (after `k` levels), with
`η_b = (d + 1) M^k μ` (`M = M_d`, `μ = κ_d`), the current set `ν`-closed with `ν ≤ M^k μ`,
and `η = W μ ≤ κD`, where every factor `a b M^j` (`a ≤ 4(Δ+1)`, `b ≤ (d+1)^2`, `j ≤ d+1`) is at
most `W`. Here `c = c_d`, `cd' = c_{d'}`, `c'd' = c'_{d'}`, `γ = 1/4 - ε`. -/
lemma level_numeric {Δ d k d' D : ℕ} {α γ M c cd' c'd' W μ ν η κD ηb : ℝ}
    (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (hα0 : 0 < α)
    (hd' : 1 ≤ d') (hdk : d' + k + 1 = d) (hD : D ≤ d)
    (hM : M = (d + 1) * c) (hc1 : 1 ≤ c) (hcd' : cd' ≤ c) (hc'd' : c'd' ≤ cd')
    (hW : ∀ (a b : ℝ) (j : ℕ), a ≤ 4 * (Δ + 1) → 0 ≤ b → b ≤ (d + 1) ^ 2 → j ≤ d + 1 →
      a * b * M ^ j ≤ W)
    (hμ0 : 0 < μ) (hν0 : 0 ≤ ν) (hν : ν ≤ M ^ k * μ)
    (hWμ : W * μ = η) (hηκ : η ≤ κD) (hηs1 : η ≤ γ * α / 2) (hηs2 : η ≤ 1 / 2)
    (hηb : ηb = (d + 1) * M ^ k * μ) :
    μ + (D : ℝ) * ν ≤ ηb ∧ (d' : ℝ) * ηb ≤ 1 ∧ 2 * (Δ : ℝ) * max ν μ ≤ η ∧ ν ≤ α ∧
    c'd' * ηb ≤ γ * α / 2 ∧ cd' * ηb < 1 ∧ (d' : ℝ) * (2 * Δ * (cd' * ηb)) ≤ 1 ∧ ηb ≤ κD ∧
    2 * (Δ : ℝ) * (cd' * ηb) ≤ κD ∧ max ν (cd' * ηb) ≤ M ^ (k + 1) * μ := by
  subst hηb
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hΔR : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
  have hd'R : (d' : ℝ) ≤ d := by exact_mod_cast (by omega : d' ≤ d)
  have hd'0 : (0 : ℝ) ≤ d' := Nat.cast_nonneg d'
  have hDR : (D : ℝ) ≤ d := by exact_mod_cast hD
  have hkd : k + 1 ≤ d + 1 := by omega
  have hkd' : k ≤ d + 1 := by omega
  have hM1 : 1 ≤ M := by
    rw [hM]
    nlinarith
  have hMk : 1 ≤ M ^ k := one_le_pow₀ hM1
  have hMk1 : M ^ k ≤ M ^ (k + 1) := pow_le_pow_right₀ hM1 (Nat.le_succ k)
  have hWX : ∀ X : ℝ, X ≤ W → X * μ ≤ η := fun X hX => by
    rw [← hWμ]
    exact mul_le_mul_of_nonneg_right hX hμ0.le
  have hηb0 : 0 ≤ (d + 1) * M ^ k * μ := by positivity
  have hMkμ : M ^ k * μ ≤ η := by
    have := hWX (1 * 1 * M ^ k) (hW 1 1 k (by linarith) zero_le_one (by nlinarith) hkd')
    simpa using this
  have hMk1μ : M ^ (k + 1) * μ ≤ η := by
    have := hWX (1 * 1 * M ^ (k + 1)) (hW 1 1 (k + 1) (by linarith) zero_le_one (by nlinarith) hkd)
    simpa using this
  have hcηb : cd' * ((d + 1) * M ^ k * μ) ≤ M ^ (k + 1) * μ := by
    calc cd' * ((d + 1) * M ^ k * μ) ≤ c * ((d + 1) * M ^ k * μ) :=
          mul_le_mul_of_nonneg_right hcd' hηb0
      _ = M ^ (k + 1) * μ := by rw [hM]; ring
  have hγα : γ * α / 2 ≤ α := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `μ + D ν ≤ η_b`
    have h1 : μ ≤ M ^ k * μ := le_mul_of_one_le_left hμ0.le hMk
    have h2 : (D : ℝ) * ν ≤ d * (M ^ k * μ) := mul_le_mul hDR hν hν0 hdR
    nlinarith
  · -- `d' η_b ≤ 1`
    have h := hWX (1 * (d' * (d + 1)) * M ^ k)
      (hW 1 (d' * (d + 1)) k (by linarith) (by positivity) (by nlinarith) hkd')
    have : (d' : ℝ) * ((d + 1) * M ^ k * μ) = 1 * (d' * (d + 1)) * M ^ k * μ := by ring
    rw [this]
    linarith
  · -- `2 Δ max(ν, μ) ≤ η`
    have hmax : max ν μ ≤ M ^ k * μ := max_le hν (le_mul_of_one_le_left hμ0.le hMk)
    have h := hWX (2 * Δ * 1 * M ^ k) (hW (2 * Δ) 1 k (by linarith) zero_le_one (by nlinarith) hkd')
    calc 2 * (Δ : ℝ) * max ν μ ≤ 2 * Δ * (M ^ k * μ) :=
          mul_le_mul_of_nonneg_left hmax (by positivity)
      _ = 2 * Δ * 1 * M ^ k * μ := by ring
      _ ≤ η := h
  · -- `ν ≤ α`
    linarith
  · -- `c'_{d'} η_b ≤ γ α / 2`
    have : c'd' * ((d + 1) * M ^ k * μ) ≤ cd' * ((d + 1) * M ^ k * μ) :=
      mul_le_mul_of_nonneg_right hc'd' hηb0
    linarith
  · -- `c_{d'} η_b < 1`
    linarith
  · -- `d' (2 Δ c_{d'} η_b) ≤ 1`
    have h := hWX (2 * Δ * d' * M ^ (k + 1))
      (hW (2 * Δ) d' (k + 1) (by linarith) hd'0 (by nlinarith) hkd)
    calc (d' : ℝ) * (2 * Δ * (cd' * ((d + 1) * M ^ k * μ)))
        ≤ d' * (2 * Δ * (M ^ (k + 1) * μ)) := by
          apply mul_le_mul_of_nonneg_left _ hd'0
          exact mul_le_mul_of_nonneg_left hcηb (by positivity)
      _ = 2 * Δ * d' * M ^ (k + 1) * μ := by ring
      _ ≤ η := h
      _ ≤ 1 := by linarith
  · -- `η_b ≤ κD`
    have h := hWX (1 * (d + 1) * M ^ k)
      (hW 1 (d + 1) k (by linarith) (by positivity) (by nlinarith) hkd')
    have : ((d : ℝ) + 1) * M ^ k * μ = 1 * (d + 1) * M ^ k * μ := by ring
    linarith
  · -- `2 Δ c_{d'} η_b ≤ κD`
    have h := hWX (2 * Δ * 1 * M ^ (k + 1))
      (hW (2 * Δ) 1 (k + 1) (by linarith) zero_le_one (by nlinarith) hkd)
    calc 2 * (Δ : ℝ) * (cd' * ((d + 1) * M ^ k * μ)) ≤ 2 * Δ * (M ^ (k + 1) * μ) :=
          mul_le_mul_of_nonneg_left hcηb (by positivity)
      _ = 2 * Δ * 1 * M ^ (k + 1) * μ := by ring
      _ ≤ η := h
      _ ≤ κD := hηκ
  · -- the new closedness bound
    refine max_le ?_ hcηb
    calc ν ≤ M ^ k * μ := hν
      _ ≤ M ^ (k + 1) * μ := mul_le_mul_of_nonneg_right hMk1 hμ0.le

/-- The parameter conditions of step 5 (`ν ≤ M^{d-1} μ`, `c = c_d`, `c' = c'_d`). -/
lemma final_numeric {Δ d : ℕ} {α γ M c c' W μ ν η : ℝ}
    (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (hα0 : 0 < α) (hd : 1 ≤ d)
    (hM : M = (d + 1) * c) (hc1 : 1 ≤ c) (hc' : c' ≤ c)
    (hW : ∀ (a b : ℝ) (j : ℕ), a ≤ 4 * (Δ + 1) → 0 ≤ b → b ≤ (d + 1) ^ 2 → j ≤ d + 1 →
      a * b * M ^ j ≤ W)
    (hμ0 : 0 < μ) (hν0 : 0 ≤ ν) (hν : ν ≤ M ^ (d - 1) * μ)
    (hWμ : W * μ = η) (hηs1 : η ≤ γ * α / 2) (hηs2 : η ≤ 1 / 2) :
    c' * μ ≤ γ * α / 2 ∧ c * μ < 1 ∧ 2 * (Δ : ℝ) * max (c' * μ + ν) μ ≤ η ∧
      c' * μ + ν ≤ α := by
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hΔR : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
  have hdd : d ≤ d + 1 := Nat.le_succ d
  have hM1 : 1 ≤ M := by
    rw [hM]
    nlinarith
  have hcM : c ≤ M := by
    rw [hM]
    nlinarith
  have hMd : M ≤ M ^ d := le_self_pow₀ hM1 (by omega)
  have hMd1 : M ^ (d - 1) ≤ M ^ d := pow_le_pow_right₀ hM1 (Nat.sub_le d 1)
  have hMd0 : 1 ≤ M ^ d := one_le_pow₀ hM1
  have hWX : ∀ X : ℝ, X ≤ W → X * μ ≤ η := fun X hX => by
    rw [← hWμ]
    exact mul_le_mul_of_nonneg_right hX hμ0.le
  have h2 := hWX (2 * 1 * M ^ d) (hW 2 1 d (by linarith) zero_le_one (by nlinarith) hdd)
  have h4 := hWX (4 * Δ * 1 * M ^ d) (hW (4 * Δ) 1 d (by linarith) zero_le_one (by nlinarith) hdd)
  have hcμ : c * μ ≤ M ^ d * μ := mul_le_mul_of_nonneg_right (hcM.trans hMd) hμ0.le
  have hc'μ : c' * μ ≤ c * μ := mul_le_mul_of_nonneg_right hc' hμ0.le
  have hνd : ν ≤ M ^ d * μ := hν.trans (mul_le_mul_of_nonneg_right hMd1 hμ0.le)
  have hμd : μ ≤ M ^ d * μ := le_mul_of_one_le_left hμ0.le hMd0
  have hsum : c' * μ + ν ≤ 2 * 1 * M ^ d * μ := by linarith
  have hγα : γ * α / 2 ≤ α := by nlinarith
  refine ⟨by linarith, by linarith, ?_, by linarith⟩
  have hmax : max (c' * μ + ν) μ ≤ 2 * 1 * M ^ d * μ := max_le hsum (by linarith)
  calc 2 * (Δ : ℝ) * max (c' * μ + ν) μ ≤ 2 * Δ * (2 * 1 * M ^ d * μ) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = 4 * Δ * 1 * M ^ d * μ := by ring
    _ ≤ η := h4

end Numeric

end Assembly

open Assembly

/-! ### The main lemma `D(d)` -/

/-- **Lemma `D(d)`** (`lem:D`) for all `d ≥ 1` with the closedness bound `κ_d = decKappa Δ α ε d`,
from steps 2–5: strong induction on `d`; inside, the levels `d' = d - 1, …, 1` (after `k` levels
the current set `N_k ⊆ N` is `ν`-closed with `ν ≤ M_d^k κ_d`, `e - e_k ∈ L(N)`, (I2) holds at
level `d - 1 - k`), then step 5. -/
theorem decode_of_steps (h2 : Step2Statement) (h3 : Step3Statement) (h4 : Step4Statement)
    (h5 : Step5Statement) {F : Type} [Field F] [DecidableEq F] {δ Δ : ℕ} {α ε : ℝ}
    (hδ : 0 < δ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 16) :
    ∀ d, 1 ≤ d → DecodeStatement F δ Δ α ε d (decKappa Δ α ε d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro hd n ι _ _ hcard P _ _ H hH hαn E N hE hEne hN hNne a c e ha hace hc he
  have hε4 : ε < 1 / 4 := by linarith
  have hγ : 0 < 1 / 4 - ε := by linarith
  have hn : 0 < n := pos_of_two_le_mul hαn
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  -- constants
  have hμ0 : 0 < decKappa Δ α ε d := decKappa_pos hα0 hε4 d
  have hWμ : decW Δ ε d * decKappa Δ α ε d = decKappa Δ α ε (d - 1) := decW_mul_decKappa hε4 hd
  have hηs1 := decKappa_le_gamma (Δ := Δ) hα0 hε4 (d - 1)
  have hηs2 := decKappa_le_half (Δ := Δ) hα0 hε4 (d - 1)
  have hη1 : decKappa Δ α ε (d - 1) ≤ 1 := by linarith
  have hM1 : 1 ≤ decM ε d := one_le_decM hε4 hd
  have hc1 : 1 ≤ canC (1 / 4 - ε) d := one_le_canC hγ hd
  have hW : ∀ (a b : ℝ) (j : ℕ), a ≤ 4 * (Δ + 1) → 0 ≤ b → b ≤ (d + 1) ^ 2 → j ≤ d + 1 →
      a * b * decM ε d ^ j ≤ decW Δ ε d := fun a b j ha hb0 hb hj => le_decW hM1 ha hb0 hb hj
  -- `P(d-1)` on the hyperplane cubes
  have hgen : HypGen H (decKappa Δ α ε (d - 1)) := by
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · exact hypGen_of_card_one (by omega) H _
    · exact hypGen_of_decode (IH (d - 1) (by omega) (by omega)) (by omega) hδ (by linarith)
        (decKappa_pos hα0 hε4 _) (by omega) H hH hαn
  -- `e` satisfies `S(E)`
  have hSe : SynCond H E e := ha.of_eq_add hc hace
  -- the levels `d' = d - 1 - k`
  have iter : ∀ k, k ≤ d - 1 → ∃ (Nk : Set (ι → Fin n)) (ek : (ι → Fin n) → F) (ν : ℝ),
      Nk ⊆ N ∧ IsClosedSet ν Nk ∧ SupportedIn ek Nk ∧
      e - ek ∈ lineSpan (fun i => kerCode (H i)) N ∧ LevelInv2 H δ E Nk (d - 1 - k) ∧
      0 ≤ ν ∧ ν ≤ decM ε d ^ k * decKappa Δ α ε d := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨N, e, decKappa Δ α ε d, subset_rfl, hN, he, by simp, ?_, hμ0.le, by simp⟩
      have := levelInv2_top H δ E hNne
      rw [hcard] at this
      simpa using this
    | succ k ihk =>
      intro hk
      obtain ⟨Nk, ek, ν, hNk, hcl, hsupp, hdiff, hinv, hν0, hν⟩ := ihk (by omega)
      have hd'1 : 1 ≤ d - 1 - k := by omega
      have hd'lt : d - 1 - k < Fintype.card ι := by omega
      have hSk : SynCond H E ek := by
        have h1 : e - ek ∈ boxplus (fun i => kerCode (H i)) := lineSpan_le_boxplus N hdiff
        have : ek = e - (e - ek) := by abel
        rw [this]
        exact hSe.sub_boxplus h1
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ :=
        level_numeric (Δ := Δ) (d := d) (k := k) (d' := d - 1 - k)
          (D := Fintype.card ι - (d - 1 - k)) (α := α) (γ := 1 / 4 - ε) (M := decM ε d)
          (c := canC (1 / 4 - ε) d) (cd' := canC (1 / 4 - ε) (d - 1 - k))
          (c'd' := canC' (1 / 4 - ε) (d - 1 - k)) (W := decW Δ ε d) (μ := decKappa Δ α ε d)
          (ν := ν) (η := decKappa Δ α ε (d - 1)) (κD := decKappa Δ α ε (d - 1 - k))
          (ηb := (d + 1) * decM ε d ^ k * decKappa Δ α ε d)
          hγ (by linarith) hα0 hd'1 (by omega) (by omega) rfl hc1
          (canC_mono hγ (by omega)) (canC'_le_canC hγ (by omega)) hW hμ0 hν0 hν
          hWμ (decKappa_anti hα0 hε4 (by omega)) hηs1 hηs2 rfl
      have hFDP := h2 H δ (decKappa Δ α ε d) ν ((d + 1) * decM ε d ^ k * decKappa Δ α ε d)
        (d - 1 - k) E Nk hn hd'1 hd'lt hμ0.le hν0 hE hcl hinv n1 n2
      have hGFD := h3 H δ Δ α ε (decKappa Δ α ε (d - 1)) (decKappa Δ α ε (d - 1 - k))
        (decKappa Δ α ε d) ν ((d + 1) * decM ε d ^ k * decKappa Δ α ε d) (d - 1 - k) E Nk ek
        hH hδ hε0 hε1 hαn hα1 hd'1 hd'lt (IH (d - 1 - k) (by omega) hd'1) hgen hη1 hμ0.le hν0 hE
        hEne hcl hinv hFDP hSk hsupp n3 n4 n1 n5 n6 n7 n8 n9
      obtain ⟨N', a', hN'sub, hN'cl, hN'supp, hN'diff, hN'inv⟩ :=
        h4 H δ Δ α ε (decKappa Δ α ε d) ν ((d + 1) * decM ε d ^ k * decKappa Δ α ε d) (d - 1 - k)
          E N Nk e ek hH hδ hε0 hε1 hαn hα1 hd'1 hd'lt hμ0.le hν0 hE hEne hcl hinv hFDP hNk hsupp
          hdiff hGFD n1 n5 n6
      refine ⟨N', a', max ν (canC (1 / 4 - ε) (d - 1 - k) *
          ((d + 1) * decM ε d ^ k * decKappa Δ α ε d)),
        hN'sub.trans hNk, hN'cl, hN'supp, hN'diff, ?_, le_max_of_le_left hν0, n10⟩
      have : d - 1 - k - 1 = d - 1 - (k + 1) := by omega
      rwa [this] at hN'inv
  -- step 5: canonization of the remaining word `g`
  obtain ⟨Nf, g, ν, -, hcl, hsupp, hdiff, hinv, hν0, hν⟩ := iter (d - 1) le_rfl
  rw [Nat.sub_self] at hinv
  have hSg : SynCond H E g := by
    have h1 : e - g ∈ boxplus (fun i => kerCode (H i)) := lineSpan_le_boxplus N hdiff
    have : g = e - (e - g) := by abel
    rw [this]
    exact hSe.sub_boxplus h1
  obtain ⟨m1, m2, m3, m4⟩ := final_numeric (Δ := Δ) (d := d) (α := α) (γ := 1 / 4 - ε)
    (M := decM ε d) (c := canC (1 / 4 - ε) (Fintype.card ι))
    (c' := canC' (1 / 4 - ε) (Fintype.card ι)) (W := decW Δ ε d) (μ := decKappa Δ α ε d) (ν := ν)
    (η := decKappa Δ α ε (d - 1)) hγ (by linarith) hα0 hd (by rw [hcard]; rfl)
    (by rw [hcard]; exact hc1) (canC'_le_canC hγ (by omega)) hW hμ0 hν0 hν hWμ hηs1 hηs2
  have hg := h5 H δ Δ α ε (decKappa Δ α ε (d - 1)) (decKappa Δ α ε d) ν E Nf g hH hδ hε0 hε1 hαn
    hα1 hgen hη1 hμ0.le hν0 hE hEne hcl hinv hSg hsupp m1 m2 m3 m4
  have : e = (e - g) + g := by abel
  rw [this]
  exact Submodule.add_mem_sup hdiff hg

/-! ### `P(m)` and the main theorem -/

/-- `P(d)` (corollary `cor:Pd`) for all closed sets, from steps 2–5: every `κ_d`-closed set of a
cube of dimension `d ≥ 1` is generated from inside (`M = V^d` by `generatedFromInside_univ`). -/
theorem generatedFromInside_of_steps (h2 : Step2Statement) (h3 : Step3Statement)
    (h4 : Step4Statement) (h5 : Step5Statement) {F : Type} [Field F] [DecidableEq F] {δ Δ : ℕ}
    {α ε : ℝ} (hδ : 0 < δ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 16)
    {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {P : ι → Type}
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] (H : ∀ i, Matrix (P i) (Fin n) F)
    (hH : ∀ i, IsExpanderMatrix (H i) δ Δ α ε) (hαn : 2 ≤ α * n) (M : Set (ι → Fin n))
    (hM : IsClosedSet (decKappa Δ α ε (Fintype.card ι)) M) :
    GeneratedFromInside (fun i => kerCode (H i)) M := by
  refine generatedFromInside_of_ne_univ (fun M' hM' hne => ?_) M hM
  exact generatedFromInside_of_decode
    (decode_of_steps h2 h3 h4 h5 hδ hα0 hα1 hε0 hε1 _ Fintype.card_pos) hδ (by linarith)
    (decKappa_pos hα0 (by linarith) _) rfl H hH hαn M' hM' hne

/-- For `m = 0` every collection is `ρ`-product-expanding (`⊞ = 0`). -/
lemma prodExpanding_of_isEmpty {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [IsEmpty ι] (C : ι → Submodule F (Fin n → F)) (ρ : ℝ) :
    prodExpanding C ρ := by
  intro h0 c hc
  rw [boxplus, iSup_of_empty, Submodule.mem_bot] at hc
  refine ⟨fun _ => 0, fun i => isEmptyElim i, ?_, ?_⟩
  · simp [hc]
  · simp

/-- The constant `ρ₀` of the main theorem. It depends only on `m`, `Δ`, `α`:
`ρ₀ = min((α'/2)^m/m, 1/(m c_{m,κ_m}))` with `α' = min α 1` and `κ_m` taken for `ε = 1/16`
(every `(α, ε)`-expander with `ε ≤ 1/16` is an `(α', 1/16)`-expander); `ρ₀ = 1` for `m = 0`. -/
noncomputable def rhoConst (m Δ : ℕ) (α : ℝ) : ℝ :=
  if m = 0 then 1 else
    min ((min α 1 / 2) ^ m / m) (1 / (m * closureConst m (decKappa Δ (min α 1) (1 / 16) m)))

lemma rhoConst_pos {m Δ : ℕ} {α : ℝ} (hα : 0 < α) : 0 < rhoConst m Δ α := by
  unfold rhoConst
  split_ifs with hm
  · exact one_pos
  · have hm' : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
    have hα' : 0 < min α 1 := lt_min hα one_pos
    have hκ : 0 < decKappa Δ (min α 1) (1 / 16) m := decKappa_pos hα' (by norm_num) m
    have hc : 0 < closureConst m (decKappa Δ (min α 1) (1 / 16) m) := by
      unfold closureConst
      positivity
    apply lt_min
    · positivity
    · positivity

/-- **The main theorem with an explicit constant**: under the steps 2–5, every collection of `m`
codes `ker H_i` (`H_i` — `(α, ε)`-expanders with left degree `δ`, right degrees `≤ Δ`,
`ε ≤ 1/16`) is `rhoConst m Δ α`-product-expanding. -/
theorem prodExpanding_rhoConst (h2 : Step2Statement) (h3 : Step3Statement)
    (h4 : Step4Statement) (h5 : Step5Statement) {m Δ : ℕ} {α : ℝ} (hα : 0 < α) {F : Type}
    [Field F] [DecidableEq F] {δ : ℕ} {ε : ℝ} (hδ : 0 < δ) (hε1 : ε ≤ 1 / 16) {n : ℕ}
    {P : Fin m → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (H : ∀ i, Matrix (P i) (Fin n) F) (hH : ∀ i, IsExpanderMatrix (H i) δ Δ α ε) :
    prodExpanding (fun i => kerCode (H i)) (rhoConst m Δ α) := by
  have hα'0 : 0 < min α 1 := lt_min hα one_pos
  have hα'1 : min α 1 ≤ 1 := min_le_right _ _
  have hH' : ∀ i, IsExpanderMatrix (H i) δ Δ (min α 1) (1 / 16) := fun i =>
    isExpanderMatrix_mono_eps (isExpanderMatrix_mono_alpha (hH i) (min_le_left _ _)) hε1
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact prodExpanding_of_isEmpty _ _
  · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hκ0 : 0 < decKappa Δ (min α 1) (1 / 16) m := decKappa_pos hα'0 (by norm_num) m
    have hκ1 : decKappa Δ (min α 1) (1 / 16) m ≤ 1 :=
      (decKappa_le_half hα'0 (by norm_num) m).trans (by norm_num)
    have key := prodExpanding_of_generatedFromInside_of_two_le (fun i => kerCode (H i))
      hα'0.le hκ0 hκ1 (fun hn M hM => generatedFromInside_of_steps h2 h3 h4 h5 hδ hα'0 hα'1
        (by norm_num) le_rfl H hH' (by rw [mul_comm]; exact hn) M (by rwa [Fintype.card_fin]))
    rw [Fintype.card_fin] at key
    rw [rhoConst, ite_eq_right hm.ne']
    exact key

/-- **Main theorem, uniform form** (as in the paper): `ρ₀` depends only on `m`, `Δ`, `α`
(not on the field, `δ`, `ε ≤ 1/16`, `n`). -/
def MainTheoremUniformStatement : Prop :=
  ∀ (m Δ : ℕ) (α : ℝ), 0 < α → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (F : Type) [Field F] [DecidableEq F] (δ : ℕ) (ε : ℝ), 0 < δ → 0 ≤ ε → ε ≤ 1 / 16 →
    ∀ (n : ℕ) (P : Fin m → Type) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
      (H : ∀ i, Matrix (P i) (Fin n) F), (∀ i, IsExpanderMatrix (H i) δ Δ α ε) →
      prodExpanding (fun i => kerCode (H i)) ρ₀

/-- The uniform main theorem, given the four steps of the proof of lemma `D`
(`ρ₀ = rhoConst m Δ α`). -/
theorem mainTheoremUniform_of_steps (h2 : Step2Statement) (h3 : Step3Statement)
    (h4 : Step4Statement) (h5 : Step5Statement) : MainTheoremUniformStatement :=
  fun m Δ α hα => ⟨rhoConst m Δ α, rhoConst_pos hα, fun _ _ _ _ _ hδ _ hε1 _ _ _ _ H hH =>
    prodExpanding_rhoConst h2 h3 h4 h5 hα hδ hε1 H hH⟩

/-- The main theorem, given the four steps of the proof of lemma `D`. -/
theorem mainTheorem_of_steps (h2 : Step2Statement) (h3 : Step3Statement) (h4 : Step4Statement)
    (h5 : Step5Statement) : MainTheoremStatement := by
  intro F _ _ m δ Δ α ε hδ hα hε0 hε1
  obtain ⟨ρ₀, hρ₀, h⟩ := mainTheoremUniform_of_steps h2 h3 h4 h5 m Δ α hα
  exact ⟨ρ₀, hρ₀, fun n P _ _ H hH => h F δ ε hδ hε0 hε1 n P H hH⟩

end ProductExpansion
