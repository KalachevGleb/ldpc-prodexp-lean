import ProductExpansion.MainInterface

/-!
# Step 4 of the proof of the main lemma `D(d)`

See `MainInterface.lean` (`Step4Statement`) and the proof of lemma `lem:D`.

* `faceExtendLin I b`: extension by zero of a word of the `I`-face cube to the whole cube
  (`c_b ⊗ δ_b`); `faceExtendLin_mem_lineSpan`: a word of `⊞` of the face, extended from a face
  contained in `M`, lies in `L(M)`.
* `inner_mem_faceDefect_of_ne` (geometry `(*)`): a point lying in two different full faces of
  the same dimension lies in the defect of each of them.
* `step4`: decodable faces are the pairs `⟨I, b⟩` with `|I| = d'`, `b ∉ Bad_I`, `b ∈ Y_I(N)`;
  `a' = a - ∑ ext(c_b)` and `N' = {y ∈ N | inner_I y ∈ Ŝ_b for every decodable face ∋ y}`
  (by `(*)` this is the set `(N \ ⋃ Φ_I(b)) ∪ ⋃ Ŝ_b × {b}`).
-/

open Finset

namespace ProductExpansion

section FaceExtend

variable {F : Type*} [Field F] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extension by zero of a word on the `I`-face in position `b` to the whole cube
(`x ⊗ δ_b`). -/
def faceExtendLin (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    (({i // i ∈ I} → Fin n) → F) →ₗ[F] ((ι → Fin n) → F) where
  toFun x y := if outer I y = b then x (inner I y) else 0
  map_add' x x' := by
    funext y
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

lemma faceExtendLin_apply (I : Finset ι) (b : {i // i ∉ I} → Fin n)
    (x : ({i // i ∈ I} → Fin n) → F) (y : ι → Fin n) :
    faceExtendLin I b x y = if outer I y = b then x (inner I y) else 0 := rfl

@[simp] lemma faceExtendLin_glue (I : Finset ι) (b : {i // i ∉ I} → Fin n)
    (x : ({i // i ∈ I} → Fin n) → F) (z : {i // i ∈ I} → Fin n) :
    faceExtendLin I b x (glue I z b) = x z := by
  simp [faceExtendLin_apply]

lemma faceExtendLin_of_ne {I : Finset ι} {b : {i // i ∉ I} → Fin n}
    (x : ({i // i ∈ I} → Fin n) → F) {y : ι → Fin n} (hy : outer I y ≠ b) :
    faceExtendLin I b x y = 0 := by
  rw [faceExtendLin_apply, ite_eq_right hy]

/-- A line codeword of the face cube, extended by zero, is a line codeword of the cube. -/
lemma isLineCodeword_faceExtendLin {C : ι → Submodule F (Fin n → F)} {I : Finset ι}
    {b : {i // i ∉ I} → Fin n} {x : ({i // i ∈ I} → Fin n) → F} {k : {k // k ∈ I}}
    {z : {i // i ∈ I} → Fin n} (hx : IsLineCodeword (fun k : {k // k ∈ I} => C k) x k z) :
    IsLineCodeword C (faceExtendLin I b x) k.1 (glue I z b) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [faceExtendLin_apply] at hw
    split_ifs at hw with hwb
    · obtain ⟨t, ht⟩ := hx.1 _ hw
      refine ⟨t, ?_⟩
      rw [← glue_update_inner, ← ht, ← hwb, glue_inner_outer]
    · exact absurd rfl hw
  · have : restrictLine (faceExtendLin I b x) k.1 (glue I z b) = restrictLine x k z := by
      funext t
      simp only [restrictLine]
      rw [← glue_update_inner, faceExtendLin_glue]
    rw [this]
    exact hx.2

/-- **Extension from a face.** If `x ∈ ⊞` of the `I`-face cube and the face `Φ_I(b)` lies in `M`,
then `x ⊗ δ_b ∈ L(M)`. -/
theorem faceExtendLin_mem_lineSpan {C : ι → Submodule F (Fin n → F)} {M : Set (ι → Fin n)}
    {I : Finset ι} {b : {i // i ∉ I} → Fin n} (hM : ∀ z, glue I z b ∈ M)
    {x : ({i // i ∈ I} → Fin n) → F} (hx : x ∈ boxplus (fun k : {k // k ∈ I} => C k)) :
    faceExtendLin I b x ∈ lineSpan C M := by
  have hx' := boxplus_le_lineSpan_univ (fun k : {k // k ∈ I} => C k) hx
  have key : lineSpan (fun k : {k // k ∈ I} => C k) Set.univ ≤
      Submodule.comap (faceExtendLin I b) (lineSpan C M) := by
    rw [lineSpan, Submodule.span_le]
    rintro x ⟨k, z, -, hxk⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply (isLineCodeword_faceExtendLin hxk).mem_lineSpan
    intro t
    rw [← glue_update_inner]
    exact hM _
  exact key hx'

end FaceExtend

section TwoFaces

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Geometry `(*)` of step 4.** If `y` lies in two different faces `⟨I, b⟩ ≠ ⟨I', b'⟩` with
`|I| = |I'|`, and the second face is full in `N`, then `inner_I y ∈ D_{I,b}`: some direction
`i' ∈ I' \ I` gives a full line of `N` through `y`. -/
lemma inner_mem_faceDefect_of_ne {N E : Set (ι → Fin n)} {y : ι → Fin n}
    {p q : Σ I : Finset ι, ({i // i ∉ I} → Fin n)} (hpq : p ≠ q) (hcard : p.1.card = q.1.card)
    (hp : outer p.1 y = p.2) (hq : outer q.1 y = q.2) (hqN : q.2 ∈ posFull N q.1) :
    inner p.1 y ∈ faceDefect N E p.1 p.2 := by
  obtain ⟨I, b⟩ := p
  obtain ⟨I', b'⟩ := q
  simp only at hcard hp hq hqN ⊢
  by_cases hII : I = I'
  · subst hII
    subst hp
    subst hq
    exact absurd rfl hpq
  · obtain ⟨i', hi'I', hi'I⟩ : ∃ i' ∈ I', i' ∉ I := by
      by_contra hcon
      push Not at hcon
      exact hII (Finset.eq_of_subset_of_card_le hcon (by omega)).symm
    refine Or.inr ⟨i', hi'I, fun t => ?_⟩
    rw [← hp, glue_inner_outer]
    have := hqN (inner I' (Function.update y i' t))
    rwa [← hq, ← outer_update_of_mem I' y hi'I' t, glue_inner_outer] at this

end TwoFaces

section Decodable

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {P : ι → Type*} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- Decodable faces of level `d'`: `|I| = d'`, `b ∉ Bad_I`, `Φ_I(b) ⊆ N`. -/
def IsDecodableFace (H : ∀ i, Matrix (P i) (Fin n) F) (δ : ℕ) (E N : Set (ι → Fin n)) (d' : ℕ)
    (p : Σ I : Finset ι, ({i // i ∉ I} → Fin n)) : Prop :=
  p.1.card = d' ∧ p.2 ∉ badSet H ((1 / 4 : ℝ) * δ) E p.1 ∧ p.2 ∈ posFull N p.1

/-- The canonical set `Ŝ_b` of the defect `D_{I,b}` of a face, in the face cube. -/
noncomputable def faceHat (H : ∀ i, Matrix (P i) (Fin n) F) (δ : ℕ) (ε : ℝ)
    (E N : Set (ι → Fin n)) (p : Σ I : Finset ι, ({i // i ∉ I} → Fin n)) :
    Set ({k // k ∈ p.1} → Fin n) :=
  canonicalSet (fun k : {k // k ∈ p.1} => H k) δ ε (faceDefect N E p.1 p.2)

end Decodable

theorem step4 : Step4Statement := by
  intro F _ _ n ι _ _ P _ _ H δ Δ α ε η' κ ηb d' E N0 N e0 a hH hδ hε0 hε hαn hα1 hd' hdι hη' hκ
    hE hEne hN hinv hproper hNN0 ha he0 hgood hηb hc' hc
  classical
  set Dec := IsDecodableFace H δ E N d'
  set Sh := faceHat H δ ε E N
  have hηb0 : 0 ≤ ηb := by
    have : 0 ≤ ((Fintype.card ι - d' : ℕ) : ℝ) * κ := mul_nonneg (Nat.cast_nonneg _) hκ
    linarith
  -- (0) decodable faces: `D_b ⊆ Ŝ_b`, `Ŝ_b ≠ univ`, `Ŝ_b` is `c_{d'} η_b`-closed
  have hspec : ∀ p, Dec p → faceDefect N E p.1 p.2 ⊆ Sh p ∧ Sh p ≠ Set.univ ∧
      IsClosedSet (canC (1 / 4 - ε) d' * ηb) (Sh p) := by
    intro p hp
    obtain ⟨hcard, hbad, -⟩ := hp
    have : Nonempty {k // k ∈ p.1} := by
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < p.1.card)
      exact ⟨⟨i, hi⟩⟩
    have hK : Fintype.card {k // k ∈ p.1} = d' := by simp [hcard]
    have hDcl : IsClosedSet ηb (faceDefect N E p.1 p.2) := by
      have := hN.faceDefect_closed hE p.1 p.2
      rw [hcard] at this
      exact this.mono hηb
    have hDne := hproper p.1 hcard p.2 hbad
    have spec := canonicalSet_spec (H := fun k : {k // k ∈ p.1} => H k) (fun k => hH k.1) hδ hε
      hαn hDcl hDne hηb0 (by rw [hK]; exact hc') (by rw [hK]; exact hc)
    rw [hK] at spec
    exact ⟨spec.1.trans spec.2.1, spec.2.2.1, spec.2.2.2.1⟩
  -- choice of `c_b ∈ ⊞_I` with `supp (X_b - c_b) ⊆ Ŝ_b` (step 3)
  have hdec : ∀ p : Σ I : Finset ι, ({i // i ∉ I} → Fin n),
      ∃ c : ({k // k ∈ p.1} → Fin n) → F, Dec p →
        c ∈ boxplus (fun k : {k // k ∈ p.1} => kerCode (H k)) ∧
          SupportedIn (faceRestrict a p.1 p.2 - c) (Sh p) := by
    intro p
    by_cases hp : Dec p
    · obtain ⟨c, hcmem, f, hf, hcf⟩ := Submodule.mem_sup.1 (hgood p.1 hp.1 p.2 hp.2.1 hp.2.2)
      refine ⟨c, fun _ => ⟨hcmem, ?_⟩⟩
      have : faceRestrict a p.1 p.2 - c = f := by rw [← hcf]; abel
      rw [this]
      exact hf
    · exact ⟨0, fun h => absurd h hp⟩
  choose c hcb using hdec
  -- the new word `a'` and the new set `N'`
  set 𝒟 := Finset.univ.filter Dec with h𝒟
  have hmem𝒟 : ∀ p, p ∈ 𝒟 ↔ Dec p := fun p => by simp [h𝒟]
  obtain ⟨a', ha'⟩ : ∃ a' : (ι → Fin n) → F,
      a' = a - ∑ p ∈ 𝒟, faceExtendLin p.1 p.2 (c p) := ⟨_, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N' : Set (ι → Fin n),
      N' = {y | y ∈ N ∧ ∀ p, Dec p → outer p.1 y = p.2 → inner p.1 y ∈ Sh p} := ⟨_, rfl⟩
  have hmemN' : ∀ y, y ∈ N' ↔ y ∈ N ∧ ∀ p, Dec p → outer p.1 y = p.2 → inner p.1 y ∈ Sh p := by
    intro y; rw [hN']; rfl
  have hN'N : N' ⊆ N := fun y hy => ((hmemN' y).1 hy).1
  -- (3) on a decodable face, `N'` is `Ŝ_b`
  have hface : ∀ p, Dec p → ∀ x, outer p.1 x = p.2 → (x ∈ N' ↔ inner p.1 x ∈ Sh p) := by
    intro p hp x hpx
    rw [hmemN']
    constructor
    · intro hx; exact hx.2 p hp hpx
    · intro hx
      refine ⟨?_, fun q hq hqx => ?_⟩
      · have := hp.2.2 (inner p.1 x)
        rwa [← hpx, glue_inner_outer] at this
      · by_cases hqp : q = p
        · subst hqp; exact hx
        · exact (hspec q hq).1
            (inner_mem_faceDefect_of_ne hqp (by rw [hq.1, hp.1]) hqx hpx hp.2.2)
  refine ⟨N', a', hN'N, ?_, ?_, ?_, ?_⟩
  · -- closedness: `N'` is `max κ (c_{d'} η_b)`-closed
    intro i y hcount t
    have hκle : κ * n ≤ max κ (canC (1 / 4 - ε) d' * ηb) * n :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg n)
    have hcle : canC (1 / 4 - ε) d' * ηb * n ≤ max κ (canC (1 / 4 - ε) d' * ηb) * n :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg n)
    -- (i) the line lies in `N`
    have hlineN : ∀ s, Function.update y i s ∈ N := by
      by_contra hnot
      have h1 := hN.lineCount_lt hnot
      have h2 : (lineCount N' i y : ℝ) ≤ lineCount N i y := by
        exact_mod_cast lineCount_le_of_subset hN'N i y
      linarith
    by_cases hdir : ∃ p, Dec p ∧ i ∈ p.1 ∧ outer p.1 y = p.2
    · -- (ii) the line lies in a decodable face `⟨I, b⟩`, `i ∈ I`: there `N'` is `Ŝ_b`
      obtain ⟨p, hp, hi, hpy⟩ := hdir
      have hiff : ∀ s, Function.update y i s ∈ N' ↔
          Function.update (inner p.1 y) ⟨i, hi⟩ s ∈ Sh p := by
        intro s
        rw [hface p hp _ (by rw [outer_update_of_mem p.1 y hi s, hpy]),
          inner_update_of_mem p.1 y hi s]
      have hcnt : lineCount N' i y = lineCount (Sh p) ⟨i, hi⟩ (inner p.1 y) := by
        simp only [lineCount, hiff]
      rw [hiff]
      refine (hspec p hp).2.2 ⟨i, hi⟩ (inner p.1 y) ?_ t
      rw [← hcnt]
      linarith
    · -- (iii) every point of the line lies on the line itself, a full line of `N` of a
      -- direction `∉ I` for every decodable face `⟨I, b⟩` through it
      push Not at hdir
      rw [hmemN']
      refine ⟨hlineN t, fun q hq hqx => ?_⟩
      have hiq : i ∉ q.1 := by
        intro hiq
        apply hdir q hq hiq
        rw [← outer_update_of_mem q.1 y hiq t]
        exact hqx
      apply (hspec q hq).1
      refine Or.inr ⟨i, hiq, fun s => ?_⟩
      rw [← hqx, glue_inner_outer, Function.update_idem]
      exact hlineN s
  · -- support: `supp a' ⊆ N'`
    intro y hy
    rw [hmemN']
    by_cases hin : ∃ p, Dec p ∧ outer p.1 y = p.2
    · obtain ⟨p₀, hp₀, hp₀y⟩ := hin
      refine ⟨?_, fun p hp hpy => ?_⟩
      · have := hp₀.2.2 (inner p₀.1 y)
        rwa [← hp₀y, glue_inner_outer] at this
      · by_cases huniq : ∃ q, Dec q ∧ outer q.1 y = q.2 ∧ q ≠ p
        · obtain ⟨q, hq, hqy, hqp⟩ := huniq
          exact (hspec p hp).1
            (inner_mem_faceDefect_of_ne (Ne.symm hqp) (by rw [hp.1, hq.1]) hpy hqy hq.2.2)
        · push Not at huniq
          have hsum : (∑ q ∈ 𝒟, faceExtendLin q.1 q.2 (c q)) y = c p (inner p.1 y) := by
            rw [Finset.sum_apply, Finset.sum_eq_single p]
            · rw [faceExtendLin_apply, ite_eq_left hpy]
            · intro q hq hqp
              exact faceExtendLin_of_ne _ (fun hqy => hqp (huniq q ((hmem𝒟 q).1 hq) hqy))
            · intro hp'
              exact absurd ((hmem𝒟 p).2 hp) hp'
          have hval : a' y = a y - c p (inner p.1 y) := by
            rw [ha', Pi.sub_apply, hsum]
          apply (hcb p hp).2
          show faceRestrict a p.1 p.2 (inner p.1 y) - c p (inner p.1 y) ≠ 0
          rw [faceRestrict_apply, ← hpy, glue_inner_outer, ← hval]
          exact hy
    · push Not at hin
      have hval : a' y = a y := by
        rw [ha', Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_zero, sub_zero]
        intro q hq
        exact faceExtendLin_of_ne _ (hin q ((hmem𝒟 q).1 hq))
      exact ⟨ha y (hval ▸ hy), fun q hq hqy => absurd hqy (hin q hq)⟩
  · -- `e0 - a' = (e0 - a) + ∑ ext(c_b) ∈ L(N0)`
    have hS : ∑ p ∈ 𝒟, faceExtendLin p.1 p.2 (c p) ∈ lineSpan (fun i => kerCode (H i)) N0 := by
      refine Submodule.sum_mem _ fun p hp => ?_
      have hp' := (hmem𝒟 p).1 hp
      exact lineSpan_mono hNN0 (faceExtendLin_mem_lineSpan (fun z => hp'.2.2 z) (hcb p hp').1)
    have : e0 - a' = (e0 - a) + ∑ p ∈ 𝒟, faceExtendLin p.1 p.2 (c p) := by rw [ha']; abel
    rw [this]
    exact Submodule.add_mem _ he0 hS
  · -- (I2) at level `d' - 1`
    intro J hJ b hb
    by_cases hJd : d' < J.card
    · exact hinv J hJd (posFull_mono hN'N J hb)
    · have hJc : J.card = d' := by omega
      by_contra hbad
      have hp : Dec ⟨J, b⟩ := ⟨hJc, hbad, posFull_mono hN'N J hb⟩
      apply (hspec ⟨J, b⟩ hp).2.1
      rw [Set.eq_univ_iff_forall]
      intro z
      have := (hface ⟨J, b⟩ hp (glue J z b) (outer_glue J z b)).1 (hb z)
      simpa using this

end ProductExpansion
