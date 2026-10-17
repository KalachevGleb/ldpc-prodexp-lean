import ProductExpansion.MainInterface

/-!
# Step 2 of the proof of the main lemma `D(d)`

See `MainInterface.lean` (`Step2Statement`) and the proof of lemma `lem:D`.

For `|I| = d'` and `b ∉ Bad_I` the defect `D_{I,b} = E_{I,b} ∪ ⋃_{j ∉ I} Q_j` is proper:
* `E_{I,b}` is proper since `Y_I(E) ⊆ Bad_I` (`posFull_subset_badSet`);
* `Q_j` is proper: otherwise the `(I ∪ j)`-face over `b` is full in `N`
  (`resPos_insert_mem_posFull_of_full`), so by (I2) its position lies in `Bad_{I ∪ j}`, and by (L)
  `b ∈ Bad_I`;
* (F1), (F2) in the face cube (`biUnion_ne_univ_of_isClosedSet`, family indexed by `Option ι`).
-/

open Finset

namespace ProductExpansion

section Step2Aux

variable {n : ℕ} {ι : Type*} [DecidableEq ι]

/-- If the `j`-lines (`j ∉ I`) through all points of the `I`-face in position `b` lie in `N`,
then the `(I ∪ j)`-face in position `b|_{K \ (I ∪ j)}` lies in `N` (`(YY)`). -/
lemma resPos_insert_mem_posFull_of_full {N : Set (ι → Fin n)} {I : Finset ι} {j : ι}
    (hj : j ∉ I) {b : {i // i ∉ I} → Fin n}
    (h : ∀ z t, Function.update (glue I z b) j t ∈ N) :
    resPos (Finset.subset_insert j I) b ∈ posFull N (insert j I) := by
  have key : ∀ t, Function.update b (⟨j, hj⟩ : {i // i ∉ I}) t ∈ posFull N I := by
    intro t z
    rw [glue_update_outer]
    exact h z t
  exact resPos_mem_posFull_insert key

end Step2Aux

theorem step2 : Step2Statement := by
  intro F _ _ n ι _ _ P _ _ H δ η' κ ηb d' E N hn hd' hdι hη' hκ hE hN hinv hηb hdηb I hI b hb
  -- `I ≠ univ` and the face cube is nonempty
  have hIu : I ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at hI
    omega
  have : Nonempty {i // i ∈ I} := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < I.card)
    exact ⟨⟨i, hi⟩⟩
  have hcardI : Fintype.card {i // i ∈ I} = d' := by simp [hI]
  have hcompl : ((Iᶜ : Finset ι).card : ℝ) = ((Fintype.card ι - d' : ℕ) : ℝ) := by
    rw [Finset.card_compl, hI]
  -- the family `E_{I,b}`, `Q_j` (`j ∈ Iᶜ`), indexed by `Option ι`
  set S : Option ι → Set ({i // i ∈ I} → Fin n) := fun o => o.elim {z | glue I z b ∈ E}
    (fun j => {z | glue I z b ∈ {y | ∀ t, Function.update y j t ∈ N}}) with hS
  set η : Option ι → ℝ := fun o => o.elim η' (fun _ => κ) with hηdef
  have hU : faceDefect N E I b = ⋃ o ∈ Finset.insertNone Iᶜ, S o := by
    rw [faceDefect_eq_union]
    ext z
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, Option.exists,
      Finset.some_mem_insertNone, hS, Option.elim_none, Option.elim_some]
    simp
  rw [hU]
  apply biUnion_ne_univ_of_isClosedSet hn (η := η)
  · -- closedness
    intro o _
    cases o with
    | none => exact hE.face_closed I b
    | some j => exact (hN.setOf_full_line j).face_closed I b
  · -- properness
    intro o ho
    cases o with
    | none =>
      -- `E_{I,b} = V^I` would give `b ∈ Y_I(E) ⊆ Bad_I`
      intro hfull
      apply hb
      apply posFull_subset_badSet hIu
      intro z
      have : z ∈ ({z | glue I z b ∈ E} : Set ({i // i ∈ I} → Fin n)) := by
        change ({z | glue I z b ∈ E} : Set ({i // i ∈ I} → Fin n)) = Set.univ at hfull
        rw [hfull]; trivial
      exact this
    | some j =>
      have hj : j ∉ I := by simpa using (Finset.some_mem_insertNone.1 ho)
      intro hfull
      apply hb
      have hall : ∀ z t, Function.update (glue I z b) j t ∈ N := by
        intro z
        have : z ∈ ({z | glue I z b ∈ {y | ∀ t, Function.update y j t ∈ N}} :
            Set ({i // i ∈ I} → Fin n)) := by
          change ({z | glue I z b ∈ {y | ∀ t, Function.update y j t ∈ N}} :
            Set ({i // i ∈ I} → Fin n)) = Set.univ at hfull
          rw [hfull]; trivial
        exact this
      have hpos := resPos_insert_mem_posFull_of_full hj hall
      have hcard : d' < (insert j I).card := by
        rw [Finset.card_insert_of_notMem hj, hI]; omega
      have hbad := hinv (insert j I) hcard hpos
      exact mem_badSet_of_resPos hIu (Finset.ssubset_insert hj) hbad
  · -- `d' (η' + |Iᶜ| κ) ≤ d' ηb ≤ 1`
    rw [hcardI, Finset.sum_insertNone]
    simp only [hηdef, Option.elim_none, Option.elim_some, Finset.sum_const, nsmul_eq_mul]
    rw [hcompl]
    have hd0 : (0 : ℝ) ≤ d' := Nat.cast_nonneg d'
    calc (d' : ℝ) * (η' + ((Fintype.card ι - d' : ℕ) : ℝ) * κ) ≤ d' * ηb :=
          mul_le_mul_of_nonneg_left hηb hd0
      _ ≤ 1 := hdηb

end ProductExpansion
