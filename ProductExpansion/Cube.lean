import ProductExpansion.Basic

/-!
# Cube infrastructure: faces, bases, closed sets, line-generated subspaces

Notation follows the proof.
* For `I : Finset ι`, an `I`-face is indexed by its position `b : {i // i ∉ I} → Fin n`
  (an element of the base `B_I`); its points are `glue z b` for `z : {i // i ∈ I} → Fin n`.
* `faceRestrict a I b` is the restriction `a_{I,b}` of a word to the face.
* `posFull S I` is `Y_I(S)`, the set of positions of `I`-faces contained in `S`.
* `IsClosedSet η S`: every line with at least `η n` points of `S` lies in `S`.
* `lineSpan C M` is `L(M)`: the span of codewords supported on lines contained in `M`.
-/

open Finset

namespace ProductExpansion

variable {F : Type*} [Field F]
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Glue inner coordinates `z` (indexed by `I`) and outer coordinates `b` (indexed by the
complement of `I`) into a point of the cube. -/
def glue (I : Finset ι) (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n) : ι → Fin n :=
  fun i => if h : i ∈ I then z ⟨i, h⟩ else b ⟨i, h⟩

/-- Inner part of a point with respect to `I`. -/
def inner (I : Finset ι) (y : ι → Fin n) : {i // i ∈ I} → Fin n := fun i => y i.1

/-- Outer part (position) of a point with respect to `I`. -/
def outer (I : Finset ι) (y : ι → Fin n) : {i // i ∉ I} → Fin n := fun i => y i.1

omit [Fintype ι] in
@[simp] lemma glue_inner_outer (I : Finset ι) (y : ι → Fin n) :
    glue I (inner I y) (outer I y) = y := by
  funext i; by_cases h : i ∈ I <;> simp [glue, inner, outer, h]

omit [Fintype ι] in
@[simp] lemma inner_glue (I : Finset ι) (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n) :
    inner I (glue I z b) = z := by
  funext i; simp [glue, inner, i.2]

omit [Fintype ι] in
@[simp] lemma outer_glue (I : Finset ι) (z : {i // i ∈ I} → Fin n) (b : {i // i ∉ I} → Fin n) :
    outer I (glue I z b) = b := by
  funext i; simp [glue, outer, i.2]

/-- The `I`-face in position `b`, as a finset of points. -/
def face (I : Finset ι) (b : {i // i ∉ I} → Fin n) : Finset (ι → Fin n) :=
  Finset.univ.image fun z => glue I z b

/-- Restriction `a_{I,b}` of a word to the `I`-face in position `b`. -/
def faceRestrict (a : (ι → Fin n) → F) (I : Finset ι) (b : {i // i ∉ I} → Fin n) :
    ({i // i ∈ I} → Fin n) → F :=
  fun z => a (glue I z b)

/-- `Y_I(S)`: positions of `I`-faces contained in `S`. -/
def posFull (S : Set (ι → Fin n)) (I : Finset ι) : Set ({i // i ∉ I} → Fin n) :=
  {b | ∀ z, glue I z b ∈ S}

/-- Number of points of `S` on the line in direction `i` through `y`. -/
noncomputable def lineCount (S : Set (ι → Fin n)) (i : ι) (y : ι → Fin n) : ℕ :=
  Nat.card {t : Fin n // Function.update y i t ∈ S}

/-- `S` is `η`-closed: every line with at least `η n` points of `S` is contained in `S`. -/
def IsClosedSet (η : ℝ) (S : Set (ι → Fin n)) : Prop :=
  ∀ i y, η * n ≤ (lineCount S i y : ℝ) → ∀ t, Function.update y i t ∈ S

/-- Words supported in `S`. -/
def SupportedIn (a : (ι → Fin n) → F) (S : Set (ι → Fin n)) : Prop :=
  ∀ y, a y ≠ 0 → y ∈ S

/-- The subspace of words supported in `S`. -/
def supported (F : Type*) [Field F] (S : Set (ι → Fin n)) :
    Submodule F ((ι → Fin n) → F) where
  carrier := {a | SupportedIn a S}
  add_mem' := by
    intro a b ha hb y hy
    by_contra hS
    have h1 : a y = 0 := by by_contra h; exact hS (ha y h)
    have h2 : b y = 0 := by by_contra h; exact hS (hb y h)
    exact hy (by simp [h1, h2])
  zero_mem' := by intro y hy; simp at hy
  smul_mem' := by
    intro c a ha y hy
    apply ha y
    intro h0; apply hy; simp [h0]

/-- Line codewords: words supported on the line in direction `i` through `y`, whose restriction
to that line lies in `C i`. -/
def IsLineCodeword (C : ι → Submodule F (Fin n → F)) (a : (ι → Fin n) → F) (i : ι)
    (y : ι → Fin n) : Prop :=
  SupportedIn a {z | ∃ t, z = Function.update y i t} ∧ restrictLine a i y ∈ C i

/-- `L(M)`: the span of line codewords on lines contained in `M`. -/
def lineSpan (C : ι → Submodule F (Fin n → F)) (M : Set (ι → Fin n)) :
    Submodule F ((ι → Fin n) → F) :=
  Submodule.span F {a | ∃ i y, (∀ t, Function.update y i t ∈ M) ∧ IsLineCodeword C a i y}

/-- `M` is generated from inside: every codeword of `⊞ C` supported in `M` lies in `L(M)`. -/
def GeneratedFromInside (C : ι → Submodule F (Fin n → F)) (M : Set (ι → Fin n)) : Prop :=
  boxplus C ⊓ supported F M ≤ lineSpan C M

end ProductExpansion
