import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Diagonal similarity and diagonal equivalence of matrices

This file formalizes the notion used throughout Al Ahmadieh's "The Fiber of the
Principal Minor Map" and Chatterjee–Ghosh–Gurjar–Raj's "Characterizing and Testing
Principal Minor Equivalence of Matrices":

Two `n × n` matrices `A B` over a ring are *diagonally similar* if there is an
invertible diagonal matrix `D` with `A = D * B * D⁻¹`, and *diagonally equivalent*
if `A` is diagonally similar to `B` or to `Bᵀ`.

Rather than working with `Matrix.inv` (which requires nonsingularity hypotheses and
is awkward for general rings), we represent an "invertible diagonal matrix" directly
as a function `d : n → Rˣ` into the units of `R`. The diagonal matrix is then
`Matrix.diagonal (fun i => (d i : R))` and its inverse is
`Matrix.diagonal (fun i => ((d i)⁻¹ : R))`.

We work over a `CommRing R` (matrix multiplication doesn't need commutativity per se,
but the papers work over a field/any field `F`, and `CommRing` is the natural common
generality; feel free to specialize to `Field` later if a proof genuinely needs it).
-/

namespace PrincipalMinorFormalization

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- The diagonal matrix associated to a family of units `d : n → Rˣ`. -/
def diagOfUnits (d : n → Rˣ) : Matrix n n R :=
  Matrix.diagonal (fun i => (d i : Rˣ))

/-- The inverse diagonal matrix associated to `d : n → Rˣ`, i.e. the diagonal matrix
built from `d⁻¹`. -/
def diagOfUnits_inv (d : n → Rˣ) : Matrix n n R :=
  Matrix.diagonal (fun i => ((d i)⁻¹ : Rˣ))

/-- `A` and `B` are *diagonally similar* if `A = D B D⁻¹` for some invertible
diagonal matrix `D`, encoded here via a family of units `d : n → Rˣ`. -/
def DiagSimilar (A B : Matrix n n R) : Prop :=
  ∃ d : n → Rˣ, A = diagOfUnits d * B * diagOfUnits_inv d

/-- `A` and `B` are *diagonally equivalent* if `A` is diagonally similar to `B` or
to `Bᵀ`. This is the relation `D(n)` / `\overset{DE}{=}` from the papers. -/
def DiagEquiv (A B : Matrix n n R) : Prop :=
  DiagSimilar A B ∨ DiagSimilar A Bᵀ

/-! ## Basic interaction between `diagOfUnits` and its "inverse" -/

/-- `diagOfUnits d` and `diagOfUnits_inv d` really are inverse to each other. -/
@[simp]
lemma diagOfUnits_mul_inv (d : n → Rˣ) :
    diagOfUnits d * diagOfUnits_inv d = 1 := by
    unfold diagOfUnits diagOfUnits_inv
    simp
    -- more verbose proof completion:
    -- rw [diagonal_mul_diagonal]
    -- simp_rw [Units.mul_inv]
    -- rw [diagonal_one]

@[simp]
lemma diagOfUnits_inv_mul (d : n → Rˣ) :
    diagOfUnits_inv d * diagOfUnits d = 1 := by
  unfold diagOfUnits diagOfUnits_inv
  -- simp
  -- proof completion using the previous theorem
  rw [commute_diagonal]
  change diagOfUnits d * diagOfUnits_inv d = 1
  rw [diagOfUnits_mul_inv]

/-! ## `DiagSimilar` is an equivalence relation -/

lemma diagSimilar_refl (A : Matrix n n R) : DiagSimilar A A := by
  exists fun i => 1
  unfold diagOfUnits diagOfUnits_inv
  simp

lemma diagSimilar_symm {A B : Matrix n n R} (h : DiagSimilar A B) : DiagSimilar B A := by
  obtain ⟨hdiag, hsim⟩ := h
  unfold DiagSimilar
  exists fun i => (hdiag i)⁻¹
  change B = diagOfUnits_inv hdiag * A * diagOfUnits hdiag
  rw [hsim]
  simp only [mul_assoc, diagOfUnits_inv_mul, mul_one]
  simp only [←mul_assoc, diagOfUnits_inv_mul, one_mul]

lemma diagSimilar_trans {A B C : Matrix n n R}
    (hAB : DiagSimilar A B) (hBC : DiagSimilar B C) : DiagSimilar A C := by
  obtain ⟨diagAB, hsimAB⟩ := hAB
  obtain ⟨diagBC, hsimBC⟩ := hBC
  -- the D making A,C similar is diagAB diagBC
  exists fun i => (diagAB i ) * (diagBC i)
  unfold diagOfUnits diagOfUnits_inv
  simp only [Units.val_mul, ← diagonal_mul_diagonal, mul_inv_rev]
  change A = (diagOfUnits diagAB * diagOfUnits diagBC) *
    C * (diagOfUnits_inv diagBC * diagOfUnits_inv diagAB)
  have hsimCB : C = diagOfUnits_inv diagBC * B * diagOfUnits diagBC := by
    simp [hsimBC, mul_assoc, diagOfUnits_inv_mul]
    simp [←mul_assoc]
  calc
    A = diagOfUnits diagAB * B * diagOfUnits_inv diagAB := hsimAB
    _ = diagOfUnits diagAB * (diagOfUnits diagBC * C * diagOfUnits_inv diagBC)
      * diagOfUnits_inv diagAB := by
      rw [←hsimBC]
  simp [mul_assoc]

/-- Packaged as a genuine `Equivalence` term. -/
lemma diagSimilar_equivalence : Equivalence (DiagSimilar (n := n) (R := R)) where
  refl := diagSimilar_refl
  symm := diagSimilar_symm
  trans := diagSimilar_trans

/-! ## Interaction of `DiagSimilar` with transpose

This is the key lemma needed to show `DiagEquiv` is transitive: diagonal similarity
is preserved under transposing both sides (since a diagonal matrix equals its own
transpose, `Dᵀ = D`).
-/
lemma mul_trans_swap {A B : Matrix n n R} (A * B)ᵀ = Bᵀ * Aᵀ := sorry

lemma diagSimilar_transpose {A B : Matrix n n R} (h : DiagSimilar A B) :
    DiagSimilar Aᵀ Bᵀ := by
  obtain ⟨hDiag, hsimAB⟩ := h
  exists fun i => (hDiag i)⁻¹
  calc
    Aᵀ = (diagOfUnits hDiag * B * diagOfUnits_inv hDiag)ᵀ := by rw [hsimAB]
    _ = diagOfUnits_inv hDiag * Bᵀ * diagOfUnits hDiag := by

/-! ## `DiagEquiv` is an equivalence relation -/

lemma diagEquiv_refl (A : Matrix n n R) : DiagEquiv A A := by
  sorry

lemma diagEquiv_symm {A B : Matrix n n R} (h : DiagEquiv A B) : DiagEquiv B A := by
  sorry

/-- The transitivity of `DiagEquiv` is the nontrivial case: if `A` is similar to `B`
or `Bᵀ`, and `B` is similar to `C` or `Cᵀ`, we must combine these (using
`diagSimilar_transpose` and `transpose_transpose`) to show `A` is similar to `C`
or `Cᵀ`. -/
lemma diagEquiv_trans {A B C : Matrix n n R}
    (hAB : DiagEquiv A B) (hBC : DiagEquiv B C) : DiagEquiv A C := by
  sorry

lemma diagEquiv_equivalence : Equivalence (DiagEquiv (n := n) (R := R)) where
  refl := diagEquiv_refl
  symm := diagEquiv_symm
  trans := diagEquiv_trans

/-! ## Sanity check: diagonally equivalent matrices are principal-minor equivalent

This is not needed to prove `DiagEquiv` is an equivalence relation, but it's the
first real "content" lemma of the whole project (diagonal equivalence ⇒ PME), and a
natural next target once the above is done. Left here as a placeholder / signpost —
it likely depends on a `principalMinor` definition that doesn't exist yet, so it's
commented out rather than sorry'd.
-/

-- lemma principalMinor_eq_of_diagEquiv {A B : Matrix n n R} (h : DiagEquiv A B)
--     (S : Finset n) : principalMinor A S = principalMinor B S := by
--   sorry

end PrincipalMinorFormalization
