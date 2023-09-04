/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
--import Mathlib
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic

variable {R : Type u} [CommSemiring R]


open Polynomial Nat


/-- If `f` is a polynomial over `R`
  and `d` is a derivation on an `R`-algebra `A`,
  then for all `a : A` we have

    `d(f(a)) = f.derivative (a) * d a`.

  TODO : prove in the following alternative way:
  Show that both sides of the equation are derivations
  on the polynomial ring (when regarded as functions of `f`). 
  by `mv_polynomial.derivation_ext` they are equal iff they
  agree in the case f=X. This case is easier as it does
  not involve messing around with finite sums.
-/
theorem Derivation.polynomial_eval₂ [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] (d : Derivation R A M)
  (f : R[X]) (g : A) :
  d (f.eval₂ (algebraMap R A) g)
  = (eval₂ (algebraMap R A) g (derivative (R:= R) f)) • d g :=
by
  rw [eval₂_eq_sum_range, map_sum, Finset.sum_range_succ', Derivation.leibniz,
    Derivation.leibniz_pow, Derivation.map_algebraMap, zero_nsmul, smul_zero, smul_zero, zero_add,
    add_zero]
  by_cases f.natDegree = 0
  · rw [h, Finset.sum_range_zero, derivative_of_natDegree_zero h, eval₂_zero,
      zero_smul]
  · have : (derivative (R:=R) f).natDegree < f.natDegree := natDegree_derivative_lt h
    rw [eval₂_eq_sum_range' (algebraMap R A) this, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intros
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap, smul_zero, add_zero,
      add_tsub_cancel_right, coeff_derivative, map_mul, IsScalarTower.algebraMap_smul,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, one_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul,
      smul_assoc, smul_assoc, ←cast_succ, ← nsmul_eq_smul_cast]

