/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib
import Formal.PowerSeries_comp


open PowerSeries Nat BigOperators Polynomial
-- open scoped Classical


variable {R : Type u} [CommRing R]

namespace PowerSeries

theorem isUnit_C_unit_add_X (a : Rˣ) : IsUnit (C R a + X) :=
by
  set inverse := mk (λ n ↦ (-a)^n)  
  apply isUnit_of_mul_eq_one
  sorry
  sorry

lemma isNilpotent_constantCoeff_sub_C_self (f : R⟦X⟧) :
  IsNilpotent <| constantCoeff R (f - C R (constantCoeff R f)) :=
by
  rw [map_sub, constantCoeff_C, sub_self]
  exact IsNilpotent.zero


lemma eq_C_add_X_comp (f : R⟦X⟧) :
  f = (C R (constantCoeff R f) + X: R⟦X⟧).comp (f - C R (constantCoeff R f)) :=
by
  have := isNilpotent_constantCoeff_sub_C_self f
  rw [add_comp, X_comp this, C_comp this, add_sub_cancel'_right]


theorem isUnit_iff (f : R⟦X⟧) :
  (IsUnit f) ↔ IsUnit (constantCoeff R f) :=
by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := hf
    apply isUnit_of_mul_eq_one (b := constantCoeff R g.inv)
    rw [←hg, ←map_mul, Units.inv_eq_val_inv, Units.mul_inv, map_one]
  · intro hf
    obtain ⟨a,ha⟩ := hf
    obtain ⟨g,hg⟩ := isUnit_C_unit_add_X a
    rw [eq_C_add_X_comp f]
    apply isUnit_of_mul_eq_one (b := g.inv.comp (f - C R (constantCoeff R f)))
    simp at hg
    rw [← ha, ←hg, ←mul_comp]
    rw [Units.inv_eq_val_inv, Units.mul_inv, one_comp]
    rw [ha]
    exact isNilpotent_constantCoeff_sub_C_self f 



end PowerSeries

