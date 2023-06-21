import Formal.basic


-------------------------------------------------------
-- A few examples of proving power series identities --
-------------------------------------------------------

variable {R : Type} [Field R] [CharZero R]

/-
I take the base ring to be a field of characteristic zero.
This is because
     (i) my power series have rational coefficients
         (with all natural denominators),
    (ii) there is currently no instance of `has_inv (power_series R)`
         except in the case that `R` is a field.
-/


open PowerSeries
open Nat

#check D

local notation "coeff"  => PowerSeries.coeff R
local notation "D"      => @D R _


namespace my_PowerSeries

def exp             : R⟦X⟧ := mk λ n ↦ n.factorial⁻¹
def logOneAdd       : R⟦X⟧ := mk λ n ↦ -(-1) ^ n / n
def geometricSeries : R⟦X⟧ := mk λ n ↦ (-1) ^ n 
def polylog (d : ℕ) : R⟦X⟧ := mk λ n ↦ (n⁻¹: R)^d


theorem geometricSeries_eq : geometricSeries = (1 + X : R⟦X⟧)⁻¹ :=
by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_add, mul_one]
  · ext n
    rw [map_add, geometricSeries]
    cases n with
    | zero =>
      rw [coeff_zero_mul_X, add_zero, coeff_mk, _root_.pow_zero,
        coeff_zero_eq_constantCoeff, map_one]
    | succ n =>
      rw [coeff_succ_mul_X, coeff_mk, coeff_mk, _root_.pow_succ,
        neg_one_mul, neg_add_self, coeff_one, if_neg (succ_ne_zero n)]
  · rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero


theorem D_geometricSeries : D geometricSeries = -(1 + X)⁻¹ ^ 2 :=
by
  rw [geometricSeries_eq, D_inv, map_add, D_one, D_X, zero_add,
    mul_one]

@[simp]
theorem D_exp : D exp = exp :=
by
  ext n
  rw [exp, coeff_D, coeff_mk, coeff_mk, factorial_succ, cast_mul, cast_add,
    cast_one, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [←cast_one, ←cast_add, cast_ne_zero]
  exact succ_ne_zero n

@[simp]
theorem constantCoeff_exp : constantCoeff R exp = 1 :=
by
  rw [exp, ← coeff_zero_eq_constantCoeff, coeff_mk, factorial_zero, cast_one,
    inv_one]

@[simp]
theorem exp_neg {f : R⟦X⟧} : (exp ∘ (-f) : R⟦X⟧) = (exp ∘ f : R⟦X⟧)⁻¹ :=
by
  by_cases hf : constantCoeff R f = 0
  · have : constantCoeff R (-f) = 0 := by rw [map_neg, hf, neg_eq_zero]
    rw [PowerSeries.eq_inv_iff_mul_eq_one]
    · apply eq_of_D_eq_of_const_eq
      · rw [D_mul, D_comp, D_comp, D_exp, D_one, map_neg, mul_neg, mul_neg,
          ←mul_assoc, mul_comm (exp ∘ (-f) : R⟦X⟧), mul_assoc, add_neg_self]
      · rw [map_mul, constantCoeff_comp hf, constantCoeff_comp this,
          constantCoeff_exp, map_one, mul_one]
    · rw [constantCoeff_comp hf, constantCoeff_exp]
      exact one_ne_zero
  · have : ¬constantCoeff R (-f) = 0 := by rw [map_neg, neg_eq_zero]; exact hf
    rw [comp, if_neg this, comp, if_neg hf, MvPowerSeries.zero_inv]


@[simp]
theorem exp_add (f g : R⟦X⟧) (hf : constantCoeff R f = 0) (hg : constantCoeff R g = 0) :
  (exp ∘ (f + g) : R⟦X⟧) = (exp ∘ f : R⟦X⟧) * (exp ∘ g : R⟦X⟧) :=
by
  have eq : constantCoeff R (f + g) = 0 := by rw [map_add, hf, hg, zero_add]
  suffices 1 = exp.comp f * exp.comp g * exp.comp (-(f + g))
  by
    rwa [exp_neg, MvPowerSeries.eq_mul_inv_iff_mul_eq, one_mul] at this 
    change constantCoeff R (exp ∘ (f + g)) ≠ 0
    rw [constantCoeff_comp eq, constantCoeff_exp]
    exact one_ne_zero
  apply eq_of_D_eq_of_const_eq
  · rw [D_mul, D_mul, D_comp, D_comp, D_comp, D_exp, D_one, map_neg, map_add]
    ring
  · rw [map_mul, map_mul, constantCoeff_comp hf, constantCoeff_comp hg, constantCoeff_comp,
      constantCoeff_exp, map_one, mul_one, mul_one]
    rw [map_neg, eq, neg_zero]


@[simp]
theorem constantCoeff_logOneAdd : constantCoeff R logOneAdd = 0 := by
  rw [← coeff_zero_eq_constantCoeff, logOneAdd, coeff_mk, cast_zero, div_zero]

@[simp]
theorem D_logOneAdd : D logOneAdd = (1 + X)⁻¹ :=
by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  ext n
  rw [mul_add, mul_one, map_add, coeff_D, logOneAdd, coeff_mk, cast_add,
    cast_one, div_mul_cancel]
  cases n with
  | zero =>
    rw [coeff_zero_mul_X, coeff_zero_one]; norm_num
  | succ n =>
    have : n + 1 ≠ 0 := succ_ne_zero n
    rw [coeff_succ_mul_X, coeff_D, coeff_mk, coeff_one, cast_add, cast_one, div_mul_cancel,
      _root_.pow_succ, neg_one_mul, succ_eq_add_one, neg_add_self, if_neg this]
    rw [←cast_one, ←cast_add, cast_ne_zero]
    exact this
  · rw [←cast_one, ←cast_add, cast_ne_zero]
    exact succ_ne_zero n
  · rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero

@[simp]
theorem const_exp_sub_one : constantCoeff R (exp - 1) = 0 :=
by
  rw [map_sub, constantCoeff_exp, constantCoeff_one, sub_self]

@[simp]
theorem d_log_comp_exp : D (logOneAdd ∘ (exp - 1 : R⟦X⟧)) = 1 :=
by
  rw [D_comp, D_logOneAdd, map_sub, D_one, sub_zero, D_exp]
  have : (1 + X : R⟦X⟧).comp (exp - 1) = exp
  · rw [add_comp, X_comp const_exp_sub_one, one_comp const_exp_sub_one, add_sub_cancel'_right]
  · nth_rw 2 [← this]
    rw [← mul_comp, PowerSeries.inv_mul_cancel, one_comp const_exp_sub_one]
    rw [map_add, constantCoeff_one, constantCoeff_X, add_zero]
    exact one_ne_zero

@[simp]
theorem log_exp : (logOneAdd ∘ (exp - 1 : R⟦X⟧) : R⟦X⟧) = X :=
by
  apply eq_of_D_eq_of_const_eq
  · rw [d_log_comp_exp, D_X]
  · rw [constantCoeff_comp, constantCoeff_X, constantCoeff_logOneAdd]
    exact const_exp_sub_one

@[simp]
theorem log_mul (f g : R⟦X⟧) (hf : constantCoeff R f = 0) (hg : constantCoeff R g = 0) :
  (logOneAdd ∘ ((1 + f) * (1 + g) - 1 : R⟦X⟧) : R⟦X⟧) = (logOneAdd ∘ f : R⟦X⟧) + (logOneAdd ∘ g : R⟦X⟧) :=
by
  have eq : constantCoeff R ((1 + f) * (1 + g) - 1) = 0 := by
    rw [map_sub, map_mul, map_add, map_add, hf, hg, map_one, add_zero, mul_one, sub_self]
  apply eq_of_D_eq_of_const_eq
  · rw [D_comp, map_sub, D_mul, map_add, map_add, map_add, D_one, D_comp, D_comp, zero_add,
      sub_zero, zero_add, mul_add, D_logOneAdd, add_comm]
    congr 1
    · rw [inv_comp, add_comp, one_comp eq, X_comp eq, add_comm, sub_add_cancel, inv_comp, add_comp,
        one_comp hf, X_comp hf, ← mul_assoc, PowerSeries.mul_inv_rev,
        mul_comm (1 + g)⁻¹, mul_assoc (1 + f)⁻¹, PowerSeries.inv_mul_cancel, mul_one]
      · rw [map_add, map_one, hg, add_zero]; exact one_ne_zero
      all_goals rw [map_add, map_one, constantCoeff_X, add_zero]; exact one_ne_zero
    · rw [inv_comp, add_comp, one_comp eq, X_comp eq, add_comm, sub_add_cancel, inv_comp, add_comp,
        one_comp hg, X_comp hg, ← mul_assoc, PowerSeries.mul_inv_rev, mul_assoc (1 + g)⁻¹,
        PowerSeries.inv_mul_cancel, mul_one]
      · rw [map_add, map_one, hf, add_zero]; exact one_ne_zero
      all_goals rw [map_add, map_one, constantCoeff_X, add_zero]; exact one_ne_zero
  · rw [constantCoeff_comp eq, map_add, constantCoeff_comp hf, constantCoeff_comp hg,
      constantCoeff_logOneAdd, add_zero]

@[simp]
theorem exp_log : (exp ∘ logOneAdd : R⟦X⟧) = (1 + X : R⟦X⟧) :=
by
  apply eq_of_D_eq_of_const_eq
  · rw [D_comp, map_add, D_one, zero_add, D_exp]
    apply eq_of_D_eq_of_const_eq
    · rw [D_mul, D_comp, D_exp, D_X, D_one, D_logOneAdd, D_inv, map_add, D_one, D_X, zero_add,
        mul_one, pow_two, mul_neg, ←mul_assoc, mul_comm, neg_add_self]
    · rw [D_X, map_one, D_logOneAdd, map_mul, constantCoeff_comp constantCoeff_logOneAdd,
        constantCoeff_inv, map_add, map_one, constantCoeff_X, add_zero, inv_one, mul_one,
        constantCoeff_exp]
  · rw [constantCoeff_comp constantCoeff_logOneAdd, constantCoeff_exp, map_add, constantCoeff_one,
      constantCoeff_X, add_zero]


--Polylogarithms



theorem constantCoeff_polylog_succ (n : ℕ) :
  constantCoeff R (polylog n.succ) = 0 :=
by
  rw [polylog, ← coeff_zero_eq_constantCoeff, coeff_mk, _root_.pow_succ,
    cast_zero, inv_zero, zero_mul]

theorem D_polylog_one : D (polylog 1) = (1 - X)⁻¹ :=
by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_sub, mul_one]
  · ext m
    cases m with
    | zero =>
      rw [map_sub, coeff_D, coeff_zero_mul_X, coeff_zero_eq_constantCoeff,
        sub_zero, cast_zero, zero_add, mul_one, map_one, polylog, coeff_mk,
        cast_one, pow_one, inv_one]
    | succ n => 
      rw [map_sub, coeff_succ_mul_X, coeff_one, polylog, coeff_D, coeff_D, coeff_mk,
        coeff_mk, pow_one, pow_one, cast_add, cast_add, cast_one, inv_mul_cancel,
        inv_mul_cancel, sub_self, if_neg (succ_ne_zero n)]
      · rw [←cast_succ, cast_ne_zero]
        exact succ_ne_zero n
      · rw [←cast_succ, cast_ne_zero]
        exact succ_ne_zero n.succ
  · rw [map_sub, map_one, constantCoeff_X, sub_zero]
    exact one_ne_zero



theorem X_mul_X_polylog_succ (d : ℕ) : X * D (polylog (d + 2)) = polylog (d + 1) :=
by
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff, constantCoeff_polylog_succ]
  | succ n => 
    rw [coeff_succ_X_mul, polylog, polylog, coeff_mk, coeff_D, coeff_mk, ←cast_succ,
      succ_eq_add_one, _root_.pow_succ', mul_assoc, inv_mul_cancel,
      mul_one]
    rw [cast_ne_zero]
    exact succ_ne_zero n





