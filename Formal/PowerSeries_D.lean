/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic
import Formal.Truncation_lemmas
import Formal.PowerSeries_comp
import Formal.Derivation_lemma


/-!
# Definitions

In this file we define an operation `D` (differentiation)
on formal power series in one variable (over an arbitrary commutative semi-ring).

We prove the product rule and the chain rule for differentiation of formal power series.

Under suitable assumptions, we prove that two power series are equal if their derivatives
are equal and their constant terms are equal. This gives us a simple tool for proving
power series identities. For example, one can easily prove the power series identity
`exp ( log (1+X)) = 1+X` by differentiating twice. Several examples of this kind of
identity are contained in the accomanying file "Examples.lean".


## Main results

- `PowerSeries.D_mul`  : the product rule (Leibniz' rule) for differentiating.
- `PowerSeries.D_comp` : the chain rule for differentiating power series.

## Notation

- `PowerSeries.D R`     : the formal derivative `R⟦X⟧ → R⟦X⟧`
-/




namespace PowerSeries

open Polynomial Nat

section CommutativeSemiring
variable {R : Type u} [CommSemiring R]


/-- The formal derivative of a power series in one variable.
This is defined here as a function, but will be packaged as a
deribation `D` on `R⟦X⟧`.-/
noncomputable def D_fun (f : R⟦X⟧) : R⟦X⟧ :=
  mk λ n ↦ coeff R (n + 1) f * (n + 1)

theorem coeff_D_fun (f : R⟦X⟧) (n : ℕ) :
  coeff R n f.D_fun = coeff R (n + 1) f * (n + 1) :=
by
  rw [D_fun, coeff_mk]

theorem D_fun_coe (f : R[X]) :
  (f : R⟦X⟧).D_fun = derivative f :=
by
  ext
  rw [coeff_D_fun, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_derivative]

theorem D_fun_add (f g : R⟦X⟧) : D_fun (f + g) = D_fun f + D_fun g :=
by
  ext
  rw [coeff_D_fun, map_add, map_add, coeff_D_fun, coeff_D_fun, add_mul]

theorem D_fun_C (r : R) : D_fun (C R r) = 0 :=
by
  ext n
  rw [coeff_D_fun, coeff_C]
  split_ifs with h
  · cases succ_ne_zero n h
  · rw [zero_mul, map_zero]

theorem trunc_D_fun (f : R⟦X⟧) (n : ℕ) :
  (trunc n f.D_fun : R⟦X⟧) = D_fun ↑(trunc (n + 1) f) :=
by
  ext d
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_D_fun, coeff_D_fun, Polynomial.coeff_coe, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [coeff_D_fun, Polynomial.coeff_coe, coeff_trunc, if_neg this, zero_mul]

--A special case of the next theorem, used in its proof.
private theorem D_fun_coe_mul_coe (f g : R[X]) :
  D_fun (f * g : R⟦X⟧) = f * D_fun (g : R⟦X⟧) + g * D_fun (f : R⟦X⟧) :=
by
  rw [←Polynomial.coe_mul, D_fun_coe, derivative_mul,
    D_fun_coe, D_fun_coe, add_comm, mul_comm _ g,
    ←Polynomial.coe_mul, ←Polynomial.coe_mul, Polynomial.coe_add]

/-- Leibniz rule for formal power series.-/
theorem D_fun_mul (f g : R⟦X⟧) :
  D_fun (f * g) = f • g.D_fun + g • f.D_fun :=
by
  ext n
  have h₀ : n + 1 < n + 1 + 1 := lt_succ_self (n + 1)
  have h₁ : n < n + 1 := lt_succ_self n
  have h₂ : n < n + 1 + 1 := lt_of_lt_of_le h₁ (le_of_lt h₀)
  rw [coeff_D_fun, map_add, coeff_mul_cts f g h₀ h₀,
    smul_eq_mul, smul_eq_mul,
    coeff_mul_cts g f.D_fun h₂ h₁,
    coeff_mul_cts f g.D_fun h₂ h₁, trunc_D_fun, trunc_D_fun,
    ← map_add, ← D_fun_coe_mul_coe, coeff_D_fun]

theorem D_fun_one : D_fun (1 : R⟦X⟧) = 0 :=
by
  rw [←map_one (C R), D_fun_C (1 : R)]

theorem D_fun_smul (r : R) (f : R⟦X⟧) : D_fun (r • f) = r • D_fun f :=
by
  rw [smul_eq_C_mul, smul_eq_C_mul, D_fun_mul,
    D_fun_C, smul_zero, add_zero, smul_eq_mul]

/--The formal derivative of a formal power series.-/
noncomputable def D (R : Type u) [CommSemiring R]: Derivation R R⟦X⟧ R⟦X⟧
where
  toFun             := D_fun
  map_add'          := D_fun_add
  map_smul'         := D_fun_smul
  map_one_eq_zero'  := D_fun_one
  leibniz'          := D_fun_mul

/-this can be proved by `simp`.-/
theorem D_mul : D R (f * g) = f * D R g + g * D R f :=
by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem D_one : D R 1 = 0 := D_fun_one

@[simp]
theorem D_C (r : R) : D R (C R r : R⟦X⟧) = 0 :=
  D_fun_C r

@[simp]
theorem coeff_D (f : R⟦X⟧) (n : ℕ) : coeff R n (D R f) = coeff R (n + 1) f * (n + 1) :=
  coeff_D_fun f n

theorem D_coe (f : R[X]) : D R f = derivative f :=
  D_fun_coe f

@[simp]
theorem D_X : D R (X : R⟦X⟧) = 1 :=
by
  ext
  rw [coeff_D, coeff_one, coeff_X, boole_mul]
  simp_rw [add_left_eq_self]
  split_ifs with h
  · rw [h, cast_zero, zero_add]
  · rfl

theorem trunc_D (f : R⟦X⟧) (n : ℕ) :
  trunc n (D R f) = derivative (trunc (n + 1) f) :=
by
  apply coe_inj.mp
  rw [←D_coe]
  apply trunc_D_fun

theorem trunc_D' (f : R⟦X⟧) (n : ℕ) :
  trunc (n-1) (D R f) = derivative (trunc n f) :=
by
  cases n with
  | zero =>
    simp only [zero_eq, ge_iff_le, tsub_eq_zero_of_le]
    rfl
  | succ n =>
    rw [Nat.succ_sub_one, trunc_D]



theorem D_coe_comp (f : R[X]) (g : R⟦X⟧) : D R (f.eval₂ (C R) g)
  = (derivative f).eval₂ (C R) g * D R g :=
  Derivation.polynomial_eval₂ (D R) f g



/-- The "chain rule" for formal power series in one variable:
  `D (f ∘ g) = (D f) ∘ g * D g`.
If `g` has non-nilpotent constant term then the equation
is trivially true, with both sides equal to zero.
-/
@[simp]
theorem D_comp (f g : R⟦X⟧) : D R (f ∘ g) = (D R f ∘ g : R⟦X⟧) * D R g :=
by
  by_cases IsNilpotent (constantCoeff R g)
  · by_cases hh : h.choose > 0 
    · ext n
      rw [coeff_D, coeff_comp_eq h, ←coeff_D, D_coe_comp, coeff_mul,
        coeff_mul, Finset.sum_congr rfl]
      intro ⟨x,y⟩ hxy
      have : x ≤ n :=
        Finset.Nat.antidiagonal.fst_le hxy
      rw [←trunc_D', coeff_comp_cts h.choose_spec]
      dsimp
      trans h.choose * (n+1)
      · apply mul_le_mul (le_rfl)
        apply succ_le_succ this
        apply Nat.zero_le
        apply Nat.zero_le
      · apply Nat.le_pred_of_lt
        apply Nat.mul_lt_mul_of_pos_left
        · apply Nat.lt_succ_self
        · exact hh
    · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at hh 
      have := h.choose_spec
      rw [hh, _root_.pow_zero] at this
      suffices : (C R 1) * D R ( f ∘ g ) = (C R 1) * (D R f).comp g * D R g
      · have that : C R 1 = 1 := rfl
        rwa [that, one_mul, one_mul] at this
      · rw [this, map_zero, zero_mul, zero_mul, zero_mul]
  · rw [comp_eq_zero h, comp_eq_zero h, zero_mul, map_zero]



end CommutativeSemiring




/-In the next lemma, we use `smul_right_inj`, which requires not only `no_smul_divisors ℕ R`, but
also cancellation of addition in `R`. For this reason, the next lemma is stated in the case that `R`
is a `comm_ring`.-/
/-- If `f` and `g` have the same constant term and derivative, then they are equal.-/
theorem eq_of_D_eq_of_const_eq
  {R : Type u} [CommRing R] [NoZeroSMulDivisors ℕ R]
  (f g : PowerSeries R) :
  D R f = D R g → constantCoeff R f = constantCoeff R g → f = g :=
by
  intro h1 h2
  ext n
  cases n with
  | zero => 
    rw [coeff_zero_eq_constantCoeff, h2]
  | succ n => 
    have equ : coeff R n (D (R := R) f) = coeff R n (D (R := R) g) := by rw [h1]
    rwa [coeff_D, coeff_D, ←cast_succ, mul_comm, ←nsmul_eq_mul,
      mul_comm, ←nsmul_eq_mul, smul_right_inj] at equ
    exact succ_ne_zero n


@[simp]
theorem D_inv {R : Type u} [CommRing R] (f : R⟦X⟧ˣ) :
  D R f.inv = -f.inv ^ 2 * D R f :=
by
  apply Derivation.leibniz_of_mul_eq_one
  simp only [Units.inv_eq_val_inv, Units.inv_mul]


@[simp]
theorem D_invOf {R : Type u} [CommRing R] (f : R⟦X⟧) [Invertible f] :
  D R (⅟ f) = - (⅟ f) ^ 2 * D R f :=
by
  rw [Derivation.leibniz_invOf, smul_eq_mul]

/-
The following theorem is stated only in the case that
`R` is a field. This is because there is currently no
instance of `Inv R⟦X⟧` for more general base rings `R`.

In the more general case, use `D_inv` or `D_invOf` instead.
-/
@[simp]
theorem D_inv' {R : Type u} [Field R] (f : R⟦X⟧) :
  D R f⁻¹ = -f⁻¹ ^ 2 * D R f :=
by
  by_cases constantCoeff R f = 0
  · suffices : f⁻¹ = 0
    . rw [this, pow_two, zero_mul, neg_zero, zero_mul, map_zero]
    · rwa [MvPowerSeries.inv_eq_zero]
  · apply Derivation.leibniz_of_mul_eq_one
    exact PowerSeries.inv_mul_cancel (h := h)



end PowerSeries

