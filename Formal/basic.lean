/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib
-- import Mathlib.Tactic
-- import Mathlib.RingTheory.PowerSeries.Basic
-- import Mathlib.RingTheory.Derivation.Basic
-- import Mathlib.Algebra.Algebra.Basic


/-!
# Foos and Bars

In this file we define operations `D` (differentiation) and `comp` (composition)
on formal power series in one variable (over an arbitrary commutative semi-ring).
The derivative `D f` is defined for all power series `f`. The composition `f ∘ g` only makes
sense where some power of the constant term of `g` is zero.

We prove the product rule and the chain rule for differentiation of formal power series.

Under suitable assumptions, we prove that two power series are equal if their derivatives
are equal and their constant terms are equal. This gives us a simple tool for proving
power series identities. For example, one can easily prove the power series identity
`exp ( log (1+X)) = 1+X` by differentiating twice. Several examples of this kind of
identity are contained in the accomanying file "Examples.lean".


For a formal power series `f = ∑ cₙ*X^n`

## Main results

- `PowerSeries.D_mul`  : the product rule (Leibniz' rule) for differentiating.
- `PowerSeries.D_comp` : the chain rule for differentiating power series.

## Notation

- `PowerSeries.D`      : the derivative `PowerSeries R → PowerSeries R`
- `PowerSeries.comp`   : the composition operation `PowerSeries R → PowerSeries R → PowerSeries R`.

-/




set_option profiler true
/-
TODO :
prove that composition of power series is associative.
split off a "classical" section.
-/


open PowerSeries Nat BigOperators
open scoped Classical

section CommutativeSemiring

variable {R : Type} [CommSemiring R] --[DecidableEq R]

local notation "pow"    => PowerSeries R
local notation "poly"   => Polynomial R
local notation "coeff"  => coeff R

variable (f : Polynomial R)

/-- If f is a polynomial over `R`
  and d is a derivation on an `R`-algebra then

    `d(f(g)) = f.derivarive (g) * g(d)`.

  TODO : prove in the following alternative way:
  Show that both sides of the equation are derivations
  on the polynomial ring. 
  by `mv_polynomial.derivation_ext` they are equal iff they
  agree in the case f=X. This case is easier as it does
  not involve messing around with finite sums.
-/
theorem Derivation.polynomial_eval₂ (A : Type) [CommSemiring A] [Algebra R A] (M : Type)
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] (d : Derivation R A M)
  (f : poly) (g : A) :
  d (f.eval₂ (algebraMap R A) g)
  = (Polynomial.eval₂ (algebraMap R A) g (@Polynomial.derivative R _ f)) • d g :=
by
  rw [Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_range_succ', Derivation.leibniz,
    Derivation.leibniz_pow, Derivation.map_algebraMap, zero_nsmul, smul_zero, smul_zero, zero_add,
    add_zero]
  by_cases f.natDegree = 0
  · rw [h, Finset.sum_range_zero, Polynomial.derivative_of_natDegree_zero h, Polynomial.eval₂_zero,
      zero_smul]
  · have : (@Polynomial.derivative R _ f).natDegree < f.natDegree := Polynomial.natDegree_derivative_lt h
    rw [Polynomial.eval₂_eq_sum_range' (algebraMap R A) this, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro n _
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap, smul_zero, add_zero,
      add_tsub_cancel_right, Polynomial.coeff_derivative, map_mul, IsScalarTower.algebraMap_smul,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, one_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul,
      smul_assoc, smul_assoc, ←cast_succ, ← nsmul_eq_smul_cast]




namespace PowerSeries

theorem coeff_cts (f : pow) {n m : ℕ} (h : n < m) : coeff n f = coeff n (trunc m f) :=
by
  rw [Polynomial.coeff_coe, coeff_trunc, if_pos h]

/-- The `n`-th coefficient of a`f*g` may be calculated 
from the truncations of `f` and `g`.-/
theorem coeff_mul_cts (f g : pow) {n a b : ℕ} (ha : n < a) (hb : n < b) :
  coeff n (f * g) = coeff n (trunc a f * trunc b g) :=
by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr
  · rfl
  · intro ⟨x,y⟩ hxy
    have hx : x ≤ n := Finset.Nat.antidiagonal.fst_le hxy
    have hy : y ≤ n := Finset.Nat.antidiagonal.snd_le hxy
    congr 1 <;> apply coeff_cts
    · exact lt_of_le_of_lt hx ha
    · exact lt_of_le_of_lt hy hb

/-- The formal derivative of a power series in one variable.-/
noncomputable def derivative (f : pow) : pow :=
  mk λ n ↦ coeff (n + 1) f * (n + 1)

theorem coeff_derivative (f : pow) (n : ℕ) :
  coeff n f.derivative = coeff (n + 1) f * (n + 1) :=
by
  rw [derivative, coeff_mk]

theorem derivative_coe (f : poly) :
  (f : pow).derivative = @Polynomial.derivative R _ f :=
by
  ext
  rw [coeff_derivative, Polynomial.coeff_coe, Polynomial.coeff_coe,
    Polynomial.coeff_derivative]

theorem derivative_add (f g : pow) : derivative (f + g) = derivative f + derivative g :=
by
  ext
  rw [coeff_derivative, map_add, map_add, coeff_derivative, coeff_derivative, add_mul]

theorem derivative_C (r : R) : derivative (C R r) = 0 :=
by
  ext n
  rw [coeff_derivative, coeff_C]
  split_ifs with h
  · cases succ_ne_zero n h
  · rw [zero_mul, map_zero]

theorem trunc_deriv (f : pow) (n : ℕ) :
  (trunc n f.derivative : pow) = derivative ↑(trunc (n + 1) f) :=
by
  ext d
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivative, coeff_derivative, Polynomial.coeff_coe, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [coeff_derivative, Polynomial.coeff_coe, coeff_trunc, if_neg this, zero_mul]

--A special case of the next theorem, used in its proof.
private theorem derivative_coe_mul_coe (f g : poly) :
  derivative (f * g : pow) = f * derivative (g : pow) + g * derivative (f : pow) :=
by
  rw [←Polynomial.coe_mul, derivative_coe, Polynomial.derivative_mul,
    derivative_coe, derivative_coe, add_comm, mul_comm _ g,
    ←Polynomial.coe_mul, ←Polynomial.coe_mul, Polynomial.coe_add]

/-- Leibniz rule for formal power series.-/
theorem derivative_mul (f g : pow) : derivative (f * g) = f • g.derivative + g • f.derivative :=
by
  ext n
  have h0 : n + 1 < n + 1 + 1 := lt_succ_self (n + 1)
  have h1 : n < n + 1 := lt_succ_self n
  have h2 : n < n + 1 + 1 := lt_of_lt_of_le h1 (le_of_lt h0)
  rw [coeff_derivative, map_add, coeff_mul_cts f g h0 h0,
    smul_eq_mul, smul_eq_mul,
    coeff_mul_cts g f.derivative h2 h1,
    coeff_mul_cts f g.derivative h2 h1, trunc_deriv, trunc_deriv,
    ← map_add, ← derivative_coe_mul_coe, coeff_derivative]

theorem derivative_one : derivative (1 : pow) = 0 :=
by
  rw [←map_one (C R), derivative_C (1 : R)]

theorem derivative_smul (r : R) (f : pow) : derivative (r • f) = r • derivative f :=
by
  rw [smul_eq_C_mul, smul_eq_C_mul, derivative_mul,
    derivative_C, smul_zero, add_zero, smul_eq_mul]


/--The formal derivative of a formal power series.-/
noncomputable def D : Derivation R pow pow
where
  toFun             := derivative
  map_add'          := derivative_add
  map_smul'         := derivative_smul
  map_one_eq_zero'  := derivative_one
  leibniz'          := derivative_mul

local notation "D" => @D R _

@[simp]
theorem D_mul (f g : pow) : D (f * g) = f * D g + g * D f :=
  derivative_mul f g

@[simp]
theorem D_one : D (1 : pow) = 0 :=
  derivative_one

@[simp]
theorem coeff_D (f : pow) (n : ℕ) : coeff n (D f) = coeff (n + 1) f * (n + 1) :=
  coeff_derivative f n

@[simp]
theorem D_coe (f : poly) : (f : pow).derivative = @Polynomial.derivative R _ f :=
  derivative_coe f

@[simp]
theorem D_X : D (X : pow) = 1 :=
by
  ext
  rw [coeff_D, coeff_one, coeff_X, boole_mul]
  simp_rw [add_left_eq_self]
  split_ifs with h
  · rw [h, cast_zero, zero_add]
  · rfl

theorem trunc_D (f : pow) (n : ℕ) :
  trunc n (D f) = @Polynomial.derivative R _ (trunc (n + 1) f) :=
by
  apply Polynomial.coe_inj.1
  rw [←D_coe]
  have := trunc_deriv f n
  rw [derivative_coe] at this
  exact Polynomial.coe_inj.1 this

theorem trunc_succ (f : pow) (n : ℕ) :
  trunc n.succ f = trunc n f + @Polynomial.monomial R _ n (coeff n f) :=
by
  rw [trunc, Ico_zero_eq_range, Finset.sum_range_succ, trunc, Ico_zero_eq_range]

theorem D_coe_comp (f : poly) (g : pow) : D (f.eval₂ (C R) g)
  = (@Polynomial.derivative R _ f).eval₂ (C R) g * D g :=
  Derivation.polynomial_eval₂ pow pow D f g



/--Composition of power series-/
noncomputable def comp : pow → pow → pow := λ f g ↦
  if constantCoeff R g = 0
  then mk λ n ↦ coeff n ((trunc n.succ f).eval₂ (C R) g)
  else 0

theorem comp_eq {f g : pow} (hg : constantCoeff R g = 0) :
    f.comp g = mk λ n ↦ coeff n ((trunc n.succ f).eval₂ (C R) g) :=
by
  rw [comp, if_pos hg]

theorem comp_eq_zero {f g : pow} (hg : constantCoeff R g ≠ 0) : f.comp g = 0 :=
by
  rw [comp, if_neg hg]

theorem coeff_comp_eq' (f g : pow) (n : ℕ) :
  coeff n (f.comp g) =
  if constantCoeff R g = 0
  then coeff n ((trunc n.succ f).eval₂ (C R) g)
  else 0 :=
by
  rw [comp]
  split_ifs with h
  · rw [if_pos h, coeff_mk]
  · rw [if_neg h, map_zero]

theorem coeff_comp_eq {f g : pow} {n : ℕ} (hg : constantCoeff R g = 0) :
  coeff n (f.comp g) = coeff n ((trunc n.succ f).eval₂ (C R) g) :=
by rw [coeff_comp_eq', if_pos hg]

theorem coeff_comp_eq_zero {f g : pow} {n : ℕ} (hg : ¬constantCoeff R g = 0) :
  coeff n (f.comp g) = 0 :=
by rw [coeff_comp_eq', if_neg hg]

private theorem coeff_pow_eq_zero {g : pow} (hg : constantCoeff R g = 0)
  {n a : ℕ} (ha : n < a) :
  coeff n (g ^ a) = 0 :=
by
  apply coeff_of_lt_order
  rw [← X_dvd_iff] at hg 
  have : X ^ a ∣ g ^ a := pow_dvd_pow_of_dvd hg a
  rw [order_eq_multiplicity_X]
  apply lt_of_lt_of_le _ (multiplicity.le_multiplicity_of_pow_dvd this)
  rwa [PartENat.coe_lt_coe]


/-- (Technical Lemma)
The if `n<a` then the `n`-th coefficient of `f.comp g` may be
calculated using the `a`-th truncation of `f`.
-/
theorem coeff_comp_cts {f g : pow} (h : constantCoeff R g = 0)
  {n a : ℕ} (ha: n < a) :
  coeff n (f.comp g) = coeff n ((trunc a f).eval₂ (C R) g) :=
by
  induction ha with
  | refl =>
    rw [coeff_comp_eq h]
  | step ha ih => 
    rw [trunc_succ, Polynomial.eval₂_add, map_add, ih,
      Polynomial.eval₂_monomial, coeff_C_mul,
      coeff_pow_eq_zero h ha, mul_zero, add_zero]

/-- The "chain rule" for formal power series in one variable:
  `D (f.comp g) = (D f).comp g * D g`.
If `g` has non-zero constant term then the equation
is trivially true, with both sides defined to be zero.
-/
@[simp]
theorem D_comp (f g : pow) : D (f.comp g) = (D f).comp g * D g :=
by
  by_cases constantCoeff R g = 0
  · ext n
    rw [coeff_D, coeff_comp_eq h, ←coeff_D, D_coe_comp, coeff_mul,
      coeff_mul, Finset.sum_congr rfl]
    intro ⟨x,y⟩ hxy
    have : x < n + 1 :=
      lt_succ_of_le (Finset.Nat.antidiagonal.fst_le hxy)
    rw [coeff_comp_cts h this, ← trunc_D]
  · rw [comp_eq_zero h, comp_eq_zero h, zero_mul, map_zero]

@[simp]
theorem D_C (r : R) : D (C R r : pow) = 0 :=
  derivative_C r

@[simp]
theorem D_smul (a : R) (f : pow) : D (a • f) = a • D f :=
by
  rw [smul_eq_C_mul, smul_eq_C_mul, D_mul, D_C, mul_zero, add_zero]

/-
The following are a few more results concering composition of
power series.
We show that composition is associative,
`X` is a 2-sided identity.
a.rescale f = f.comp (a*X)
-/
theorem natDegree_trunc_lt (f : pow) (n : ℕ) : (trunc (n + 1) f).natDegree < n + 1 :=
by
  rw [lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_trunc]
  split_ifs with h
  · rw [lt_succ, ←not_lt] at h
    contradiction
  · rfl

theorem constantCoeff_comp {f g : pow} (h : constantCoeff R g = 0) :
  constantCoeff R (f.comp g) = constantCoeff R f :=
by
  have : (trunc 1 f).natDegree < 1 := natDegree_trunc_lt f 0
  rw [← coeff_zero_eq_constantCoeff, coeff_comp_eq h,
    Polynomial.eval₂_eq_sum_range' (C R) this, Finset.sum_range_one,
    _root_.pow_zero, mul_one, coeff_zero_C, coeff_trunc, if_pos zero_lt_one]


@[simp]
theorem trunc_trunc (f : pow) {n : ℕ} : trunc n ↑(trunc n f) = trunc n f :=
by
  ext m
  rw [coeff_trunc, coeff_trunc, Polynomial.coeff_coe]
  split_ifs with h
  · rw [coeff_trunc, if_pos h]
  · rfl

@[simp]
theorem trunc_trunc_mul_trunc (f g : pow) (n : ℕ) :
  trunc n (trunc n f * trunc n g : pow) = trunc n (f * g) :=
by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, Finset.sum_congr]
    rfl
    rintro ⟨a, b⟩ hab
    have ha := Finset.Nat.antidiagonal.fst_le hab
    have hb := Finset.Nat.antidiagonal.snd_le hab
    dsimp at ha hb ⊢
    have ha : a < n := lt_of_le_of_lt ha h
    have hb : b < n := lt_of_le_of_lt hb h
    rw [Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_trunc, coeff_trunc, if_pos ha, if_pos hb]
  · rfl


theorem trunc_coe_eq_self {f : poly} {n : ℕ} (hn : n > f.natDegree) : trunc n (f : pow) = f :=
by
  induction hn with
  | refl => 
    ext a
    rw [coeff_trunc]
    split_ifs with h
    · exact Polynomial.coeff_coe _ _
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      rwa [not_lt, succ_le_iff] at h 
  | step hm ih =>
    · rw [trunc_succ, ih, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt hm, map_zero, add_zero]

theorem coe_comp {f : poly} {g : pow} (hg : constantCoeff R g = 0) :
  (f : pow).comp g = f.eval₂ (C R) g :=
by
  ext n
  by_cases n < f.natDegree + 1
  rw [coeff_comp_cts hg h, trunc_coe_eq_self]
  exact lt_succ_self _
  rw [coeff_comp_eq hg, trunc_coe_eq_self]
  rw [succ_eq_add_one]
  apply lt_succ_of_le
  apply le_of_lt
  apply lt_of_succ_le
  apply le_of_not_gt h


theorem trunc_of_trunc_comp {f g : pow} {n : ℕ} (hg : constantCoeff R g = 0) :
  trunc n ((trunc n f : pow).comp g) = trunc n (f.comp g) :=
by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_comp_cts hg h, coeff_comp_cts hg h, trunc_trunc]
  · rfl

@[simp]
theorem mul_comp (f g h : pow) :
  (f * g).comp h = f.comp h * g.comp h :=
by
  by_cases hh : constantCoeff R h = 0
  · ext n
    let T : pow → poly := trunc (n + 1)
    have hT : T = trunc (n + 1) := by rfl
    have hn : n < n + 1 := lt_succ_self n
    calc
      coeff n ((f * g).comp h) = coeff n ((T (f * g) : pow).comp h) := by
        rw [coeff_comp_cts hh hn, coeff_comp_cts hh hn, trunc_trunc]
      _ = coeff n ((T (T f * T g : pow) : pow).comp h) := by rw [hT, trunc_trunc_mul_trunc]
      _ = coeff n ((T f * T g : pow).comp h) := by
        rw [coeff_comp_cts hh hn, coeff_comp_cts hh hn, trunc_trunc]
      _ = coeff n ((T f : pow).comp h * (T g : pow).comp h) := by
        rw [← Polynomial.coe_mul, coe_comp hh, coe_comp hh, coe_comp hh, Polynomial.eval₂_mul]
      _ = coeff n (T ((T f : pow).comp h) * T ((T g : pow).comp h) : pow) := by
        rw [coeff_mul_cts _ _ hn hn]
      _ = coeff n (T (f.comp h) * T (g.comp h) : pow) := by
        rw [hT, trunc_of_trunc_comp hh, trunc_of_trunc_comp hh]
      _ = coeff n (f.comp h * g.comp h) := by rw [←(coeff_mul_cts _ _ hn hn)]
  · rw [comp_eq_zero hh, comp_eq_zero hh, MulZeroClass.zero_mul]


@[simp]
theorem add_comp (f g h : pow) : (f + g).comp h = f.comp h + g.comp h :=
by
  by_cases hh : constantCoeff R h = 0
  · ext
    rw [coeff_comp_eq hh, trunc_add, Polynomial.eval₂_add, map_add, map_add,
      coeff_comp_eq hh, coeff_comp_eq hh]
  · rw [comp_eq_zero hh, comp_eq_zero hh, comp_eq_zero hh, add_zero]

@[simp]
theorem one_comp {f : pow} (hf : constantCoeff R f = 0) : (1 : pow).comp f = 1 :=
by
  ext
  rw [coeff_comp_eq hf, succ_eq_add_one, trunc_one, Polynomial.eval₂_one]


@[simp]
theorem comp_zero (f : pow) : f.comp 0 = C R (constantCoeff R f) :=
by
  ext n
  have : constantCoeff R (0 : pow) = 0 := map_zero _
  rw [coeff_comp_eq this, Polynomial.eval₂_at_zero, coeff_trunc, coeff_zero_eq_constantCoeff,
    coeff_C]
  split_ifs with h₁ h₂
  · rw [h₁, coeff_zero_eq_constantCoeff, constantCoeff_C]
  · cases h₂ (zero_lt_succ n)
  · rw [coeff_C, if_neg h₁]


/-NOTE: `instance : has_inv power_series R` is currently only defined
when `R` is a field.  -/
@[simp]
theorem inv_comp {R : Type} [Field R] (f g : PowerSeries R) (hf : constantCoeff R f ≠ 0) :
  f⁻¹.comp g = (f.comp g)⁻¹ :=
by
  by_cases constantCoeff R g = 0
  · symm
    rw [MvPowerSeries.inv_eq_iff_mul_eq_one, ← mul_comp, PowerSeries.inv_mul_cancel]
    exact one_comp h
    exact hf
    suffices : constantCoeff R (f.comp g) ≠ 0
    exact this
    rwa [constantCoeff_comp h]
  rw [comp]
  dsimp
  split_ifs
  · contradiction
  · rw [comp, if_neg h, PowerSeries.zero_inv]




theorem Polynomial.eval₂_X_eq_coe (f : poly) : f.eval₂ (C R) X = ↑f :=
by
  nth_rw 2 [(@Polynomial.eval₂_C_X R _ f).symm]
  rw [←Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, map_sum]
  apply Finset.sum_congr
  · rfl
  · intro x _
    rw [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]





@[simp]
theorem comp_X (f : pow) : f.comp X = f :=
by
  ext n
  rw [coeff_comp_eq (@constantCoeff_X R _),
    Polynomial.eval₂_X_eq_coe, ← coeff_cts]
  exact lt_succ_self n

@[simp]
theorem trunc_X {n : ℕ} : trunc (n + 2) X = (Polynomial.X : poly) :=
by
  ext d
  rw [coeff_trunc]
  rw [coeff_X]
  split_ifs with h1 h2
  · rw [h2, Polynomial.coeff_X_one]
  · rw [Polynomial.coeff_X_of_ne_one h2]
  · have : d ≠ 1 := by linarith [h1]
    rw [Polynomial.coeff_X_of_ne_one this]

@[simp]
theorem X_comp {f : pow} (h : constantCoeff R f = 0) : X.comp f = f :=
by
  ext n
  rw [coeff_comp_cts h (lt_add_of_pos_right n (succ_pos 1)),
    trunc_X, Polynomial.eval₂_X]



-- TODO:
-- # ASK John about the best way of dealing with a finite sum with only one non-zero term.
-- lemma rescale_eq_comp_mul_X (f : pow) (r : R) :
--   rescale r f = f.comp (↑r * X) :=
-- begin
--   have : constantCoeff R (↑r * X) = 0,
--   {
--     simp only [coeff_zero_eq_constantCoeff,
--       map_mul, constantCoeff_X, mul_zero],
--   },
--   ext,
--   rw [coeff_rescale, coeff_comp_eq this,
--     polynomial.eval₂_eq_sum_range' (C R) (natDegree_trunc_lt f n),
--     map_sum],
--   simp_rw [mul_pow, ← mul_assoc],
--   sorry,
-- end
-- @[simp]
-- lemma D_rescale (f : pow) ( r : R ):
--   D (rescale r f) = ↑r * rescale r (D f) :=
-- begin
--   rw [rescale_eq_comp_mul_X, D_comp, rescale_eq_comp_mul_X],
--   have : ↑r = C R r := by refl,
--   rw this,
--   rw C_eq_algebra_map,
--   simp only [D_X, smul_eq_mul, derivation.leibniz, mul_one, 
--     derivation.map_algebra_map, mul_zero, add_zero],
--   ring,
-- end
-- TODO : fill this in.
-- lemma comp_invertible_iff {f : pow} (h1 : coeff 0 f = 0) (h2 : is_unit (coeff 1 f)):
--   (∃ g : pow , f.comp g = X) :=
--   sorry

end PowerSeries

end CommutativeSemiring

open PowerSeries

/-In the next lemma, we use `smul_right_inj`, which requires not only `no_smul_divisors ℕ R`, but
also cancellation of addition in `R`. For this reason, the next lemma is stated in the case that `R`
is a `comm_ring`.-/
/-- If `f` and `g` have the same constant term and derivative, then they are equal.-/
theorem PowerSeries.eq_of_D_eq_of_const_eq
  {R : Type} [CommRing R] [NoZeroSMulDivisors ℕ R]
  (f g : PowerSeries R) :
  @D R _ f = @D R _ g → constantCoeff R f = constantCoeff R g → f = g :=
by
  intro h1 h2
  ext n
  cases n with
  | zero => 
    rw [coeff_zero_eq_constantCoeff]
    exact h2
  | succ n => 
    have eq : coeff R n (@D R _ f) = coeff R n (@D R _ g) := by rw [h1]
    rwa [coeff_D, coeff_D, ←cast_succ, mul_comm, ←nsmul_eq_mul,
      mul_comm, ←nsmul_eq_mul, smul_right_inj] at eq
    exact succ_ne_zero n


@[simp]
theorem PowerSeries.D_inv {R : Type} [Field R] (f : PowerSeries R) :
  @D R _ f⁻¹ = -f⁻¹ ^ 2 * @D R _ f :=
by
  by_cases constantCoeff R f = 0
  · suffices : f⁻¹ = 0
    rw [this, pow_two, MulZeroClass.zero_mul, neg_zero, MulZeroClass.zero_mul, map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  · refine' Derivation.leibniz_of_mul_eq_one _ (_ : f⁻¹ * f = 1)
    exact PowerSeries.inv_mul_cancel _ h



