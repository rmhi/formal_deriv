/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib   -- designed to be compatible with the whole of mathlib.
--import Mathlib.Tactic --not currently needed
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic
--import Mathlib.Algebra.Algebra.Basic --not currently needed


/-!
# Definitions

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

- `PowerSeries.D`     : the derivative `PowerSeries R → PowerSeries R`
- `PowerSeries.comp`  : the composition operation `PowerSeries R → PowerSeries R → PowerSeries R`.
                        `f.comp g` is also overloaded as `(f ∘ g : pow)`, or sometimes just `f ∘ g`.
-/



--set_option profiler true
/-
TODO :
prove that composition of power series is associative.
split off a "classical" section.
-/


open PowerSeries Nat BigOperators Polynomial
open scoped Classical

section CommutativeSemiring

variable {R : Type} [CommSemiring R] --[DecidableEq R]

--local notation "pow"    => PowerSeries R
--local notation "poly"   => Polynomial R
local notation "coeff"  => PowerSeries.coeff R

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




namespace PowerSeries

scoped notation:9000 R "⟦X⟧" => PowerSeries R



theorem coeff_cts (f : R⟦X⟧) {n m : ℕ} (h : n < m) : coeff n f = coeff n (trunc m f) :=
by
  rw [Polynomial.coeff_coe, coeff_trunc, if_pos h]

/-- The `n`-th coefficient of a`f*g` may be calculated 
from the truncations of `f` and `g`.-/
theorem coeff_mul_cts (f g : R⟦X⟧) {n a b : ℕ} (ha : n < a) (hb : n < b) :
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
noncomputable def derivative_fun (f : R⟦X⟧) : R⟦X⟧ :=
  mk λ n ↦ coeff (n + 1) f * (n + 1)

theorem coeff_derivative (f : R⟦X⟧) (n : ℕ) :
  coeff n f.derivative_fun = coeff (n + 1) f * (n + 1) :=
by
  rw [derivative_fun, coeff_mk]

theorem derivative_coe (f : R[X]) :
  (f : R⟦X⟧).derivative_fun = derivative (R := R) f :=
by
  ext
  rw [coeff_derivative, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_derivative]

theorem derivative_add (f g : R⟦X⟧) : derivative_fun (f + g) = derivative_fun f + derivative_fun g :=
by
  ext
  rw [coeff_derivative, map_add, map_add, coeff_derivative, coeff_derivative, add_mul]

theorem derivative_C (r : R) : derivative_fun (C R r) = 0 :=
by
  ext n
  rw [coeff_derivative, coeff_C]
  split_ifs with h
  · cases succ_ne_zero n h
  · rw [zero_mul, map_zero]

theorem trunc_derivative (f : R⟦X⟧) (n : ℕ) :
  (trunc n f.derivative_fun : R⟦X⟧) = derivative_fun ↑(trunc (n + 1) f) :=
by
  ext d
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    rw [coeff_derivative, coeff_derivative, Polynomial.coeff_coe, coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [coeff_derivative, Polynomial.coeff_coe, coeff_trunc, if_neg this, zero_mul]

--A special case of the next theorem, used in its proof.
private theorem derivative_coe_mul_coe (f g : R[X]) :
  derivative_fun (f * g : R⟦X⟧) = f * derivative_fun (g : R⟦X⟧) + g * derivative_fun (f : R⟦X⟧) :=
by
  rw [←Polynomial.coe_mul, derivative_coe, derivative_mul,
    derivative_coe, derivative_coe, add_comm, mul_comm _ g,
    ←Polynomial.coe_mul, ←Polynomial.coe_mul, Polynomial.coe_add]

/-- Leibniz rule for formal power series.-/
theorem derivative_mul (f g : R⟦X⟧) :
  derivative_fun (f * g) = f • g.derivative_fun + g • f.derivative_fun :=
by
  ext n
  have h₀ : n + 1 < n + 1 + 1 := lt_succ_self (n + 1)
  have h₁ : n < n + 1 := lt_succ_self n
  have h₂ : n < n + 1 + 1 := lt_of_lt_of_le h₁ (le_of_lt h₀)
  rw [coeff_derivative, map_add, coeff_mul_cts f g h₀ h₀,
    smul_eq_mul, smul_eq_mul,
    coeff_mul_cts g f.derivative_fun h₂ h₁,
    coeff_mul_cts f g.derivative_fun h₂ h₁, trunc_derivative, trunc_derivative,
    ← map_add, ← derivative_coe_mul_coe, coeff_derivative]

theorem derivative_one : derivative_fun (1 : R⟦X⟧) = 0 :=
by
  rw [←map_one (C R), derivative_C (1 : R)]

theorem derivative_smul (r : R) (f : R⟦X⟧) : derivative_fun (r • f) = r • derivative_fun f :=
by
  rw [smul_eq_C_mul, smul_eq_C_mul, derivative_mul,
    derivative_C, smul_zero, add_zero, smul_eq_mul]

/--The formal derivative of a formal power series.-/
noncomputable def D : Derivation R R⟦X⟧ R⟦X⟧
where
  toFun             := derivative_fun
  map_add'          := derivative_add
  map_smul'         := derivative_smul
  map_one_eq_zero'  := derivative_one
  leibniz'          := derivative_mul

local notation "D" => D (R := R)

@[simp]
theorem D_mul (f g : R⟦X⟧) : D (f * g) = f * D g + g * D f :=
  derivative_mul f g

@[simp]
theorem D_one : D (1 : R⟦X⟧) = 0 :=
  derivative_one

@[simp]
theorem coeff_D (f : R⟦X⟧) (n : ℕ) : coeff n (D f) = coeff (n + 1) f * (n + 1) :=
  coeff_derivative f n

@[simp]
theorem D_coe (f : R[X]) : (f : R⟦X⟧).derivative_fun = derivative (R := R) f :=
  derivative_coe f

@[simp]
theorem D_X : D (X : R⟦X⟧) = 1 :=
by
  ext
  rw [coeff_D, coeff_one, coeff_X, boole_mul]
  simp_rw [add_left_eq_self]
  split_ifs with h
  · rw [h, cast_zero, zero_add]
  · rfl

theorem trunc_D (f : R⟦X⟧) (n : ℕ) :
  trunc n (D f) = derivative (R := R) (trunc (n + 1) f) :=
by
  apply coe_inj.mp
  rw [←D_coe, ←trunc_derivative]
  rfl


theorem trunc_D' (f : R⟦X⟧) (n : ℕ) :
  trunc (n-1) (D f) = derivative (R := R) (trunc n f) :=
by
  cases n with
  | zero =>
    simp only [zero_eq, ge_iff_le, tsub_eq_zero_of_le]
    rfl
  | succ n =>
    rw [Nat.succ_sub_one, trunc_D]



theorem trunc_succ (f : R⟦X⟧) (n : ℕ) :
  trunc n.succ f = trunc n f + Polynomial.monomial (R := R) n (coeff n f) :=
by
  rw [trunc, Ico_zero_eq_range, Finset.sum_range_succ, trunc, Ico_zero_eq_range]

theorem D_coe_comp (f : R[X]) (g : R⟦X⟧) : D (f.eval₂ (C R) g)
  = (derivative (R := R) f).eval₂ (C R) g * D g :=
  Derivation.polynomial_eval₂ D f g

-- /--Composition of power series-/
-- noncomputable def comp : R⟦X⟧ → R⟦X⟧ → R⟦X⟧ := λ f g ↦
--   if constantCoeff R g = 0
--   then mk λ n ↦ coeff n ((trunc n.succ f).eval₂ (C R) g)
--   else 0

lemma pow_tendsto_zero_of_nilpotent_const' {f : R⟦X⟧} {b : ℕ} (hb : (constantCoeff R f) ^ b = 0)
    ⦃n m : ℕ⦄ (hm : b * (n + 1) ≤ m) : coeff n (f ^ m) = 0 := by
  have : constantCoeff R (f ^ b) = 0
  · rwa [map_pow]
  rw [←X_dvd_iff] at this
  apply coeff_of_lt_order
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  rw [hk, pow_add]
  rw [pow_mul, order_eq_multiplicity_X]
  have : X ^ (n+1) ∣ (f^b) ^ (n+1) * f^k
  · apply dvd_mul_of_dvd_left
    exact pow_dvd_pow_of_dvd this (n+1)
  have := multiplicity.le_multiplicity_of_pow_dvd this
  apply lt_of_lt_of_le _ this
  rw [PartENat.coe_lt_coe, Nat.lt_succ]

lemma pow_tendsto_zero_of_nilpotent_const {f : R⟦X⟧} (hf : IsNilpotent (constantCoeff R f)) 
    (n : ℕ) : ∃ N, ∀ m, N ≤ m → coeff n (f^m) = 0 := by
  obtain ⟨b,hb⟩ := hf
  use b * (n + 1)
  apply pow_tendsto_zero_of_nilpotent_const' hb

@[reducible]
noncomputable def comp_aux (f g : R⟦X⟧) (b : ℕ) : R⟦X⟧ :=
  mk λ n ↦ coeff n ((trunc b f).eval₂ (C R) g)

lemma comp_aux_spec (f g : R⟦X⟧) {b c : ℕ} (hb : (constantCoeff R g) ^ (b / (n + 1)) = 0)
    (hc : (constantCoeff R g) ^ (c / (n + 1)) = 0) : 
    coeff n (comp_aux f g b) = coeff n (comp_aux f g c) := by
  wlog h : b ≤ c
  · refine (this f g hc hb ?_).symm
    exact Nat.le_of_not_le h
  · simp only [comp_aux]
    clear hc
    simp only [coeff_mk]
    induction h with
  | refl => rfl
  | step h IH =>
    rename_i m
    change b ≤ m at h
    simp only [comp_aux]
    rw [trunc_succ, eval₂_add, map_add, ←IH]
    convert (add_zero (M := R) _).symm
    rw [eval₂_monomial, coeff_C_mul]
    convert mul_zero (M₀ := R) _
    apply pow_tendsto_zero_of_nilpotent_const' hb
    refine le_trans ?_ h
    apply div_mul_le_self
    done

lemma comp_aux_spec' (f g : R⟦X⟧) {b c : ℕ} (hb : (constantCoeff R g) ^ (b / (n + 1)) = 0)
    (hc : (constantCoeff R g) ^ (c / (n + 1)) = 0) : 
    coeff n ((trunc b f).eval₂ (C R) g) = coeff n ((trunc c f).eval₂ (C R) g) := by
  convert comp_aux_spec f g hb hc using 1 <;>
  rw [comp_aux, coeff_mk]

/--Composition of power series including the case of Nilpotent constant terms-/
noncomputable def comp : R⟦X⟧ → R⟦X⟧ → R⟦X⟧ := λ f g ↦
  if h : IsNilpotent (constantCoeff R g)
  then mk fun n ↦ coeff n (comp_aux f g (h.choose * (n + 1)))
  else 0

scoped infixr:90 " ∘ "  => PowerSeries.comp

theorem comp_eq {f g : R⟦X⟧} (hg : IsNilpotent (constantCoeff R g)) :
    (f ∘ g : R⟦X⟧) = mk λ n ↦ coeff n ((trunc (hg.choose * (n + 1)) f).eval₂ (C R) g) := by
  simp_rw [comp, dif_pos hg, comp_aux, coeff_mk]

theorem comp_eq_zero {f g : R⟦X⟧} (hg : ¬ IsNilpotent (constantCoeff R g)) : (f ∘ g : R⟦X⟧) = 0 := by
  rw [comp, dif_neg hg]

theorem coeff_comp_eq' (f g : R⟦X⟧) (n : ℕ) :
  coeff n (f ∘ g) =
    if hg : IsNilpotent (constantCoeff R g)
    then coeff n ((trunc (hg.choose * (n + 1)) f).eval₂ (C R) g)
    else 0 :=
by
  rw [comp]
  split
  · case inl h => simp_rw [dif_pos h, comp_aux, coeff_mk]
  · case inr h => rw [dif_neg h, map_zero]

theorem coeff_comp_eq {f g : R⟦X⟧} {n : ℕ} (hg : IsNilpotent (constantCoeff R g)) :
  coeff n (f ∘ g) = coeff n ((trunc (hg.choose * (n + 1)) f).eval₂ (C R) g) :=
by rw [coeff_comp_eq', dif_pos hg]

theorem coeff_comp_eq_zero {f g : R⟦X⟧} {n : ℕ} (hg : ¬IsNilpotent (constantCoeff R g)) :
  coeff n (f ∘ g) = 0 :=
by rw [coeff_comp_eq', dif_neg hg]

example (x : R) (n m : ℕ) (h : n ≤ m) (h' : x^n = 0) : x^m = 0 := by exact pow_eq_zero_of_le h h'
-- private theorem coeff_pow_eq_zero {g : R⟦X⟧} {b : ℕ} (hb : (constantCoeff R g) ^ b = 0)
--   {n a : ℕ} (ha : (b * (n + 1)) ≤ a) :
--   coeff n (g ^ a) = 0 :=
-- pow_tendsto_zero_of_nilpotent_const' hb ha

/-- (Technical Lemma)
The if `n<a` then the `n`-th coefficient of `f ∘ g` may be
calculated using the `a`-th truncation of `f`.
-/
theorem coeff_comp_cts {f g : R⟦X⟧} {b : ℕ} (hb : (constantCoeff R g) ^ b = 0)
  {n a : ℕ} (ha : (b * (n + 1)) ≤ a) :
  coeff n (f ∘ g) = coeff n ((trunc a f).eval₂ (C R) g) :=
by
  rw [coeff_comp_eq ⟨b, hb⟩]
  apply comp_aux_spec'
  · simp
    apply Exists.choose_spec (⟨b, hb⟩ : ∃ n, (constantCoeff R g) ^ n = 0)
  · convert pow_eq_zero_of_le _ hb
    have goo : 0 < n + 1 := by simp
    exact Iff.mpr (Nat.le_div_iff_mul_le goo) ha

/-- The "chain rule" for formal power series in one variable:
  `D (f ∘ g) = (D f) ∘ g * D g`.
If `g` has non-zero constant term then the equation
is trivially true, with both sides defined to be zero.
-/
@[simp]
theorem D_comp (f g : R⟦X⟧) : D (f ∘ g) = ((D f) ∘ g : R⟦X⟧) * D g :=
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
      suffices : (C R 1) * D ( f ∘ g ) = (C R 1) * (D f).comp g * D g
      · have that : C R 1 = 1 := rfl
        rwa [that, one_mul, one_mul] at this
      · rw [this, map_zero, zero_mul, zero_mul, zero_mul]
  · rw [comp_eq_zero h, comp_eq_zero h, zero_mul, map_zero]

@[simp]
theorem D_C (r : R) : D (C R r : R⟦X⟧) = 0 :=
  derivative_C r

@[simp]
theorem D_smul (a : R) (f : R⟦X⟧) : D (a • f) = a • D f :=
  Derivation.map_smul D a f

/-
The following are a few more results concering composition of
power series.
We show that composition is associative,
`X` is a 2-sided identity.
a.rescale f = f ∘ (a*X)
-/
theorem natDegree_trunc_lt (f : R⟦X⟧) (n : ℕ) : (trunc (n + 1) f).natDegree < n + 1 :=
by
  rw [lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_trunc]
  split_ifs with h
  · rw [lt_succ, ←not_lt] at h
    contradiction
  · rfl

theorem constantCoeff_comp {f g : R⟦X⟧} (h : constantCoeff R g = 0 ) :
  constantCoeff R (f ∘ g) = constantCoeff R f :=
by
  have : (trunc 1 f).natDegree < 1 := natDegree_trunc_lt f 0
  have h' : (constantCoeff R g)^1 = 0
  · rwa [pow_one]
  rw [←coeff_zero_eq_constantCoeff, coeff_comp_cts h',
    eval₂_eq_sum_range' (C R) this g,
    Finset.sum_range_one,
    _root_.pow_zero, mul_one, coeff_zero_C, coeff_trunc, if_pos zero_lt_one]
  rfl

@[simp]
theorem trunc_trunc (f : R⟦X⟧) {n : ℕ} : trunc n ↑(trunc n f) = trunc n f :=
by
  ext m
  rw [coeff_trunc, coeff_trunc, Polynomial.coeff_coe]
  split_ifs with h
  · rw [coeff_trunc, if_pos h]
  · rfl

@[simp]
theorem trunc_trunc_mul_trunc (f g : R⟦X⟧) (n : ℕ) :
  trunc n (trunc n f * trunc n g : R⟦X⟧) = trunc n (f * g) :=
by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, Finset.sum_congr rfl]
    rintro ⟨a, b⟩ hab
    have ha : a < n := lt_of_le_of_lt (Finset.Nat.antidiagonal.fst_le hab) h
    have hb : b < n := lt_of_le_of_lt (Finset.Nat.antidiagonal.snd_le hab) h
    rw [Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_trunc, coeff_trunc, if_pos ha, if_pos hb]
  · rfl

theorem trunc_coe_eq_self {f : R[X]} {n : ℕ} (hn : n > f.natDegree) :
  trunc n (f : R⟦X⟧) = f :=
by
  have this : support f ⊆ Finset.Ico 0 n
  · calc
      support f
        ⊆ Finset.range (f.natDegree + 1)  := supp_subset_range_natDegree_succ
      _ ⊆ Finset.range n                  := Iff.mpr Finset.range_subset hn
      _ = Finset.Ico 0 n                  := by rw [Finset.range_eq_Ico]
  nth_rw 2 [←sum_monomial_eq f]
  rw [trunc, sum_eq_of_subset f _ _ _ this, Finset.sum_congr rfl]
  · intros
    rw [Polynomial.coeff_coe]
  · intros
    exact monomial_zero_right _

theorem coe_comp {f : R[X]} {g : R⟦X⟧} (hg : constantCoeff R g = 0) :
  ((f:R⟦X⟧) ∘ g : R⟦X⟧) = f.eval₂ (C R) g :=
by
  ext n
  by_cases n < f.natDegree + 1
  · rw [coeff_comp_cts hg h, trunc_coe_eq_self]
    exact lt_succ_self _
  · rw [coeff_comp_eq hg, trunc_coe_eq_self]
    exact lt_succ_of_le (le_of_lt (lt_of_succ_le (le_of_not_gt h)))


theorem trunc_of_trunc_comp {f g : R⟦X⟧} {n : ℕ} (hg : constantCoeff R g = 0) :
  trunc n ((trunc n f : R⟦X⟧) ∘ g) = trunc n (f ∘ g) :=
by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_comp_cts hg h, coeff_comp_cts hg h, trunc_trunc]
  · rfl

@[simp]
theorem mul_comp (f g h : R⟦X⟧) :
  ((f * g) ∘ h : R⟦X⟧) = (f ∘ h : R⟦X⟧) * (g ∘ h : R⟦X⟧) :=
by
  by_cases hh : constantCoeff R h = 0
  · ext n
    let T : R⟦X⟧ → R[X] := trunc (n + 1)
    have hT : T = trunc (n + 1) := by rfl
    have hn : n < n + 1 := lt_succ_self n
    calc
      coeff n ((f * g) ∘ h) = coeff n ((T (f * g) : R⟦X⟧) ∘ h) := by
        rw [coeff_comp_cts hh hn, coeff_comp_cts hh hn, trunc_trunc]
      _ = coeff n ((T (T f * T g : R⟦X⟧) : R⟦X⟧) ∘ h) :=
        by rw [hT, trunc_trunc_mul_trunc]
      _ = coeff n ((T f * T g : R⟦X⟧) ∘ h) :=
        by rw [coeff_comp_cts hh hn, coeff_comp_cts hh hn, trunc_trunc]
      _ = coeff n ((T f : R⟦X⟧).comp h * (T g : R⟦X⟧).comp h) :=
        by rw [←Polynomial.coe_mul, coe_comp hh, coe_comp hh, coe_comp hh, eval₂_mul]
      _ = coeff n (T ((T f : R⟦X⟧) ∘ h) * T ((T g : R⟦X⟧) ∘ h) : R⟦X⟧) :=
        by rw [coeff_mul_cts _ _ hn hn]
      _ = coeff n (T (f ∘ h) * T (g ∘ h) : R⟦X⟧) :=
        by rw [hT, trunc_of_trunc_comp hh, trunc_of_trunc_comp hh]
      _ = coeff n (f.comp h * g.comp h) :=
        by rw [←(coeff_mul_cts _ _ hn hn)]
  · rw [comp_eq_zero hh, comp_eq_zero hh, zero_mul]


@[simp]
theorem add_comp (f g h : R⟦X⟧) : ((f + g) ∘ h : R⟦X⟧) = (f ∘ h : R⟦X⟧) + (g ∘ h : R⟦X⟧) :=
by
  by_cases hh : constantCoeff R h = 0
  · ext
    rw [coeff_comp_eq hh, trunc_add, eval₂_add, map_add, map_add,
      coeff_comp_eq hh, coeff_comp_eq hh]
  · rw [comp_eq_zero hh, comp_eq_zero hh, comp_eq_zero hh, add_zero]

@[simp]
theorem one_comp {f : R⟦X⟧} (hf : constantCoeff R f = 0) : (1 ∘ f : R⟦X⟧) = 1 :=
by
  ext
  rw [coeff_comp_eq hf, succ_eq_add_one, trunc_one, eval₂_one]


@[simp]
theorem comp_zero (f : R⟦X⟧) : f ∘ 0 = C R (constantCoeff R f) :=
by
  ext n
  have : constantCoeff R (0 : R⟦X⟧) = 0 := map_zero _
  rw [coeff_comp_eq this, eval₂_at_zero, coeff_trunc,
    coeff_zero_eq_constantCoeff, coeff_C]
  split_ifs with h₁ h₂
  · rw [h₁, coeff_zero_eq_constantCoeff, constantCoeff_C]
  · cases h₂ (zero_lt_succ n)
  · rw [coeff_C, if_neg h₁]


/-NOTE: `instance : has_inv power_series R` is currently only defined
when `R` is a field.  -/
@[simp]
theorem inv_comp {R : Type} [Field R]
  (f g : PowerSeries R) (hf : constantCoeff R f ≠ 0) :
  (f⁻¹ ∘ g : R⟦X⟧) = (f ∘ g : R⟦X⟧)⁻¹ :=
by
  by_cases constantCoeff R g = 0
  · symm
    rw [MvPowerSeries.inv_eq_iff_mul_eq_one, ←mul_comp, PowerSeries.inv_mul_cancel]
    · exact one_comp h
    · exact hf
    · change constantCoeff R (f ∘ g) ≠ 0
      rwa [constantCoeff_comp h]
  · rw [comp]
    split_ifs
    · contradiction
    · rw [comp, if_neg h, PowerSeries.zero_inv]




theorem _root_.Polynomial.eval₂_X_eq_coe (f : R[X]) : f.eval₂ (C R) X = ↑f :=
by
  nth_rw 2 [(@eval₂_C_X R _ f).symm]
  rw [←coeToPowerSeries.ringHom_apply,
    eval₂_eq_sum_range, eval₂_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_mul, map_pow, coeToPowerSeries.ringHom_apply,
    coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]





@[simp]
theorem comp_X (f : R⟦X⟧) : f ∘ X = f :=
by
  ext n
  rw [coeff_comp_eq (@constantCoeff_X R _), eval₂_X_eq_coe, ←coeff_cts]
  exact lt_succ_self n

@[simp]
theorem trunc_X {n : ℕ} : trunc (n + 2) X = (Polynomial.X : R[X]) :=
by
  ext d
  rw [coeff_trunc, coeff_X]
  split_ifs with h₁ h₂
  · rw [h₂, coeff_X_one]
  · rw [coeff_X_of_ne_one h₂]
  · rw [coeff_X_of_ne_one]
    by_contra hd
    apply h₁
    rw [hd]
    exact one_lt_succ_succ n

@[simp]
theorem X_comp {f : R⟦X⟧} (h : constantCoeff R f = 0) : (X ∘ f : R⟦X⟧) = f :=
by
  ext n
  rw [coeff_comp_cts h (lt_add_of_pos_right n (succ_pos 1)), trunc_X, eval₂_X]



-- TODO:
-- # ASK John about the best way of dealing with a finite sum with only one non-zero term.
-- lemma rescale_eq_comp_mul_X (f : pow) (r : R) :
--   rescale r f = f ∘ (↑r * X) :=
-- begin
--   have : constantCoeff R (↑r * X) = 0,
--   {
--     simp only [coeff_zero_eq_constantCoeff,
--       map_mul, constantCoeff_X, mul_zero],
--   },
--   ext,
--   rw [coeff_rescale, coeff_comp_eq this,
--     eval₂_eq_sum_range' (C R) (natDegree_trunc_lt f n),
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
--   (∃ g : pow , f ∘ g = X) :=
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
  D (R := R) f = D (R := R) g → constantCoeff R f = constantCoeff R g → f = g :=
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
theorem PowerSeries.D_inv {R : Type} [Field R] (f : PowerSeries R) :
  D (R := R) f⁻¹ = -f⁻¹ ^ 2 * D (R := R) f :=
by
  by_cases constantCoeff R f = 0
  · suffices : f⁻¹ = 0
    . rw [this, pow_two, zero_mul, neg_zero, zero_mul, map_zero]
    · rwa [MvPowerSeries.inv_eq_zero]
  · apply Derivation.leibniz_of_mul_eq_one
    exact PowerSeries.inv_mul_cancel _ h



