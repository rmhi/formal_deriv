/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Formal.Truncation_lemmas

/-!
# Definitions

In this file we define an operation `comp` (composition)
on formal power series in one variable (over an arbitrary commutative semi-ring).
The composition `f.comp g` always makes sense if the constant term of `g` is
a nilpotent element of `R`. In other cases, the composition is defined to be zero.

The composition can also be written `f ∘ g`, as long as no confusion arises with other kinds of composition.

Under suitable assumptions, we prove that two power series are equal if their derivatives
are equal and their constant terms are equal. This gives us a simple tool for proving
power series identities. For example, one can easily prove the power series identity
`exp ( log (1+X)) = 1+X` by differentiating twice. Several examples of this kind of
identity are contained in the accomanying file "Examples.lean".


## Main results

## Notation

- `PowerSeries.comp`  : the composition operation `R⟦X⟧ → R⟦X⟧ → R⟦X⟧`.
                        `f.comp g` is also overloaded as `(f ∘ g : R⟦X⟧)`,
                        or sometimes just `f ∘ g`.
-/



open PowerSeries Nat BigOperators Polynomial
open scoped Classical

section CommutativeSemiring

variable {R : Type u} [CommSemiring R]

namespace PowerSeries



def hasComp (f g : R⟦X⟧) : Prop :=
  ∀ d, ∃ N, ∀ n, N ≤ n → (coeff R n f) * coeff R d (g^n) = 0

noncomputable def comp (f g : R⟦X⟧) : R⟦X⟧ :=
  if h : f.hasComp g
  then mk (λ d ↦ coeff R d ((trunc (h d).choose f).eval₂ (C R) g ))
  else 0


-- lemma X_dvd_pow_of_isNilpotent_constantCoeff {g : R⟦X⟧} (hg : IsNilpotent (constantCoeff R g)) :
--   ∃ N, X ∣ g^N :=
-- by
--   obtain ⟨N, hN⟩ := hg
--   use N
--   rwa [X_dvd_iff, map_pow]

lemma pow_X_dvd_pow_of_isNilpotent_constantCoeff {g : R⟦X⟧} (d : ℕ) (hg : IsNilpotent (constantCoeff R g)) :
  ∃ N, X^d ∣ g^N :=
by
  obtain ⟨N, hN⟩ := hg
  use N * d
  rw [pow_mul]
  apply pow_dvd_pow_of_dvd
  rwa [X_dvd_iff, map_pow]



lemma hasComp_of_isNilpotent_constantCoeff {f g : R⟦X⟧} (hg : IsNilpotent (constantCoeff R g)) :
  f.hasComp g :=
by
  intro d
  obtain ⟨N, hN⟩ := pow_X_dvd_pow_of_isNilpotent_constantCoeff d.succ hg
  use N 
  intro n hn
  have : X ^ d.succ ∣ g^n
  · trans g ^ N
    exact hN
    apply pow_dvd_pow (h := hn)
  rw [PowerSeries.X_pow_dvd_iff] at this
  rw [this, mul_zero]
  exact lt.base d


lemma hasComp_of_zero {f g : R⟦X⟧} {hg : constantCoeff R g = 0} :
  f.hasComp g :=
by
  apply hasComp_of_isNilpotent_constantCoeff
  rw [hg]
  exact IsNilpotent.zero


lemma coe_has_comp {f : R[X]} {g : R⟦X⟧} :
  (f : R⟦X⟧).hasComp g :=
by
  intro d
  use f.natDegree + 1
  intro n hn
  rw [coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt, zero_mul]
  rw [←Nat.succ_le]
  exact hn



-- lemma pow_tendsto_zero_of_nilpotent_const' {f : R⟦X⟧} {b : ℕ} (hb : (constantCoeff R f) ^ b = 0)
--     ⦃n m : ℕ⦄ (hm : b * (n + 1) ≤ m) : coeff R n (f ^ m) = 0 := by
--   have : constantCoeff R (f ^ b) = 0
--   · rwa [map_pow]
--   rw [←X_dvd_iff] at this
--   apply coeff_of_lt_order
--   obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
--   rw [hk, pow_add]
--   rw [pow_mul, order_eq_multiplicity_X]
--   have : X ^ (n+1) ∣ (f^b) ^ (n+1) * f^k
--   · apply dvd_mul_of_dvd_left
--     exact pow_dvd_pow_of_dvd this (n+1)
--   have := multiplicity.le_multiplicity_of_pow_dvd this
--   apply lt_of_lt_of_le _ this
--   rw [PartENat.coe_lt_coe, Nat.lt_succ]

-- lemma pow_tendsto_zero_of_nilpotent_const {f : R⟦X⟧} (hf : IsNilpotent (constantCoeff R f)) 
--     (n : ℕ) : ∃ N, ∀ m, N ≤ m → coeff R n (f^m) = 0 := by
--   obtain ⟨b,hb⟩ := hf
--   use b * (n + 1)
--   apply pow_tendsto_zero_of_nilpotent_const' hb


@[reducible]
noncomputable def comp_aux (f g : R⟦X⟧) (b : ℕ) : R⟦X⟧ :=
  mk λ n ↦ coeff R n ((trunc b f).eval₂ (C R) g)

lemma comp_aux_spec (f g : R⟦X⟧) {b c : ℕ} (hb : (constantCoeff R g) ^ (b / (n + 1)) = 0)
    (hc : (constantCoeff R g) ^ (c / (n + 1)) = 0) : 
    coeff R n (comp_aux f g b) = coeff R n (comp_aux f g c) := by
  wlog h : b ≤ c
  · refine (this f g hc hb ?_).symm
    exact le_of_not_le h
  · simp only [comp_aux]
    clear hc
    simp only [coeff_mk]
    induction h with
  | refl => rfl
  | step h IH =>
    rename_i m
    change b ≤ m at h
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
    coeff R n ((trunc b f).eval₂ (C R) g) = coeff R n ((trunc c f).eval₂ (C R) g) := by
  convert comp_aux_spec f g hb hc using 1 <;>
  rw [comp_aux, coeff_mk]

/--Composition of power series. If `g` has nilpotent constant term then `f.comp g`
is defined in the usual way. If the constant term of `g` is not nilpotent then `f.comp g`
is defined to be `0`.-/
noncomputable def comp : R⟦X⟧ → R⟦X⟧ → R⟦X⟧ := λ f g ↦
  if h : IsNilpotent (constantCoeff R g)
  then mk fun n ↦ coeff R n (comp_aux f g (h.choose * (n + 1)))
  else 0

scoped infixr:90 " ∘ "  => PowerSeries.comp

theorem comp_eq {f g : R⟦X⟧} (hg : IsNilpotent (constantCoeff R g)) :
    (f ∘ g : R⟦X⟧) = PowerSeries.mk λ n ↦ coeff R n ((trunc (hg.choose * (n + 1)) f).eval₂ (C R) g) := by
  simp_rw [comp, dif_pos hg, comp_aux, coeff_mk]

theorem comp_eq_zero {f g : R⟦X⟧} (hg : ¬ IsNilpotent (constantCoeff R g)) : (f ∘ g : R⟦X⟧) = 0 := by
  rw [comp, dif_neg hg]

theorem coeff_comp_eq' (f g : R⟦X⟧) (n : ℕ) :
  coeff R n (f ∘ g) =
    if hg : IsNilpotent (constantCoeff R g)
    then coeff R n ((trunc (hg.choose * (n + 1)) f).eval₂ (C R) g)
    else 0 :=
by
  rw [comp]
  split
  · case inl h => simp_rw [dif_pos h, comp_aux, coeff_mk]
  · case inr h => rw [dif_neg h, map_zero]

theorem coeff_comp_eq {f g : R⟦X⟧} {n : ℕ} (hg : IsNilpotent (constantCoeff R g)) :
  coeff R n (f ∘ g) = coeff R n ((trunc (hg.choose * (n + 1)) f).eval₂ (C R) g) :=
by rw [coeff_comp_eq', dif_pos hg]

theorem coeff_comp_eq_zero {f g : R⟦X⟧} {n : ℕ} (hg : ¬IsNilpotent (constantCoeff R g)) :
  coeff R n (f ∘ g) = 0 :=
by rw [coeff_comp_eq', dif_neg hg]

/-- (Technical Lemma)
If `(g 0)^b = 0` and `b * (n + 1) ≤ a`
then the `n`-th coefficient of `f ∘ g` may be
calculated using the `a`-th truncation of `f`.
-/
theorem coeff_comp_cts {f g : R⟦X⟧} {b : ℕ} (hb : (constantCoeff R g) ^ b = 0)
  {n a : ℕ} (ha : b * (n + 1) ≤ a) :
  coeff R n (f ∘ g) = coeff R n ((trunc a f).eval₂ (C R) g) :=
by
  rw [coeff_comp_eq ⟨b, hb⟩]
  apply comp_aux_spec'
  · simp only [add_pos_iff, or_true, mul_div_left]
    apply Exists.choose_spec (⟨b, hb⟩ : ∃ n, (constantCoeff R g) ^ n = 0)
  · convert pow_eq_zero_of_le _ hb
    have goo : 0 < n + 1 := by simp
    exact Iff.mpr (Nat.le_div_iff_mul_le goo) ha


/--
If `a^0 = 0` in `R`, then any two power series are equal.
This is a technical lemma, which deals with the following situation.
We often assume `IsNilpotent : constantCoeff f`, which means that
`(constantCoeff f) ^ n = 0` for some `n`. We may effectively assume that
`n` is positive, since otherwise this lemma shows that all equalities are
true.
-/
private lemma pow_zero_eq_zero {a : R} (ha : a^0 = 0) {f g : R⟦X⟧} :
  f = g :=
by
  rw [_root_.pow_zero] at ha
  calc
    _ = (C R 1) * f := by rw [map_one, one_mul]
    _ = 0           := by rw [ha, map_zero, zero_mul]
    _ = (C R 1) * g := by rw [ha, map_zero, zero_mul]
    _ = g           := by rw [map_one, one_mul]

theorem natDegree_trunc_lt (f : R⟦X⟧) (n : ℕ) : (trunc (n + 1) f).natDegree < n + 1 :=
by
  rw [lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_trunc]
  split_ifs with h
  · rw [lt_succ, ←not_lt] at h
    contradiction
  · rfl

-- @[simp] -- currently unused
-- lemma trunc_zero' {f : R⟦X⟧} : trunc 0 f = 0 := rfl

theorem eval₂_trunc_eq_sum_range [Semiring S] {f : R⟦X⟧} {n : ℕ} {G : R →+* S} {s : S} :
  (trunc n f).eval₂ G s = ∑ i in Finset.range n, G (coeff R i f) * s ^ i :=
by
  cases n with
  | zero => 
    rw [zero_eq, trunc, Ico_zero_eq_range, Finset.range_zero,
      Finset.sum_empty, Finset.sum_empty, eval₂_zero]
  | succ n =>
    have := natDegree_trunc_lt f n
    rw [eval₂_eq_sum_range' (hn := this)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi 
    congr
    rw [coeff_trunc, if_pos hi]


theorem trunc_comp_cts {f g : R⟦X⟧} {b : ℕ} (hb : (constantCoeff R g) ^ b = 0)
  {n c d : ℕ} (ha : b * n ≤ c := by rfl) (hd : n ≤ d := by rfl) :
  trunc n (f ∘ g) = trunc n ((trunc c f).comp (trunc d g)) :=
by
  ext m
  by_cases m < n
  · have hmc : b * (m + 1) ≤ c
    · trans b*n
      apply Nat.mul_le_mul_left
      rwa [Nat.succ_le_iff]
      assumption
    have hmd : m < d := lt_of_lt_of_le h hd
    rw [coeff_trunc, if_pos h, coeff_comp_cts hb hmc,
      coeff_trunc, if_pos h, Polynomial.comp,
      eval₂_trunc_eq_sum_range, eval₂_trunc_eq_sum_range]
    rw [map_sum]
    simp only [coeff_C_mul, Polynomial.coeff_coe, finset_sum_coeff, Polynomial.coeff_C_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    congr
    trans Polynomial.coeff (trunc d (g^i)) m
    · rw [coeff_trunc, if_pos hmd]
    · rw [←trunc_trunc_pow, coeff_trunc, if_pos hmd, Polynomial.coeff_coe]
  · rw [coeff_trunc, if_neg h, coeff_trunc, if_neg h]



/-
The following are a few more results concering composition of
power series.
We show that composition is associative,
`X` is a 2-sided identity.
a.rescale f = f ∘ (a*X)
-/

theorem constantCoeff_comp {f g : R⟦X⟧} (h : constantCoeff R g = 0 ) :
  constantCoeff R (f ∘ g) = constantCoeff R f :=
by
  have h' : (constantCoeff R g)^1 = 0
  · rwa [pow_one]
  rw [←coeff_zero_eq_constantCoeff, coeff_comp_cts h',
    eval₂_trunc_eq_sum_range,
    Finset.sum_range_one,
    _root_.pow_zero, mul_one, coeff_zero_C]
  rfl



theorem coe_comp {f : R[X]} {g : R⟦X⟧} (hg : IsNilpotent (constantCoeff R g)) :
  ((f:R⟦X⟧) ∘ g : R⟦X⟧) = f.eval₂ (C R) g :=
by
  set b := hg.choose with b_def
  have hb := hg.choose_spec
  ext n
  by_cases b * (n+1) ≤ f.natDegree + 1
  · rw [coeff_comp_cts hb h, trunc_coe_eq_self]
    apply lt_succ_self
  · rw [coeff_comp_eq hg, trunc_coe_eq_self]
    rw [←b_def]
    rw [not_le] at h
    apply lt_of_succ_lt h

--TODO:
--`theorem coe_comp_coe` if f and g are polynomials then the composition of their
--coercions is the coercion of their compositions. 


theorem coe_comp' {f : R[X]} {g : R⟦X⟧} (hg : constantCoeff R g = 0) :
  ((f:R⟦X⟧) ∘ g : R⟦X⟧) = f.eval₂ (C R) g :=
by
  apply coe_comp
  rw [hg]
  exact IsNilpotent.zero

theorem trunc_of_trunc_comp {f g : R⟦X⟧} {n : ℕ} (hg : constantCoeff R g = 0) :
  trunc n ((trunc n f : R⟦X⟧) ∘ g) = trunc n (f ∘ g) :=
by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split
  · have hg' : (constantCoeff R g)^1 = 0
    · rwa [pow_one]
    rw [coeff_comp_cts hg', coeff_comp_cts hg', trunc_trunc] <;>
    · rwa [one_mul, succ_le]
  · rfl

theorem trunc_of_trunc_comp' {f g : R⟦X⟧} {n : ℕ} (hg : (constantCoeff R g)^r = 0) :
  trunc n ((trunc (r*n) f : R⟦X⟧) ∘ g) = trunc n (f ∘ g) :=
by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split
  · rw [coeff_comp_cts hg, coeff_comp_cts hg, trunc_trunc] <;>
    · apply Nat.mul_le_mul (by rfl)
      rwa [succ_le]
  · rfl


@[simp]
theorem mul_comp (f g h : R⟦X⟧) :
  ((f * g) ∘ h : R⟦X⟧) = (f ∘ h : R⟦X⟧) * (g ∘ h : R⟦X⟧) :=
by
  by_cases hh : IsNilpotent (constantCoeff R h)
  · have hh' := hh
    obtain ⟨r, hr⟩ := hh'
    by_cases hr' : 0 < r
    case neg =>
      clear hh
      rw [not_lt, nonpos_iff_eq_zero] at hr'
      rw [hr'] at hr
      apply pow_zero_eq_zero hr
    case pos =>
      ext n
      set T : R⟦X⟧ → R[X] := trunc (r* (n + 1)) with hT
      set T' : R⟦X⟧ → R[X] := trunc (n + 1) with hT'
      have hn : n < n + 1 := lt_succ_self n
      calc
        coeff R n ((f * g) ∘ h) = coeff R n ((T (f * g) : R⟦X⟧) ∘ h) := by
          rw [coeff_comp_cts hr (by rfl), coeff_comp_cts hr (by rfl), trunc_trunc]
        _ = coeff R n ((T (T f * T g : R⟦X⟧) : R⟦X⟧) ∘ h) :=
          by rw [hT, trunc_trunc_mul_trunc]
        _ = coeff R n ((T f * T g : R⟦X⟧) ∘ h) :=
          by rw [coeff_comp_cts hr (by rfl), coeff_comp_cts hr (by rfl), trunc_trunc]
        _ = coeff R n ((T f : R⟦X⟧).comp h * (T g : R⟦X⟧).comp h) :=
          by rw [←Polynomial.coe_mul, coe_comp hh, coe_comp hh, coe_comp hh, eval₂_mul]
        _ = coeff R n (T' ((T f : R⟦X⟧) ∘ h) * T' ((T g : R⟦X⟧) ∘ h) : R⟦X⟧) :=
          by rw [coeff_mul_cts _ _ hn hn]
        _ = coeff R n (T' (f ∘ h) * T' (g ∘ h) : R⟦X⟧) :=
          by rw [hT, hT', trunc_of_trunc_comp' hr, trunc_of_trunc_comp' hr]
        _ = coeff R n (f.comp h * g.comp h) :=
          by rw [←(coeff_mul_cts (f ∘ h) (g ∘ h)) hn hn]
  · rw [comp_eq_zero hh, comp_eq_zero hh, zero_mul]

@[simp]
theorem add_comp (f g h : R⟦X⟧) : ((f + g) ∘ h : R⟦X⟧) = (f ∘ h : R⟦X⟧) + (g ∘ h : R⟦X⟧) :=
by
  by_cases hh : IsNilpotent (constantCoeff R h)
  · ext
    rw [coeff_comp_eq hh, trunc_add, eval₂_add, map_add, map_add,
      coeff_comp_eq hh, coeff_comp_eq hh]
  · rw [comp_eq_zero hh, comp_eq_zero hh, comp_eq_zero hh, add_zero]

@[simp]
theorem one_comp {f : R⟦X⟧} (hf : IsNilpotent (constantCoeff R f)) : (1 ∘ f : R⟦X⟧) = 1 :=
by
  ext
  rw [coeff_comp_cts hf.choose_spec (le_of_lt (lt_succ_self _)), trunc_one, eval₂_one]

@[simp]
theorem one_comp' {f : R⟦X⟧} (hf : constantCoeff R f = 0) : (1 ∘ f : R⟦X⟧) = 1 :=
by
  apply one_comp
  rw [hf]
  exact IsNilpotent.zero

@[simp]
theorem comp_zero (f : R⟦X⟧) : f ∘ 0 = C R (constantCoeff R f) :=
by
  ext n
  have : IsNilpotent <| constantCoeff R (0 : R⟦X⟧) := IsNilpotent.zero
  rw [coeff_comp_eq this, eval₂_at_zero, coeff_trunc,
    coeff_zero_eq_constantCoeff, coeff_C]
  split_ifs with h₁ h₂
  · rw [h₁, coeff_zero_eq_constantCoeff, constantCoeff_C]
  · rw [h₁, zero_add, mul_one, not_lt, nonpos_iff_eq_zero] at h₂
    have := this.choose_spec
    rw [h₂, _root_.pow_zero] at this
    trans 1 * (coeff R n) ( (C R) ((constantCoeff R) f) )
    · rw [this, zero_mul]
    · rw [one_mul]
  · rw [coeff_C, if_neg h₁]



lemma C_comp {f : R⟦X⟧} (hf : IsNilpotent (constantCoeff R f)) (a : R) :
  (C R a) ∘ f = C R a :=
by
  rwa [←Polynomial.coe_C, coe_comp, eval₂_C, Polynomial.coe_C]


/-NOTE: `instance : has_inv power_series R` is currently only defined
when `R` is a field, so the following two results can only be stated in in the case that
`R` is a field.
The second result `inv_comp` should eventually be extended to the case that
`R` is a commutative ring.-/
@[simp]
theorem inv_comp' {R : Type u} [Field R]
  (f g : PowerSeries R) (hf : constantCoeff R f ≠ 0) :
  (f⁻¹ ∘ g : R⟦X⟧) = (f ∘ g : R⟦X⟧)⁻¹ :=
by
  by_cases IsNilpotent <| constantCoeff R g
  case pos =>
    have : (f⁻¹.comp g) * (f.comp g) = 1
    · rw [←mul_comp, PowerSeries.inv_mul_cancel (h := hf), one_comp h]
    symm
    rw [MvPowerSeries.inv_eq_iff_mul_eq_one, this]
    · change constantCoeff R (f ∘ g) ≠ 0
      by_contra h'
      have : constantCoeff R 1 = 0
      · rw [←this, map_mul, h', mul_zero]
      rw [map_one] at this
      apply one_ne_zero this
  case neg =>
    rw [comp_eq_zero h, comp_eq_zero h, zero_inv]

theorem inv_comp {R : Type u} [Field R]
  (f g : R⟦X⟧) (hf : IsUnit (constantCoeff R f)) :
  (f⁻¹ ∘ g : R⟦X⟧) = (f ∘ g : R⟦X⟧)⁻¹ :=
by
  apply inv_comp'
  exact IsUnit.ne_zero hf

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
  have : (constantCoeff R X)^1 = 0
  · rw [constantCoeff_X, pow_one]
  rw [coeff_comp_cts this (by rfl), eval₂_X_eq_coe, ←coeff_cts]
  rw [one_mul]
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
theorem X_comp {f : R⟦X⟧} (h : IsNilpotent (constantCoeff R f)) : (X ∘ f : R⟦X⟧) = f :=
by
  ext n
  obtain ⟨r,h⟩ := h
  have : r * (n + 1) ≤ r * (n + 1) + 2
  · apply Nat.le_add_right
  rw [coeff_comp_cts h this, trunc_X, eval₂_X]

theorem X_comp' {f : R⟦X⟧} (h : constantCoeff R f = 0) : (X ∘ f : R⟦X⟧) = f :=
by
  apply X_comp
  rw [h]
  exact IsNilpotent.zero

lemma _root_.isNilpotent_pow_succ [Semiring S] {x : S} (hx : IsNilpotent x) :
  IsNilpotent (x ^ (succ n)) :=
by
  rw [_root_.pow_succ]
  apply Commute.isNilpotent_mul_left
  · exact Commute.self_pow x n
  · exact hx

theorem IsNilpotent_constantCoeff_comp
    (hf : IsNilpotent (constantCoeff R f)) { g : R⟦X⟧ } :
  IsNilpotent (constantCoeff R (f ∘ g)) :=
by
  by_cases hg : IsNilpotent (constantCoeff R g)
  · rw [comp_eq hg]
    simp_rw [←coeff_zero_eq_constantCoeff_apply]
    rw [coeff_mk, zero_add, mul_one, eval₂_trunc_eq_sum_range, map_sum]
    apply isNilpotent_sum
    intro i hi
    rw [coeff_zero_eq_constantCoeff_apply, map_mul]
    cases i with
    | zero => 
      apply Commute.isNilpotent_mul_left
      apply Commute.all
      rw [zero_eq, coeff_zero_eq_constantCoeff, constantCoeff_C]
      exact hf
    | succ n =>
      apply Commute.isNilpotent_mul_right
      apply Commute.all
      rw [map_pow]
      apply isNilpotent_pow_succ hg
  · rw [comp_eq_zero hg, map_zero]
    exact IsNilpotent.zero

#check coeff_comp_cts

-- theorem comp_assoc {f g h : R⟦X⟧}
--   (hg : IsNilpotent (constantCoeff R g)) (hh : IsNilpotent (constantCoeff R h)):
--   (f ∘ g) ∘ h = f.comp (g ∘ h) :=
-- by
--   suffices : ∀ n, trunc n ((f ∘ g) ∘ h) = trunc n (f.comp (g ∘ h))
--   · ext m
--     specialize this m.succ
--     trans coeff R m (trunc m.succ ((f ∘ g) ∘ h))
--     · rw [Polynomial.coeff_coe, coeff_trunc, if_pos (lt.base m)]
--     · rw [this, Polynomial.coeff_coe, coeff_trunc, if_pos (lt.base m)]
--   intro n
--   have hgh : IsNilpotent (constantCoeff R (g ∘ h)) := IsNilpotent_constantCoeff_comp hg
--   obtain ⟨rg,hg⟩ := hg
--   obtain ⟨rh,hh⟩ := hh
--   obtain ⟨rgh,hgh⟩ := hgh
--   set N := (rg*rh).max (rh.max rgh) * n with hN
--   have hrh : rh * n ≤ N := sorry
--   have hrgh : rgh * n ≤ N := sorry
--   have hrgrh : rg * (rh * n) ≤ N := sorry 
--   rw [trunc_comp_cts hh]
--   rw [trunc_comp_cts hg hrgrh, trunc_comp_cts hgh hrgh, trunc_comp_cts hh hrh]
--   --rw [Polynomial.comp_assoc]
  
--   ext n
--   rw [coeff_comp_eq hh]
--   set Nf := max (rg * rh * (n+1)) (rgh * (n+1))
--   have : rgh * (n+1) ≤ Nf := le_max_right _ _
--   rw [coeff_comp_cts hgh this]
--   rw [coeff_comp_cts hh (by rfl)]
--   rw [←trunc_of_trunc_comp' hg]
--   rw [coe_comp]
--   sorry
--   sorry


-- TODO:
-- # ASK John about the best way of dealing with a finite sum with only one non-zero term.
lemma rescale_eq_comp_mul_X (f : R⟦X⟧) (r : R) :
  rescale r f = f.comp (r • X) :=
by
  have nilp : IsNilpotent <| constantCoeff R (r • X)
  · rw [smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]
    use 1
    rw [_root_.pow_one]
  set m := Exists.choose nilp with hm
  have hm' := Exists.choose_spec nilp
  rw [←hm] at hm'
  by_cases m = 0
  · case pos =>
    apply pow_zero_eq_zero
    rwa [h] at hm'
  · case neg =>
    ext n
    have : m*(n+1) ≠ 0
    · apply mul_ne_zero h (succ_ne_zero n)
    rw [coeff_rescale, coeff_comp_eq nilp, ←hm,
      eval₂_trunc_eq_sum_range]
    rw [map_sum, smul_eq_C_mul]
    simp_rw [mul_pow, ← mul_assoc]
    sorry


end PowerSeries