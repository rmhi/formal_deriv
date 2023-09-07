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




/--`f.hasComp g` states that the power series `g` may be substituted into
the power series `f = ∑ₙ fₙ * Xⁿ` to give a new power series, whose `d`-coefficient is

  `∑ₙ fₙ * coeff R d (g ^ n)`

For the composition to make sense, we require that each of these sums has finite support.
-/
def hasComp (f g : R⟦X⟧) : Prop :=
  ∀ d, ∃ N, ∀ n, N ≤ n → (coeff R n f) * coeff R d (g^n) = 0


/--Composition of power series.
If `f.hasComp g` then `f.comp g` is defined in the usual way. If not then `f.comp g`
is defined to be `0`.-/
noncomputable def comp (f g : R⟦X⟧) : R⟦X⟧ :=
  if h : f.hasComp g
  then mk (λ d ↦ coeff R d ((trunc (h d).choose f).eval₂ (C R) g ))
  else 0

scoped infixr:90 " ∘ "  => PowerSeries.comp


/-
Criteria for `hasComp`:
-/

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


lemma hasComp_of_constantCoeff_eq_zero {f g : R⟦X⟧} {hg : constantCoeff R g = 0} :
  f.hasComp g :=
by
  apply hasComp_of_isNilpotent_constantCoeff
  rw [hg]
  exact IsNilpotent.zero


lemma coe_hasComp {f : R[X]} {g : R⟦X⟧} :
  (f : R⟦X⟧).hasComp g :=
by
  intro d
  use f.natDegree + 1
  intro n hn
  rw [coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt, zero_mul]
  rw [←Nat.succ_le]
  exact hn


lemma add_hasComp {f₁ f₂ g : R⟦X⟧} (h₁ : f₁.hasComp g) (h₂ : f₂.hasComp g) :
  (f₁ + f₂).hasComp g :=
by
  intro d
  obtain ⟨N₁,hN₁⟩ := h₁ d
  obtain ⟨N₂,hN₂⟩ := h₂ d
  use max N₁ N₂
  intro n hn
  rw [map_add, add_mul, hN₁, hN₂, add_zero]
  exact le_of_max_le_right hn
  exact le_of_max_le_left hn
  
lemma mul_hasComp_aux {f g : R⟦X⟧} (hfg : f.hasComp g) (n : ℕ) :
  ∃ N: ℕ, ∀ d m : ℕ, d ≤ n → N ≤ m → (coeff R m f) * coeff R d (g ^ m) = 0 :=
by
  induction n with
  | zero =>
    use (hfg 0).choose
    intro d m hd hm
    rw [zero_eq, nonpos_iff_eq_zero] at hd
    rw [hd]
    apply (hfg 0).choose_spec
    exact hm
  | succ n ih =>
    obtain ⟨N₁, hN₁⟩ := ih
    obtain ⟨N₂, hN₂⟩ := hfg n.succ
    use max N₁ N₂
    intro d m hd hm
    have : d ≤ n ∨ d = n.succ := le_or_eq_of_le_succ hd
    cases this with
    | inl h =>
      apply hN₁
      exact h
      exact le_of_max_le_left hm
    | inr h =>
      rw [h]
      apply hN₂
      exact le_of_max_le_right hm




lemma mul_hasComp {f₁ f₂ g : R⟦X⟧} (h₁ : f₁.hasComp g) (h₂ : f₂.hasComp g) :
  (f₁ * f₂).hasComp g :=
by
  intro d
  obtain ⟨N₁,hN₁⟩ := mul_hasComp_aux h₁ d
  obtain ⟨N₂,hN₂⟩ := mul_hasComp_aux h₂ d
  use N₁ + N₂
  intro m hm
  rw [coeff_mul, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro ⟨i,j⟩ hij
  rw [Finset.Nat.mem_antidiagonal] at hij
  dsimp at hij ⊢
  rw [←hij, pow_add, coeff_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro ⟨r,s⟩ hrs
  rw [Finset.Nat.mem_antidiagonal] at hrs
  dsimp at hrs ⊢
  rw [mul_assoc, mul_comm (coeff R j f₂), mul_assoc, ←mul_assoc]
  rw [←hij] at hm
  have := le_or_le_of_add_le_add hm
  cases this with
  | inl h =>
    apply mul_eq_zero_of_left
    apply hN₁
    rw [←hrs]
    apply le_self_add
    exact h
  | inr h =>
    apply mul_eq_zero_of_right
    rw [mul_comm]
    apply hN₂
    rw [←hrs]
    apply le_add_self
    exact h


theorem hasComp_trans {f g h : R⟦X⟧} (hfg : f.hasComp g) (hgh : g.hasComp h) :
  f.hasComp h :=
by
  sorry



/-
Some lemmas allowing us to calculate the compositions.
-/


theorem comp_eq {f g : R⟦X⟧} (h : f.hasComp g) :
  (f ∘ g : R⟦X⟧) = mk λ n ↦ coeff R n ((trunc (h n).choose f).eval₂ (C R) g) :=
by
  rw [comp, dif_pos h]

lemma comp_eq_zero {f g : R⟦X⟧} (h : ¬(f.hasComp g)) :
  f ∘ g = 0 :=
by
  rw [comp, dif_neg h]

lemma coeff_comp {f g : R⟦X⟧} (h : f.hasComp g) :
  coeff R n (f ∘ g) = coeff R n ((trunc (h n).choose f).eval₂ (C R) g) :=
by
  rw [comp, dif_pos h, coeff_mk]

lemma coeff_comp_cts {n d : ℕ} {f g : R⟦X⟧} {h : f.hasComp g} (hn : (h d).choose ≤ n := by rfl) :
  coeff R d (f ∘ g) = coeff R d ((trunc n f).eval₂ (C R) g) :=
by
  induction hn with
  | refl => apply coeff_comp
  | step ih1 ih2 =>
    rw [trunc_succ, eval₂_add, map_add, ih2, eval₂_monomial, coeff_C_mul,
      (h d).choose_spec, add_zero]
    exact ih1

lemma coeff_comp_eq_aux {n N M : ℕ} {f g : R⟦X⟧}
  (hN : ∀ m, N ≤ m → coeff R m f * coeff R n (g^m) = 0) (hM : N ≤ M):
  coeff R n ((trunc M f).eval₂ (C R) g) = coeff R n ((trunc N f).eval₂ (C R) g) :=
by
  induction hM with
  | refl => rfl
  | step ih1 ih2 =>
    rw [trunc_succ, eval₂_add, eval₂_monomial, map_add, coeff_C_mul, ih2, hN _ ih1, add_zero]


lemma coeff_comp_of_stable {n N : ℕ} {f g : R⟦X⟧} (h : f.hasComp g)
  (hN : ∀ m, N ≤ m → coeff R m f * coeff R n (g^m) = 0) :
  coeff R n (f ∘ g) = coeff R n ((trunc N f).eval₂ (C R) g) :=
by
  by_cases h' : N ≤ (h n).choose
  · rw [coeff_comp]
    apply coeff_comp_eq_aux hN h'
  · rw [not_le] at h'
    apply coeff_comp_cts
    apply le_of_lt h'


theorem coe_comp {f : R[X]} {g : R⟦X⟧} :
  ((f:R⟦X⟧) ∘ g) = f.eval₂ (C R) g :=
by
  ext n
  have := trunc_coe_eq_self f.natDegree.lt_succ_self
  nth_rw 3 [←this]
  apply coeff_comp_of_stable coe_hasComp
  intro m hm
  rw [succ_le] at hm
  apply mul_eq_zero_of_left
  rw [coeff_coe]
  apply coeff_eq_zero_of_natDegree_lt hm



theorem coeff_comp_of_constantCoeff_eq_zero {f g : R⟦X⟧} (h : constantCoeff R g = 0 ) :
  coeff R n (f ∘ g) = coeff R n ((trunc (n+1) f).eval₂ (C R) g) :=
by
  apply coeff_comp_of_stable
  apply hasComp_of_constantCoeff_eq_zero
  exact h
  intro m hm
  rw [succ_le] at hm
  apply mul_eq_zero_of_right
  have : X^m ∣ g^m
  · apply pow_dvd_pow_of_dvd
    rw [PowerSeries.X_dvd_iff, h]
  rw [X_pow_dvd_iff] at this
  apply this
  exact hm

theorem constantCoeff_comp {f g : R⟦X⟧} (h : constantCoeff R g = 0 ) :
  constantCoeff R (f ∘ g) = constantCoeff R f :=
by
  rw [←coeff_zero_eq_constantCoeff, coeff_comp_of_constantCoeff_eq_zero h,
    zero_add, eval₂_trunc_eq_sum_range, Finset.sum_range_one,
    _root_.pow_zero, mul_one, coeff_zero_C]



lemma coeff_comp_of_stable' {n N : ℕ} {f g : R⟦X⟧} (h : f.hasComp g)
  (hN : ∀ m, N ≤ m → coeff R m f * coeff R n (g^m) = 0) :
  coeff R n (f ∘ g) = coeff R n ((trunc N f) ∘ g) :=
by
  rw [coeff_comp_of_stable h hN, coe_comp]



lemma coeff_comp_cts' {n d : ℕ} {f g : R⟦X⟧} {h : f.hasComp g}
  (hn : (h d).choose ≤ n := by rfl) :
  coeff R d (f ∘ g) = coeff R d ((trunc n f) ∘ g) :=
by
  rw [coeff_comp_cts hn, coe_comp]


lemma coeff_comp_stable {f g : R⟦X⟧} (h : f.hasComp g) (d : ℕ) :
  ∃ N, ∀ n, N ≤ n → coeff R d (f ∘ g) = coeff R d ((trunc n f) ∘ g) :=
by
  use (h d).choose
  intro n hn
  apply coeff_comp_cts' hn

lemma trunc_comp_stable_old {f g : R⟦X⟧} (hfg : hasComp f g) (d : ℕ) :
  ∃ N, ∀ n, N ≤ n → trunc d (f ∘ g) = trunc d ( (trunc n f: R⟦X⟧) ∘ g) :=
by
  obtain ⟨N, hN⟩ := mul_hasComp_aux hfg d
  use N
  intro n hn
  ext m
  rw [coeff_trunc, coeff_trunc]
  split
  · induction hn with
    | refl =>
      apply coeff_comp_of_stable' hfg
      intro r
      apply hN
      apply le_of_lt
      assumption      
    | step hm ih =>
      rw [coe_comp, trunc_succ, eval₂_add, map_add, eval₂_monomial, coeff_C_mul, hN, add_zero, ih, coe_comp]
      apply le_of_lt
      assumption
      assumption
  rfl

theorem trunc_comp_stable {f g : R⟦X⟧}  (hfg : f.hasComp g) (d : ℕ):
  ∃ N, ∀ M, N ≤ M → trunc d (f ∘ g) = trunc d ( (trunc M f).eval₂ (C R) g ) :=
by
  simp_rw [←coe_comp]
  apply trunc_comp_stable_old hfg




private lemma coe_mul_coe_comp (f g : R[X]) (h : R⟦X⟧) :
  (f * g : R⟦X⟧) ∘ h = (f:R⟦X⟧) ∘ h * (g : R⟦X⟧) ∘ h :=
by
  rw [coe_comp, coe_comp, ←coe_mul, coe_comp, eval₂_mul]


/--This is the tricky key lemma is proving mul_comp.-/
private theorem coeff_mul_comp_stable {f g h : R⟦X⟧} (hf :f.hasComp h)
  (hg : g.hasComp h) (d : ℕ) :
  ∃ N , ∀ M, N ≤ M →
  coeff R d ( (f * g) ∘ h) = coeff R d ( ((trunc M f) * (trunc M g)) ∘ h ) :=
by
  have hfg := mul_hasComp hf hg
  obtain ⟨Nf,hNf⟩ := mul_hasComp_aux hf d
  obtain ⟨Ng,hNg⟩ := mul_hasComp_aux hg d
  obtain ⟨Nfg, hNfg⟩ := mul_hasComp_aux hfg d
  use max (Nf + Ng) Nfg
  intro M hM
  trans coeff R d ((trunc M (f * g)) ∘ h)
  · apply coeff_comp_of_stable' hfg
    intro m hm
    apply hNfg
    rfl
    trans M
    apply le_of_max_le_right hM
    exact hm
  · rw [←trunc_trunc_mul_trunc]
    symm
    apply coeff_comp_of_stable'
    rw [←coe_mul]
    apply coe_hasComp
    intro m hm
    rw [coeff_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro ⟨i,j⟩ hij
    rw [Finset.Nat.mem_antidiagonal] at hij
    dsimp at hij ⊢
    rw [←hij, pow_add, coeff_mul, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro ⟨r,s⟩ hrs
    rw [Finset.Nat.mem_antidiagonal] at hrs
    dsimp at hrs ⊢
    rw [mul_assoc, mul_comm (coeff R j _), mul_assoc, ←mul_assoc]
    have : Nf+Ng ≤ i+j
    · rw [hij]
      trans M
      apply le_of_max_le_left hM
      exact hm
    have := le_or_le_of_add_le_add this
    cases this
    · apply mul_eq_zero_of_left
      rw [coeff_coe, coeff_trunc]
      split
      · apply hNf
        rw [←hrs]
        apply le_self_add
        assumption
      · rw [zero_mul]
    · apply mul_eq_zero_of_right
      rw [mul_comm, coeff_coe, coeff_trunc]
      split
      · apply hNg
        rw [←hrs]
        apply le_add_self
        assumption
      · rw [zero_mul]

@[simp]
theorem mul_comp (f g h : R⟦X⟧) (hf : f.hasComp h) (hg : g.hasComp h) :
  ((f * g) ∘ h : R⟦X⟧) = (f ∘ h : R⟦X⟧) * (g ∘ h : R⟦X⟧) :=
by
  ext d
  obtain ⟨Nfg,hNfg⟩ := coeff_mul_comp_stable hf hg d
  have hN_mul := coeff_mul_stable d (f := f ∘ h) (g := g ∘ h) d.succ (by rfl)
  rw [hN_mul]
  obtain ⟨Nf,hNf⟩ := trunc_comp_stable_old hf d.succ
  obtain ⟨Ng,hNg⟩ := trunc_comp_stable_old hg d.succ
  set N := Nfg.max (Nf.max Ng)
  rw [hNf N]
  rw [hNg N]
  rw [hNfg N]
  symm
  rw [coeff_stable (by rfl)]
  rw [trunc_trunc_mul_trunc, ←coe_mul_coe_comp]
  rw [←coeff_stable (by rfl)]
  apply le_max_left
  trans max Nf Ng
  apply le_max_right
  apply le_max_right
  trans max Nf Ng
  apply le_max_left
  apply le_max_right

@[simp]
theorem add_comp {f g h : R⟦X⟧} (hf : f.hasComp h) (hg : g.hasComp h) :
  ((f + g) ∘ h : R⟦X⟧) = (f ∘ h : R⟦X⟧) + (g ∘ h : R⟦X⟧) :=
by
  have hfg := add_hasComp hf hg
  ext d
  obtain ⟨Nf,hNf⟩ := coeff_comp_stable hf d
  obtain ⟨Ng,hNg⟩ := coeff_comp_stable hg d
  obtain ⟨Nfg,hNfg⟩ := coeff_comp_stable hfg d
  set N := max (max Nf Ng) Nfg
  rw [map_add, hNf N, hNg N, hNfg N, coe_comp, coe_comp, coe_comp,
    trunc_add, eval₂_add, map_add]
  apply le_max_right
  apply le_max_of_le_left
  apply le_max_right
  apply le_max_of_le_left
  apply le_max_left


@[simp]
theorem one_comp {f : R⟦X⟧} : (1 ∘ f : R⟦X⟧) = 1 :=
by
  rw [←coe_one, coe_comp, eval₂_one, coe_one]


@[simp]
theorem comp_zero (f : R⟦X⟧) : f ∘ 0 = C R (constantCoeff R f) :=
by
  have h : f.hasComp 0
  · apply hasComp_of_constantCoeff_eq_zero
    rw [map_zero]
  ext n
  rw [coeff_comp_of_constantCoeff_eq_zero (by rw [map_zero]),
    eval₂_at_zero, coeff_trunc,
    coeff_zero_eq_constantCoeff, coeff_C]
  split_ifs with h₁ h₂
  · rw [h₁, coeff_zero_eq_constantCoeff, constantCoeff_C]
  · exfalso
    apply h₂
    apply zero_lt_succ
  · rw [coeff_C, if_neg h₁]


lemma C_comp {f : R⟦X⟧} (a : R) :
  (C R a) ∘ f = C R a :=
by
  rw [←Polynomial.coe_C, coe_comp, eval₂_C, Polynomial.coe_C]


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
    · rw [←mul_comp, PowerSeries.inv_mul_cancel (h := hf), one_comp]
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