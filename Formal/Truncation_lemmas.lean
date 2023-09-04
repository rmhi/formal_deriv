/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib.RingTheory.PowerSeries.Basic


/-
Some lemma about truncations of power series.
-/


namespace PowerSeries 

open Polynomial Nat

variable {R : Type u} [CommSemiring R]
scoped notation:9000 R "⟦X⟧" => PowerSeries R

theorem trunc_trunc_of_le (f : R⟦X⟧) {n m : ℕ} (hnm : n ≤ m) :
  trunc n ↑(trunc m f) = trunc n f :=
by
  ext d
  rw [coeff_trunc, coeff_trunc, Polynomial.coeff_coe]
  split_ifs with h
  · have : d < m := lt_of_lt_of_le h hnm
    rw [coeff_trunc, if_pos this]
  · rfl

@[simp]
theorem trunc_trunc (f : R⟦X⟧) {n : ℕ} : trunc n ↑(trunc n f) = trunc n f :=
by
  exact trunc_trunc_of_le f (by rfl)

@[simp]
theorem trunc_trunc_mul (f g : R ⟦X⟧) (n : ℕ) :
  trunc n ( (trunc n f) * g : R⟦X⟧ ) = trunc n ( f * g ) :=
by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, Finset.sum_congr rfl]
    rintro ⟨a, b⟩ hab
    have ha : a < n := lt_of_le_of_lt (Finset.Nat.antidiagonal.fst_le hab) h
    rw [Polynomial.coeff_coe, coeff_trunc, if_pos ha]
  · rfl

@[simp]
theorem trunc_mul_trunc (f g : R ⟦X⟧) (n : ℕ) :
  trunc n ( f * (trunc n g) : R⟦X⟧ ) = trunc n ( f * g ) :=
by
  rw [mul_comm, trunc_trunc_mul, mul_comm]

@[simp]
theorem trunc_trunc_mul_trunc (f g : R⟦X⟧) (n : ℕ) :
  trunc n (trunc n f * trunc n g : R⟦X⟧) = trunc n (f * g) :=
by
  rw [trunc_trunc_mul, trunc_mul_trunc]

@[simp]
theorem trunc_trunc_pow (f : R⟦X⟧) (n a : ℕ) :
  trunc n ((trunc n f) ^ a) = trunc n (f ^ a) :=
by
  induction a with
  | zero =>
    rw [_root_.pow_zero, _root_.pow_zero, Polynomial.coe_one]
  | succ a ih =>
    rw [_root_.pow_succ, _root_.pow_succ, Polynomial.coe_mul, Polynomial.coe_pow,
      trunc_trunc_mul, ←trunc_trunc_mul_trunc, ←Polynomial.coe_pow, ih,
      trunc_trunc_mul_trunc]

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
  rw [trunc, sum_eq_of_subset (hs := this), Finset.sum_congr rfl]
  · intros
    rw [Polynomial.coeff_coe]
  · intros
    apply monomial_zero_right

theorem trunc_succ (f : R⟦X⟧) (n : ℕ) :
  trunc n.succ f = trunc n f + Polynomial.monomial n (coeff R n f) :=
by
  rw [trunc, Ico_zero_eq_range, Finset.sum_range_succ, trunc, Ico_zero_eq_range]


/-- The function `coeff n : R⟦X⟧ → R` is continuous. I.e. `coeff n f` depends only on a sufficiently
long truncation of the power series `f`.-/
theorem coeff_cts (f : R⟦X⟧) {n m : ℕ} (h : n < m) : coeff R n f = coeff R n (trunc m f) :=
by
  rw [Polynomial.coeff_coe, coeff_trunc, if_pos h]

/-- The `n`-th coefficient of a`f*g` may be calculated 
from the truncations of `f` and `g`.-/
theorem coeff_mul_cts (f g : R⟦X⟧) {n a b : ℕ} (ha : n < a) (hb : n < b) :
  coeff R n (f * g) = coeff R n (trunc a f * trunc b g) :=
by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨x,y⟩ hxy
  have hx : x ≤ n := Finset.Nat.antidiagonal.fst_le hxy
  have hy : y ≤ n := Finset.Nat.antidiagonal.snd_le hxy
  congr 1 <;> apply coeff_cts
  · exact lt_of_le_of_lt hx ha
  · exact lt_of_le_of_lt hy hb

end PowerSeries