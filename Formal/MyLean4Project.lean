--import Mathlib.Tactic
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Basic

set_option profiler true
open PowerSeries Nat

open scoped Classical

-- open_locale big_operators
section CommutativeSemiring

variable {R : Type} [CommSemiring R]

-- derivarions are defined only in the case that the base is a `comm_semiring`.
local notation "pow" => PowerSeries R

local notation "poly" => Polynomial R

local notation "coeff" => coeff R

--# ASK : is there a way of speeding up elaboration in this proof? Currentlt 1.39s.
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
theorem Derivation.polynomial_eval₂ (A : Type) [CommSemiring A] [Algebra R A]
  (M : Type) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  (d : Derivation R A M) (f : poly) (g : A) :
  d (f.eval₂ (algebraMap R A) g) = f.derivative.eval₂ (algebraMap R A) g • d g :=
by
  rw [Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_range_succ',
    Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    zero_nsmul, smul_zero, smul_zero, zero_add, add_zero]
  by_cases f.natDegree = 0
  · rw [h, Finset.sum_range_zero, Polynomial.derivative_of_natDegree_zero h,
      Polynomial.eval₂_zero, zero_smul]
  · have : f.derivative.natDegree < f.natDegree := Polynomial.natDegree_derivative_lt h
    rw [Polynomial.eval₂_eq_sum_range' (algebraMap R A) this, Finset.sum_smul]
    apply Finset.sum_congr; rfl
    intro n _
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap, smul_zero, add_zero,
      add_tsub_cancel_right, Polynomial.coeff_derivative, map_mul, IsScalarTower.algebraMap_smul,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, one_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, one_mul,
      smul_assoc, smul_assoc, ←cast_succ, ← nsmul_eq_smul_cast]
#align derivation.polynomial_eval₂ Derivation.polynomial_eval₂

namespace PowerSeries

--# ASK : how do I replace this simp with a rw?
theorem coeff_cts (f : pow) {n m : ℕ} (h : n < m) : coeff n f = coeff n (trunc m f) := by
  rw [Polynomial.coeff_coe, coeff_trunc, if_pos h]
#align power_series.coeff_cts PowerSeries.coeff_cts

--# ASK elaboration:1.44s. How do I improve this? -- solved (replace linarith).
/-- The `n`-th coefficient of a`f*g` may be calculated 
from the truncations of `f` and `g`.-/
theorem coeff_mul_cts (f g : pow) {n a b : ℕ} (ha : n < a) (hb : n < b) :
    coeff n (f * g) = coeff n (trunc a f * trunc b g) :=
  by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr
  rfl
  intro x hx
  have h_xfst : x.fst ≤ n := Finset.Nat.antidiagonal.fst_le hx
  have h_xsnd : x.snd ≤ n := Finset.Nat.antidiagonal.snd_le hx
  congr 1 <;> apply coeff_cts
  exact lt_of_le_of_lt h_xfst ha
  exact lt_of_le_of_lt h_xsnd hb
#align power_series.coeff_mul_cts PowerSeries.coeff_mul_cts

/-- The formal derivative of a power series in one variable.-/
noncomputable def derivative : pow → pow := λ f => mk (λ n => coeff (n + 1) f * (n + 1))
#align power_series.derivative PowerSeries.derivative

theorem coeff_derivative (f : pow) (n : ℕ) : coeff n f.derivative = coeff (n + 1) f * (n + 1) := by
  rw [derivative, coeff_mk]
#align power_series.coeff_derivative PowerSeries.coeff_derivative

theorem derivative_coe (f : poly) : (f : pow).derivative = Polynomial.derivative f :=
  by
  ext
  rw [coeff_derivative, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_derivative]
#align power_series.derivative_coe PowerSeries.derivative_coe

-- # ASK:
-- why does it slow down the elaboration when I give more
-- information here (eg. entering the arguments of coeff_derivative).
theorem derivative_add (f g : pow) : derivative (f + g) = derivative f + derivative g :=
  by
  ext
  rw [coeff_derivative, map_add, map_add, coeff_derivative, coeff_derivative, add_mul]
#align power_series.derivative_add PowerSeries.derivative_add

theorem derivative_C (r : R) : derivative (C R r) = 0 :=
by
  ext n
  rw [coeff_derivative, coeff_C]
  split_ifs with h
  exfalso
  apply succ_ne_zero n h
  rw [MulZeroClass.zero_mul]
  rfl
--#align power_series.derivative_C PowerSeries.derivative_C

theorem trunc_deriv (f : pow) (n : ℕ) :
    (trunc n f.derivative : pow) = derivative ↑(trunc (n + 1) f) :=
  by
  ext d
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ_iff.2 h
    simp only [coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_coe, coeff_trunc,
      this, if_true]
  -- # ASK : what sequence of rewrites would do this?
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    simp only [coeff_derivative, Polynomial.coeff_coe, coeff_trunc, this, if_false,
      MulZeroClass.zero_mul]
#align power_series.trunc_deriv PowerSeries.trunc_deriv

-- # same question here.
--A special case of the next theorem, used in its proof.
private theorem derivative_coe_mul_coe (f g : poly) :
    derivative (f * g : pow) = derivative (f : pow) * g + f * derivative (g : pow) := by
  rw [← Polynomial.coe_mul, derivative_coe, derivative_coe, derivative_coe,
    Polynomial.derivative_mul, ← Polynomial.coe_mul, ← Polynomial.coe_mul, Polynomial.coe_add]

--# elaboration 246ms.
/-- Leibniz rule for formal power series.-/
theorem derivative_mul (f g : pow) : derivative (f * g) = f.derivative * g + f * g.derivative :=
  by
  ext n
  have h0 : n + 1 < n + 1 + 1 := lt_succ_self (n + 1)
  have h1 : n < n + 1 := lt_succ_self n
  have h2 : n < n + 1 + 1 := lt_of_lt_of_le h1 (le_of_lt h0)
  rw [coeff_derivative, map_add, coeff_mul_cts f g h0 h0, coeff_mul_cts f.derivative g h1 h2,
    coeff_mul_cts f g.derivative h2 h1, trunc_deriv, trunc_deriv, ← map_add, ←
    derivative_coe_mul_coe, coeff_derivative]
#align power_series.derivative_mul PowerSeries.derivative_mul

theorem derivative_one : derivative (1 : pow) = 0 :=
by
  rw [← derivative_C (1 : R), map_one (C R)]
#align power_series.derivative_one PowerSeries.derivative_one

theorem derivative_smul (r : R) (f : pow) : derivative (r • f) = r • derivative f := by
  rw [smul_eq_C_mul f r, smul_eq_C_mul f.derivative r, derivative_mul, derivative_C,
    MulZeroClass.zero_mul, zero_add]
#align power_series.derivative_smul PowerSeries.derivative_smul

--# much slower using dsimp.
noncomputable def D : Derivation R pow pow
    where
  toFun := derivative
  map_add' := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' a b :=
    by
      dsimp
      rw [mul_comm b, add_comm]
      exact derivative_mul a b
    -- rw [LinearMap.coe_mk, Algebra.id.smul_eq_mul]
    -- rw [Algebra.id.smul_eq_mul]
    -- rw [derivative_mul, add_comm,
    --   mul_comm b]
--#align power_series.D PowerSeries.D

local notation "D" => @D R _

@[simp]
theorem D_mul (f g : pow) : D (f * g) = D f * g + f * D g :=
  derivative_mul f g
-- #align power_series.D_mul PowerSeries.D_mul

@[simp]
theorem D_one : D (1 : pow) = 0 :=
  derivative_one
-- #align power_series.D_one PowerSeries.D_one

@[simp]
theorem coeff_D (f : pow) (n : ℕ) : coeff n (D f) = coeff (n + 1) f * (n + 1) :=
  coeff_derivative f n
-- #align power_series.coeff_D PowerSeries.coeff_D

@[simp]
theorem D_poly (f : poly) : (f : pow).derivative = Polynomial.derivative f :=
  derivative_coe f
-- #align power_series.D_poly PowerSeries.D_poly

@[simp]
theorem D_X : D (X : pow) = 1 := by
  ext
  rw [coeff_D, coeff_one, coeff_X, boole_mul]
  -- add_left_eq_self],
  simp_rw [add_left_eq_self]
  split_ifs with h
  rw [h, cast_zero, zero_add]
  rfl
-- #align power_series.D_X PowerSeries.D_X

-- # ASK: why is this slow?
theorem trunc_D (f : pow) (n : ℕ) : trunc n (D f) = Polynomial.derivative (trunc (n + 1) f) :=
  by
  have := trunc_deriv f n
  rw [derivative_coe] at this 
  exact_mod_cast this
-- #align power_series.trunc_D PowerSeries.trunc_D

theorem trunc_succ (f : pow) (n : ℕ) :
    trunc n.succ f = trunc n f + Polynomial.monomial n (coeff n f) :=
  by
  rw [trunc, Ico_zero_eq_range, Finset.sum_range_succ, trunc, Ico_zero_eq_range]
#align power_series.trunc_succ PowerSeries.trunc_succ

theorem D_poly_comp (f : poly) (g : pow) : D (f.eval₂ (C R) g) = f.derivative.eval₂ (C R) g * D g :=
  Derivation.polynomial_eval₂ pow pow D f g
-- #align power_series.D_poly_comp PowerSeries.D

noncomputable def comp : pow → pow → pow := λ f g =>
  if constantCoeff R g = 0 then mk λ n => coeff n ((trunc n.succ f).eval₂ (C R) g)
  else 0
#align power_series.comp PowerSeries.comp

theorem coeff_comp_eq' (f g : pow) (n : ℕ) :
  coeff n (f.comp g) = if constantCoeff R g = 0
                        then coeff n ((trunc n.succ f).eval₂ (C R) g)
                        else 0 :=
by
  rw [comp]
  split_ifs with h
  rw [if_pos h, coeff_mk]
  rw [if_neg h, map_zero]
#align power_series.coeff_comp_eq' PowerSeries.coeff_comp_eq'

theorem coeff_comp_eq {f g : pow} {n : ℕ} (hg : constantCoeff R g = 0) :
    coeff n (f.comp g) = coeff n ((trunc n.succ f).eval₂ (C R) g) := by
  rw [coeff_comp_eq', hg, eq_self_iff_true, if_true]
#align power_series.coeff_comp_eq PowerSeries.coeff_comp_eq

theorem coeff_comp_eq_zero {f g : pow} {n : ℕ} (hg : ¬constantCoeff R g = 0) :
    coeff n (f.comp g) = 0 := by simp only [coeff_comp_eq', hg, if_false]
#align power_series.coeff_comp_eq_zero PowerSeries.coeff_comp_eq_zero

private theorem coeff_pow_eq_zero {g : pow} (hg : constantCoeff R g = 0) {n a : ℕ} :
    n < a → coeff n (g ^ a) = 0 := by
  intro ha
  apply coeff_of_lt_order
  rw [← X_dvd_iff] at hg 
  have : X ^ a ∣ g ^ a := pow_dvd_pow_of_dvd hg a
  rw [order_eq_multiplicity_X]
  have : ↑a ≤ multiplicity X (g^a) := multiplicity.le_multiplicity_of_pow_dvd this
  apply lt_of_lt_of_le _ this
  rw [PartENat.coe_lt_coe]
  exact ha


/-- (Technical Lemma)
The if `n<a` then the `n`-th coefficient of `f.comp g` may be
calculated using the `a`-th truncation of `f`.
-/
theorem coeff_comp_cts {f g : pow} (h : constantCoeff R g = 0) {n a : ℕ} :
    n < a → coeff n (f.comp g) = coeff n ((trunc a f).eval₂ (C R) g) :=
by
  apply le_induction
  · rw [coeff_comp_eq h]
  intro a ha ih
  rw [trunc_succ, Polynomial.eval₂_add, map_add, ih, Polynomial.eval₂_monomial, coeff_C_mul]
  suffices coeff n (g ^ a) = 0 by rw [this, MulZeroClass.mul_zero, add_zero]
  exact coeff_pow_eq_zero h ha
#align power_series.coeff_comp_cts PowerSeries.coeff_comp_cts

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
    rw [coeff_D, coeff_comp_eq h, ← coeff_D, D_poly_comp, coeff_mul, coeff_mul, Finset.sum_congr]
    · rfl
    intro x hx
    rw [Finset.Nat.mem_antidiagonal] at hx 
    have : x.fst < n + 1 := lt_succ_of_le (le.intro hx)
    rw [coeff_comp_cts h this, ← trunc_D]
  · simp only [comp, MulZeroClass.zero_mul, if_false, h, map_zero _]
-- #align power_series.D_comp PowerSeries.D_comp



@[simp] theorem D_C (r : R) : D ( C R r ) = 0 :=
  derivative_C r
-- #align power_series.D_coe PowerSeries.D_C

@[simp] theorem D_smul (a : R) (f : pow) : D (a • f) = a • D f :=
by
  rw [smul_eq_C_mul, smul_eq_C_mul]
  rw [D_mul, D_C, MulZeroClass.zero_mul, zero_add _]
-- #align power_series.D_coe_mul PowerSeries.D_smul

/-
The following are a few more results concering composition of
power series.
We show that composition is associative,
`X` is a 2-sided identity.
a.rescale f = f.comp (a*X)
-/
theorem natDegree_trunc_lt (f : pow) (n : ℕ) : (trunc (n + 1) f).natDegree < n + 1 :=
by
  apply lt_succ_of_le
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_trunc]
  split_ifs with h
  · exfalso
    linarith [h, hm]
  · rfl
#align power_series.nat_degree_trunc_lt PowerSeries.natDegree_trunc_lt

theorem constantCoeff_comp {f g : pow} (h : constantCoeff R g = 0) :
  constantCoeff R (f.comp g) = constantCoeff R f :=
by
  have : (trunc 1 f).natDegree < 1 := natDegree_trunc_lt f 0
  rw [← coeff_zero_eq_constantCoeff, coeff_comp_eq h,
    Polynomial.eval₂_eq_sum_range' (C R) this,
    Finset.sum_range_one, _root_.pow_zero, mul_one, coeff_zero_C, coeff_trunc]
  simp_rw [lt_one_iff, eq_self_iff_true, if_true]
  done
#align power_series.constant_coeff_comp PowerSeries.constantCoeff_comp


lemma comp_assoc (f g h:pow) (hh : constantCoeff R h = 0):
  (f.comp g).comp h = f.comp (g.comp h) :=
by
  by_cases hg : constantCoeff R g = 0
  · ext n
    rw [coeff_comp_eq hh]
    sorry
  rw [comp, if_pos hh, comp, if_neg hg, comp, constantCoeff_comp hh,
    comp, if_pos hh, if_neg hg]
  simp_rw [trunc_zero]
  rw [Polynomial.eval₂_zero]
  rfl
  done



@[simp]
theorem trunc_trunc (f : pow) {n : ℕ} : trunc n ↑(trunc n f) = trunc n f :=
by
  ext m : 1 
  rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_trunc, if_pos h, Polynomial.coeff_coe, coeff_trunc, if_pos h]
  · rw [coeff_trunc, if_neg h]
#align power_series.trunc_trunc PowerSeries.trunc_trunc

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
    simp only [Polynomial.coeff_coe, coeff_trunc, ha, hb, if_true]
  · rfl
#align power_series.trunc_trunc_mul_trunc PowerSeries.trunc_trunc_mul_trunc

theorem trunc_coe_eq_self {f : poly} {n : ℕ} (hn : n > f.natDegree) : trunc n (f : pow) = f :=
  by
  induction' hn with m hm ih
  · ext a
    rw [coeff_trunc]
    split_ifs with h
    exact Polynomial.coeff_coe _ _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    rwa [not_lt, succ_le_iff] at h 
  · rw [trunc_succ, ih, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hm, map_zero,
      add_zero]
#align power_series.trunc_coe_eq_self PowerSeries.trunc_coe_eq_self

theorem coe_comp {f : poly} {g : pow} (hg : constantCoeff R g = 0) :
    (f : pow).comp g = f.eval₂ (C R) g := by
  ext n
  by_cases n < f.natDegree + 1
  rw [coeff_comp_cts hg h, trunc_coe_eq_self]
  exact lt_succ_self _
  rw [coeff_comp_eq hg, trunc_coe_eq_self]
  rw [succ_eq_add_one]
  linarith [h]
#align power_series.coe_comp PowerSeries.coe_comp

theorem trunc_of_trunc_comp {f g : pow} {n : ℕ} (hg : constantCoeff R g = 0) :
    trunc n ((trunc n f : pow).comp g) = trunc n (f.comp g) :=
  by
  ext m
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  rw [coeff_comp_cts hg h, coeff_comp_cts hg h, trunc_trunc]
  rfl
#align power_series.trunc_of_trunc_comp PowerSeries.trunc_of_trunc_comp

@[simp]
theorem mul_comp (f g h : pow) : (f * g).comp h = f.comp h * g.comp h :=
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
      _ = coeff n (f.comp h * g.comp h) := by nth_rw 1 [←coeff_mul_cts _ _ hn hn]
  · rw [comp, if_neg hh, comp, if_neg hh, MulZeroClass.zero_mul]
#align power_series.mul_comp PowerSeries.mul_comp

@[simp]
theorem add_comp (f g h : pow) : (f + g).comp h = f.comp h + g.comp h :=
  by
  by_cases hh : constantCoeff R h = 0
  ext
  rw [coeff_comp_eq hh, trunc_add, Polynomial.eval₂_add, map_add, map_add, coeff_comp_eq hh,
    coeff_comp_eq hh]
  simp only [comp, hh, if_false, add_zero]
#align power_series.add_comp PowerSeries.add_comp

@[simp]
theorem one_comp {f : pow} (hf : constantCoeff R f = 0) : (1 : pow).comp f = 1 :=
  by
  ext
  rw [coeff_comp_eq hf, succ_eq_add_one, trunc_one, Polynomial.eval₂_one]
#align power_series.one_comp PowerSeries.one_comp

@[simp]
theorem comp_zero (f : pow) : f.comp 0 = C R (constantCoeff R f) :=
  by
  ext n
  have : constantCoeff R (0 : pow) = 0 := map_zero _
  rw [coeff_comp_eq this, Polynomial.eval₂_at_zero, coeff_trunc,
    coeff_zero_eq_constantCoeff, coeff_C]
  split_ifs with h₁ h₂
  rw [h₁, coeff_zero_eq_constantCoeff]
  rfl
  cases h₂ (zero_lt_succ n)
  rw [coeff_C, if_neg h₁]
#align power_series.comp_zero PowerSeries.comp_zero

/-NOTE: `instance : has_inv power_series R` is currently only defined
when `R` is a field.  -/
@[simp]
theorem inv_comp {R : Type} [Field R] (f g : PowerSeries R) (hf : constantCoeff R f ≠ 0) :
    f⁻¹.comp g = (f.comp g)⁻¹ := by
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
#align power_series.inv_comp PowerSeries.inv_comp


theorem _root_.Polynomial.eval₂_X_eq_coe (f : poly) : f.eval₂ (C R) X = ↑f :=
  by
  nth_rw 2 [(@Polynomial.eval₂_C_X R _ f).symm]
  let d := f.natDegree.succ
  have : f.natDegree < d
  · simp
  rw [Polynomial.eval₂_eq_sum_range' (C R) this,
    Polynomial.eval₂_eq_sum_range' Polynomial.C this,
  ]
  induction' d with d hd
  · rw [Finset.sum_range_zero, Finset.sum_range_zero, Polynomial.coe_zero]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, hd,
      Polynomial.coe_add]
    simp
-- #align polynomial.eval₂_X_eq_coe Polynomial.eval₂_X_eq_coe

@[simp]
theorem comp_x (f : pow) : f.comp X = f := by
  ext n
  rw [coeff_comp_eq (@constantCoeff_X R _), Polynomial.eval₂_X_eq_coe, ← coeff_cts]
  exact lt_succ_self n
-- #align power_series.comp_X PowerSeries.comp_x

@[simp]
theorem trunc_X {n : ℕ} : trunc (n + 2) X = (Polynomial.X : poly) :=
  by
  ext d
  rw [coeff_trunc]
  rw [coeff_X]
  split_ifs with h1 h2
  · rw [h2, Polynomial.coeff_X_one]
  · rw [Polynomial.coeff_X_of_ne_one h2]
  · have : d ≠ 1
    · intro h
      apply h1
      rw [h]
      exact one_lt_succ_succ n
    rw [Polynomial.coeff_X_of_ne_one this]
-- #align power_series.trunc_X PowerSeries.trunc_X

@[simp]
theorem X_comp {f : pow} (h : constantCoeff R f = 0) : X.comp f = f :=
  by
  ext n
  rw [coeff_comp_cts h (lt_add_of_pos_right n (succ_pos 1)), trunc_X, Polynomial.eval₂_X]
-- #align power_series.X_comp PowerSeries.X_comp

#check lt_add_of_pos_right

-- TODO:
-- # ASK John about the best way of dealing with a finite sum with only one non-zero term.
-- lemma rescale_eq_comp_mul_X (f : pow) (r : R) :
--   rescale r f = f.comp (↑r * X) :=
-- begin
--   have : constant_coeff R (↑r * X) = 0,
--   {
--     simp only [coeff_zero_eq_constant_coeff,
--       map_mul, constant_coeff_X, mul_zero],
--   },
--   ext,
--   rw [coeff_rescale, coeff_comp_eq this,
--     polynomial.eval₂_eq_sum_range' (C R) (nat_degree_trunc_lt f n),
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
theorem eq_of_D_eq_of_const_eq {R : Type} [CommRing R] [NoZeroSMulDivisors ℕ R]
    (f g : PowerSeries R) : @D R _ f = @D R _ g → constantCoeff R f = constantCoeff R g → f = g :=
  by
  intro h1 h2
  ext n : 1
  cases' n with n
  rw [coeff_zero_eq_constantCoeff]
  exact h2
  have eq : coeff R n (@D R _ f) = coeff R n (@D R _ g) := by rw [h1]
  rw [coeff_D, coeff_D] at eq 
  simp only [succ_eq_add_one]
  norm_cast at eq
  rwa [--←@algebraMap.coe_one ℕ R,
    --←algebraMap.coe_add,
    mul_comm,
    ←nsmul_eq_mul, mul_comm,
    ←nsmul_eq_mul, smul_right_inj] at eq 
  exact succ_ne_zero n
-- #align eq_of_D_eq_of_const_eq eq_of_d_eq_of_const_eq

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
-- #align power_series.D_inv PowerSeries.d_inv
