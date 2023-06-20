import Std.Tactic.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Basic


set_option profiler true
/-
TODO : prove that composition of power series is associative.
-/


open PowerSeries Nat

open scoped Classical

--open bigOperators
section CommutativeSemiring

variable {R : Type} [CommSemiring R]

-- derivarions are defined only in the case that the base is a `comm_semiring`.
local notation "pow"    => PowerSeries R
local notation "poly"   => Polynomial R
local notation "coeff"  => coeff R

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
theorem Derivation.polynomial_eval₂ (A : Type) [CommSemiring A] [Algebra R A] (M : Type)
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] (d : Derivation R A M)
  (f : poly) (g : A) :
  d (f.eval₂ (algebraMap R A) g) = f.derivative.eval₂ (algebraMap R A) g • d g :=
by
  rw [Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_range_succ', Derivation.leibniz,
    Derivation.leibniz_pow, Derivation.map_algebraMap, zero_nsmul, smul_zero, smul_zero, zero_add,
    add_zero]
  by_cases f.natDegree = 0
  · rw [h, Finset.sum_range_zero, Polynomial.derivative_of_natDegree_zero h, Polynomial.eval₂_zero,
      zero_smul]
  · have : f.derivative.natDegree < f.natDegree := Polynomial.natDegree_derivative_lt h
    rw [Polynomial.eval₂_eq_sum_range' (algebraMap R A) this, Finset.sum_smul]
    apply Finset.sum_congr; rfl
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
#align power_series.coeff_cts PowerSeries.coeff_cts

/-- The `n`-th coefficient of a`f*g` may be calculated 
from the truncations of `f` and `g`.-/
theorem coeff_mul_cts (f g : pow) {n a b : ℕ} (ha : n < a) (hb : n < b) :
  coeff n (f * g) = coeff n (trunc a f * trunc b g) :=
by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr
  · rfl
  · rintro ⟨ x, y⟩ hxy
    have hx : x ≤ n := Finset.Nat.antidiagonal.fst_le hxy
    have hy : y ≤ n := Finset.Nat.antidiagonal.snd_le hxy
    congr 1 <;> apply coeff_cts
    exact lt_of_le_of_lt hx ha
    exact lt_of_le_of_lt hy hb

/-- The formal derivative of a power series in one variable.-/
noncomputable def derivative : pow → pow := λ f =>
  mk λ n => coeff (n + 1) f * (n + 1)

theorem coeff_derivative (f : pow) (n : ℕ) : coeff n f.derivative = coeff (n + 1) f * (n + 1) :=
by
  rw [derivative, coeff_mk]

theorem derivative_coe (f : poly) : (f : pow).derivative = Polynomial.derivative f :=
by
  ext
  rw [coeff_derivative, Polynomial.coeff_coe, Polynomial.coeff_coe,
    Polynomial.coeff_derivative]

theorem derivative_add (f g : pow) : derivative (f + g) = derivative f + derivative g :=
by
  ext
  rw [coeff_derivative, map_add, map_add, coeff_derivative,
    coeff_derivative, add_mul]

theorem derivative_C (r : R) : derivative (C R r) = 0 :=
by
  ext n
  rw [coeff_derivative, coeff_C]
  split_ifs with h
  · exfalso
    apply succ_ne_zero n h
  · rw [zero_mul]
    rfl

theorem trunc_deriv (f : pow) (n : ℕ) :
  (trunc n f.derivative : pow) = derivative ↑(trunc (n + 1) f) :=
by
  ext d
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · have : d + 1 < n + 1 := succ_lt_succ h
    rw [coeff_derivative, coeff_derivative, Polynomial.coeff_coe,
      coeff_trunc, if_pos this]
  · have : ¬d + 1 < n + 1 := by rwa [succ_lt_succ_iff]
    rw [coeff_derivative, Polynomial.coeff_coe, coeff_trunc,
      if_neg this, MulZeroClass.zero_mul]

--A special case of the next theorem, used in its proof.
private theorem derivative_coe_mul_coe (f g : poly) :
  derivative (f * g : pow) = f * derivative (g : pow) + g * derivative (f : pow) :=
by
  rw [← Polynomial.coe_mul, derivative_coe, Polynomial.derivative_mul,
    derivative_coe, derivative_coe, add_comm, mul_comm _ g,
    ← Polynomial.coe_mul, ← Polynomial.coe_mul, Polynomial.coe_add]

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
  rw [smul_eq_C_mul f r, smul_eq_C_mul f.derivative r, derivative_mul,
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
theorem D_poly (f : poly) : (f : pow).derivative = Polynomial.derivative f :=
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
  trunc n (D f) = Polynomial.derivative (trunc (n + 1) f) :=
by
  have := trunc_deriv f n
  rw [derivative_coe] at this 
  exact (propext Polynomial.coe_inj).mp this

theorem trunc_succ (f : pow) (n : ℕ) :
  trunc n.succ f = trunc n f + Polynomial.monomial n (coeff n f) :=
by
  rw [trunc, Ico_zero_eq_range, Finset.sum_range_succ, trunc, Ico_zero_eq_range]

theorem D_poly_comp (f : poly) (g : pow) : D (f.eval₂ (C R) g) = f.derivative.eval₂ (C R) g * D g :=
  Derivation.polynomial_eval₂ pow pow D f g



/--Composition of power series-/
noncomputable def comp : pow → pow → pow := λ f g =>
  if constantCoeff R g = 0 then mk fun n => coeff n ((trunc n.succ f).eval₂ (C R) g) else 0

theorem comp_eq {f g : pow} (hg : constantCoeff R g = 0) :
    f.comp g = mk fun n => coeff n ((trunc n.succ f).eval₂ (C R) g) :=
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

private theorem coeff_pow_eq_zero {g : pow} (hg : constantCoeff R g = 0) {n a : ℕ} :
  n < a → coeff n (g ^ a) = 0 :=
by
  intro ha
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
theorem coeff_comp_cts {f g : pow} (h : constantCoeff R g = 0) {n a : ℕ} :
  n < a → coeff n (f.comp g) = coeff n ((trunc a f).eval₂ (C R) g) :=
by
  apply le_induction
  · rw [coeff_comp_eq h]
  · intro a ha ih
    rw [trunc_succ, Polynomial.eval₂_add, map_add, ih, Polynomial.eval₂_monomial, coeff_C_mul]
    suffices coeff n (g ^ a) = 0 by rw [this, MulZeroClass.mul_zero, add_zero]
    exact coeff_pow_eq_zero h ha



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
  · rw [comp_eq_zero h, comp_eq_zero h, MulZeroClass.zero_mul, map_zero]

@[simp]
theorem D_C (r : R) : D (C R r : pow) = 0 :=
  derivative_C r

@[simp]
theorem D_smul (a : R) (f : pow) : D (a • f) = a • D f :=
by
  rw [smul_eq_C_mul, smul_eq_C_mul, D_mul, D_C, MulZeroClass.mul_zero, add_zero]

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
    rw [lt_succ, ←not_lt] at h
    contradiction
  · rfl

theorem constantCoeff_comp {f g : pow} (h : constantCoeff R g = 0) :
  constantCoeff R (f.comp g) = constantCoeff R f :=
by
  have : (trunc 1 f).natDegree < 1 := natDegree_trunc_lt f 0
  rw [← coeff_zero_eq_constantCoeff, coeff_comp_eq h, Polynomial.eval₂_eq_sum_range' (C R) this,
    Finset.sum_range_one, _root_.pow_zero, mul_one, coeff_zero_C, coeff_trunc]
  simp_rw [lt_one_iff, eq_self_iff_true, if_true]


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
  induction' hn with m hm ih
  · ext a
    rw [coeff_trunc]
    split_ifs with h
    · exact Polynomial.coeff_coe _ _
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      rwa [not_lt, succ_le_iff] at h 
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
  cases' n with n
  rw [coeff_zero_eq_constantCoeff]
  exact h2
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





------------------------------------------------------
-- A few examples of proving power series identities--
------------------------------------------------------

section CharZeroField

variable {R : Type} [Field R] [CharZero R]

/-
I take the base ring to be a field of characteristic zero.
This is because
     (i) my power series have rational coefficients
         (with all natural denominators),
    (ii) there is currently no instance of `has_inv (power_series R)`
         except in the case that `R` is a field.
-/
local notation "pow" => PowerSeries R

local notation "coeff" => coeff R

local notation "D" => @D R _

def exp             : pow := mk λ n => (n.factorial⁻¹ : R)
def logOneAdd       : pow := mk λ n => (-(-1) ^ n / n : R)
def geometricSeries : pow := mk λ n => (-1) ^ n
def polylog (d : ℕ) : pow := mk λ n => (n:R)⁻¹^d


theorem geometricSeries_eq : geometricSeries = ((1:pow) + X)⁻¹ :=
by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_add, mul_one]
  · ext n
    rw [map_add, geometricSeries]
    cases' n with n
    · rw [coeff_zero_mul_X, add_zero, coeff_mk, _root_.pow_zero,
      coeff_zero_eq_constantCoeff, map_one]
    · rw [coeff_succ_mul_X, coeff_mk, coeff_mk, _root_.pow_succ,
        neg_one_mul, neg_add_self, coeff_one, if_neg (succ_ne_zero n)]
  · rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero


theorem D_geometricSeries : D geometricSeries = -(1 + X)⁻¹ ^ 2 := by
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
theorem constantCoeff_exp : constantCoeff R exp = 1 := by
  rw [exp, ← coeff_zero_eq_constantCoeff, coeff_mk, factorial_zero, cast_one,
    inv_one]

@[simp]
theorem exp_neg {f : pow} : exp.comp (-f) = (exp.comp f)⁻¹ :=
by
  by_cases hf : constantCoeff R f = 0
  · have : constantCoeff R (-f) = 0 := by rw [map_neg, hf, neg_eq_zero]
    rw [PowerSeries.eq_inv_iff_mul_eq_one]
    · apply eq_of_D_eq_of_const_eq
      · rw [D_mul, D_comp, D_comp, D_exp, D_one, map_neg, mul_neg, mul_neg,
          ←mul_assoc, mul_comm (exp.comp (-f)), mul_assoc, add_neg_self]
      · rw [map_mul, constantCoeff_comp hf, constantCoeff_comp this,
          constantCoeff_exp, map_one, mul_one]
    · rw [constantCoeff_comp hf, constantCoeff_exp]
      exact one_ne_zero
  · have : ¬constantCoeff R (-f) = 0 := by rw [map_neg, neg_eq_zero]; exact hf
    rw [comp, if_neg this, comp, if_neg hf, MvPowerSeries.zero_inv]

@[simp]
theorem exp_add (f g : pow) (hf : constantCoeff R f = 0) (hg : constantCoeff R g = 0) :
  exp.comp (f + g) = exp.comp f * exp.comp g :=
by
  have eq : constantCoeff R (f + g) = 0 := by rw [map_add, hf, hg, zero_add]
  suffices 1 = exp.comp f * exp.comp g * exp.comp (-(f + g))
    by
    rwa [exp_neg, MvPowerSeries.eq_mul_inv_iff_mul_eq, one_mul] at this 
    change constantCoeff R (exp.comp (f + g)) ≠ 0
    rw [constantCoeff_comp eq, constantCoeff_exp]
    exact one_ne_zero
  · apply eq_of_D_eq_of_const_eq
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
  cases' n with n
  · rw [coeff_zero_mul_X, coeff_zero_one]; norm_num
  · have : n + 1 ≠ 0 := succ_ne_zero n
    rw [coeff_succ_mul_X, coeff_D, coeff_mk, coeff_one, cast_add, cast_one, div_mul_cancel,
      _root_.pow_succ, neg_one_mul, succ_eq_add_one, neg_add_self, if_neg this]
    rw [←cast_one, ←cast_add, cast_ne_zero]
    exact this
  · rw [←cast_one, ←cast_add, cast_ne_zero]
    exact succ_ne_zero n
  · rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero

@[simp]
theorem const_exp_sub_one : constantCoeff R (exp - 1) = 0 := by
  rw [map_sub, constantCoeff_exp, constantCoeff_one, sub_self]
#align const_exp_sub_one const_exp_sub_one

@[simp]
theorem d_log_comp_exp : D (logOneAdd.comp ((exp : pow) - 1)) = 1 :=
  by
  rw [D_comp, D_logOneAdd, map_sub, D_one, sub_zero, D_exp]
  have : (1 + (X : pow)).comp (exp - 1) = exp := by
    rw [add_comp, X_comp const_exp_sub_one, one_comp const_exp_sub_one, add_sub_cancel'_right]
  nth_rw 2 [← this]
  rw [← mul_comp, PowerSeries.inv_mul_cancel, one_comp const_exp_sub_one]
  rw [map_add, constantCoeff_one, constantCoeff_X, add_zero]
  exact one_ne_zero

@[simp]
theorem log_exp : logOneAdd.comp ((exp : pow) - 1) = X :=
  by
  apply eq_of_D_eq_of_const_eq
  rw [d_log_comp_exp, D_X]
  rw [constantCoeff_comp, constantCoeff_X, constantCoeff_logOneAdd]
  exact const_exp_sub_one

@[simp]
theorem log_mul (f g : pow) (hf : constantCoeff R f = 0) (hg : constantCoeff R g = 0) :
    logOneAdd.comp ((1 + f) * (1 + g) - 1) = logOneAdd.comp f + logOneAdd.comp g :=
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
  rw [constantCoeff_comp eq, map_add, constantCoeff_comp hf, constantCoeff_comp hg,
    constantCoeff_logOneAdd, add_zero]

@[simp]
theorem exp_log : exp.comp logOneAdd = (1 + X : pow) :=
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
      · rw [←cast_succ, cast_ne_zero];
        exact succ_ne_zero n
      · rw [←cast_succ, cast_ne_zero];
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

end CharZeroField

