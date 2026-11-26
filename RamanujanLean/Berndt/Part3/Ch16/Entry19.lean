import RamanujanLean.Defs.Theta
import QseriesFormalization.Chapter03

/-!
# Berndt, Ramanujan's Notebooks Part III, Chapter 16, Entry 19

Source: Berndt, *Ramanujan's Notebooks, Part III* (Springer, 1991), p. 35,
Entry 19 (Jacobi's triple product identity). Cited in this form in
Rajkhowa–Saikia, arXiv:2305.14988, eq. (1.3):

  f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞,   |ab| < 1.

Here `(x; q)_∞ = ∏_{n ≥ 0} (1 - x q^n)`, so the three products are
`∏ (1 + a (ab)^n)`, `∏ (1 + b (ab)^n)` and `∏ (1 - (ab)^{n+1})`.

The proof reuses Jacobi's triple product from `invitation-to-qseries-lean`
(Apache-2.0), `QseriesFormalization.PartI.Ch02.jacobiTripleProduct`, which is
stated for `‖q‖ < 1` and `z ≠ 0` as `∑ z^n q^{n²} = ∏ (1 - q^{2n})(1 + z q^{2n-1})
(1 + z⁻¹ q^{2n-1})`. For `ab ≠ 0` we take `q` with `q² = ab` and `z = a / q`, so
`a = z q` and `b = z⁻¹ q`. The case `ab = 0` is outside that theorem and is
done directly: then `f(a, b) = 1 + a + b` and the products are `1 + a`, `1 + b`
and `1`.
-/

namespace RamanujanLean.Berndt.Part3.Ch16

open QseriesFormalization.PartI.Ch02
  (jacobiTripleProduct jacobiInfiniteProduct_eq_tprod_components
   hasSum_jacobiInfiniteSeries_terms jacobiProductEvenFactor jacobiProductOddFactor
   summable_norm_mul_geometric_complex)

private lemma two_dvd_mul_add_one' (t : ℤ) : (2 : ℤ) ∣ t * (t + 1) := by
  rcases Int.even_or_odd t with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (t + 1), by rw [hm]; ring⟩
  · exact ⟨t * (m + 1), by rw [hm]; ring⟩

private lemma two_dvd_mul_sub_one' (t : ℤ) : (2 : ℤ) ∣ t * (t - 1) := by
  have h := two_dvd_mul_add_one' (t - 1)
  rwa [show (t - 1) * (t - 1 + 1) = t * (t - 1) by ring] at h

/-- In the `q, z` variables, the `t`-th term of `f(zq, z⁻¹q)` is `z^t q^{t²}`. -/
theorem ramanujanThetaTerm_mul_inv_mul (z q : ℂ) (hz : z ≠ 0) (hq : q ≠ 0) (t : ℤ) :
    ramanujanThetaTerm (z * q) (z⁻¹ * q) t = z ^ t * q ^ (t ^ 2) := by
  unfold ramanujanThetaTerm
  set m := t * (t + 1) / 2 with hm_def
  set k := t * (t - 1) / 2 with hk_def
  have hm : m * 2 = t * (t + 1) := Int.ediv_mul_cancel (two_dvd_mul_add_one' t)
  have hk : k * 2 = t * (t - 1) := Int.ediv_mul_cancel (two_dvd_mul_sub_one' t)
  have hsub : m - k = t := by linarith
  have hadd : m + k = t ^ 2 := by nlinarith
  rw [mul_zpow, mul_zpow, inv_zpow']
  calc z ^ m * q ^ m * (z ^ (-k) * q ^ k)
      = (z ^ m * z ^ (-k)) * (q ^ m * q ^ k) := by ring
    _ = z ^ (m + -k) * q ^ (m + k) := by rw [zpow_add₀ hz, zpow_add₀ hq]
    _ = z ^ t * q ^ (t ^ 2) := by rw [← sub_eq_add_neg, hsub, hadd]

/-- If `ab = 0`, every term of `f(a, b)` other than `t = -1, 0, 1` vanishes. -/
private lemma ramanujanThetaTerm_eq_zero_of_mul_eq_zero (a b : ℂ) (hab : a * b = 0)
    (t : ℤ) (ht : t ∉ ({-1, 0, 1} : Finset ℤ)) : ramanujanThetaTerm a b t = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  obtain ⟨h1, h0, h2⟩ := ht
  unfold ramanujanThetaTerm
  rcases mul_eq_zero.mp hab with ha | hb
  · subst ha
    have hne : t * (t + 1) / 2 ≠ 0 := by
      intro h
      have hm : t * (t + 1) / 2 * 2 = t * (t + 1) := Int.ediv_mul_cancel (two_dvd_mul_add_one' t)
      rw [h, zero_mul] at hm
      rcases mul_eq_zero.mp hm.symm with h' | h'
      · exact h0 h'
      · exact h1 (by linarith)
    rw [zero_zpow _ hne, zero_mul]
  · subst hb
    have hne : t * (t - 1) / 2 ≠ 0 := by
      intro h
      have hk : t * (t - 1) / 2 * 2 = t * (t - 1) := Int.ediv_mul_cancel (two_dvd_mul_sub_one' t)
      rw [h, zero_mul] at hk
      rcases mul_eq_zero.mp hk.symm with h' | h'
      · exact h0 h'
      · exact h2 (by linarith)
    rw [zero_zpow _ hne, mul_zero]

/-- If `ab = 0`, then `f(a, b) = 1 + a + b`. -/
private lemma hasSum_ramanujanThetaTerm_of_mul_eq_zero (a b : ℂ) (hab : a * b = 0) :
    HasSum (fun t : ℤ => ramanujanThetaTerm a b t) (1 + a + b) := by
  have h : HasSum (fun t : ℤ => ramanujanThetaTerm a b t)
      (∑ t ∈ ({-1, 0, 1} : Finset ℤ), ramanujanThetaTerm a b t) :=
    hasSum_sum_of_ne_finset_zero (ramanujanThetaTerm_eq_zero_of_mul_eq_zero a b hab)
  convert h using 1
  simp [ramanujanThetaTerm]
  ring

/-- `∏_{n ≥ 0} (1 + c rⁿ)` converges for `‖r‖ < 1`. -/
private lemma multipliable_one_add_mul_pow (c r : ℂ) (hr : ‖r‖ < 1) :
    Multipliable fun n : ℕ => 1 + c * r ^ n :=
  multipliable_one_add_of_summable (summable_norm_mul_geometric_complex c r hr)

/-- `∏_{n ≥ 0} (1 - r^{n+1})` converges for `‖r‖ < 1`. -/
private lemma multipliable_one_sub_pow_succ (r : ℂ) (hr : ‖r‖ < 1) :
    Multipliable fun n : ℕ => 1 - r ^ (n + 1) :=
  (multipliable_one_add_mul_pow (-r) r hr).congr fun n => by ring

/-- If `r = 0`, then `∏_{n ≥ 0} (1 + c rⁿ) = 1 + c`. -/
private lemma tprod_one_add_mul_zero_pow (c : ℂ) :
    ∏' n : ℕ, (1 + c * (0 : ℂ) ^ n) = 1 + c := by
  have h : HasProd (fun n : ℕ => 1 + c * (0 : ℂ) ^ n)
      (∏ n ∈ ({0} : Finset ℕ), (1 + c * (0 : ℂ) ^ n)) :=
    hasProd_prod_of_ne_finset_one (fun n hn => by
      have : n ≠ 0 := by simpa using hn
      simp [zero_pow this])
  simpa using h.tprod_eq

/-- **Entry 19** (Berndt, Part III, Ch. 16, p. 35), Jacobi's triple product in
Ramanujan's form. For complex `a, b` with `|ab| < 1`, the three products
`(-a; ab)_∞`, `(-b; ab)_∞`, `(ab; ab)_∞` converge, and the series `f(a, b)`
converges to their product. -/
theorem entry19 (a b : ℂ) (hab : ‖a * b‖ < 1) :
    HasProd (fun n : ℕ => 1 + a * (a * b) ^ n) (∏' n : ℕ, (1 + a * (a * b) ^ n)) ∧
    HasProd (fun n : ℕ => 1 + b * (a * b) ^ n) (∏' n : ℕ, (1 + b * (a * b) ^ n)) ∧
    HasProd (fun n : ℕ => 1 - (a * b) ^ (n + 1)) (∏' n : ℕ, (1 - (a * b) ^ (n + 1))) ∧
    HasSum (fun t : ℤ => ramanujanThetaTerm a b t)
      ((∏' n : ℕ, (1 + a * (a * b) ^ n)) * (∏' n : ℕ, (1 + b * (a * b) ^ n)) *
        (∏' n : ℕ, (1 - (a * b) ^ (n + 1)))) := by
  refine ⟨(multipliable_one_add_mul_pow a (a * b) hab).hasProd,
    (multipliable_one_add_mul_pow b (a * b) hab).hasProd,
    (multipliable_one_sub_pow_succ (a * b) hab).hasProd, ?_⟩
  by_cases h0 : a * b = 0
  · -- Degenerate case `ab = 0`: outside `jacobiTripleProduct` (which needs `z ≠ 0`).
    rw [h0, tprod_one_add_mul_zero_pow, tprod_one_add_mul_zero_pow]
    rw [show (∏' n : ℕ, (1 - (0 : ℂ) ^ (n + 1))) = 1 by simp]
    convert hasSum_ramanujanThetaTerm_of_mul_eq_zero a b h0 using 1
    linear_combination h0
  · -- Main case: `q² = ab`, `z = a / q`.
    obtain ⟨q, hq2⟩ := IsAlgClosed.exists_pow_nat_eq (a * b) (by norm_num : 0 < 2)
    have ha : a ≠ 0 := left_ne_zero_of_mul h0
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact h0 (by rw [← hq2]; ring)
    have hqn : ‖q‖ < 1 := by
      have h2 : ‖q‖ ^ 2 < 1 := by rwa [← norm_pow, hq2]
      nlinarith [norm_nonneg q]
    set z := a / q with hz_def
    have hz0 : z ≠ 0 := div_ne_zero ha hq0
    have hza : z * q = a := by rw [hz_def]; field_simp
    have hzb : z⁻¹ * q = b := by
      rw [hz_def, inv_div]
      field_simp
      exact hq2
    -- The series side.
    have hS := hasSum_jacobiInfiniteSeries_terms q z hqn
    rw [← jacobiTripleProduct q z hqn hz0, jacobiInfiniteProduct_eq_tprod_components q z hqn]
      at hS
    have hT : (fun t : ℤ => ramanujanThetaTerm a b t) = fun t : ℤ => z ^ t * q ^ (t ^ 2) := by
      funext t
      rw [← hza, ← hzb, ramanujanThetaTerm_mul_inv_mul z q hz0 hq0 t]
    rw [hT]
    -- The product side, factor by factor.
    have hodd : ∀ (c : ℂ) (n : ℕ), jacobiProductOddFactor q c n = 1 + c * q * (a * b) ^ n := by
      intro c n
      rw [jacobiProductOddFactor, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, pow_succ,
        pow_mul, hq2]
      ring
    have heven : ∀ n : ℕ, jacobiProductEvenFactor q n = 1 - (a * b) ^ (n + 1) := by
      intro n
      rw [jacobiProductEvenFactor, pow_mul, hq2]
    have hPa : (∏' n : ℕ, jacobiProductOddFactor q z n) = ∏' n : ℕ, (1 + a * (a * b) ^ n) :=
      tprod_congr fun n => by rw [hodd, hza]
    have hPb : (∏' n : ℕ, jacobiProductOddFactor q z⁻¹ n) =
        ∏' n : ℕ, (1 + b * (a * b) ^ n) :=
      tprod_congr fun n => by rw [hodd, hzb]
    have hPc : (∏' n : ℕ, jacobiProductEvenFactor q n) =
        ∏' n : ℕ, (1 - (a * b) ^ (n + 1)) :=
      tprod_congr fun n => heven n
    rw [hPa, hPb, hPc] at hS
    convert hS using 1
    ring

/-- Entry 19 in Ramanujan's notation: `f(a, b) = (-a; ab)_∞ (-b; ab)_∞ (ab; ab)_∞`
for `|ab| < 1`. This is an equation of `tsum` and `tprod`; convergence is stated
in `entry19`. -/
theorem entry19_ramanujanTheta (a b : ℂ) (hab : ‖a * b‖ < 1) :
    ramanujanTheta a b =
      (∏' n : ℕ, (1 + a * (a * b) ^ n)) * (∏' n : ℕ, (1 + b * (a * b) ^ n)) *
        (∏' n : ℕ, (1 - (a * b) ^ (n + 1))) :=
  (entry19 a b hab).2.2.2.tsum_eq

end RamanujanLean.Berndt.Part3.Ch16
