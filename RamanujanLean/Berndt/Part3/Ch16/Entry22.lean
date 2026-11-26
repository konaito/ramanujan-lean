import RamanujanLean.Defs.Theta
import RamanujanLean.Berndt.Part3.Ch16.Entry19
import QseriesFormalization.Chapter04

/-!
# Berndt, Ramanujan's Notebooks Part III, Chapter 16, Entry 22

Source: Berndt, *Ramanujan's Notebooks, Part III* (Springer, 1991), p. 36,
Entry 22(i)-(iii). Cited in this form in Rajkhowa–Saikia, arXiv:2305.14988,
eqs. (1.4)-(1.6). For `|q| < 1`, with `(x; r)_∞ = ∏_{n ≥ 0} (1 - x rⁿ)`:

* (i)   φ(q) := f(q, q) = ∑_{t=-∞}^{∞} q^{t²} = (-q; -q)_∞ / (q; -q)_∞,
* (ii)  ψ(q) := f(q, q³) = ∑_{t=0}^{∞} q^{t(t+1)/2} = (q²; q²)_∞ / (q; q²)_∞,
* (iii) f(-q) := f(-q, -q²) = ∑_{t=-∞}^{∞} (-1)^t q^{t(3t-1)/2} = (q; q)_∞.

(i) and (ii) are special cases of Entry 19 (`entry19`) with `a = b = q` and
`a = q, b = q³`. Turning the three products of Entry 19 into the quotients above
uses Euler's identity `(-q; q²)_∞ (q; q²)_∞ (-q²; q²)_∞ = 1`, proved here from
`(1 + x)(1 - x) = 1 - x²`, splitting products into even and odd indices, and
`(q⁴; q⁴)_∞ ≠ 0` (`QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_ne_zero`).

(iii) reuses Euler's pentagonal number theorem from `invitation-to-qseries-lean`
(Apache-2.0), `QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum'`.
-/

namespace RamanujanLean.Berndt.Part3.Ch16

open QseriesFormalization.PartI.Ch04
  (eulerPentagonalInfiniteProduct eulerPentagonalInfiniteProduct_eq_tsum'
   eulerPentagonalInfiniteProduct_ne_zero hasProd_eulerPentagonalProductFactor
   eulerPentagonalProductFactor)

private lemma two_dvd_mul_add_one (t : ℤ) : (2 : ℤ) ∣ t * (t + 1) := by
  rcases Int.even_or_odd t with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (t + 1), by rw [hm]; ring⟩
  · exact ⟨t * (m + 1), by rw [hm]; ring⟩

private lemma two_dvd_mul_sub_one (t : ℤ) : (2 : ℤ) ∣ t * (t - 1) := by
  have h := two_dvd_mul_add_one (t - 1)
  rwa [show (t - 1) * (t - 1 + 1) = t * (t - 1) by ring] at h

private lemma two_dvd_pent (t : ℤ) : (2 : ℤ) ∣ t * (3 * t - 1) := by
  have h := two_dvd_mul_sub_one t
  rcases h with ⟨c, hc⟩
  exact ⟨c + t * t, by linear_combination hc⟩

private lemma neg_one_zpow_sq (t : ℤ) : (-1 : ℂ) ^ (t * t) = (-1 : ℂ) ^ t := by
  rcases two_dvd_mul_sub_one t with ⟨c, hc⟩
  have : t * t = t + 2 * c := by linear_combination hc
  rw [this, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

/-- Each term of `f(-q, -q²)` is `(-1)^t q^{t(3t-1)/2}`. -/
theorem ramanujanThetaTerm_neg_neg_sq (q : ℂ) (t : ℤ) :
    ramanujanThetaTerm (-q) (-q ^ 2) t = (-1 : ℂ) ^ t * q ^ (t * (3 * t - 1) / 2) := by
  unfold ramanujanThetaTerm
  set m := t * (t + 1) / 2 with hm_def
  set k := t * (t - 1) / 2 with hk_def
  set e := t * (3 * t - 1) / 2 with he_def
  have hm : m * 2 = t * (t + 1) := Int.ediv_mul_cancel (two_dvd_mul_add_one t)
  have hk : k * 2 = t * (t - 1) := Int.ediv_mul_cancel (two_dvd_mul_sub_one t)
  have he : e * 2 = t * (3 * t - 1) := Int.ediv_mul_cancel (two_dvd_pent t)
  have hmk : m + k = t * t := by linarith
  have hm2k : m + 2 * k = e := by linarith
  by_cases hq : q = 0
  · subst hq
    by_cases ht : t = 0
    · subst ht; simp [hm_def, hk_def, he_def]
    · have he0 : e ≠ 0 := by
        intro h0
        rw [h0] at he
        have : t * (3 * t - 1) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact ht h
        · omega
      have hmk0 : m ≠ 0 ∨ k ≠ 0 := by
        by_contra h
        push_neg at h
        have : t * t = 0 := by rw [← hmk, h.1, h.2]; ring
        exact ht (mul_self_eq_zero.mp this)
      rw [zero_zpow _ he0, mul_zero]
      rcases hmk0 with h | h
      · simp [zero_zpow _ h]
      · simp [zero_zpow _ h]
  · have hq2 : (-q ^ 2 : ℂ) = (-1) * q ^ (2 : ℤ) := by rw [zpow_two, sq]; ring
    have hq1 : (-q : ℂ) = (-1) * q := by ring
    rw [hq1, hq2, mul_zpow, mul_zpow, ← zpow_mul]
    have hne : (-1 : ℂ) ≠ 0 := by norm_num
    calc (-1 : ℂ) ^ m * q ^ m * ((-1) ^ k * q ^ (2 * k))
        = ((-1 : ℂ) ^ m * (-1) ^ k) * (q ^ m * q ^ (2 * k)) := by ring
      _ = (-1 : ℂ) ^ (m + k) * q ^ (m + 2 * k) := by
          rw [zpow_add₀ hne, zpow_add₀ hq]
      _ = (-1 : ℂ) ^ t * q ^ e := by rw [hmk, hm2k, neg_one_zpow_sq]

/-- **Entry 22(iii)** (Berndt, Part III, Ch. 16, p. 36). For `|q| < 1`,
the series `f(-q, -q²)` and `∑ (-1)^t q^{t(3t-1)/2}` converge and both equal
the convergent product `(q; q)_∞ = ∏_{n ≥ 1} (1 - q^n)`. -/
theorem entry22_iii (q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 - q ^ (n + 1)) (∏' n : ℕ, (1 - q ^ (n + 1))) ∧
    HasSum (fun t : ℤ => (-1 : ℂ) ^ t * q ^ (t * (3 * t - 1) / 2))
      (∏' n : ℕ, (1 - q ^ (n + 1))) ∧
    HasSum (fun t : ℤ => ramanujanThetaTerm (-q) (-q ^ 2) t)
      (∏' n : ℕ, (1 - q ^ (n + 1))) := by
  have hP : eulerPentagonalInfiniteProduct q = ∏' n : ℕ, (1 - q ^ (n + 1)) := rfl
  -- Euler's form, summed over `j` with exponent `j(3j+1)/2`.
  set S : ℤ → ℂ := fun j => (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) with hS
  have hSum : Summable S := by
    by_contra hns
    have h0 := tsum_eq_zero_of_not_summable hns
    have h1 := eulerPentagonalInfiniteProduct_eq_tsum' q hq
    exact eulerPentagonalInfiniteProduct_ne_zero q hq (h1.trans h0)
  have hHasS : HasSum S (∏' n : ℕ, (1 - q ^ (n + 1))) := by
    rw [← hP, eulerPentagonalInfiniteProduct_eq_tsum' q hq]
    exact hSum.hasSum
  -- Reindex `t ↦ -t` to get Ramanujan's exponent `t(3t-1)/2`.
  have hneg : ∀ t : ℤ, (-1 : ℂ) ^ (-t) = (-1 : ℂ) ^ t := by
    intro t
    have h2 : (-1 : ℂ) ^ (2 * t) = 1 := by rw [zpow_mul]; norm_num
    calc (-1 : ℂ) ^ (-t) = (-1 : ℂ) ^ (-t) * (-1 : ℂ) ^ (2 * t) := by rw [h2, mul_one]
      _ = (-1 : ℂ) ^ t := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
          congr 1
          ring
  have hR : (fun t : ℤ => (-1 : ℂ) ^ t * q ^ (t * (3 * t - 1) / 2)) =
      S ∘ ⇑(Equiv.neg ℤ) := by
    funext t
    simp only [hS, Function.comp_apply, Equiv.neg_apply, hneg]
    rw [show -t * (3 * -t + 1) = t * (3 * t - 1) by ring]
  have h2 : HasSum (fun t : ℤ => (-1 : ℂ) ^ t * q ^ (t * (3 * t - 1) / 2))
      (∏' n : ℕ, (1 - q ^ (n + 1))) := by
    rw [hR]
    exact (Equiv.neg ℤ).hasSum_iff.mpr hHasS
  refine ⟨hasProd_eulerPentagonalProductFactor q hq, h2, ?_⟩
  rw [show (fun t : ℤ => ramanujanThetaTerm (-q) (-q ^ 2) t) = _ from
    funext (ramanujanThetaTerm_neg_neg_sq q)]
  exact h2

/-- Entry 22(iii) in Ramanujan's notation: `f(-q, -q²) = (q; q)_∞` for `|q| < 1`.
This is an equation of `tsum` and `tprod`; convergence is stated in `entry22_iii`. -/
theorem entry22_iii_ramanujanTheta (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanTheta (-q) (-q ^ 2) = ∏' n : ℕ, (1 - q ^ (n + 1)) :=
  (entry22_iii q hq).2.2.tsum_eq


/-! ## Entry 22(i) and 22(ii) -/

open QseriesFormalization.PartI.Ch02 (summable_norm_mul_geometric_complex)

private lemma norm_pow_lt_one (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) (hk : k ≠ 0) : ‖q ^ k‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hk

/-- `∏_{n ≥ 0} (1 + c rⁿ)` converges for `‖r‖ < 1`. -/
private lemma hasProd_one_add_mul_pow (c r : ℂ) (hr : ‖r‖ < 1) :
    HasProd (fun n : ℕ => 1 + c * r ^ n) (∏' n : ℕ, (1 + c * r ^ n)) :=
  (multipliable_one_add_of_summable (summable_norm_mul_geometric_complex c r hr)).hasProd

/-- `∏_{n ≥ 0} (1 - c rⁿ)` converges for `‖r‖ < 1`. -/
private lemma hasProd_one_sub_mul_pow (c r : ℂ) (hr : ‖r‖ < 1) :
    HasProd (fun n : ℕ => 1 - c * r ^ n) (∏' n : ℕ, (1 - c * r ^ n)) :=
  ((multipliable_one_add_of_summable (summable_norm_mul_geometric_complex (-c) r hr)).congr
    fun n => by ring).hasProd

/-- `∏_{n ≥ 0} (1 + r^{n+1})` converges for `‖r‖ < 1`. -/
private lemma hasProd_one_add_pow_succ (r : ℂ) (hr : ‖r‖ < 1) :
    HasProd (fun n : ℕ => 1 + r ^ (n + 1)) (∏' n : ℕ, (1 + r ^ (n + 1))) :=
  ((multipliable_one_add_of_summable (summable_norm_mul_geometric_complex r r hr)).congr
    fun n => by ring).hasProd

/-- `∏_{n ≥ 0} (1 - r^{n+1})` converges for `‖r‖ < 1`. -/
private lemma hasProd_one_sub_pow_succ (r : ℂ) (hr : ‖r‖ < 1) :
    HasProd (fun n : ℕ => 1 - r ^ (n + 1)) (∏' n : ℕ, (1 - r ^ (n + 1))) :=
  ((multipliable_one_add_of_summable (summable_norm_mul_geometric_complex (-r) r hr)).congr
    fun n => by ring).hasProd

/-- Euler's identity `(-q; q²)_∞ (q; q²)_∞ (-q²; q²)_∞ = 1`, together with
`(q²; q²)_∞ = (-q; q²)_∞ (q; q²)_∞ (q⁴; q⁴)_∞`. -/
private lemma euler_odd_distinct (q : ℂ) (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) *
        (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) = 1 ∧
    (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) =
      (∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) *
        (∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1))) := by
  have hq2 := norm_pow_lt_one q hq 2 (by norm_num)
  have hq4 := norm_pow_lt_one q hq 4 (by norm_num)
  -- `(-q; q²)_∞ (q; q²)_∞ = (q²; q⁴)_∞`
  have hR : HasProd (fun n : ℕ => 1 - q ^ 2 * (q ^ 4) ^ n)
      ((∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 - q * (q ^ 2) ^ n))) := by
    convert (hasProd_one_add_mul_pow q (q ^ 2) hq2).mul
      (hasProd_one_sub_mul_pow q (q ^ 2) hq2) using 1
    funext n
    ring
  -- `(q²; q²)_∞ = (q²; q⁴)_∞ (q⁴; q⁴)_∞`, splitting into even and odd indices.
  have hE2 : HasProd (fun n : ℕ => 1 - (q ^ 2) ^ (n + 1))
      ((∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) *
        (∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1)))) := by
    refine HasProd.even_mul_odd ?_ ?_
    · convert hR using 1
      funext k
      ring
    · convert hasProd_one_sub_pow_succ (q ^ 4) hq4 using 1
      funext k
      ring
  -- `(-q²; q²)_∞ (q²; q²)_∞ = (q⁴; q⁴)_∞`
  have hE4 : HasProd (fun n : ℕ => 1 - (q ^ 4) ^ (n + 1))
      ((∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)))) := by
    convert (hasProd_one_add_pow_succ (q ^ 2) hq2).mul
      (hasProd_one_sub_pow_succ (q ^ 2) hq2) using 1
    funext n
    ring
  have hE2eq := (hasProd_one_sub_pow_succ (q ^ 2) hq2).unique hE2
  have hE4eq := (hasProd_one_sub_pow_succ (q ^ 4) hq4).unique hE4
  have hE4ne : (∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1))) ≠ 0 :=
    eulerPentagonalInfiniteProduct_ne_zero (q ^ 4) hq4
  refine ⟨?_, hE2eq⟩
  apply mul_left_cancel₀ hE4ne
  calc (∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1))) *
        ((∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) *
          (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))))
      = (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) *
          ((∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) *
            (∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1)))) := by ring
    _ = ∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1)) := by rw [← hE2eq, ← hE4eq]
    _ = (∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1))) * 1 := (mul_one _).symm

/-- For nonnegative exponents, `q^(m+k) = q^m q^k` holds also at `q = 0`. -/
private lemma zpow_add_of_nonneg (q : ℂ) {m k : ℤ} (hm : 0 ≤ m) (hk : 0 ≤ k) :
    q ^ (m + k) = q ^ m * q ^ k := by
  lift m to ℕ using hm
  lift k to ℕ using hk
  rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]

private lemma tri_nonneg (t : ℤ) : 0 ≤ t * (t + 1) / 2 := by
  apply Int.ediv_nonneg _ (by norm_num)
  rcases le_or_gt 0 t with h | h
  · exact mul_nonneg h (by omega)
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

private lemma tri_sub_nonneg (t : ℤ) : 0 ≤ t * (t - 1) / 2 := by
  have h := tri_nonneg (t - 1)
  rwa [show (t - 1) * (t - 1 + 1) = t * (t - 1) by ring] at h

/-- Each term of `f(q, q)` is `q^{t²}`. -/
theorem ramanujanThetaTerm_self (q : ℂ) (t : ℤ) :
    ramanujanThetaTerm q q t = q ^ (t ^ 2) := by
  unfold ramanujanThetaTerm
  rw [← zpow_add_of_nonneg q (tri_nonneg t) (tri_sub_nonneg t)]
  congr 1
  have hm : t * (t + 1) / 2 * 2 = t * (t + 1) := Int.ediv_mul_cancel (two_dvd_mul_add_one t)
  have hk : t * (t - 1) / 2 * 2 = t * (t - 1) := Int.ediv_mul_cancel (two_dvd_mul_sub_one t)
  nlinarith

/-- Each term of `f(q, q³)` is `q^{t(2t-1)}`. -/
theorem ramanujanThetaTerm_cube (q : ℂ) (t : ℤ) :
    ramanujanThetaTerm q (q ^ 3) t = q ^ (t * (2 * t - 1)) := by
  unfold ramanujanThetaTerm
  have h3 : (q ^ 3 : ℂ) ^ (t * (t - 1) / 2) = q ^ (3 * (t * (t - 1) / 2)) := by
    rw [zpow_mul]
    norm_cast
  have hk0 : 0 ≤ 3 * (t * (t - 1) / 2) := by have := tri_sub_nonneg t; omega
  rw [h3, ← zpow_add_of_nonneg q (tri_nonneg t) hk0]
  congr 1
  have hm : t * (t + 1) / 2 * 2 = t * (t + 1) := Int.ediv_mul_cancel (two_dvd_mul_add_one t)
  have hk : t * (t - 1) / 2 * 2 = t * (t - 1) := Int.ediv_mul_cancel (two_dvd_mul_sub_one t)
  nlinarith

/-- The bijection `ℕ ≃ ℤ`, `2j ↦ -j`, `2j + 1 ↦ j + 1`. Under it the exponent
`t(2t-1)` of `f(q, q³)` becomes the triangular number `k(k+1)/2`. -/
private def natEquivIntPsi : ℕ ≃ ℤ where
  toFun k := if k % 2 = 0 then -((k / 2 : ℕ) : ℤ) else ((k / 2 : ℕ) : ℤ) + 1
  invFun t := if t ≤ 0 then (-(2 * t)).toNat else (2 * t - 1).toNat
  left_inv k := by dsimp only; split_ifs <;> omega
  right_inv t := by dsimp only; split_ifs <;> omega

private lemma natEquivIntPsi_exponent (k : ℕ) :
    natEquivIntPsi k * (2 * natEquivIntPsi k - 1) = ((k * (k + 1) / 2 : ℕ) : ℤ) := by
  have hk : (k : ℤ) = if natEquivIntPsi k ≤ 0 then -2 * natEquivIntPsi k
      else 2 * natEquivIntPsi k - 1 := by
    simp only [natEquivIntPsi, Equiv.coe_fn_mk]
    split_ifs <;> omega
  have hT : ((k * (k + 1) / 2 : ℕ) : ℤ) * 2 = (k : ℤ) * ((k : ℤ) + 1) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
  split_ifs at hk <;> rw [hk] at hT <;> nlinarith

/-- **Entry 22(i)** (Berndt, Part III, Ch. 16, p. 36). For `|q| < 1`, the products
`(-q; -q)_∞ = ∏_{n ≥ 0} (1 - (-q)^{n+1})` and `(q; -q)_∞ = ∏_{n ≥ 0} (1 - q (-q)ⁿ)`
converge, the second is nonzero, and both `f(q, q)` and `∑_{t ∈ ℤ} q^{t²}` converge
to `(-q; -q)_∞ / (q; -q)_∞`. -/
theorem entry22_i (q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 - (-q) ^ (n + 1)) (∏' n : ℕ, (1 - (-q) ^ (n + 1))) ∧
    HasProd (fun n : ℕ => 1 - q * (-q) ^ n) (∏' n : ℕ, (1 - q * (-q) ^ n)) ∧
    (∏' n : ℕ, (1 - q * (-q) ^ n)) ≠ 0 ∧
    HasSum (fun t : ℤ => ramanujanThetaTerm q q t)
      ((∏' n : ℕ, (1 - (-q) ^ (n + 1))) / ∏' n : ℕ, (1 - q * (-q) ^ n)) ∧
    HasSum (fun t : ℤ => q ^ (t ^ 2))
      ((∏' n : ℕ, (1 - (-q) ^ (n + 1))) / ∏' n : ℕ, (1 - q * (-q) ^ n)) := by
  have hnq : ‖-q‖ < 1 := by rwa [norm_neg]
  have hq2 := norm_pow_lt_one q hq 2 (by norm_num)
  have hA := hasProd_one_sub_pow_succ (-q) hnq
  have hB := hasProd_one_sub_mul_pow q (-q) hnq
  -- `(-q; -q)_∞ = (-q; q²)_∞ (q²; q²)_∞`
  have hA' : HasProd (fun n : ℕ => 1 - (-q) ^ (n + 1))
      ((∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)))) := by
    refine HasProd.even_mul_odd ?_ ?_
    · convert hasProd_one_add_mul_pow q (q ^ 2) hq2 using 1
      funext k
      rw [pow_succ, pow_mul, neg_sq]
      ring
    · convert hasProd_one_sub_pow_succ (q ^ 2) hq2 using 1
      funext k
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, neg_sq]
  -- `(q; -q)_∞ = (q; q²)_∞ (-q²; q²)_∞`
  have hB' : HasProd (fun n : ℕ => 1 - q * (-q) ^ n)
      ((∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)))) := by
    refine HasProd.even_mul_odd ?_ ?_
    · convert hasProd_one_sub_mul_pow q (q ^ 2) hq2 using 1
      funext k
      rw [pow_mul, neg_sq]
    · convert hasProd_one_add_pow_succ (q ^ 2) hq2 using 1
      funext k
      rw [pow_succ, pow_mul, neg_sq]
      ring
  have hAeq := hA.unique hA'
  have hBeq := hB.unique hB'
  have hEuler := (euler_odd_distinct q hq).1
  have hBinv : (∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 - q * (-q) ^ n)) = 1 := by
    rw [hBeq]
    linear_combination hEuler
  have hBne : (∏' n : ℕ, (1 - q * (-q) ^ n)) ≠ 0 :=
    right_ne_zero_of_mul (by rw [hBinv]; exact one_ne_zero)
  -- Entry 19 with `a = b = q`.
  have h19 := (entry19 q q (by rw [show q * q = q ^ 2 by ring]; exact hq2)).2.2.2
  rw [show q * q = q ^ 2 by ring] at h19
  have hval : (∏' n : ℕ, (1 - (-q) ^ (n + 1))) / (∏' n : ℕ, (1 - q * (-q) ^ n)) =
      (∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) * (∏' n : ℕ, (1 + q * (q ^ 2) ^ n)) *
        (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) := by
    rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_left hBinv, hAeq]
    ring
  rw [hval]
  refine ⟨hA, hB, hBne, h19, ?_⟩
  rwa [show (fun t : ℤ => q ^ (t ^ 2)) = fun t : ℤ => ramanujanThetaTerm q q t from
    funext fun t => (ramanujanThetaTerm_self q t).symm]

/-- Entry 22(i) in Ramanujan's notation: `φ(q) = f(q, q) = (-q; -q)_∞ / (q; -q)_∞`
for `|q| < 1`. This is an equation of `tsum` and `tprod`; convergence is stated in
`entry22_i`. -/
theorem entry22_i_ramanujanTheta (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanTheta q q =
      (∏' n : ℕ, (1 - (-q) ^ (n + 1))) / ∏' n : ℕ, (1 - q * (-q) ^ n) :=
  (entry22_i q hq).2.2.2.1.tsum_eq

/-- **Entry 22(ii)** (Berndt, Part III, Ch. 16, p. 36). For `|q| < 1`, the products
`(q²; q²)_∞ = ∏_{n ≥ 0} (1 - (q²)^{n+1})` and `(q; q²)_∞ = ∏_{n ≥ 0} (1 - q (q²)ⁿ)`
converge, the second is nonzero, and both `f(q, q³)` (summed over `t ∈ ℤ`) and
`∑_{t ≥ 0} q^{t(t+1)/2}` converge to `(q²; q²)_∞ / (q; q²)_∞`. -/
theorem entry22_ii (q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 - (q ^ 2) ^ (n + 1)) (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) ∧
    HasProd (fun n : ℕ => 1 - q * (q ^ 2) ^ n) (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) ∧
    (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) ≠ 0 ∧
    HasSum (fun t : ℤ => ramanujanThetaTerm q (q ^ 3) t)
      ((∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) / ∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) ∧
    HasSum (fun t : ℕ => q ^ (t * (t + 1) / 2))
      ((∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) / ∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) := by
  have hq2 := norm_pow_lt_one q hq 2 (by norm_num)
  have hq4 := norm_pow_lt_one q hq 4 (by norm_num)
  obtain ⟨hEuler, hE2⟩ := euler_odd_distinct q hq
  -- `(-q; q²)_∞ = (-q; q⁴)_∞ (-q³; q⁴)_∞`
  have hP1 : HasProd (fun n : ℕ => 1 + q * (q ^ 2) ^ n)
      ((∏' n : ℕ, (1 + q * (q ^ 4) ^ n)) * (∏' n : ℕ, (1 + q ^ 3 * (q ^ 4) ^ n))) := by
    refine HasProd.even_mul_odd ?_ ?_
    · convert hasProd_one_add_mul_pow q (q ^ 4) hq4 using 1
      funext k
      ring
    · convert hasProd_one_add_mul_pow (q ^ 3) (q ^ 4) hq4 using 1
      funext k
      ring
  have hP1eq := (hasProd_one_add_mul_pow q (q ^ 2) hq2).unique hP1
  have hDne : (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) ≠ 0 := by
    intro h0
    rw [h0] at hEuler
    simp at hEuler
  -- Entry 19 with `a = q`, `b = q³`.
  have h19 := (entry19 q (q ^ 3) (by rw [show q * q ^ 3 = q ^ 4 by ring]; exact hq4)).2.2.2
  rw [show q * q ^ 3 = q ^ 4 by ring] at h19
  have hval : (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) / (∏' n : ℕ, (1 - q * (q ^ 2) ^ n)) =
      (∏' n : ℕ, (1 + q * (q ^ 4) ^ n)) * (∏' n : ℕ, (1 + q ^ 3 * (q ^ 4) ^ n)) *
        (∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1))) := by
    rw [div_eq_iff hDne, hE2, hP1eq]
    ring
  rw [hval]
  refine ⟨hasProd_one_sub_pow_succ (q ^ 2) hq2, hasProd_one_sub_mul_pow q (q ^ 2) hq2, hDne,
    h19, ?_⟩
  -- Fold the two-sided sum over `t ∈ ℤ` into the one-sided sum over `ℕ`.
  have h := natEquivIntPsi.hasSum_iff.mpr h19
  convert h using 1
  funext k
  rw [Function.comp_apply, ramanujanThetaTerm_cube, natEquivIntPsi_exponent, zpow_natCast]

/-- Entry 22(ii) in Ramanujan's notation: `ψ(q) = f(q, q³) = (q²; q²)_∞ / (q; q²)_∞`
for `|q| < 1`. This is an equation of `tsum` and `tprod`; convergence is stated in
`entry22_ii`. -/
theorem entry22_ii_ramanujanTheta (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanTheta q (q ^ 3) =
      (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) / ∏' n : ℕ, (1 - q * (q ^ 2) ^ n) :=
  (entry22_ii q hq).2.2.2.1.tsum_eq

end RamanujanLean.Berndt.Part3.Ch16
