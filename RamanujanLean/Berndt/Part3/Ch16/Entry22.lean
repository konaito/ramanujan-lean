import RamanujanLean.Defs.Theta
import QseriesFormalization.Chapter04

/-!
# Berndt, Ramanujan's Notebooks Part III, Chapter 16, Entry 22(iii)

Source: Berndt, *Ramanujan's Notebooks, Part III* (Springer, 1991), p. 36,
Entry 22(iii). Cited in this form in Rajkhowa–Saikia, arXiv:2305.14988, eq. (1.6):

  f(-q) := f(-q, -q²) = ∑_{t=-∞}^{∞} (-1)^t q^{t(3t-1)/2} = (q; q)_∞,   |q| < 1.

The proof reuses Euler's pentagonal number theorem from
`invitation-to-qseries-lean` (Apache-2.0),
`QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum'`.
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

/-- Entry 22(iii) in Ramanujan's notation: `f(-q, -q²) = (q; q)_∞` for `|q| < 1`. -/
theorem entry22_iii_ramanujanTheta (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanTheta (-q) (-q ^ 2) = ∏' n : ℕ, (1 - q ^ (n + 1)) :=
  (entry22_iii q hq).2.2.tsum_eq

end RamanujanLean.Berndt.Part3.Ch16
