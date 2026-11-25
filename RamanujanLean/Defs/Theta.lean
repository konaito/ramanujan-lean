import Mathlib

/-!
# Ramanujan's general theta function

Berndt, *Ramanujan's Notebooks, Part III*, p. 34:

  f(a, b) = ∑_{t = -∞}^{∞} a^{t(t+1)/2} b^{t(t-1)/2},   |ab| < 1.

The exponents `t(t+1)/2` and `t(t-1)/2` are nonnegative integers for every
`t : ℤ`, so `zpow` agrees with the usual power here.

`ramanujanTheta` is defined with `tsum`, which is `0` for a non-summable
family. Theorems about it should therefore state `HasSum` (convergence and
value), not only an equation between `tsum`s.
-/

namespace RamanujanLean

/-- The `t`-th term of Ramanujan's `f(a, b)`. -/
noncomputable def ramanujanThetaTerm (a b : ℂ) (t : ℤ) : ℂ :=
  a ^ (t * (t + 1) / 2) * b ^ (t * (t - 1) / 2)

/-- Ramanujan's general theta function `f(a, b)`. -/
noncomputable def ramanujanTheta (a b : ℂ) : ℂ :=
  ∑' t : ℤ, ramanujanThetaTerm a b t

end RamanujanLean
