import Mathlib
import Aesop

--set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- [thm:1.1] If `a` and `b` are integers with `b > 0`, then there is a unique pair of integers
`q` and `r` such that `a = q*b + r` and `0 ≤ r < b`. -/
theorem thm_1_1 (a b : ℤ) (hb : 0 < b) :
  ∃! (qr : ℤ × ℤ), a = qr.1 * b + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < b := by sorry

/-- [cor:1.2] If `a` and `b` are integers with `b ≠ 0`, then there is a unique pair of integers
`q` and `r` such that `a = q*b + r` and `0 ≤ r < |b|`. -/
theorem cor_1_2 (a b : ℤ) (hb : b ≠ 0) :
  ∃! p : ℤ × ℤ, a = p.1 * b + p.2 ∧ 0 ≤ p.2 ∧ p.2 < Int.natAbs b := by sorry

/-- [thm:1.3] (a) If `c` divides each `aᵢ`, then `c` divides any linear combination
`a₁u₁ + ⋯ + aₖuₖ`. (b) `a ∣ b` and `b ∣ a` iff `a = ± b`. -/
theorem thm_1_3 :  (∀ (k : ℕ) (c : ℤ) (a : Fin k → ℤ) (u : Fin k → ℤ),
  (∀ i, c ∣ a i) → c ∣ (∑ i, a i * u i)) ∧
  (∀ a b : ℤ, (a ∣ b ∧ b ∣ a) ↔ (a = b ∨ a = -b)) := by sorry

/-- [cor:1.4] If `c` divides `a` and `b`, then `c` divides `a*u + b*v` for all integers `u` and
`v`. -/
theorem cor_1_4 (a b c : ℤ) (h1 : c ∣ a) (h2 : c ∣ b) : ∀ u v : ℤ, c ∣ (a * u + b * v) := by sorry

/-- [lem:1.5] If `a = q*b + r` then `gcd a b = gcd b r`. -/
theorem lem_1_5 {a b q r : Int} (h : a = q * b + r) :
  Int.gcd a b = Int.gcd b r := by
  sorry

/-- [thm:1.6] In the Euclidean algorithm calculation, the final Bézout coefficients satisfy
`d = a*x + b*y` for a concrete example `a = 37`, `b = 12`. -/
theorem thm_1_6 :
  let a : ℤ := 37
  let b : ℤ := 12
  let d : ℤ := Int.gcd a b
  ∃ x y : ℤ, d = a * x + b * y ∧ x = Int.gcdA a b ∧ y = Int.gcdB a b := by
  sorry

/-- [thm:1.7] If `a` and `b` are integers, not both zero, then there exist integers `u` and `v`
such that `gcd a b = a*u + b*v`. -/
theorem thm_1_7 (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
  ∃ u v : ℤ, Int.gcd a b = a * u + b * v := by
  sorry

/-- [thm:1.8] Let `a` and `b` be integers (not both zero) with greatest common divisor `d`. Then
`c = a*x + b*y` iff `c` is a multiple of `d`; moreover `d` is the least positive integer of that
form. -/
theorem thm_1_8 (a b : Int) (h : ¬(a = 0 ∧ b = 0)) :
  let d := Int.gcd a b
  (∀ c : Int,
    (∃ x y : Int, c = a * x + b * y) ↔ ∃ k : Int, c = d * k) ∧
  (∃ x y : Int, d = a * x + b * y) ∧
  (∀ x y : Int, 0 < a * x + b * y → d ≤ a * x + b * y) := by
  sorry

/-- [cor:1.9] Two integers `a` and `b` are coprime iff there exist integers `x, y` with
`a*x + b*y = 1`. -/
theorem cor_1_9 (a b : Int) :
  Int.gcd a b = 1 ↔ ∃ (x y : Int), a * x + b * y = 1 := by
  sorry

/-- [cor:1.10] If `gcd a b = d` then `gcd (m*a) (m*b) = m*d` for every integer `m > 0`, and
`gcd (a/d) (b/d) = 1`. -/
theorem cor_1_10 (a b d : ℤ) (h : Int.gcd a b = d) (hd : d ≠ 0) :
  (∀ (m : ℕ), 0 < m → Int.gcd (m * a) (m * b) = m * d) ∧
  Int.gcd (a / d) (b / d) = 1 := by
  sorry

/-- [cor:1.11] Let `a` and `b` be coprime integers. (a) If `a ∣ c` and `b ∣ c` then `a*b ∣ c`.
(b) If `a ∣ b*c` then `a ∣ c`. -/
theorem cor_1_11 :
  ∀ (a b c : Int),
  Int.gcd a b = 1 →
  ((a ∣ c) ∧ (b ∣ c) → (a * b ∣ c)) ∧
  ((a ∣ b * c) → (a ∣ c)) := by
  sorry

/-- [thm:1.12] Let `a` and `b` be positive integers with `d = gcd a b` and `l = lcm a b`. Then
`d * l = a * b`. -/
theorem thm_1_12 (a b : Nat) (ha : a > 0) (hb : b > 0) :
  (Nat.gcd a b) * (Nat.lcm a b) = a * b := by
  sorry

/-- [thm:1.13] Let `a, b, c` be integers, with `a` and `b` not both 0, and `d = gcd a b`. The
equation `a*x + b*y = c` has integer solutions iff `d ∣ c`, and when it does the solutions are
`x = x₀ + (b*n)/d`, `y = y₀ - (a*n)/d` for `n ∈ ℤ`. -/
theorem thm_1_13 (a b c : ℤ) (h_not_both_zero :
  ¬(a = 0 ∧ b = 0))(d : ℤ) (h_d : d = Int.gcd a b) :
  (∃ x y : ℤ, a * x + b * y = c) ↔ (d ∣ c) ∧(∃ x₀ y₀ : ℤ, a * x₀ + b * y₀ = c ∧
  ∀ x y : ℤ, a * x + b * y = c ↔
  ∃ n : ℤ, x = x₀ + (b * n) / d ∧ y = y₀ - (a * n) / d) := by
  sorry
