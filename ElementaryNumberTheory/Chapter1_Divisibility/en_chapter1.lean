import Mathlib

/-!
# Elementary Number Theory - Chapter 1: Divisibility
**Source:** Gareth A. Jones and J. Mary Jones, Springer Undergraduate Mathematics Series.

This file contains the formal statements of the theorems in Chapter 1.
-/

namespace ElementaryNumberTheory.Chapter1

section Divisors

/-! ## 1.1 Divisors -/

/-
### Theorem 1.1 (The Division Algorithm)
If $a$ and $b$ are integers with $b > 0$, then there is a unique pair of integers $q$ and $r$
such that $a = qb + r$ and $0 \le r < b$.
-/
#check Int.ediv_add_emod
#check Int.emod_nonneg
#check Int.emod_lt
#check Int.ediv_emod_unique

theorem theorem_1_1_division_algorithm (a b : ℤ) (h : b > 0) :
  ∃! r : ℤ × ℤ, a = r.1 * b + r.2 ∧ 0 ≤ r.2 ∧ r.2 < b := by
  refine ⟨⟨a/b, a%b⟩ , ?_, ?_⟩
  · simp
    rw [Int.mul_comm]
    rw [Int.mul_ediv_add_emod]
    simp
    constructor
    · refine Int.emod_nonneg a (by linarith)
    · have hb : b ≠ 0 := by linarith
      have := Int.emod_lt a hb
      have hb_abs : (b:ℤ) = (Int.natAbs b) := by omega
      rw [← hb_abs] at this
      exact this
  · intro r ⟨hq, hr1, hr2⟩
    have huniq := Int.ediv_emod_unique (a := a) (b := b) (q := r.1) (r := r.2) h
    have huniq' := huniq.mpr ⟨by
      rw [add_comm, mul_comm]
      exact hq.symm, hr1, hr2⟩
    rw [huniq'.1, huniq'.2]
  done
/-
### Corollary 1.2
If $a$ and $b$ are integers with $b \ne 0$, then there is a unique pair of integers $q$ and $r$
such that $a = qb + r$ and $0 \le r < |b|$.
-/
#check Int.ediv_emod_unique'
theorem corollary_1_2_general_division (a b : ℤ) (h : b ≠ 0) :
  ∃! r : ℤ × ℤ, a = r.1 * b + r.2 ∧ 0 ≤ r.2 ∧ r.2 < abs b := by
  refine ⟨⟨a/b, a%b⟩ , ?_, ?_⟩
  · simp
    rw [Int.mul_comm]
    rw [Int.mul_ediv_add_emod]
    simp
    constructor
    · exact Int.emod_nonneg a h
    · have hb_abs : abs b = Int.natAbs b := by exact Int.abs_eq_natAbs b
      have := Int.emod_lt a h
      rw [← hb_abs] at this
      exact this
  · intro r ⟨hq, hr1, hr2⟩
    --对b>0和b<0两种情况分别讨论
    by_cases hb : b > 0
    · have huniq := Int.ediv_emod_unique (a := a) (b := b) (q := r.1) (r := r.2) hb
      have absb : abs b = b := by exact abs_of_pos hb
      have huniq' := huniq.mpr ⟨by
        rw [add_comm, mul_comm]
        exact hq.symm, hr1, by exact lt_of_lt_of_eq hr2 absb⟩
      rw [huniq'.1, huniq'.2]
    · have hb_neg : b < 0 := by
        apply lt_of_le_of_ne
        linarith
        exact h
      have huniq := Int.ediv_emod_unique' (a := a) (b := b) (q := r.1) (r := r.2) hb_neg
      have absb : abs b = - b := by exact abs_of_neg hb_neg
      have huniq' := huniq.mpr ⟨by
        rw [add_comm, mul_comm]
        exact hq.symm, hr1, by exact lt_of_lt_of_eq hr2 absb⟩
      rw [huniq'.1, huniq'.2]
  done

/-
### Definition: Divisibility
An integer $b$ divides $a$ (written $b \mid a$) if $a = qb$ for some integer $q$.
Note: In Mathlib, this is represented by the notation `\|` (typed as `\|`).
-/
#check Dvd.dvd
/-
### Theorem 1.3
(a) If $c$ divides $a_1, \dots, a_k$, then $c$ divides $a_1 u_1 + \dots + a_k u_k$ for all integers $u_1, \dots, u_k$.
-/
theorem theorem_1_3_a_aux (k : ℕ) (a u : Fin k → ℤ) (c : ℤ) (h : ∀ i, c ∣ a i) :
  ∀ i, c ∣ a i * u i := by
  intro i
  exact dvd_mul_of_dvd_left (h i) (u i)

theorem theorem_1_3_a (k : ℕ) (a u : Fin k → ℤ) (c : ℤ) (h : ∀ i, c ∣ a i) :
  c ∣ ∑ i, a i * u i := by
  have hmul := theorem_1_3_a_aux (k := k) (a := a) (u := u) (c := c) h
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin k))) ?base ?step
  · simp
  · intro i s hi ih
    have hc : c ∣ a i * u i := hmul i
    have hs : c ∣ ∑ j ∈ s, a j * u j := ih
    have hsum : c ∣ a i * u i + ∑ j ∈ s, a j * u j := dvd_add hc hs
    simpa [Finset.sum_insert, hi, add_comm, add_left_comm, add_assoc] using hsum
  done
/-
(b) $a \mid b$ and $b \mid a$ if and only if $a = \pm b$.
-/
-- Part (a) formulated for two integers (See Corollary 1.4) or List.
-- Here we formalize part (b)
theorem theorem_1_3_b (a b : ℤ) :
  a ∣ b ∧ b ∣ a ↔ a = b ∨ a = -b := by
  constructor
  · rintro ⟨hab, hba⟩
    obtain ⟨k, hk⟩ := hab
    obtain ⟨l, hl⟩ := hba
    -- combine the two divisibility equalities
    have hcomp : a = a * (k * l) := by
      calc
        a = b * l := hl
        _ = (a * k) * l := by simpa [hk]
        _ = a * (k * l) := by ring
    have hzero : (1 - k * l) * a = 0 := by
      calc
        (1 - k * l) * a = a - a * (k * l) := by ring
        _ = a - a := by rw [← hcomp]
        _ = 0 := by ring
    have hcases := eq_zero_or_eq_zero_of_mul_eq_zero hzero
    cases hcases with
    | inr ha0 =>
        -- a = 0 ⇒ b = 0
        have hb0 : b = 0 := by simpa [hk, ha0]
        left; simp [ha0, hb0]
    | inl hkl1 =>
        have hkl1' : k * l = 1 := by linarith
        have hunit_l : IsUnit l := by
          have hunit_prod : IsUnit (k * l) := by simpa [hkl1'] using (isUnit_one : IsUnit (1:ℤ))
          exact isUnit_of_mul_isUnit_right hunit_prod
        rcases Int.isUnit_iff.mp hunit_l with rfl | rfl
        · -- l = 1
          left; simpa [hk] using hl
        · -- l = -1
          right; have : a = b * (-1) := by simpa using hl
          simpa using this
  · intro h
    constructor
    · rcases h with rfl | rfl <;> simp
    · rcases h with rfl | rfl <;> simp
  done
/-
### Corollary 1.4
If $c$ divides $a$ and $b$, then $c$ divides $au + bv$ for all integers $u$ and $v$.
-/
theorem corollary_1_4 (a b c u v : ℤ) (ha : c ∣ a) (hb : c ∣ b) :
  c ∣ (a * u + b * v) := by
  -- package the two coefficients into functions on `Fin 2`
  let A : Fin 2 → ℤ := Fin.cases a (fun _ => b)
  let U : Fin 2 → ℤ := Fin.cases u (fun _ => v)
  -- `c` divides each `A i`
  have hA : ∀ i, c ∣ A i := by
    intro i; refine Fin.cases ?h0 ?h1 i
    · simpa [A] using ha
    · intro _; simpa [A] using hb
  -- apply Theorem 1.3(a)
  have hsum : c ∣ ∑ i, A i * U i :=
    theorem_1_3_a (k := 2) (a := A) (u := U) (c := c) hA
  -- unfold the packaged functions and the sum over `Fin 2`
  simpa [A, U, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] using hsum

/-
### Definition: Greatest Common Divisor
Let $a$ and $b$ be integers, not both 0. The greatest common divisor $d = \gcd(a, b)$ is the unique integer satisfying:
1. $d \mid a$ and $d \mid b$.
2. If $c \mid a$ and $c \mid b$, then $c \le d$.

Note: In Mathlib, `Int.gcd a b` returns a `Nat`. We usually cast it to `Int` using `(a.gcd b : ℤ)`.
 `Int.gcd 0 0` returns `0`.
-/

/-
### Lemma 1.5
If $a = qb + r$, then $\gcd(a, b) = \gcd(b, r)$.
-/
#check gcd_comm
theorem lemma_1_5 (a b q r : ℤ) (h : a = q * b + r) :
  Int.gcd a b = Int.gcd b r := by
  subst h
  -- use invariance of gcd under adding a multiple of the second argument to the first
  calc
    Int.gcd (q * b + r) b = Int.gcd (r + q * b) b := by
      simp [add_comm, add_left_comm, add_assoc]
    _ = Int.gcd r b := by simp
    _ = Int.gcd b r := Int.gcd_comm _ _

/-
Theorem 1.6 (Euclid's Algorithm Result)
Statement: In the Euclidean algorithm calculation,
          the greatest common divisor $d$ is equal to
          the last non-zero remainder $r_{n-1}$.
Formalization: This implies that the recursive calculation
           of GCD terminates and computes the correct value.
-/

end Divisors

section Bezout

/-! ## 1.2 Bezout's Identity -/

/-
### Theorem 1.7 (Bezout's Identity)
If $a$ and $b$ are integers (not both 0), then there exist integers $u$ and $v$ such that
$\gcd(a, b) = au + bv$.
在Mathlib中，`Int.gcd a b`返回一个自然数，我们通常将其转换为整数使用`(Int.gcd a b : ℤ)`。
且`Int.gcd 0 0`返回`0`,因此无需额外假设`a`和`b`不全为零。
-/
#check Int.gcd_eq_gcd_ab
theorem theorem_1_7_bezout (a b : ℤ) :
  ∃ u v : ℤ, (Int.gcd a b : ℤ) = a * u + b * v := by
  refine ⟨Int.gcdA a b, Int.gcdB a b, ?_⟩
  simpa using Int.gcd_eq_gcd_ab a b

/-
### Theorem 1.8
Let $a$ and $b$ be integers (not both 0) with greatest common divisor $d$.
Then an integer $c$ has the form $ax + by$ for some $x, y \in \mathbb{Z}$ if and only if $c$ is a multiple of $d$.
In particular, $d$ is the least positive integer of the form $ax + by$.
-/
theorem theorem_1_8_a (a b c : ℤ) :
  (∃ x y : ℤ, c = a * x + b * y) ↔ (Int.gcd a b : ℤ) ∣ c := by
  constructor
  -- Forward direction: if c = a*x + b*y, then gcd(a,b) | c
  · intro ⟨x, y, hxy⟩
    have ha : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
    have hb : (Int.gcd a b : ℤ) ∣ b := Int.gcd_dvd_right a b
    have hax : (Int.gcd a b : ℤ) ∣ a * x := dvd_mul_of_dvd_left ha x
    have hby : (Int.gcd a b : ℤ) ∣ b * y := dvd_mul_of_dvd_left hb y
    have : (Int.gcd a b : ℤ) ∣ a * x + b * y := dvd_add hax hby
    rwa [hxy]
  -- Backward direction: if gcd(a,b) | c, then c = a*x + b*y for some x, y
  · intro ⟨k, hk⟩
    -- By Bezout's identity, gcd(a,b) = a*u + b*v for some u, v
    obtain ⟨u, v, huv⟩ := theorem_1_7_bezout a b
    -- Since c = k * gcd(a,b) = k * (a*u + b*v) = a*(k*u) + b*(k*v)
    refine ⟨k * u, k * v, ?_⟩
    calc
      c = k * (Int.gcd a b : ℤ) := by rw [hk, mul_comm]
      _ = k * (a * u + b * v) := by rw [← huv]
      _ = a * (k * u) + b * (k * v) := by ring

--定理1_8_b待优化
theorem theorem_1_8_b (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
  0 < (Int.gcd a b : ℤ) ∧
  (∃ x y : ℤ, (Int.gcd a b : ℤ) = a * x + b * y) ∧
  ∀ e : ℤ, 0 < e → (∃ x y : ℤ, e = a * x + b * y) → (Int.gcd a b : ℤ) ≤ e := by
  -- positivity of gcd when not both zero
  have hgcd_ne_zero : Int.gcd a b ≠ 0 := by
    have hzero_iff := Int.gcd_eq_zero_iff (a := a) (b := b)
    exact by
      intro h0
      have := (hzero_iff.mp h0)
      rcases this with ⟨ha, hb⟩
      cases h with
      | inl ha' => exact (ha' ha).elim
      | inr hb' => exact (hb' hb).elim
  have hgcd_pos : 0 < (Int.gcd a b : ℤ) := by
    have hgcd_pos_nat : 0 < Int.gcd a b := Nat.pos_of_ne_zero hgcd_ne_zero
    exact_mod_cast hgcd_pos_nat
  -- Bézout representation from Mathlib
  have hbezout : ∃ x y : ℤ, (Int.gcd a b : ℤ) = a * x + b * y :=
    theorem_1_7_bezout a b
  -- minimality among positive linear combinations
  have hmin : ∀ e : ℤ, 0 < e → (∃ x y : ℤ, e = a * x + b * y) → (Int.gcd a b : ℤ) ≤ e := by
    intro e hepos hexpr
    obtain ⟨x, y, hxy⟩ := hexpr
    -- gcd divides any linear combination
    have hdvd : (Int.gcd a b : ℤ) ∣ e := by
      have hdvd_a : (Int.gcd a b : ℤ) ∣ a := by exact Int.gcd_dvd_left a b
      have hdvd_b : (Int.gcd a b : ℤ) ∣ b := by exact Int.gcd_dvd_right a b
      have hdvd_ax : (Int.gcd a b : ℤ) ∣ a * x := dvd_mul_of_dvd_left hdvd_a x
      have hdvd_by : (Int.gcd a b : ℤ) ∣ b * y := dvd_mul_of_dvd_left hdvd_b y
      have hdvd_sum : (Int.gcd a b : ℤ) ∣ a * x + b * y := dvd_add hdvd_ax hdvd_by
      simpa [hxy] using hdvd_sum
    rcases hdvd with ⟨k, hk⟩
    -- k must be positive since e and gcd are positive
    have hkpos : 0 < k := by
      have hmulpos : 0 < (Int.gcd a b : ℤ) * k := by simpa [hk] using hepos
      have := (mul_pos_iff_of_pos_left hgcd_pos).1 hmulpos
      exact this
    have hk1 : (1 : ℤ) ≤ k := by linarith
    calc
      (Int.gcd a b : ℤ) = (Int.gcd a b : ℤ) * 1 := by ring
      _ ≤ (Int.gcd a b : ℤ) * k := by
        have hgcd_nonneg : 0 ≤ (Int.gcd a b : ℤ) := le_of_lt hgcd_pos
        exact mul_le_mul_of_nonneg_left hk1 hgcd_nonneg
      _ = e := by simpa [hk, mul_comm]
  exact ⟨hgcd_pos, hbezout, hmin⟩
/-
### [cite_start]Corollary 1.9 [cite: 107]
Two integers $a$ and $b$ are coprime if and only if there exist integers $x$ and $y$ such that
$ax + by = 1$.
-/
#check Nat.Coprime
#check Int.isCoprime_gcdA
#check IsCoprime
theorem corollary_1_9 (a b : ℤ) :
  Int.gcd a b = 1 ↔ ∃ x y : ℤ, a * x + b * y = 1 := by
  constructor
  · intro h
    obtain ⟨u, v, huv⟩ := theorem_1_7_bezout a b
    refine ⟨u, v, ?_⟩
    rw [h] at huv
    simp at huv
    exact huv.symm
  · intro ⟨x, y, hxy⟩
    have ha : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
    have hb : (Int.gcd a b : ℤ) ∣ b := Int.gcd_dvd_right a b
    have h1 : (Int.gcd a b : ℤ) ∣ 1 := by
      have : (Int.gcd a b : ℤ) ∣ a * x + b * y :=
        dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y)
      rwa [hxy] at this
    have hcases : (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = -1 := by
      refine (theorem_1_3_b (↑(a.gcd b)) 1).mp ?_
      simpa using h1
    have hnonneg : 0 ≤ (Int.gcd a b : ℤ) := by
      exact_mod_cast (Nat.zero_le (Int.gcd a b))
    cases hcases with
    | inl hpos => exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm hpos)))
    | inr hneg =>
        exfalso
        have : (0:ℤ) ≤ -1 := by simpa [hneg] using hnonneg
        linarith

theorem corollary_1_9' (a b : ℤ) :
  IsCoprime a b ↔ ∃ x y : ℤ, a * x + b * y = 1 := by
  have h_gcd_1 : Int.gcd a b = 1 ↔ IsCoprime a b := by
    exact Iff.symm Int.isCoprime_iff_gcd_eq_one
  rw [← h_gcd_1]
  exact corollary_1_9 a b

/-
### [cite_start]Corollary 1.10 [cite: 108]
If $\gcd(a, b) = d$, then $\gcd(ma, mb) = m \cdot d$ for every integer $m > 0$, and
$\gcd(a/d, b/d) = 1$.
-/
theorem corollary_1_10 (a b : ℤ) (m : ℕ) (hm : m > 0) :
  Int.gcd (a * m) (b * m) = (Int.gcd a b) * m := by
  -- `Int.gcd` is defined via `Nat.gcd` on `natAbs`, so we work there.
  have ha : Int.natAbs (a * m) = m * Int.natAbs a := by
    -- `natAbs` distributes over multiplication and `natAbs (m:ℤ) = m`.
    have := Int.natAbs_mul a (m : ℤ)
    simpa [Nat.mul_comm] using this
  have hb : Int.natAbs (b * m) = m * Int.natAbs b := by
    have := Int.natAbs_mul b (m : ℤ)
    simpa [Nat.mul_comm] using this
  -- unfold and use the natural-number lemma `Nat.gcd_mul_left`.
  unfold Int.gcd
  simp [ha, hb, Nat.gcd_mul_left, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem corollary_1_10_part2 (a b : ℤ) (d : ℤ) (h : d = Int.gcd a b) (hd : d ≠ 0) :
  Int.gcd (a / d) (b / d) = 1 := by
  -- divisibility of `d` into `a` and `b`
  have ha : d ∣ a := by simpa [h] using Int.gcd_dvd_left a b
  have hb : d ∣ b := by simpa [h] using Int.gcd_dvd_right a b
  rcases ha with ⟨ka, hka⟩
  rcases hb with ⟨kb, hkb⟩
  -- Bézout for `a` and `b`, rewritten using `d`.
  obtain ⟨u, v, huv⟩ := theorem_1_7_bezout a b
  have huv' : d = a * u + b * v := by simpa [h] using huv
  -- factor out `d`.
  have hfact : d = d * (ka * u + kb * v) := by
    calc
      d = a * u + b * v := huv'
      _ = (d * ka) * u + (d * kb) * v := by simpa [hka, hkb, mul_comm, mul_left_comm, mul_assoc]
      _ = d * (ka * u + kb * v) := by ring
  -- cancel the nonzero factor `d` to get a Bézout identity for `ka` and `kb`.
  have hcomb : ka * u + kb * v = 1 := by
    have hd' : d ≠ 0 := hd
    have hdiv := congrArg (fun x => x / d) hfact
    have hleft : d / d = (1 : ℤ) := Int.ediv_self hd'
    have hright : (d * (ka * u + kb * v)) / d = ka * u + kb * v := Int.mul_ediv_cancel_left _ hd'
    calc
      ka * u + kb * v = (d * (ka * u + kb * v)) / d := hright.symm
      _ = d / d := by rw [← hfact]
      _ = 1 := hleft
  -- gcd(ka, kb) = 1 by the Bézout identity.
  have hgcd : Int.gcd ka kb = 1 := (corollary_1_9 ka kb).2 ⟨u, v, hcomb⟩
  -- identify the quotients `a / d` and `b / d` with `ka` and `kb`.
  have hqa : a / d = ka := by
    have hd' : d ≠ 0 := hd
    calc
      a / d = (d * ka) / d := by simpa [hka]
      _ = ka := Int.mul_ediv_cancel_left _ hd'
  have hqb : b / d = kb := by
    have hd' : d ≠ 0 := hd
    calc
      b / d = (d * kb) / d := by simpa [hkb]
      _ = kb := Int.mul_ediv_cancel_left _ hd'
  -- conclude.
  simpa [hqa, hqb, hgcd]

/-
### [cite_start]Corollary 1.11 [cite: 108]
Let $a$ and $b$ be coprime integers.
(a) If $a \mid c$ and $b \mid c$, then $ab \mid c$.
(b) If $a \mid bc$, then $a \mid c$ (Euclid's Lemma).
-/
theorem corollary_1_11_b (a b c : ℤ) (h_coprime : Int.gcd a b = 1) :
  a ∣ (b * c) → a ∣ c := by
  intro hdiv
  obtain ⟨x, y, hxy⟩ := (corollary_1_9 a b).1 h_coprime
  have h1 : a ∣ a * (x * c) := by
    refine ⟨x * c, ?_⟩
    ring
  have h2 : a ∣ b * (y * c) := by
    have hbc : a ∣ b * c := hdiv
    have hbc_mul : a ∣ (b * c) * y := dvd_mul_of_dvd_left hbc y
    have : b * (y * c) = (b * c) * y := by ring
    rw [this]
    exact hbc_mul
  have hsum : a ∣ a * (x * c) + b * (y * c) := dvd_add h1 h2
  have hbezout_mul : a * (x * c) + b * (y * c) = c := by
    calc
      a * (x * c) + b * (y * c) = (a * x + b * y) * c := by ring
      _ = 1 * c := by simpa [hxy]
      _ = c := by ring
  simpa [hbezout_mul] using hsum

theorem corollary_1_11_a (a b c : ℤ) (h_coprime : Int.gcd a b = 1) :
  a ∣ c → b ∣ c → (a * b) ∣ c := by
  intro ha hb
  rcases ha with ⟨k, hk⟩
  rcases hb with ⟨l, hl⟩
  have hb_coprime : Int.gcd b a = 1 := by simpa [Int.gcd_comm] using h_coprime
  have hbk : b ∣ a * k := by
    refine ⟨l, ?_⟩
    calc
      a * k = c := hk.symm
      _ = b * l := hl
  have hdivk : b ∣ k := corollary_1_11_b b a k hb_coprime hbk
  rcases hdivk with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  calc
    c = a * k := hk
    _ = a * (b * t) := by simpa [ht, mul_left_comm, mul_assoc]
    _ = a * b * t := by ring

end Bezout

section LCM

/-! ## 1.3 Least Common Multiples -/

/-
### [cite_start]Definition: Least Common Multiple [cite: 109]
The least common multiple $l = \text{lcm}(a, b)$ of non-zero integers $a, b$ is the unique positive integer satisfying:
1. $a \mid l$ and $b \mid l$.
2. If $a \mid c$ and $b \mid c$ with $c > 0$, then $l \le c$.
-/

/-
### [cite_start]Theorem 1.12 [cite: 109]
Let $a$ and $b$ be positive integers. Then $\gcd(a, b) \cdot \text{lcm}(a, b) = ab$.
-/
theorem theorem_1_12 (a b : ℕ) (ha : a > 0) (hb : b > 0) :
  (Nat.gcd a b) * (Nat.lcm a b) = a * b := by
  -- standard identity from `Nat`
  simpa using Nat.gcd_mul_lcm a b

end LCM

section Diophantine

/-! ## 1.4 Linear Diophantine Equations -/

/-
### [cite_start]Theorem 1.13 [cite: 110]
Let $a, b, c$ be integers with $a, b$ not both 0, and let $d = \gcd(a, b)$.
Then the equation $ax + by = c$ has an integer solution $x, y$ if and only if $d$ divides $c$.
If $d \mid c$, then there are infinitely many solutions. If $(x_0, y_0)$ is a particular solution,
the general solution is given by:
$x = x_0 + (b/d)n$
$y = y_0 - (a/d)n$
where $n \in \mathbb{Z}$.
-/
theorem theorem_1_13_solvability (a b c : ℤ) (h_not_zero : a ≠ 0 ∨ b ≠ 0) :
  (∃ x y : ℤ, a * x + b * y = c) ↔ (Int.gcd a b : ℤ) ∣ c := by
  -- this is exactly Theorem 1.8(a)
  rw [← theorem_1_8_a a b c]
  aesop

theorem theorem_1_13_general_solution (a b c x₀ y₀ : ℤ)
  (h_gcd : (Int.gcd a b : ℤ) ∣ c)
  (h_particular : a * x₀ + b * y₀ = c)
  (d : ℤ) (hd : d = Int.gcd a b) (hd_nez : d ≠ 0) :
  ∀ x y : ℤ, (a * x + b * y = c) ↔
    ∃ n : ℤ, x = x₀ + (b / d) * n ∧ y = y₀ - (a / d) * n := by
  -- write a = d * a', b = d * b'
  rcases Int.gcd_dvd_left a b with ⟨a', ha'⟩
  rcases Int.gcd_dvd_right a b with ⟨b', hb'⟩
  have hcop : Int.gcd (a / d) (b / d) = 1 := by
    have := corollary_1_10_part2 a b d hd hd_nez
    exact this
  -- rewrite the quotients once so we can reuse
  have ha_div : a / d = a' := by
    calc
      a / d = ((a.gcd b)* a') / d := by
          --只在目标的第一个a处替换 1st_rewrite
          nth_rw 1 [ha']
      _ = (d * a') / d := by rw [← hd]
      _ = a' := Int.mul_ediv_cancel_left _ hd_nez
  have hb_div : b / d = b' := by
    calc
      b / d = ((a.gcd b) * b') / d := by
        -- 只在目标的第一个 b 处替换
        nth_rw 1 [hb']
      _ = (d * b') / d := by rw [← hd]
      _ = b' := Int.mul_ediv_cancel_left _ hd_nez
  intro x y
  constructor
  · intro hxy
    -- subtract the particular solution
    have hdiff : a * (x - x₀) + b * (y - y₀) = 0 := by
      calc
        a * (x - x₀) + b * (y - y₀)
            = (a * x + b * y) - (a * x₀ + b * y₀) := by ring
        _ = 0 := by linarith [hxy, h_particular]
    -- factor out d
    have hfactor : d * (a' * (x - x₀) + b' * (y - y₀)) = 0 := by
      calc
        d * (a' * (x - x₀) + b' * (y - y₀))
            = (d * a') * (x - x₀) + (d * b') * (y - y₀) := by ring
        _ = a * (x - x₀) + b * (y - y₀) := by
              rw [← ha_div, ← hb_div]
              have h_dad : d * (a / d) = a := by
                have hd_nez' : d ≠ 0 := hd_nez
                #check Int.ediv_mul_cancel
                rw [Int.mul_comm]
                rw [Int.ediv_mul_cancel]
                  -- goal: d ∣ a, with hd : d = ↑(Int.gcd a b)
                have hg : (↑(Int.gcd a b) : Int) ∣ a := Int.gcd_dvd_left a b
                rw [← hd] at hg
                exact hg
              have h_dbd : d * (b / d) = b := by
                have hd_nez' : d ≠ 0 := hd_nez
                #check Int.ediv_mul_cancel
                rw [Int.mul_comm]
                rw [Int.ediv_mul_cancel]
                  -- goal: d ∣ b, with hd : d = ↑(Int.gcd a b)
                have hg : (↑(Int.gcd a b) : Int) ∣ b := Int.gcd_dvd_right a b
                rw [← hd] at hg
                exact hg
              rw [h_dad, h_dbd]
        _ = 0 := hdiff
    have hsum : a' * (x - x₀) + b' * (y - y₀) = 0 := by
      have hzero := mul_eq_zero.mp hfactor
      cases hzero with
      | inl hd0 => cases hd_nez hd0
      | inr hs => exact hs
    -- deduce divisibility of the differences
    have hrel : a' * (x - x₀) = - b' * (y - y₀) := by linarith
    have hcop' : Int.gcd b' a' = 1 := by simpa [Int.gcd_comm, ha_div, hb_div] using hcop
    -- handle the special case b' = 0 separately
    by_cases hb0' : b' = 0
    · -- when b' = 0, we construct n directly
      -- first, show a' ≠ 0
      have ha'_ne0 : a' ≠ 0 := by
        intro ha'_0
        have ha_0 : a = 0 := by
          calc
            a = (Int.gcd a b) * a' := by exact_mod_cast ha'
            _ = d * a' := by rw [hd]
            _ = d * 0 := by rw [ha'_0]
            _ = 0 := by ring
        have hb_0 : b = 0 := by
          rw [hb', hb0']
          rfl
        have hd_0 : Int.gcd a b = 0 := by
          simp [ha_0, hb_0]
        rw [hd_0] at hd
        exact hd_nez hd
      -- show x = x₀ using hrel
      have hx_eq_x0 : x = x₀ := by
        have : a' * (x - x₀) = 0 := by
          rw [hb0'] at hrel
          rw [hrel]
          simp
        rcases mul_eq_zero.mp this with ha'_0 | hx_x0
        · exact (ha'_ne0 ha'_0).elim
        · exact sub_eq_zero.mp hx_x0
      -- construct n = (y₀ - y) / a'
      -- first, show a' is a unit (when b'=0, we use the coprime condition)
      have ha'_unit : IsUnit a' := by
        -- From hcop': b'.gcd a' = 1 and b' = 0
        -- we have 0.gcd a' = 1, which means |a'| = 1
        have h_abs : a'.natAbs = 1 := by
          have : b'.gcd a' = 1 := hcop'
          rwa [hb0', Int.gcd_zero_left] at this
        -- If |a'| = 1, then a' = 1 or a' = -1, both are units
        -- We use a lemma to show that natAbs a' = 1 implies a' = ±1
        have h_eq_or : a' = 1 ∨ a' = -1 := by
          -- Case analysis on whether a' ≥ 0 or a' < 0
          by_cases h_nonneg : 0 ≤ a'
          · -- If a' ≥ 0, then natAbs a' = a'
            have : a'.natAbs = a' := Int.natAbs_of_nonneg h_nonneg
            rw [← this, h_abs]
            exact Or.inl rfl
          · -- If a' < 0, then natAbs a' = -a'
            push_neg at h_nonneg
            have h_neg : a' < 0 := h_nonneg
            have : -a' > 0 := Int.neg_pos_of_neg h_neg
            have h_nonneg' : 0 ≤ -a' := Int.le_of_lt this
            have h_eq : (-a').natAbs = -a' := Int.natAbs_of_nonneg h_nonneg'
            have h_sym : (-a').natAbs = a'.natAbs := by rw [Int.natAbs_neg]
            -- Now: (-a').natAbs = -a' and (-a').natAbs = a'.natAbs = 1
            -- So -a' = 1, which means a' = -1
            have h_eq_one : -a' = 1 := by
              -- Use the two equalities to prove -a' = 1
              have h1 : -a' = ((-a').natAbs : ℤ) := by
                rw [← h_eq]
                rfl
              have h2 : ((-a').natAbs : ℤ) = (a'.natAbs : ℤ) := by
                rw [h_sym]
              have h3 : (a'.natAbs : ℤ) = 1 := by
                rw [h_abs]
                rfl
              calc
                -a' = ((-a').natAbs : ℤ) := by exact h1
                _ = (a'.natAbs : ℤ) := by exact h2
                _ = 1 := by exact h3
            have h_neg_one : a' = -1 := by
              calc
                a' = -(-a') := by ring
                _ = -1 := by rw [h_eq_one]
            exact Or.inr h_neg_one
        -- Now use h_eq_or to show a' is a unit
        rcases h_eq_or with h_one | h_neg_one
        · rw [h_one]
          exact ⟨1, by rfl⟩
        · rw [h_neg_one]
          exact ⟨-1, by rfl⟩
      have a'_dvd : a' ∣ (y₀ - y) := ha'_unit.dvd
      let n : ℤ := (y₀ - y) / a'
      have hn : a' * n + (y - y₀) = 0 := by
        have : a' * n = y₀ - y := by
          apply Int.mul_ediv_cancel'
          exact a'_dvd
        linarith
      have hx : x = x₀ + (b / d) * n := by
        rw [hb_div, hb0', hx_eq_x0]
        ring
      have hy : y = y₀ - (a / d) * n := by
        have : y = y₀ - a' * n := by
          have : y₀ - y = a' * n := by
            calc
              y₀ - y = -(y - y₀) := by ring
              _ = a' * n := by
                  have : a' * n + (y - y₀) = 0 := hn
                  linarith
          linarith
        calc
          y = y₀ - a' * n := by exact this
          _ = y₀ - (a / d) * n := by
              rw [← ha_div]
      exact ⟨n, hx, hy⟩
    · -- when b' ≠ 0, use the divisibility argument
      have hb_divides : b' ∣ (x - x₀) :=
        corollary_1_11_b b' a' (x - x₀) hcop' ⟨-(y - y₀), by
          have : a' * (x - x₀) = b' * (-(y - y₀)) := by
            rw [hrel]
            ring
          simpa [mul_comm] using this⟩
      rcases hb_divides with ⟨n, hn⟩
      -- find the corresponding expression for y using the zero-sum relation
      have hsum_subst : a' * (b' * n) + b' * (y - y₀) = 0 := by
        simpa [hn, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hsum
      -- factor b' and use that Int is an integral domain
      have hzero_prod : b' * (a' * n + (y - y₀)) = 0 := by
        ring_nf at hsum_subst
        rw [← hsum_subst]
        ring
      -- since we're in the b' ≠ 0 branch, we can conclude a'*n + (y-y₀) = 0
      have hy_rel : a' * n + (y - y₀) = 0 := by
        have := mul_eq_zero.mp hzero_prod
        cases this with
        | inl hb0 =>
          -- this can't happen since we're in the b' ≠ 0 branch
          exact (hb0' hb0).elim
        | inr hy => exact hy
      have hy_eq : y = y₀ - a' * n := by
        linarith
      refine ⟨n, ?_, ?_⟩
      · -- x expression
        have : b / d = b' := hb_div
        rw [this, ← hn]
        simp
      · -- y expression
        have : a / d = a' := ha_div
        rw [this, hy_eq]
  · rintro ⟨n, hx, hy⟩
    -- plug the parametrization back in to check it satisfies the equation
    subst hx; subst hy
    have h_eq : a * (b / d) = b * (a / d) := by
      calc
        a * (b / d) = a * b' := by rw [hb_div]
        _ = ((a.gcd b) * a') * b' := by rw [← ha']
        _ = (d * a') * b' := by
          have hd' : (a.gcd b : ℤ) = d := by exact_mod_cast hd.symm
          rw [hd']
        _ = d * (a' * b') := by ring
        _ = d * (b' * a') := by ring
        _ = (d * b') * a' := by ring
        _ = b * a' := by
          calc
            (d * b') * a' = ((a.gcd b : ℤ) * b') * a' := by rw [← hd]
            _ = b * a' := by rw [← hb']
        _ = b * (a / d) := by rw [ha_div]

    have : a * (x₀ + (b / d) * n) + b * (y₀ - (a / d) * n)
            = a * x₀ + b * y₀ := by
      calc
        a * (x₀ + (b / d) * n) + b * (y₀ - (a / d) * n)
            = a * x₀ + a * ((b / d) * n) + b * y₀ - b * ((a / d) * n) := by ring
        _ = a * x₀ + b * y₀ + n * (a * (b / d) - b * (a / d)) := by ring
        _ = a * x₀ + b * y₀ + n * 0 := by rw [h_eq]; ring
        _ = a * x₀ + b * y₀ := by ring
    simpa [h_particular]

end Diophantine

end ElementaryNumberTheory.Chapter1
