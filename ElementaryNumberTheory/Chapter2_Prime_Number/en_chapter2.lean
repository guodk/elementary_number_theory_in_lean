import Mathlib

/-!
# Elementary Number Theory - Chapter 2: Prime Numbers
**Source:** Gareth A. Jones and J. Mary Jones, Springer Undergraduate Mathematics Series.

This file contains the formal statements of the theorems in Chapter 2.
Note: We switch primarily to `Nat` (Natural Numbers) for prime theory as is standard in Mathlib.
-/

namespace ElementaryNumberTheory.Chapter2

section PrimeFactorisation

/-! ## 2.1 Prime numbers and prime-power factorisations -/

/-
### Definition: Prime Number
An integer p > 1 is said to be prime if the only positive divisors of p are 1 and p itself.
(Formalized via `Nat.Prime` class)
-/

/-
### Lemma 2.1
Let p be prime, and let a and b be any integers.
(a) either p divides a, or a and p are coprime;
(b) if p divides ab, then p divides a or p divides b.
-/
theorem lemma_2_1_a (p a : ℕ) (hp : p.Prime) :
  p ∣ a ∨ Nat.Coprime a p := by
  sorry

theorem lemma_2_1_b (p a b : ℕ) (hp : p.Prime) :
  p ∣ (a * b) → p ∣ a ∨ p ∣ b := by
  sorry

/-
### Corollary 2.2
If p is prime and p divides a_1 ... a_k, then p divides a_i for some i.
-/
theorem corollary_2_2 (p : ℕ) (as : List ℕ) (hp : p.Prime) :
  p ∣ as.prod → ∃ a ∈ as, p ∣ a := by
  sorry

/-
### Theorem 2.3 (Fundamental Theorem of Arithmetic)
Each integer n > 1 has a prime-power factorisation
n = p_1^{e_1} ... p_k^{e_k},
where p_1, ..., p_k are distinct primes and e_i are positive integers;
this factorisation is unique, apart from permutations of the factors.
-/
-- In Mathlib, this corresponds to `Nat.prime_factorization` (MultiSet of primes)
-- or `Nat.factors` (List of primes).
-- We state the existence via the property that the product of prime factors equals n.
theorem theorem_2_3_fundamental_theorem (n : ℕ) (hn : n > 1) :
  ∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n := by
  sorry

/-
### Lemma 2.4
If a_1, ..., a_r are mutually coprime positive integers, and a_1 ... a_r is an m-th
power for some integer m >= 2, then each a_i is an m-th power.
-/
theorem lemma_2_4 (as : List ℕ) (m : ℕ) (hm : m ≥ 2)
  (h_coprime : as.Pairwise Nat.Coprime)
  (h_power : ∃ k, as.prod = k ^ m) :
  ∀ a ∈ as, ∃ k, a = k ^ m := by
  sorry

/-
### Corollary 2.5
If a positive integer m is not a perfect square, then sqrt(m) is irrational.
-/
theorem corollary_2_5 (m : ℕ) (h_not_square : ¬ ∃ k, m = k ^ 2) :
  Irrational (Real.sqrt m) := by
  sorry

end PrimeFactorisation

section Distribution

/-! ## 2.2 Distribution of primes -/

/-
### Theorem 2.6 (Euclid)
There are infinitely many primes.
-/
theorem theorem_2_6_infinitude_primes :
  Set.Infinite { p : ℕ | p.Prime } := by
  sorry

/-
### Corollary 2.7
The n-th prime p_n satisfies p_n <= 2^(2^(n-1)) for all n >= 1.
Note: In Mathlib, `Nat.nth` usually starts indexing at 0.
-/
theorem corollary_2_7_prime_bound (n : ℕ) (hn : n ≥ 1) :
  Nat.nth Nat.Prime (n - 1) ≤ 2 ^ (2 ^ (n - 1)) := by
  sorry

/-
### Theorem 2.9
There are infinitely many primes of the form 4q + 3.
-/
theorem theorem_2_9_primes_4q_plus_3 :
  Set.Infinite { p : ℕ | p.Prime ∧ p % 4 = 3 } := by
  sorry

/-
### Theorem 2.10 (Dirichlet's Theorem)
If a and b are coprime integers then there are infinitely many primes of the form aq + b.
-/
theorem theorem_2_10_dirichlet (a b : ℕ) (h_coprime : Nat.Coprime a b) :
  Set.Infinite { p : ℕ | p.Prime ∧ p % a = b } := by
  sorry

end Distribution

section FermatMersenne

/-! ## 2.3 Fermat and Mersenne primes -/

/-
### Lemma 2.11
If 2^m + 1 is prime then m = 2^n for some integer n >= 0.
-/
theorem lemma_2_11 (m : ℕ) :
  (2 ^ m + 1).Prime → ∃ n, m = 2 ^ n := by
  sorry

/-
### Lemma 2.12
Distinct Fermat numbers F_n = 2^(2^n) + 1 are mutually coprime.
-/
def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

theorem lemma_2_12 (m n : ℕ) (h : m ≠ n) :
  Nat.Coprime (fermatNumber m) (fermatNumber n) := by
  sorry

/-
### Theorem 2.13
If m > 1 and a^m - 1 is prime, then a = 2 and m is prime.
-/
theorem theorem_2_13 (a m : ℕ) (hm : m > 1) :
  (a ^ m - 1).Prime → a = 2 ∧ m.Prime := by
  sorry

end FermatMersenne

section PrimalityTesting

/-! ## 2.4 Primality-testing and factorisation -/

/-
### Lemma 2.14
An integer n > 1 is composite if and only if it is divisible by some prime p <= sqrt(n).
-/
theorem lemma_2_14 (n : ℕ) (hn : n > 1) :
  ¬ n.Prime ↔ ∃ p, p.Prime ∧ p ∣ n ∧ p ^ 2 ≤ n := by
  sorry

end PrimalityTesting

end ElementaryNumberTheory.Chapter2
