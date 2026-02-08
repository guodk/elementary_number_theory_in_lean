import Mathlib

set_option maxHeartbeats 0
/-!
#### Elementary Number Theory - Chapter 2: Prime Numbers
**Source:** Gareth A. Jones and J. Mary Jones, Springer Undergraduate Mathematics Series.

This file contains the formal statements of the theorems in Chapter 2.
Note: We switch primarily to `Nat` (Natural Numbers) for prime theory as is standard in Mathlib.
-/

namespace ElementaryNumberTheory.Chapter2

section PrimeFactorisation

/-! ## 2.1 Prime numbers and prime-power factorisations -/

/-
#### Definition: Prime Number
An integer p > 1 is said to be prime if the only positive divisors of p are 1 and p itself.
(Formalized via `Nat.Prime` class)
-/
/- ####check Nat.Prime -/
/-
#### Lemma 2.1
Let p be prime, and let a and b be any integers.
(a) either p divides a, or a and p are coprime;
(b) if p divides ab, then p divides a or p divides b.
-/
theorem lemma_2_1_a (p : ℕ) (a : ℤ) (hp : p.Prime) :
  (p : ℤ) ∣ a ∨ IsCoprime a p := by
  have hpZ : _root_.Prime (p : ℤ) := (Nat.prime_iff_prime_int).1 hp
  by_cases h : (p : ℤ) ∣ a
  · exact Or.inl h
  · right
    have hcop : IsCoprime (p : ℤ) a :=
      (Prime.coprime_iff_not_dvd (p := (p : ℤ)) (n := a) hpZ).2 h
    -- swap arguments in `IsCoprime` manually
    rcases hcop with ⟨x, y, hxy⟩
    refine ⟨y, x, ?_⟩
    -- `hxy : x * (p:ℤ) + y * a = 1`
    -- want: `y * a + x * (p:ℤ) = 1`
    simpa [add_comm] using hxy

end PrimeFactorisation
end ElementaryNumberTheory.Chapter2


theorem lemma_2_1_b (p : ℕ) (a b : ℤ) (hp : p.Prime) :
  (p : ℤ) ∣ (a * b) → (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b := by
  intro h
  exact Int.Prime.dvd_mul' (m := a) (n := b) hp h

/-
#### Corollary 2.2
If p is prime and p divides a_1 ... a_k, then p divides a_i for some i.
-/
theorem corollary_2_2 (p : ℕ) (as : List ℕ) (hp : p.Prime) :
  p ∣ as.prod → ∃ a ∈ as, p ∣ a := by
  induction as with
  | nil =>
      intro h
      -- prod [] = 1, contradicting that a prime does not divide 1
      have : p ∣ (1 : ℕ) := by simpa [List.prod_nil] using h
      exact (hp.not_dvd_one this).elim
  | cons a as ih =>
      intro h
      -- use divisibility of a product
      have h' : p ∣ a * as.prod := by simpa [List.prod_cons] using h
      have : p ∣ a ∨ p ∣ as.prod := (hp.dvd_mul).1 h'
      cases this with
      | inl ha =>
          exact ⟨a, by simp, ha⟩
      | inr hasProd =>
          rcases ih hasProd with ⟨x, hxmem, hxdvd⟩
          exact ⟨x, by simp [hxmem], hxdvd⟩

theorem corollary_2_2' (p : ℕ) (as : List ℤ) (hp : p.Prime) :
  (p : ℤ) ∣ as.prod → ∃ a ∈ as, (p : ℤ) ∣ a := by
  intro h
  have hpZ : _root_.Prime (p : ℤ) := (Nat.prime_iff_prime_int).1 hp
  exact (Prime.dvd_prod_iff (p := (p : ℤ)) (L := as) hpZ).1 h
/-
#### Theorem 2.3 (Fundamental Theorem of Arithmetic)
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
  refine ⟨n.primeFactorsList, ?_, ?_⟩
  · intro p hp
    exact Nat.prime_of_mem_primeFactorsList hp
  · have hn0 : n ≠ 0 := by
      exact ne_of_gt (Nat.zero_lt_one.trans hn)
    simpa using (Nat.prod_primeFactorsList (n := n) hn0)

/-
#### Lemma 2.4
If a_1, ..., a_r are mutually coprime positive integers, and a_1 ... a_r is an m-th
power for some integer m >= 2, then each a_i is an m-th power.
-/
theorem lemma_2_4 (as : Finset ℕ) (m : ℕ) (f : ℕ → ℕ)
  (h_coprime : ∀ i ∈ as, ∀ j ∈ as, i ≠ j → IsCoprime (f i) (f j))
  (h_power : ∃ c, ∏ i ∈ as, f i = c ^ m) :
   ∀ a ∈ as, ∃ t, f a = t ^ m := by
  rcases h_power with ⟨c, h_mul_eq⟩
  apply Finset.exists_eq_pow_of_mul_eq_pow_of_coprime (R := ℕ) h_coprime h_mul_eq

/-
### Corollary 2.5
If a positive integer m is not a perfect square, then sqrt(m) is irrational.
-/
theorem corollary_2_5 (m : ℕ) (h_not_square : ¬ ∃ k, m = k ^ 2) :
  Irrational (Real.sqrt m) := by
  rw [irrational_sqrt_natCast_iff, isSquare_iff_exists_mul_self]
  simpa [pow_two] using h_not_square


section Distribution

/-! ## 2.2 Distribution of primes -/

/-
### Theorem 2.6 (Euclid)
There are infinitely many primes.
-/
theorem theorem_2_6_infinitude_primes :
  Set.Infinite { p : ℕ | p.Prime } := by
  simpa using Nat.infinite_setOf_prime

/-
### Corollary 2.7
The n-th prime p_n satisfies p_n <= 2^(2^(n-1)) for all n >= 1.
Note: In Mathlib, `Nat.nth` usually starts indexing at 0.
-/
theorem corollary_2_7_prime_bound (n : ℕ) (hn : n ≥ 1) :
  Nat.nth Nat.Prime (n - 1) ≤ 2 ^ (2 ^ (n - 1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => contradiction -- n ≥ 1
    | succ n =>
      by_cases h_base : n = 0
      · simp [h_base, Nat.nth_prime_zero_eq_two]
      · let p (i : ℕ) := Nat.nth Nat.Prime i
        -- p_n ≤ (∏_{i < n} p_i) + 1
        have h_bound : p n ≤ (∏ i ∈ Finset.range n, p i) + 1 := by
          let N := (∏ i ∈ Finset.range n, p i) + 1
          have hN_gt_1 : 1 < N := by
            have h_prod_pos : 0 < ∏ i ∈ Finset.range n, p i :=
              Finset.prod_pos (fun i _ => Nat.Prime.pos (Nat.prime_nth_prime i))
            dsimp [N]
            linarith
          let q := N.minFac
          have q_prime : q.Prime := Nat.minFac_prime (ne_of_gt hN_gt_1)
          have q_not_in_range : ∀ i ∈ Finset.range n, q ≠ p i := by
            intro i hi h_eq
            rw [h_eq] at q_prime
            have h_dvd_prod : p i ∣ ∏ j ∈ Finset.range n, p j := Finset.dvd_prod_of_mem p hi
            have h_dvd_N : q ∣ ∏ j ∈ Finset.range n, p j + 1 := Nat.minFac_dvd N
            rw [h_eq] at h_dvd_N
            have h_dvd_one : p i ∣ 1 := (Nat.dvd_add_iff_right h_dvd_prod).mpr h_dvd_N
            have not_h_dvd_one : ¬ (p i ∣ 1) := Nat.Prime.not_dvd_one (Nat.prime_nth_prime i)
            contradiction
          have h_q_ge_pn : q ≥ p n := by
            obtain ⟨k, _, hk_eq⟩ := Nat.exists_lt_card_nth_eq q_prime
            have inj_iff : ∀ (x y : Nat), p x ≠ p y ↔ x ≠ y := by
              intro x y
              exact Function.Injective.ne_iff (Nat.nth_injective Nat.infinite_setOf_prime)
            rw [ge_iff_le, ← hk_eq, Nat.nth_le_nth Nat.infinite_setOf_prime]
            by_contra h_lt
            specialize q_not_in_range k (Finset.mem_range.mpr (not_le.mp h_lt))
            rw [← hk_eq] at q_not_in_range
            contradiction
          have h_q_le_N : q ≤ N := Nat.minFac_le (by linarith)
          exact le_trans h_q_ge_pn h_q_le_N
        have h_prod_le : ∏ i ∈ Finset.range n, p i ≤ ∏ i ∈ Finset.range n, 2 ^ (2 ^ i) := by
          apply Finset.prod_le_prod
          · intros; apply Nat.zero_le
          · intros i hi
            specialize ih (i + 1) (by
              simp only [Finset.mem_range] at hi
              exact Nat.succ_le_succ hi) (Nat.succ_pos i)
            simp only [Nat.add_one_sub_one] at ih
            exact ih
        -- ∑_{i=0}^{n-1} 2^i = 2^n - 1
        have h_exp_sum : ∏ i ∈ Finset.range n, 2 ^ (2 ^ i) = 2 ^ (2 ^ n - 1) := by
          rw [Finset.prod_pow_eq_pow_sum]
          congr
          simp only [le_refl, Nat.geomSum_eq, Nat.add_one_sub_one, Nat.div_one]
        calc p n ≤ (∏ i ∈ Finset.range n, p i) + 1 := by exact h_bound
               _ ≤ 2 ^ (2 ^ n - 1) + 1 := Nat.add_le_add_right (h_prod_le.trans_eq h_exp_sum) 1
               _ ≤ 2 ^ (2 ^ n - 1) + 2 ^ (2 ^ n - 1) := by
                apply Nat.add_le_add_left
                apply Nat.one_le_pow
                exact Nat.succ_pos 1
               _ = 2 * 2 ^ (2 ^ n - 1) := by rw [two_mul]
               _ = 2 ^ (2 ^ n) := by
                rw [← Nat.pow_succ']
                simp only [Nat.succ_eq_add_one, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one,
                  not_false_eq_true, pow_right_inj₀]
                apply Nat.sub_one_add_one
                exact Ne.symm (NeZero.ne' (2 ^ n))

/-
### Theorem 2.9
There are infinitely many primes of the form 4q + 3.
-/
theorem theorem_2_9_primes_4q_plus_3 :
  Set.Infinite { p : ℕ | p.Prime ∧ p % 4 = 3 } := by
  apply Set.infinite_iff_exists_gt.mpr
  intro n
  let M := 4 * Nat.factorial n - 1
  have hM_gt_1 : 1 < M := by
    have h_fact : 1 ≤ Nat.factorial n := Nat.factorial_pos n
    calc 1 < 4 * 1 - 1 := by norm_num
         _ ≤ 4 * Nat.factorial n - 1 := by rel [h_fact]
  have h_pos : 0 < 4 * Nat.factorial n := by positivity
  have hM_mod : M ≡ 3 [MOD 4] := by
    calc M ≡ 4 * Nat.factorial n - 1 [MOD 4] := by rfl
         _ ≡ 4 - 1 [MOD 4] := by
          apply Nat.ModEq.sub_right (by linarith) (by linarith)
          calc 4 * Nat.factorial n ≡ 0 [MOD 4] := by
                rw [show 4 * Nat.factorial n = 4 * Nat.factorial n + 0 by rfl]
                apply Nat.ModEq.modulus_mul_add
            _ ≡ 4 [MOD 4] := by rfl
  have exists_prime_factor_mod_4_eq_3 {m : ℕ} (h1 : 1 < m) (h3 : m ≡ 3 [MOD 4]) :
      ∃ p, p.Prime ∧ p ∣ m ∧ p ≡ 3 [MOD 4] := by
    by_contra h_none
    push_neg at h_none
    have m_odd : m % 2 = 1 := by
      have : m % 4 = 3 := h3
      rw [← Nat.mod_mod_of_dvd m (show 2 ∣ 4 by norm_num), this]
    have all_mod_1 : ∀ p ∈ m.primeFactors, p ≡ 1 [MOD 4] := by
      intro p hp
      have p_prime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have p_dvd_m : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
      have p_odd : p % 2 = 1 :=
        Nat.odd_iff.mp (Odd.of_dvd_nat (Nat.odd_iff.mpr m_odd) p_dvd_m)
      have p_cases : p % 4 = 1 ∨ p % 4 = 3 := by
        have h_lt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
        interval_cases h : p % 4
        · exfalso
          have : p % 2 = 0 := by
            rw [← Nat.mod_mod_of_dvd p (show 2 ∣ 4 by norm_num), h]
          rw [this] at p_odd
          contradiction
        · left; rfl
        · exfalso
          have : p % 2 = 0 := by
            rw [← Nat.mod_mod_of_dvd p (show 2 ∣ 4 by norm_num), h]
          rw [this] at p_odd
          contradiction
        · right; rfl
      cases p_cases with
      | inl h => exact h
      | inr h => exfalso; exact h_none p p_prime p_dvd_m h
    have m_mod_1 : m ≡ 1 [MOD 4] := by
      rw [← Nat.factorization_prod_pow_eq_self (pos_of_gt h1).ne']
      apply Finset.prod_induction (p := fun x => x ≡ 1 [MOD 4])
      · intro a b ha hb; exact ha.mul hb
      · rfl
      · intro p hp
        have hp_mod1 : p ≡ 1 [MOD 4] := all_mod_1 p hp
        have h_pow := hp_mod1.pow (m.factorization p)
        rwa [Nat.ModEq, Nat.one_pow, ← Nat.ModEq] at h_pow
    have : 1 ≡ 3 [MOD 4] := Nat.ModEq.trans m_mod_1.symm h3
    norm_num at this
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := exists_prime_factor_mod_4_eq_3 hM_gt_1 hM_mod
  use p
  constructor
  · exact ⟨hp_prime, hp_mod⟩
  · by_contra h_le
    have h_p_div_4fact : p ∣ 4 * Nat.factorial n :=
      dvd_mul_of_dvd_right (hp_prime.dvd_factorial.mpr (not_lt.mp h_le)) 4
    have h_p_div_one : p ∣ 1 := by
      rw [← Nat.dvd_sub_iff_right (n := 4 * Nat.factorial n) (by linarith)]
      · exact hp_div
      · exact h_p_div_4fact
    exact Nat.Prime.not_dvd_one hp_prime h_p_div_one

/-
### Theorem 2.10 (Dirichlet's Theorem)
If a and b are coprime integers then there are infinitely many primes of the form aq + b.
-/
theorem theorem_2_10_dirichlet (a : ℕ) (b : ℤ) (ha : a ≠ 0) (h_coprime : IsCoprime b a) :
  Set.Infinite { p : ℕ | p.Prime ∧ p ≡ b [ZMOD a] } := by
  apply Set.infinite_iff_exists_gt.mpr
  simp only [Set.mem_setOf_eq]
  intro n
  rcases Nat.forall_exists_prime_gt_and_zmodEq n ha h_coprime with ⟨p, _, _, _⟩
  use p

end Distribution

section FermatMersenne

/-! ## 2.3 Fermat and Mersenne primes -/

/-
### Lemma 2.11
If 2^m + 1 is prime then m = 2^n for some integer n >= 0.
-/
theorem lemma_2_11 (m : ℕ) (hm : m ≠ 0) :
  (2 ^ m + 1).Prime → ∃ n, m = 2 ^ n := Nat.pow_of_pow_add_prime (by norm_num) hm


/-
### Lemma 2.12
Distinct Fermat numbers F_n = 2^(2^n) + 1 are mutually coprime.
-/
def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

theorem lemma_2_12 (m n : ℕ) (h : m ≠ n) :
  Nat.Coprime (fermatNumber m) (fermatNumber n) := Nat.coprime_fermatNumber_fermatNumber h

/-
### Theorem 2.13
If m > 1 and a^m - 1 is prime, then a = 2 and m is prime.
-/
theorem theorem_2_13 (a m : ℕ) (hm : m > 1) :
  (a ^ m - 1).Prime → a = 2 ∧ m.Prime := Nat.prime_of_pow_sub_one_prime hm.ne'

end FermatMersenne

section PrimalityTesting

/-! ## 2.4 Primality-testing and factorisation -/

/-
### Lemma 2.14
An integer n > 1 is composite if and only if it is divisible by some prime p <= sqrt(n).
-/
theorem lemma_2_14 (n : ℕ) (hn : n > 1) :
  ¬ n.Prime ↔ ∃ p, p.Prime ∧ p ∣ n ∧ p ^ 2 ≤ n := by
  constructor
  · intro h_composite
    have h_minfac := Nat.minFac_sq_le_self (by positivity) h_composite
    use Nat.minFac n
    exact ⟨Nat.minFac_prime (hn.ne'), Nat.minFac_dvd n, h_minfac⟩
  · intro h
    rcases h with ⟨p, hp_prime, hp_dvd, hp_sq_le⟩
    apply Nat.not_prime_of_dvd_of_lt hp_dvd (Nat.Prime.two_le hp_prime)
    calc p < p ^ 2 := by
          rw [Nat.pow_two, Nat.lt_mul_iff_one_lt_right (Nat.Prime.pos hp_prime)]
          exact Nat.Prime.two_le hp_prime
         _ ≤ n := hp_sq_le
theorem lemma_2_14' (n : ℕ) (hn : n > 1) :
  ¬ n.Prime ↔ ∃ p, p.Prime ∧ p ∣ n ∧ p ≤ Nat.sqrt n := by
  simp_rw [lemma_2_14 n hn, Nat.le_sqrt, Nat.pow_two]

end PrimalityTesting
