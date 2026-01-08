import Mathlib
import Aesop

--set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat


/-- [thm:1.1] If $a$ and $b$ are integers with $b > 0$, then there is a unique pair of integers $q$ and $r$ such that $a = qb + r$ and $0 \le r < b$. --/
theorem thm_1_1 (a b : ℤ) (hb : 0 < b) : 
  ∃! (qr : ℤ × ℤ), a = qr.1 * b + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < b := by sorry

/-- [cor:1.2] If $a$ and $b$ are integers with $b \neq 0$, then there is a unique pair of integers $q$ and $r$ such that $a = qb + r$ and $0 \le r < |b|$. --/
theorem cor_1_2 (a b : ℤ) (hb : b ≠ 0) : 
  ∃! p : ℤ × ℤ, a = p.1 * b + p.2 ∧ 0 ≤ p.2 ∧ p.2 < Int.natAbs b := by sorry

/-- [thm:1.3] (a) If $c$ divides $a_1, \dots, a_k$, then $c$ divides $a_1 u_1 + \dots + a_k u_k$ for all integers $u_1, \dots, u_k$.
(b) $a|b$ and $b|a$ if and only if $a = \pm b$. --/
theorem thm_1_3 : 
  (∀ (k : ℕ) (c : ℤ) (a : Fin k → ℤ) (u : Fin k → ℤ), 
    (∀ i, c ∣ a i) → c ∣ (∑ i, a i * u i)) ∧
  (∀ a b : ℤ, (a ∣ b ∧ b ∣ a) ↔ (a = b ∨ a = -b)) := by sorry

/-- [cor:1.4] If $c$ divides $a$ and $b$, then $c$ divides $au + bv$ for all integers $u$ and $v$. --/
theorem cor_1_4 (a b c : ℤ) (h1 : c ∣ a) (h2 : c ∣ b) :
  ∀ u v : ℤ, c ∣ (a * u + b * v) := by sorry

/-- [lem:1.5] If $a = qb + r$ then $\gcd(a, b) = \gcd(b, r)$. --/
theorem lem_1_5 {a b q r : Int} (h : a = q * b + r) : 
  Int.gcd a b = Int.gcd b r := by sorry

/-- [thm:1.6] In the Euclidean algorithm calculation, we have $d = r_{n-1}$ (the last non-zero remainder). --/
theorem thm_1_6 : 
  let a : ℤ := 37
  let b : ℤ := 12
  let d : ℤ := Int.gcd a b
  ∃ x y : ℤ, d = a * x + b * y ∧ x = Int.gcdA a b ∧ y = Int.gcdB a b := by sorry

/-- [thm:1.7] If $a$ and $b$ are integers (not both 0), then there exist integers $u$ and $v$ such that $\gcd(a, b) = au + bv$. --/
theorem thm_1_7 (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) : 
  ∃ u v : ℤ, Int.gcd a b = a * u + b * v := by sorry

/-- [thm:1.8] Let $a$ and $b$ be integers (not both 0) with greatest common divisor $d$. Then an integer $c$ has the form $ax + by$ for some $x, y \in \mathbb{Z}$ if and only if $c$ is a multiple of $d$. In particular, $d$ is the least positive integer of the form $ax + by$ ($x, y \in \mathbb{Z}$). --/
theorem thm_1_8 
  (a b : Int) (h : ¬(a = 0 ∧ b = 0)) : 
  let d := Int.gcd a b
  -- Part 1: Characterization of multiples of d
  (∀ c : Int, 
    (∃ x y : Int, c = a * x + b * y) ↔ ∃ k : Int, c = d * k) ∧
  -- Part 2: Minimality of d
  (∃ x y : Int, d = a * x + b * y) ∧  -- d is a linear combination
  (∀ x y : Int, 0 < a * x + b * y → d ≤ a * x + b * y)  -- d is minimal positive
  := by sorry

/-- [cor:1.9] Two integers $a$ and $b$ are coprime if and only if there exist integers $x$ and $y$ such that $ax + by = 1$. --/
theorem cor_1_9 (a b : Int) :
  Int.gcd a b = 1 ↔ ∃ (x y : Int), a * x + b * y = 1 := by sorry

/-- [cor:1.10] If $\gcd(a, b) = d$ then $\gcd(ma, mb) = md$ for every integer $m > 0$, and $\gcd(\frac{a}{d}, \frac{b}{d}) = 1$. --/
theorem cor_1_10 (a b d : ℤ) (h : Int.gcd a b = d) (hd : d ≠ 0) :
  (∀ (m : ℕ), 0 < m → Int.gcd (m * a) (m * b) = m * d) ∧ 
  Int.gcd (a / d) (b / d) = 1 := by sorry

/-- [cor:1.11] Let $a$ and $b$ be coprime integers.
(a) If $a|c$ and $b|c$ then $ab|c$.
(b) If $a|bc$ then $a|c$. --/
theorem cor_1_11 :
  ∀ (a b c : Int),
    Int.gcd a b = 1 →  -- a and b are coprime
    ((a ∣ c) ∧ (b ∣ c) → (a * b ∣ c)) ∧  -- part (a)
    ((a ∣ b * c) → (a ∣ c))  -- part (b)
  := by sorry

/-- [thm:1.12] Let $a$ and $b$ be positive integers, with $d = \gcd(a, b)$ and $l = \text{lcm}(a, b)$. Then $dl = ab$. --/
theorem thm_1_12 (a b : Nat) (ha : a > 0) (hb : b > 0) :
  (Nat.gcd a b) * (Nat.lcm a b) = a * b := by sorry

/-- [thm:1.13] Let $a, b$ and $c$ be integers, with $a$ and $b$ not both 0, and let $d = \gcd(a, b)$. Then the equation $ax + by = c$ has an integer solution $x, y$ if and only if $c$ is a multiple of $d$, in which case there are infinitely many solutions. These are the pairs $x = x_0 + \frac{bn}{d}, \quad y = y_0 - \frac{an}{d} \quad (n \in \mathbb{Z}),$ where $x_0, y_0$ is any particular solution. --/
theorem thm_1_13 (a b c : ℤ) (h_not_both_zero : ¬(a = 0 ∧ b = 0)) 
  (d : ℤ) (h_d : d = Int.gcd a b) :
  (∃ x y : ℤ, a * x + b * y = c) ↔ (d ∣ c) ∧
  (∃ x₀ y₀ : ℤ, a * x₀ + b * y₀ = c ∧
    ∀ x y : ℤ, a * x + b * y = c ↔ 
      ∃ n : ℤ, x = x₀ + (b * n) / d ∧ y = y₀ - (a * n) / d) := by sorry

/-- [lem:2.1] Let $p$ be prime, and let $a$ and $b$ be any integers. Then (a) either $p$ divides $a$, or $a$ and $p$ are coprime; (b) if $p$ divides $ab$, then $p$ divides $a$ or $p$ divides $b$. --/
theorem lem_2_1 (p : ℕ) (a b : ℤ) (hp : Nat.Prime p) :
  ((p : ℤ) ∣ a ∨ Nat.Coprime (Int.natAbs a) p) ∧
  ((p : ℤ) ∣ (a * b) → (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b) := by sorry

/-- [cor:2.2] If $p$ is prime and $p$ divides $a_1 \dots a_k$, then $p$ divides $a_i$ for some $i$. --/
theorem cor_2_2 (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (a : Fin k → ℤ) 
  (h : (p : ℤ) ∣ (Finset.univ : Finset (Fin k)).prod a) : 
  ∃ i : Fin k, (p : ℤ) ∣ a i := by sorry

/-- [thm:2.3] Each integer $n > 1$ has a prime-power factorisation $n = p_1^{e_1} \dots p_k^{e_k}$, where $p_1, \dots, p_k$ are distinct primes and $e_1, \dots, e_k$ are positive integers; this factorisation is unique, apart from permutations of the factors. --/
theorem thm_2_3 (n : ℕ) (hn : n > 1) : 
  ∃ (primes : Finset ℕ) (exponents : ℕ → ℕ), 
    (∀ p ∈ primes, Nat.Prime p) ∧
    (∀ p ∈ primes, exponents p > 0) ∧
    (n = primes.prod (fun p => p ^ exponents p)) ∧
    (∀ (primes' : Finset ℕ) (exponents' : ℕ → ℕ), 
      (∀ p ∈ primes', Nat.Prime p) →
      (∀ p ∈ primes', exponents' p > 0) →
      (n = primes'.prod (fun p => p ^ exponents' p)) →
      primes = primes' ∧ ∀ p ∈ primes, exponents p = exponents' p)
  := by sorry

/-- [lem:2.4] If $a_1, \dots, a_r$ are mutually coprime positive integers, and $a_1 \dots a_r$ is an $m$-th power for some integer $m \ge 2$, then each $a_i$ is an $m$-th power. --/
theorem lem_2_4 (r : ℕ) (a : Fin r → ℕ) (m : ℕ) 
  (ha_pos : ∀ i, 0 < a i)
  (hm : 2 ≤ m) 
  (h_coprime : ∀ i j : Fin r, i ≠ j → Nat.gcd (a i) (a j) = 1)
  (h_power : ∃ k : ℕ, (Finset.univ.prod a) = k^m) :
  ∀ i : Fin r, ∃ k : ℕ, a i = k^m := by sorry

/-- [cor:2.5] If a positive integer $m$ is not a perfect square, then $\sqrt{m}$ is irrational. --/
theorem cor_2_5 (m : ℕ) (hm_pos : m > 0) (hm_not_square : ¬∃ k : ℕ, k^2 = m) : 
  Irrational (Real.sqrt m) := by sorry

/-- [thm:2.6] There are infinitely many primes. --/
theorem thm_2_6 : Set.Infinite {p : ℕ | Nat.Prime p} := by sorry

/-- [cor:2.7] The $n$-th prime $p_n$ satisfies $p_n \le 2^{2^{n-1}}$ for all $n \ge 1$. --/
theorem cor_2_7 : ∀ n : ℕ, n ≥ 1 → 
  ∃ p : ℕ, Nat.Prime p ∧ 
  (∃ S : Finset ℕ, S = (Finset.range (p + 1)).filter Nat.Prime ∧ S.card = n) ∧
  p ≤ 2^(2^(n-1)) := by sorry

/-- [cor:2.8] $\pi(x) \ge \lfloor \lg(\lg x) \rfloor + 1$. --/
theorem cor_2_8 : ∀ x : ℕ, x ≥ 2 → 
  (Nat.primeCounting x : ℤ) ≥ ⌊Real.logb 2 (Real.logb 2 (x : ℝ))⌋ + 1 := by sorry

/-- [thm:2.9] There are infinitely many primes of the form $4q + 3$. --/
theorem thm_2_9 : Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 3} := by sorry

/-- [lem:2.11] If $2^m + 1$ is prime then $m = 2^n$ for some integer $n \ge 0$. --/
theorem lem_2_11 (m : ℕ) : Nat.Prime (2^m + 1) → ∃ n : ℕ, m = 2^n := by sorry

/-- [lem:2.12] Distinct Fermat numbers $F_n$ are mutually coprime. --/
def fermat_number (n : ℕ) : ℕ := 2^(2^n) + 1

theorem lem_2_12 : ∀ m n : ℕ, m ≠ n → Nat.gcd (fermat_number m) (fermat_number n) = 1 := by sorry

/-- [lem:2.14] An integer $n > 1$ is composite if and only if it is divisible by some prime $p \le \sqrt{n}$. --/
theorem lem_2_14 (n : ℕ) (hn : n > 1) : 
  (¬Nat.Prime n) ↔ (∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p ≤ Nat.sqrt n) := by sorry

/-- [lem:3.1] For any fixed $n \ge 1$ we have $a \equiv b \pmod n$ if and only if $n | (a - b)$. --/
theorem lem_3_1 (n : ℕ) (a b : ℤ) (hn : n ≥ 1) : 
  a ≡ b [ZMOD n] ↔ (n : ℤ) ∣ (a - b) := by sorry

/-- [lem:3.2] For any fixed $n \ge 1$ we have
(a) $a \equiv a$ for all integers $a$;
(b) if $a \equiv b$ then $b \equiv a$;
(c) if $a \equiv b$ and $b \equiv c$ then $a \equiv c$. --/
theorem lem_3_2 (n : ℕ) (hn : n ≥ 1) :
  (∀ a : ℤ, a ≡ a [ZMOD n]) ∧
  (∀ a b : ℤ, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]) ∧
  (∀ a b c : ℤ, a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n]) := by sorry

/-- [lem:3.3] For a given $n \ge 1$, if $a' \equiv a$ and $b' \equiv b$ then $a' + b' \equiv a + b$, $a' - b' \equiv a - b$ and $a'b' \equiv ab$. --/
theorem lem_3_3 (n : ℕ) (hn : n ≥ 1) :
  ∀ (a b a' b' : ℤ), 
    (a' ≡ a [ZMOD n]) → 
    (b' ≡ b [ZMOD n]) → 
    (a' + b' ≡ a + b [ZMOD n]) ∧ 
    (a' - b' ≡ a - b [ZMOD n]) ∧ 
    (a' * b' ≡ a * b [ZMOD n]) := by sorry

/-- [thm:3.4] Let $n$ have prime-power factorisation $n = p_1^{e_1} \dots p_k^{e_k}$, where $p_1, \dots, p_k$ are distinct primes. Then for any integers $a$ and $b$ we have $a \equiv b \pmod n$ if and only if $a \equiv b \pmod{p_i^{e_i}}$ for each $i = 1, \dots, k$. --/
theorem thm_3_4 (n : ℕ) (hn : 0 < n) (a b : ℤ) :
  a ≡ b [ZMOD n] ↔ ∀ p ∈ n.factorization.support, a ≡ b [ZMOD (p ^ n.factorization p)] := by sorry

/-- [lem:3.5] Let $f(x)$ be a polynomial with integer coefficients, and let $n \ge 1$. If $a \equiv b \pmod n$ then $f(a) \equiv f(b) \pmod n$. --/
theorem lem_3_5 (f : Polynomial ℤ) (n : ℕ) (hn : n ≥ 1) (a b : ℤ) 
  (h : a ≡ b [ZMOD n]) : f.eval a ≡ f.eval b [ZMOD n] := by sorry

/-- [thm:3.6] There is no non-constant polynomial $f(x)$, with integer coefficients, such that $f(x)$ is prime for all integers $x$. --/
theorem thm_3_6 : ¬∃ (f : Polynomial ℤ), f.degree > 0 ∧ ∀ x : ℤ, ∃ p : ℕ, Nat.Prime p ∧ f.eval x = ↑p := by sorry

/-- [thm:3.7] If $d = \gcd(a, n)$, then the linear congruence $ax \equiv b \pmod n$ has a solution if and only if $d$ divides $b$. If $d$ does divide $b$, and if $x_0$ is any solution, then the general solution is given by $x = x_0 + \frac{nt}{d}$ where $t \in \mathbb{Z}$; in particular, the solutions form exactly $d$ congruence classes mod $(n)$, with representatives $x = x_0, x_0 + \frac{n}{d}, x_0 + \frac{2n}{d}, \dots, x_0 + \frac{(d - 1)n}{d}$. --/
theorem thm_3_7 (a b n : ℤ) (d : ℕ) (h : d = Int.natAbs (Int.gcd a n)) :
  -- Part 1: Existence condition
  ((∃ x : ℤ, a * x ≡ b [ZMOD n]) ↔ (d : ℤ) ∣ b) ∧
  -- Part 2: General solution form
  ((∃ x₀ : ℤ, a * x₀ ≡ b [ZMOD n]) →
    ∀ x : ℤ, a * x ≡ b [ZMOD n] ↔ ∃ t : ℤ, x = x₀ + (n / (d : ℤ)) * t) ∧
  -- Part 3: Number of solution classes
  ((d : ℤ) ∣ b →
    ∃ (represents : Fin d → ℤ), 
      (∀ i j : Fin d, i ≠ j → ¬(represents i ≡ represents j [ZMOD n])) ∧
      (∀ x : ℤ, a * x ≡ b [ZMOD n] ↔ 
        ∃ i : Fin d, x ≡ represents i [ZMOD n])) := by sorry

/-- [cor:3.8] If $\gcd(a, n) = 1$ then the solutions $x$ of the linear congruence $ax \equiv b \pmod n$ form a single congruence class mod $(n)$. --/
theorem cor_3_8 (a b n : ℤ) (ha : Int.gcd a n = 1) :
  ∀ x₁ x₂ : ℤ, (a * x₁ ≡ b [ZMOD n] ∧ a * x₂ ≡ b [ZMOD n]) → x₁ ≡ x₂ [ZMOD n] := by sorry

/-- [lem:3.9] (a) Let $m$ divide $a, b$ and $n$, and let $a' = a/m, b' = b/m$ and $n' = n/m$; then $ax \equiv b \pmod n$ if and only if $a'x \equiv b' \pmod{n'}$.
(b) Let $a$ and $n$ be coprime, let $m$ divide $a$ and $b$, and let $a' = a/m$ and $b' = b/m$; then $ax \equiv b \pmod n$ if and only if $a'x \equiv b' \pmod n$. --/
theorem lem_3_9 : 
  (∀ (a b n m : ℕ), m ∣ a → m ∣ b → m ∣ n → 
    let a' := a / m
    let b' := b / m  
    let n' := n / m
    ∀ x : ℤ, (a : ℤ) * x ≡ b [ZMOD n] ↔ (a' : ℤ) * x ≡ b' [ZMOD n']) ∧
  (∀ (a b n m : ℕ), Nat.Coprime a n → m ∣ a → m ∣ b →
    let a' := a / m
    let b' := b / m
    ∀ x : ℤ, (a : ℤ) * x ≡ b [ZMOD n] ↔ (a' : ℤ) * x ≡ b' [ZMOD n]) := by sorry

/-- [thm:3.10] Let $n_1, n_2, \dots, n_k$ be positive integers, with $\gcd(n_i, n_j) = 1$ whenever $i \neq j$, and let $a_1, a_2, \dots, a_k$ be any integers. Then the solutions of the simultaneous congruences $x \equiv a_1 \pmod{n_1}, \dots, x \equiv a_k \pmod{n_k}$ form a single congruence class mod $(n)$, where $n = n_1 n_2 \dots n_k$. --/
theorem thm_3_10 (k : ℕ) (n : Fin k → ℕ+) (a : Fin k → ℤ) 
  (h_coprime : ∀ i j : Fin k, i ≠ j → Nat.gcd (n i) (n j) = 1) :
  ∃ x₀ : ℤ, ∀ x : ℤ, (∀ i : Fin k, (x : ZMod (n i)) = (a i : ZMod (n i))) ↔ 
    (x : ZMod (∏ i : Fin k, (n i : ℕ))) = (x₀ : ZMod (∏ i : Fin k, (n i : ℕ))) := by sorry

/-- [thm:3.11] Let $n = n_1 \dots n_k$ where the integers $n_i$ are mutually coprime, and let $f(x)$ be a polynomial with integer coefficients. Suppose that for each $i = 1, \dots, k$ there are $N_i$ congruence classes $x \in \mathbb{Z}_{n_i}$ such that $f(x) \equiv 0 \pmod{n_i}$. Then there are $N = N_1 \dots N_k$ classes $x \in \mathbb{Z}_n$ such that $f(x) \equiv 0 \pmod n$. --/
theorem thm_3_11 (k : ℕ) (n : ℕ) (f : Polynomial ℤ) 
  (n_list : Fin k → ℕ) (N_list : Fin k → ℕ)
  (h_coprime : ∀ i j : Fin k, i ≠ j → Nat.Coprime (n_list i) (n_list j))
  (h_n : n = (Finset.univ : Finset (Fin k)).prod n_list)
  (h_positive : ∀ i : Fin k, 0 < n_list i)
  (h_N : ∀ i : Fin k, N_list i = Set.ncard {x : ZMod (n_list i) | (f.map (Int.castRingHom (ZMod (n_list i)))).eval x = 0}) :
  Set.ncard {x : ZMod n | (f.map (Int.castRingHom (ZMod n))).eval x = 0} = 
  (Finset.univ : Finset (Fin k)).prod N_list := by sorry

/-- [thm:3.12] Let $n_1, \dots, n_k$ be positive integers, and let $a_1, \dots, a_k$ be any integers. Then the simultaneous congruences $x \equiv a_1 \pmod{n_1}, \dots, x \equiv a_k \pmod{n_k}$ have a solution $x$ if and only if $\gcd(n_i, n_j)$ divides $a_i - a_j$ whenever $i \neq j$. When this condition is satisfied, the general solution forms a single congruence class mod $(n)$, where $n$ is the least common multiple of $n_1, \dots, n_k$. --/
theorem thm_3_12 (k : ℕ) (n : Fin k → ℕ) (a : Fin k → ℤ) 
    (hn : ∀ i, 0 < n i) :
    (∃ x : ℤ, ∀ i : Fin k, x ≡ a i [ZMOD n i]) ↔ 
    (∀ i j : Fin k, i ≠ j → (Nat.gcd (n i) (n j) : ℤ) ∣ (a i - a j)) := by sorry

/-- [thm:4.1] Let $p$ be prime, and let $f(x) = a_d x^d + \dots + a_1 x + a_0$ be a polynomial with integer coefficients, where $a_i \not\equiv 0 \pmod p$ for some $i$. Then the congruence $f(x) \equiv 0 \pmod p$ is satisfied by at most $d$ congruence classes $[x] \in \mathbb{Z}_p$. --/
theorem thm_4_1 (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) 
    (hf : ¬(∀ i, f.coeff i ≡ 0 [ZMOD p])) :
    Set.ncard {x : ZMod p | (f.map (Int.castRingHom (ZMod p))).eval x = 0} ≤ f.natDegree := by sorry

/-- [cor:4.2] Let $f(x) = a_d x^d + \dots + a_1 x + a_0$ be a polynomial with integer coefficients, and let $p$ be prime. If $f(x)$ has more than $d$ roots in $\mathbb{Z}_p$, then $p$ divides each of its coefficients $a_i$. --/
theorem cor_4_2 (f : Polynomial ℤ) (p : ℕ) [Fact (Nat.Prime p)] 
  (h : Nat.card {x : ZMod p | (f.map (Int.castRingHom (ZMod p))).eval x = 0} > f.natDegree) :
  ∀ i, (p : ℤ) ∣ f.coeff i := by sorry

/-- [thm:4.3] If $p$ is prime and $a \not\equiv 0 \pmod p$, then $a^{p-1} \equiv 1 \pmod p$. --/
theorem thm_4_3 (p : ℕ) (a : ℤ) (hp : Nat.Prime p) (ha : ¬(a ≡ 0 [ZMOD p])) : 
  a^(p - 1) ≡ 1 [ZMOD p] := by sorry

/-- [cor:4.4] If $p$ is prime then $a^p \equiv a \pmod p$ for every integer $a$. --/
theorem cor_4_4 (p : ℕ) (a : ℤ) (hp : Nat.Prime p) : 
  (a ^ p) ≡ a [ZMOD p] := by sorry

/-- [cor:4.5] An integer $n$ is prime if and only if $(n - 1)! \equiv -1 \pmod n$. --/
theorem cor_4_5 (n : ℕ) (h : Nat.Prime n) : (n - 1).factorial ≡ -1 [ZMOD n] := by sorry

/-- [thm:4.6] Let $p$ be an odd prime. Then the quadratic congruence $x^2 + 1 \equiv 0 \pmod p$ has a solution if and only if $p \equiv 1 \pmod 4$. --/
theorem thm_4_6 (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : Odd p) :
  (∃ x : ℕ, x^2 + 1 ≡ 0 [MOD p]) ↔ p ≡ 1 [MOD 4] := by sorry

/-- [thm:4.7] There are infinitely many pseudo-primes. --/
def is_pseudo_prime (p : ℕ) : Prop :=
  p > 1 ∧ ¬ Nat.Prime p ∧ (p ∣ 2^(p-1) - 1 ∨ p ∣ 2^(p-1) + 1)

theorem thm_4_7 : ∀ n : ℕ, ∃ p : ℕ, is_pseudo_prime p ∧ p > n := sorry

/-- [lem:5.1] $[a]$ is a unit in $\mathbb{Z}_n$ if and only if $\gcd(a, n) = 1$. --/
theorem lem_5_1 (a : ℤ) (n : ℕ) : 
  IsUnit (a : ZMod n) ↔ Int.gcd a n = 1 := by sorry

/-- [thm:5.2] For each integer $n \ge 1$, the set $U_n$ forms a group under multiplication mod $(n)$, with identity element $[1]$. --/
theorem thm_5_2 (n : ℕ) (hn : 1 ≤ n) : 
  let U := {u : ZMod n | Nat.gcd u.val n = 1}
  (∀ u v : ZMod n, u ∈ U → v ∈ U → u * v ∈ U) ∧
  (1 : ZMod n) ∈ U ∧
  (∀ u : ZMod n, u ∈ U → ∃ v : ZMod n, v ∈ U ∧ u * v = 1) := by sorry

/-- [thm:5.3] If $\gcd(a, n) = 1$ then $a^{\phi(n)} \equiv 1 \pmod n$. --/
theorem thm_5_3 (a n : ℕ) (h : Nat.gcd a n = 1) : 
  a ^ Nat.totient n ≡ 1 [MOD n] := by sorry

/-- [lem:5.4] If $n = p^e$ where $p$ is prime, then $\phi(n) = p^e - p^{e-1} = p^{e-1}(p - 1) = n(1 - \frac{1}{p})$. --/
theorem lem_5_4 (p e : ℕ) (hp : Nat.Prime p) (he : e > 0) :
  Nat.totient (p^e) = (p^e) - (p^e) / p := by sorry

/-- [lem:5.5] If $A$ is a complete set of residues mod $(n)$, and if $m$ and $c$ are integers with $m$ coprime to $n$, then the set $Am + c = \{am + c \mid a \in A\}$ is also a complete set of residues mod $(n)$. --/
theorem lem_5_5 (n : ℕ) (A : Finset ℤ) (m c : ℤ) 
  (hn : n > 0)
  (hA_complete : A.card = n ∧ ∀ a b : ℤ, a ∈ A → b ∈ A → a ≡ b [ZMOD n] → a = b)
  (hm_coprime : Int.gcd m n = 1) :
  let B := A.image (fun a => a * m + c)
  B.card = n ∧ ∀ x y : ℤ, x ∈ B → y ∈ B → x ≡ y [ZMOD n] → x = y := by sorry

/-- [thm:5.6] If $m$ and $n$ are coprime, then $\phi(mn) = \phi(m)\phi(n)$. --/
theorem thm_5_6 (m n : ℕ) (h : Nat.Coprime m n) : 
  Nat.totient (m * n) = Nat.totient m * Nat.totient n := by sorry

/-- [cor:5.7] If $n$ has prime-power factorisation $n = p_1^{e_1} \dots p_k^{e_k}$ then $\phi(n) = \prod_{i=1}^k (p_i^{e_i} - p_i^{e_i-1}) = n \prod_{i=1}^k (1 - \frac{1}{p_i})$. --/
theorem cor_5_7 (n : ℕ) (h : n > 0) : 
  (Nat.totient n = ∏ p ∈ n.primeFactors, (p^(n.factorization p) - p^(n.factorization p - 1))) ∧
  (Nat.totient n = n * ∏ p ∈ n.primeFactors, (1 - 1/(p : ℚ))) := by sorry

/-- [thm:5.8] If $n \ge 1$ then $\sum_{d|n} \phi(d) = n$. --/
theorem thm_5_8 (n : ℕ) (hn : n ≥ 1) : ∑ d ∈ (Nat.divisors n), Nat.totient d = n := by sorry

/-- [lem:6.1] $U_n$ is an abelian group under multiplication mod $(n)$. --/
theorem lem_6_1 (n : ℕ) : 
  Nat.card (ZMod n)ˣ = Nat.totient n := by sorry

/-- [lem:6.2] If $l$ and $m$ are coprime positive integers, then $2^l - 1$ and $2^m - 1$ are coprime. --/
theorem lem_6_2 (l m : ℕ) (hl : 0 < l) (hm : 0 < m) (h : Nat.Coprime l m) : 
  Nat.Coprime (2^l - 1) (2^m - 1) := by sorry

/-- [cor:6.3] Distinct Mersenne numbers are coprime. --/
theorem cor_6_3 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : 
  Nat.gcd (2^a - 1) (2^b - 1) = 1 := by sorry

/-- [lem:6.4] An element $a \in U_n$ is a primitive root if and only if $a^{\phi(n)/q} \not\equiv 1$ in $U_n$ for each prime $q$ dividing $\phi(n)$. --/
theorem lem_6_4 (n : ℕ) (hn : 0 < n) (a : (ZMod n)ˣ) : 
  orderOf a = Nat.totient n ↔ 
  ∀ q : ℕ, Nat.Prime q → q ∣ Nat.totient n → (a : ZMod n) ^ (Nat.totient n / q) ≠ 1 := by sorry

/-- [thm:6.5] If $p$ is prime, then the group $U_p$ has $\phi(d)$ elements of order $d$ for each $d$ dividing $p - 1$. --/
theorem thm_6_5 (p : ℕ) [Fact (Nat.Prime p)] (d : ℕ) (hd : d ∣ p - 1) : 
  Nat.card {x : (ZMod p)ˣ | orderOf x = d} = Nat.totient d := by sorry

/-- [cor:6.6] If $p$ is prime then the group $U_p$ is cyclic. --/
theorem cor_6_6 (p : ℕ) (hp : Nat.Prime p) : IsCyclic (ZMod p)ˣ := by sorry

/-- [thm:6.7] If $p$ is an odd prime, then $U_{p^e}$ is cyclic for all $e \ge 1$. --/
theorem thm_6_7 (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : Odd p) :
  ∀ e : ℕ, e ≥ 1 → IsCyclic ((ZMod (p^e))ˣ) := by sorry

/-- [thm:6.8] The group $U_{2^e}$ is cyclic if and only if $e = 1$ or $e = 2$. --/
theorem thm_6_8 (e : ℕ) : IsCyclic (Units (ZMod (2^e))) ↔ e = 1 ∨ e = 2 := by sorry

/-- [lem:6.9] $2^{n+2} || 5^{2^n} - 1$ for all $n \ge 0$. --/
theorem lem_6_9 : ∀ n : ℕ, (2^(n+2) ∣ 5^(2^n) - 1) ∧ ¬(2^(n+3) ∣ 5^(2^n) - 1) := by sorry

/-- [thm:6.10] If $e \ge 3$ then $U_{2^e} = \{ \pm 5^i \mid 0 \le i < 2^{e-2} \}$. --/
theorem thm_6_10 (e : ℕ) (he : e ≥ 3) : 
  {x : ZMod (2^e) | IsUnit x} = 
  {x : ZMod (2^e) | ∃ i : ℕ, i < 2^(e-2) ∧ (x = (5 : ZMod (2^e))^i ∨ x = -(5 : ZMod (2^e))^i)} := by sorry

/-- [thm:6.11] The group $U_n$ is cyclic if and only if $n = 1, 2, 4, p^e$ or $2p^e$, where $p$ is an odd prime. --/
theorem thm_6_11 (n : ℕ) : 
  IsCyclic (ZMod n)ˣ ↔ 
  (n = 1 ∨ n = 2 ∨ n = 4 ∨ 
   (∃ (p : ℕ) (e : ℕ), Nat.Prime p ∧ Odd p ∧ e > 0 ∧ n = p^e) ∨
   (∃ (p : ℕ) (e : ℕ), Nat.Prime p ∧ Odd p ∧ e > 0 ∧ n = 2 * p^e)) := by sorry

/-- [lem:6.12] If $n = rs$ where $r$ and $s$ are coprime and are both greater than 2, then $U_n$ is not cyclic. --/
theorem lem_6_12 (r s : ℕ) 
  (h1 : Nat.Coprime r s) 
  (h2 : r > 2) 
  (h3 : s > 2) : 
  ¬ IsCyclic (ZMod (r * s))ˣ := by sorry

/-- [thm:6.13] If $n = n_1 \dots n_k$ where $n_1, \dots, n_k$ are mutually coprime, then there is a ring-isomorphism $\mathbb{Z}_n \to \mathbb{Z}_{n_1} \times \dots \times \mathbb{Z}_{n_k}$ which restricts to a group-isomorphism $U_n \to U_{n_1} \times \dots \times U_{n_k}$. --/
theorem thm_6_13 (k : ℕ) (n : Fin k → ℕ) 
  (h_coprime : ∀ i j : Fin k, i ≠ j → Nat.Coprime (n i) (n j))
  (h_pos : ∀ i : Fin k, 0 < n i) :
  let N := (Finset.univ : Finset (Fin k)).prod n
  ∃ (ring_iso : ZMod N ≃+* (Π i : Fin k, ZMod (n i))),
    ∃ (group_iso : (ZMod N)ˣ ≃ (Π i : Fin k, (ZMod (n i))ˣ)),
      ∀ x : (ZMod N)ˣ, ∀ i : Fin k, 
        (ring_iso (x : ZMod N)) i = (group_iso x) i := by sorry

/-- [cor:6.14] Structure of $U_n$ as a direct product of cyclic groups. --/
theorem cor_6_14 (n : ℕ) (hn : 0 < n) : 
  (IsCyclic (MulAut (ZMod n)) ∧ Nat.card (MulAut (ZMod n)) = Nat.totient n) ∧ 
  Nonempty (MulEquiv (ZMod n)ˣ (MulAut (ZMod n))) := by sorry

/-- [thm:6.15] If $n$ is a Carmichael number then $n$ is square-free, and $p - 1$ divides $n - 1$ for each prime $p$ dividing $n$. --/
theorem thm_6_15 (n : ℕ) 
  (h_carmichael : ¬Nat.Prime n ∧ n > 1 ∧ ∀ a : ℤ, a^n ≡ a [ZMOD n]) : 
  Squarefree n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → (p - 1) ∣ (n - 1) := by sorry

/-- [lem:7.1] If $a \in Q_n$, then the number $N$ of elements $t \in U_n$ such that $t^2 = a$ is given by $2^{k+1}$ if $n \equiv 0 \pmod 8$, $2^{k-1}$ if $n \equiv 2 \pmod 4$, and $2^k$ otherwise, where $k$ is the number of distinct prime factors of $n$. --/
theorem lem_7_1 (n : ℕ) (hn : 0 < n) (a : ZMod n) (h : a ∈ {x : ZMod n | ∃ t : (ZMod n)ˣ, t^2 = x}) :
  let k := (Nat.primeFactors n).card
  let U_n := (ZMod n)ˣ
  let N := Set.ncard {t : U_n | (t : ZMod n)^2 = a}
  (n % 8 = 0 → N = 2^(k + 1)) ∧
  (n % 4 = 2 → N = 2^(k - 1)) ∧
  (n % 8 ≠ 0 ∧ n % 4 ≠ 2 → N = 2^k) := by sorry

/-- [lem:7.2] $Q_n$ is a subgroup of $U_n$. --/
theorem lem_7_2 (n : ℕ) (Q_n : Set (ZMod n)ˣ) 
  (h_closed : ∀ a b, a ∈ Q_n → b ∈ Q_n → a * b ∈ Q_n)
  (h_one : (1 : (ZMod n)ˣ) ∈ Q_n)
  (h_inv : ∀ a ∈ Q_n, a⁻¹ ∈ Q_n) :
  ∃ (H : Subgroup (ZMod n)ˣ), H.carrier = Q_n := by sorry

/-- [lem:7.3] Let $n > 2$, and suppose that there is a primitive root $g$ mod $(n)$; then $Q_n$ is a cyclic group of order $\phi(n)/2$, generated by $g^2$, consisting of the even powers of $g$. --/
theorem lem_7_3 (n : ℕ) (hn : 2 < n) (QR : Subgroup (ZMod n)ˣ) 
    (hQR : ∀ x : (ZMod n)ˣ, x ∈ QR ↔ ∃ y : (ZMod n)ˣ, y^2 = x)
    (A : Set (ZMod n)ˣ) (hA : A ⊆ QR) 
    (h_card : A.ncard > (A.image (fun x => x⁻¹)).ncard) :
    ∃ x ∈ A, x⁻¹ ∈ A := by sorry

/-- [cor:7.4] If $p$ is an odd prime, and $g$ is a primitive root mod $(p)$, then $(\frac{g^i}{p}) = (-1)^i$. --/
theorem cor_7_4 (p : ℕ) (g : ℕ) (hp_prime : Nat.Prime p) (hp_odd : Odd p) 
  (hg_coprime : Nat.gcd g p = 1) (hg_primitive : orderOf (g : ZMod p) = p - 1) :
  ∀ i : ℕ, jacobiSym (g^i : ℤ) p = (-1 : ℤ)^i := by sorry

/-- [thm:7.5] If $p$ is an odd prime, then $(\frac{ab}{p}) = (\frac{a}{p}) (\frac{b}{p})$ for all integers $a$ and $b$. --/
theorem thm_7_5 (p : ℕ) [Fact (Nat.Prime p)] (hp_odd : Odd p) (a b : ℤ) :
  jacobiSym (a * b) p = jacobiSym a p * jacobiSym b p := by sorry

/-- [thm:7.6] If $p$ is an odd prime, then for all integers $a$ we have $(\frac{a}{p}) \equiv a^{(p-1)/2} \pmod p$. --/
theorem thm_7_6 
  (p : ℕ) 
  (hp : Nat.Prime p) 
  (hp_odd : p % 2 = 1) 
  (a : ℤ) : 
  jacobiSym a p ≡ a ^ ((p - 1) / 2) [ZMOD p] := by sorry

/-- [cor:7.7] Let $p$ be an odd prime. Then $-1 \in Q_p$ if and only if $p \equiv 1 \pmod 4$. --/
theorem cor_7_7 (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : Odd p) :
  IsSquare (-1 : ZMod p) ↔ p % 4 = 1 := by sorry

/-- [cor:7.8] There are infinitely many primes $p \equiv 1 \pmod 4$. --/
theorem cor_7_8 : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % 4 = 1 := by sorry

/-- [thm:7.9] If $p$ is an odd prime and $a \in U_p$, then $(\frac{a}{p}) = (-1)^\mu$ where $\mu = |aP \cap N|$. --/
theorem thm_7_9 (p : ℕ) (a : ℤ) (hp : p.Prime) (hp_odd : Odd p) 
  (ha : 1 ≤ a ∧ a < p) :
  let P : Set ℤ := {x | 0 < x ∧ 2 * x < p}
  let N : Set ℤ := {x | -p / 2 < x ∧ x < 0}
  let aP : Set ℤ := {x | ∃ y ∈ P, x = a * y}
  let μ : ℕ := Set.ncard (aP ∩ N)
  jacobiSym a p = (-1 : ℤ) ^ μ := by sorry

/-- [cor:7.10] If $p$ is an odd prime then $(\frac{2}{p}) = (-1)^{(p^2-1)/8}$; thus $2 \in Q_p$ if and only if $p \equiv \pm 1 \pmod 8$. --/
theorem cor_7_10 (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : Odd p) :
  (legendreSym 2 p = (-1 : ℤ) ^ ((p^2 - 1) / 8)) ∧ 
  (IsSquare (2 : ZMod p) ↔ (p % 8 = 1 ∨ p % 8 = 7)) := by sorry

/-- [thm:7.11] If $p$ and $q$ are distinct odd primes, then $(\frac{q}{p}) = (\frac{p}{q})$ except when $p \equiv q \equiv 3 \pmod 4$, in which case $(\frac{q}{p}) = -(\frac{p}{q})$. --/
theorem thm_7_11 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) 
  (hp_odd : Odd p) (hq_odd : Odd q) (h_distinct : p ≠ q) :
  (p % 4 = 3 ∧ q % 4 = 3 → jacobiSym q p = -jacobiSym p q) ∧
  (¬(p % 4 = 3 ∧ q % 4 = 3) → jacobiSym q p = jacobiSym p q) := by sorry

/-- [cor:7.12] If $n \ge 1$, then the Fermat number $F_n = 2^{2^n} + 1$ is prime if and only if $3^{(F_n-1)/2} \equiv -1 \pmod{F_n}$. --/
theorem cor_7_12 (n : ℕ) (hn : n ≥ 1) : 
  let F_n := 2^(2^n) + 1
  Nat.Prime F_n ↔ (3 : ZMod F_n)^((F_n - 1) / 2) = (-1 : ZMod F_n) := by sorry

/-- [thm:7.13] Let $p$ be an odd prime, let $e \ge 1$, and let $a \in \mathbb{Z}$. Then $a \in Q_{p^e}$ if and only if $a \in Q_p$. --/
theorem thm_7_13 (p : ℕ) (e : ℕ) (a : ℤ) (hp : Nat.Prime p) (hp_odd : Odd p) (he : 1 ≤ e) :
  (∃ x : ZMod (p ^ e), x ^ 2 = (a : ZMod (p ^ e))) ↔ 
  (∃ x : ZMod p, x ^ 2 = (a : ZMod p)) := by sorry

/-- [thm:7.14] Let $a$ be an odd integer. Then (a) $a \in Q_2$; (b) $a \in Q_4$ iff $a \equiv 1 \pmod 4$; (c) if $e \ge 3$, then $a \in Q_{2^e}$ iff $a \equiv 1 \pmod 8$. --/
def Q (n : ℕ) : Set ℤ := {a | ∃ x : ℤ, x^2 ≡ a [ZMOD n]}

theorem thm_7_14 (a : ℤ) (h : Odd a) :
  (a ∈ Q 2) ∧ 
  (a ∈ Q 4 ↔ a ≡ 1 [ZMOD 4]) ∧ 
  (∀ e : ℕ, e ≥ 3 → (a ∈ Q (2^e) ↔ a ≡ 1 [ZMOD 8])) := by sorry

/-- [thm:7.15] Let $n = n_1 n_2 \dots n_k$, where the integers $n_i$ are mutually coprime. Then $a \in Q_n$ if and only if $a \in Q_{n_i}$ for each $i$. --/
theorem thm_7_15 (n : ℕ) (S : Finset ℕ) (h_pos : ∀ m ∈ S, 0 < m)
    (h_coprime : ∀ m₁ m₂, m₁ ∈ S → m₂ ∈ S → m₁ ≠ m₂ → Nat.gcd m₁ m₂ = 1) 
    (h_prod : n = S.prod id) :
    ∀ a : ℤ, (∃ x : ZMod n, x^2 = (a : ZMod n)) ↔ 
             (∀ m ∈ S, ∃ y : ZMod m, y^2 = (a : ZMod m)) := by sorry

/-- [thm:7.16] Let $a \in U_n$. Then $a \in Q_n$ if and only if (1) $a \in Q_p$ for each odd prime $p$ dividing $n$, and (2) $a \equiv 1 \pmod 4$ if $2^2 || n$, and $a \equiv 1 \pmod 8$ if $2^3 | n$. --/
theorem thm_7_16 (n : ℕ) (a : ℕ) (ha : Nat.gcd a n = 1) :
  (∃ x : ℕ, Nat.gcd x n = 1 ∧ x^2 ≡ a [ZMOD n]) ↔ 
  (∀ p : ℕ, Nat.Prime p → p ≠ 2 → p ∣ n → ∃ x : ℕ, Nat.gcd x p = 1 ∧ x^2 ≡ a [ZMOD p]) ∧
  ((n % 4 = 0 ∧ n % 8 ≠ 0 → a % 4 = 1) ∧
   (n % 8 = 0 → a % 8 = 1)) := by sorry

/-- [lem:8.1] If $g$ is a multiplicative function and $f(n) = \sum_{d|n} g(d)$ for all $n$, then $f$ is multiplicative. --/
theorem lem_8_1 (g : ℕ → ℤ) (hg : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) :
  let f : ℕ → ℤ := fun n => ∑ d ∈ n.divisors, g d
  ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n := by sorry

/-- [thm:8.2] The divisor functions $\tau$ and $\sigma$ are multiplicative. --/
theorem thm_8_2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : Nat.gcd m n = 1) :
  (Finset.card (Nat.divisors (m * n)) = Finset.card (Nat.divisors m) * Finset.card (Nat.divisors n)) ∧
  ((Nat.divisors (m * n)).sum id = ((Nat.divisors m).sum id) * ((Nat.divisors n).sum id)) := by sorry

/-- [thm:8.3] If $n = p_1^{e_1} \dots p_k^{e_k}$, then $\tau(n) = \prod (e_i + 1)$ and $\sigma(n) = \prod \frac{p_i^{e_i+1}-1}{p_i-1}$. --/
theorem thm_8_3 (n : ℕ) (hn : n > 0) :
  (n.factorization.support.prod (fun p => n.factorization p + 1) = (Nat.divisors n).card) ∧
  (n.factorization.support.prod (fun p => (p ^ (n.factorization p + 1) - 1) / (p - 1)) = (Nat.divisors n).sum id) := by sorry

/-- [thm:8.4] (a) If $n = 2^{p-1}(2^p - 1)$ where $p$ and $2^p - 1$ are both prime, then $n$ is perfect. (b) If $n$ is even and perfect, then $n$ has the form given in (a). --/
theorem thm_8_4 : 
  (∀ p : ℕ, Nat.Prime p → Nat.Prime (2^p - 1) → 
    let n := 2^(p-1) * (2^p - 1)
    (∑ d ∈ (Nat.divisors n).filter (· < n), d) = n) ∧
  (∀ n : ℕ, Even n → (∑ d ∈ (Nat.divisors n).filter (· < n), d) = n →
    ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (2^p - 1) ∧ n = 2^(p-1) * (2^p - 1)) := by sorry

/-- [lem:8.5] Let $f$ and $g$ be multiplicative functions, with $f(p^e) = g(p^e)$ for all primes $p$ and integers $e \ge 0$. Then $f = g$. --/
theorem lem_8_5 (f g : ℕ → ℝ) 
  (hf : ∀ m n : ℕ, 0 < m → 0 < n → Nat.gcd m n = 1 → f (m * n) = f m * f n)
  (hg : ∀ m n : ℕ, 0 < m → 0 < n → Nat.gcd m n = 1 → g (m * n) = g m * g n)
  (h : ∀ p : ℕ, Nat.Prime p → ∀ e : ℕ, f (p ^ e) = g (p ^ e)) :
  ∀ n : ℕ, 0 < n → f n = g n := by sorry

/-- [thm:8.6] Let $f$ and $g$ be arithmetic functions. If $f(n) = \sum_{d|n} g(d)$ for all $n$, then $g(n) = \sum_{d|n} f(d)\mu(n/d) = \sum_{d|n} \mu(d)f(n/d)$ for all $n$. --/
theorem thm_8_6 {R : Type*} [CommRing R] (f g : ℕ → R) 
  (h : ∀ n, f n = ∑ d ∈ Nat.divisors n, g d) :
  ∀ n, g n = ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius (n / d) * f d ∧
       g n = ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius d * f (n / d) := by sorry

/-- [cor:8.7] If $n \ge 1$ then $\phi(n) = \sum_{d|n} d\mu(n/d) = \sum_{d|n} \mu(d) \frac{n}{d}$. --/
theorem cor_8_7 (n : ℕ) (hn : n ≥ 1) : 
  Nat.totient n = (Nat.divisors n).sum (fun d => d * ArithmeticFunction.moebius (n / d)) ∧
  Nat.totient n = (Nat.divisors n).sum (fun d => ArithmeticFunction.moebius d * (n / d)) := by sorry

/-- [thm:8.8] If $n = p_1^{e_1} \dots p_k^{e_k}$, then $\mu(n) = (-1)^k$ if each $e_i = 1$, and $0$ if some $e_i > 1$. --/
theorem thm_8_8 (n : ℕ) (hn : 0 < n) : 
  ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius d = 1 := by sorry

/-- [cor:8.9] The function $\mu$ is multiplicative. --/
theorem cor_8_9 (a b : ℕ) (h : Nat.Coprime a b) : 
  ArithmeticFunction.moebius (a * b) = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b := by sorry

/-- [lem:8.10] The Dirichlet product is commutative and associative, and has $I$ as an identity. --/
theorem lem_8_10 (f : ℕ → ℝ) : 
  let I : ℕ → ℝ := fun n => if n = 1 then 1 else 0
  let dirichlet_product (f g : ℕ → ℝ) (n : ℕ) := ∑ d ∈ (Nat.divisors n), f d * g (n / d)
  ∀ n : ℕ, dirichlet_product f I n = f n ∧ dirichlet_product I f n = f n := by sorry

/-- [lem:8.11] If $f$ is an arithmetic function with $f(1) \neq 0$, then there exists an arithmetic function $g$ such that $f * g = I = g * f$. --/
theorem lem_8_11 (R : Type*) [Field R] (f : ℕ → R) (hf : f 1 ≠ 0) :
  ∃ g : ℕ → R, 
    (∀ n : ℕ, (∑ d ∈ n.divisors, f d * g (n / d)) = if n = 1 then 1 else 0) ∧
    (∀ n : ℕ, (∑ d ∈ n.divisors, g d * f (n / d)) = if n = 1 then 1 else 0) := by sorry

/-- [thm:8.12] The set of arithmetic functions with $f(1) \neq 0$ is an abelian group under Dirichlet product. --/
theorem thm_8_12 (R : Type*) [Field R] :
  let ArithmeticFunction := ℕ → R
  let dirichlet_conv (f g : ArithmeticFunction) : ArithmeticFunction := 
    fun n => ∑ d ∈ n.divisors, f d * g (n / d)
  let non_zero_at_one := {f : ArithmeticFunction | f 1 ≠ 0}
  -- The set of arithmetic functions with f(1) ≠ 0 forms an abelian group under Dirichlet convolution
  (∃ (inst : Group non_zero_at_one), 
    (∀ f : non_zero_at_one, ∀ g : non_zero_at_one, 
      dirichlet_conv f.val g.val = dirichlet_conv g.val f.val) ∧
    -- The inverse of f is the function f_inv where
    (∀ f : non_zero_at_one, ∃ f_inv : ArithmeticFunction,
      f_inv 1 = 1 / f.val 1 ∧
      (∀ n : ℕ, n > 1 → 
        f_inv n = -1 / f.val 1 * ∑ d ∈ (n.divisors.filter (· < n)), 
          f.val (n / d) * f_inv d) ∧
      -- f_inv is the group inverse of f
      dirichlet_conv f.val f_inv = (fun _ => 1) ∧
      dirichlet_conv f_inv f.val = (fun _ => 1))) := by sorry

/-- [thm:8.13] $f = g * u$ if and only if $g = f * \mu$. --/
theorem thm_8_13 :
  ∀ {α : Type*} [CommRing α] (f g : ArithmeticFunction α),
  f = g * ArithmeticFunction.zeta ↔ g = f * ArithmeticFunction.moebius := by sorry

/-- [thm:8.14] If $g$ and $h$ are multiplicative functions, and if $f = g * h$, then $f$ is multiplicative. --/
theorem thm_8_14 (g h : ℕ → ℤ) 
  (hg : ∀ m n : ℕ, 0 < m → 0 < n → Nat.gcd m n = 1 → g (m * n) = g m * g n)
  (hh : ∀ m n : ℕ, 0 < m → 0 < n → Nat.gcd m n = 1 → h (m * n) = h m * h n) :
  let f : ℕ → ℤ := fun n => ∑ d ∈ (Nat.divisors n), g d * h (n / d)
  ∀ m n : ℕ, 0 < m → 0 < n → Nat.gcd m n = 1 → f (m * n) = f m * f n := by sorry

/-- [cor:8.15] Suppose that $f(n) = \sum_{d|n} g(d)$. Then $f$ is multiplicative if and only if $g$ is multiplicative. --/
theorem cor_8_15 (f g : ℕ → ℂ) 
  (h : ∀ n : ℕ, n > 0 → f n = ∑ d ∈ Nat.divisors n, g d) :
  (∀ m n : ℕ, m > 0 → n > 0 → Nat.gcd m n = 1 → f (m * n) = f m * f n) ↔ 
  (∀ m n : ℕ, m > 0 → n > 0 → Nat.gcd m n = 1 → g (m * n) = g m * g n) := by sorry

/-- [thm:9.1] The series $\zeta(s) = \sum 1/n^s$ converges for all real $s > 1$, and diverges for all real $s \le 1$. --/
theorem thm_9_1 (s : ℝ) : 
  (Summable (fun n : ℕ+ => (1 : ℝ) / (n : ℝ) ^ s)) ↔ s > 1 := by sorry

/-- [thm:9.2] The series $\sum 1/p_n$ diverges. --/
noncomputable def nthPrime (n : ℕ) : ℕ := sorry

-- Properties of the nthPrime function
axiom nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n)
axiom nthPrime_strictly_increasing (m n : ℕ) : m < n → nthPrime m < nthPrime n
axiom nthPrime_complete (p : ℕ) : Nat.Prime p → ∃ n : ℕ, nthPrime n = p

-- The main theorem: the sum of reciprocals of primes diverges
theorem thm_9_2 : 
  ¬ Summable (fun n : ℕ => (1 : ℝ) / (nthPrime n)) := by sorry

/-- [thm:9.3] If $s > 1$ then $\zeta(s) = \prod_p (1 - p^{-s})^{-1}$. --/
theorem thm_9_3 (s : ℂ) (hs : 1 < s.re) : 
  riemannZeta s = ∏' p : ℕ, if Nat.Prime p then (1 - (p : ℂ)^(-s))⁻¹ else 1 := by sorry

/-- [thm:9.4] If $s > 1$ then $\sum_{n=1}^\infty \frac{\mu(n)}{n^s} = \frac{1}{\zeta(s)}$. --/
theorem thm_9_4 (s : ℝ) (hs : s > 1) : 
  ∑' n : ℕ+, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ s = 1 / riemannZeta s := by sorry

/-- [thm:9.5] The probability that two randomly- and independently-chosen integers are coprime is given by $1/\zeta(2) = 6/\pi^2$. --/
theorem thm_9_5 : 
  Filter.Tendsto (fun N : ℕ => 
    ((Finset.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = 1) 
      (Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N))).card : ℝ) / (N : ℝ)^2) 
    Filter.atTop (nhds (6 / Real.pi^2)) := by sorry

/-- [thm:9.6] Multiplication of Dirichlet series corresponds to Dirichlet product of coefficients. --/
theorem thm_9_6 (a b : ℕ → ℂ) (s : ℂ) :
  (∑' n : ℕ, if n = 0 then 0 else a n / (n : ℂ) ^ s) * 
  (∑' n : ℕ, if n = 0 then 0 else b n / (n : ℂ) ^ s) = 
  ∑' n : ℕ, (if n = 0 then 0 else (∑ d ∈ (n : ℕ).divisors, a d * b (n / d))) / (n : ℂ) ^ s := by sorry

/-- [thm:9.7] Euler product for multiplicative functions. --/
theorem thm_9_7 (g : ℕ → ℂ) 
  (hg : ∀ m n : ℕ, Nat.gcd m n = 1 → g (m * n) = g m * g n) :
  let f : ℕ → ℂ := fun n => ∏ d ∈ Nat.divisors n, g d
  (∀ m n : ℕ, Nat.gcd m n = 1 → f (m * n) = f m * f n) ∧ 
  ∀ s : ℂ, (∑' n : ℕ, f (n + 1) / (n + 1 : ℂ)^s) = 
    ∏' p : ℕ, if Nat.Prime p then (1 - g p / (p : ℂ)^s)⁻¹ else 1 := by sorry

/-- [cor:9.8] Euler product for Dirichlet series of multiplicative functions. --/
theorem cor_9_8 (f : ℕ → ℂ) 
  (hf : ∀ m n : ℕ, Nat.gcd m n = 1 → f (m * n) = f m * f n)
  (s : ℂ) :
  (∑' n : ℕ, if n = 0 then 0 else f n / (n : ℂ)^s) = 
  ∏' p : ℕ, if Nat.Prime p then (1 - f p / (p : ℂ)^s)⁻¹ else 1 := by sorry

/-- [thm:9.9] Existence of abscissa of absolute convergence. --/
theorem thm_9_9 
  (a : ℕ → ℝ) 
  (lambda : ℕ → ℝ) 
  (hlambda_nonneg : ∀ n, 0 ≤ lambda n)
  (hlambda_strict_mono : StrictMono lambda)
  (hlambda_tendsto : Filter.Tendsto lambda Filter.atTop Filter.atTop)
  (sigma : ℝ)
  (h_conv : ∀ s : ℂ, s.re > sigma → Summable (fun n => |a n| * Real.exp (-(s.re * lambda n))))
  (h_div : ∀ s : ℂ, s.re < sigma → ¬Summable (fun n => |a n| * Real.exp (-(s.re * lambda n))))
  : ∀ sigma' : ℝ, 
    (∀ s : ℂ, s.re > sigma' → Summable (fun n => |a n| * Real.exp (-(s.re * lambda n)))) ∧
    (∀ s : ℂ, s.re < sigma' → ¬Summable (fun n => |a n| * Real.exp (-(s.re * lambda n))))
    → sigma' = sigma := by sorry

/-- [thm:9.10] Analyticity of Dirichlet series. --/
theorem thm_9_10 
  (a : ℕ → ℂ) 
  (ha_bounded : ∃ M : ℝ, ∀ n : ℕ, n ≥ 1 → Complex.abs (a n) ≤ M) :
  let σ_a := sInf {σ : ℝ | Summable (fun n : ℕ => if n ≥ 1 then Complex.abs (a n) * (n : ℝ)^(-σ) else 0)}
  AnalyticOn ℂ (fun s : ℂ => ∑' n : ℕ, if n ≥ 1 then a n * (n : ℂ)^(-s) else 0)
    {s : ℂ | s.re > σ_a} := by sorry

/-- [lem:10.1] The set $S_2$, consisting of the sums of two squares, is closed under multiplication. --/
theorem lem_10_1 : 
  ∀ a b : ℤ, 
    (∃ x y : ℤ, a = x^2 + y^2) → 
    (∃ u v : ℤ, b = u^2 + v^2) → 
    (∃ p q : ℤ, a * b = p^2 + q^2) := by sorry

/-- [thm:10.2] Each prime $p \equiv 1 \pmod 4$ is a sum of two squares. --/
theorem thm_10_2 (p : ℕ) (hp_prime : Nat.Prime p) (hp_mod : p % 4 = 1) : 
  ∃ a b : ℕ, p = a^2 + b^2 := by sorry

/-- [thm:10.3] A positive integer $n$ is a sum of two squares if and only if every prime $q \equiv 3 \pmod 4$ divides $n$ to an even power. --/
theorem thm_10_3 (n : ℕ) (hn : 0 < n) :
  (∃ a b : ℕ, a^2 + b^2 = n) ↔ 
  (∀ p : ℕ, Nat.Prime p → p % 4 = 3 → Even (Nat.factorization n p)) := by sorry

/-- [cor:10.4] A prime $p$ is a sum of two squares if and only if $p = 2$ or $p \equiv 1 \pmod 4$. --/
theorem cor_10_4 (p : ℕ) (hp : Nat.Prime p) : 
  (∃ a b : ℤ, p = a^2 + b^2) ↔ (p = 2 ∨ p % 4 = 1) := by sorry

/-- [lem:10.5] The set $S_4$, consisting of the sums of four squares, is closed under multiplication. --/
theorem lem_10_5 : 
  ∀ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℤ, 
    ∃ c₁ c₂ c₃ c₄ : ℤ, 
      (a₁^2 + a₂^2 + a₃^2 + a₄^2) * (b₁^2 + b₂^2 + b₃^2 + b₄^2) = c₁^2 + c₂^2 + c₃^2 + c₄^2 := by sorry

/-- [thm:10.6] Every non-negative integer is a sum of four squares. --/
theorem thm_10_6 : ∀ n : ℕ, ∃ a b c d : ℤ, (n : ℤ) = a^2 + b^2 + c^2 + d^2 := by sorry

open Real Topology
/-- [lem:10.7] If $\Lambda$ is a lattice in $\mathbb{R}^n$, then $\Lambda$ is a subgroup of $\mathbb{R}^n$ under addition. --/
theorem lem_10_7 (n : ℕ) (Λ : Set (Fin n → ℝ)) 
  (h_lattice : -- Λ is a lattice ∈ ℝⁿ, meaning it's a discrete subgroup
     -- Λ is a subgroup
     (∀ x y : Fin n → ℝ, x ∈ Λ → y ∈ Λ → (fun i => x i + y i) ∈ Λ) ∧ 
     -- Λ is discrete
     (∃ d > 0, ∀ x y : Fin n → ℝ, x ∈ Λ → y ∈ Λ → x ≠ y → 
       ∃ i, |x i - y i| ≥ d) ∧
     -- Λ is generated by n linearly independent vectors
     (∃ (B : Matrix (Fin n) (Fin n) ℝ), 
       LinearIndependent ℝ (fun j : Fin n => fun i => B j i) ∧
       ∀ v : Fin n → ℝ, v ∈ Λ ↔ ∃ z : Fin n → ℤ, v = fun i => ∑ j, z j * B j i)) :
  -- The theorem statement properly concludes that Λ is an additive subgroup
  ∃ (H : AddSubgroup (Fin n → ℝ)), ↑H = Λ := sorry

/-- [lem:10.8] For each $v \in \mathbb{R}^n$ there is a unique $w \in F$ with $v \sim w$. --/
theorem lem_10_8 (n : ℕ) (F : Subspace ℝ (Fin n → ℝ)) 
  (π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  (h_range : ∀ v : Fin n → ℝ, π v ∈ F)
  (h_unique : ∀ v : Fin n → ℝ, ∀ w₁ w₂ : Fin n → ℝ, 
    w₁ ∈ F → w₂ ∈ F → π v = w₁ → π v = w₂ → w₁ = w₂) :
  (π ∘ₗ π = π) ∧ (F = {v : Fin n → ℝ | π v = v}) := sorry

open MeasureTheory
/-- [lem:10.9] If $\text{vol}(X) > \text{vol}(F)$ then the restriction $\phi|_X$ of $\phi$ to $X$ is not one-to-one. --/
theorem lem_10_9 {X F : Set ℝ} 
  (φ : ℝ → ℝ) 
  (h : volume X > volume F) :
  ¬Function.Injective (fun x : X => φ x) := by sorry

open MeasureTheory MeasureTheory.Measure Set Topology
/-- [thm:10.10] Let $\Lambda$ be a lattice in $\mathbb{R}^n$ with fundamental region $F$, and let $X$ be a centrally symmetric convex set in $\mathbb{R}^n$ with $\text{vol}(X) > 2^n \text{vol}(F)$. Then $X$ contains a non-zero lattice-point of $\Lambda$. --/
theorem thm_10_10 (n : ℕ) (Λ : AddSubgroup (Fin n → ℝ)) 
  (F : Set (Fin n → ℝ))
  (X : Set (Fin n → ℝ))
  (hΛ : ∃ (B : Fin n → (Fin n → ℝ)), LinearIndependent ℝ B ∧ 
        Submodule.span ℝ (Set.range B) = ⊤ ∧ 
        ∀ x : Fin n → ℝ, x ∈ Λ ↔ ∃ (c : Fin n → ℤ), x = ∑ i, c i • B i)
  (hF : ∀ x y, x ∈ F → y ∈ Λ → (∀ z, z ∈ F → z ≠ x + y)) -- Translates of F by Λ are disjoint
  (hF_cover : ∀ x : Fin n → ℝ, ∃ y ∈ Λ, ∃ z ∈ F, x = y + z) -- F with translates covers all of ℝ^n
  (hX_symm : ∀ x, x ∈ X ↔ -x ∈ X)
  (hX_conv : Convex ℝ X)
  (hvol : volume X > 2^n * volume F) :
  ∃ p : Fin n → ℝ, p ∈ Λ ∧ p ≠ 0 ∧ p ∈ X := sorry

/-- [thm:11.2] There is no Pythagorean triple $(a, b, c)$ with $a = b$. --/
theorem thm_11_2 : ¬∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ a = b := by sorry

/-- [thm:11.3] If $u$ and $v$ are coprime positive integers of opposite parity, with $u > v$, then the numbers $a = u^2 - v^2$, $b = 2uv$, $c = u^2 + v^2$ form a primitive Pythagorean triple. Conversely, every primitive Pythagorean triple is given by this form. --/
theorem thm_11_3 : 
  ∀ (a b c : ℕ), 
    (a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ Nat.gcd (Nat.gcd a b) c = 1) ↔ 
    (∃ (u v : ℕ), u > 0 ∧ v > 0 ∧ Nat.gcd u v = 1 ∧ (u % 2) ≠ (v % 2) ∧ u > v ∧ 
      a = u^2 - v^2 ∧ b = 2 * u * v ∧ c = u^2 + v^2) := by sorry

/-- [cor:11.4] The general form for a Pythagorean triple is a multiple of a primitive one. --/
theorem cor_11_4 : 
  ∀ (a b c : ℕ), 
    0 < a ∧ 0 < b ∧ 0 < c ∧ a^2 + b^2 = c^2 → 
    ∃ (k d e f : ℕ), 
      0 < k ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
      a = k * d ∧ b = k * e ∧ c = k * f ∧
      d^2 + e^2 = f^2 ∧ Nat.gcd (Nat.gcd d e) f = 1 := by sorry

/-- [thm:11.5] There are no positive integer solutions $x, y$ and $z$ of $x^4 + y^4 = z^2$. --/
theorem thm_11_5 : ¬ ∃ (x y z : ℕ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x^4 + y^4 = z^2 := by sorry

/-- [cor:11.6] There are no positive integer solutions of $a^4 + b^4 = c^4$. --/
theorem cor_11_6 : ¬∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a^4 + b^4 = c^4 := by sorry

/-- [cor:11.7] If $n$ is divisible by 4 then there are no positive integer solutions of $a^n + b^n = c^n$. --/
theorem cor_11_7 (n : ℕ) (h : 4 ∣ n) : 
  ¬∃ (a b c : ℕ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a^n + b^n = c^n := by sorry

/-- [thm:11.8] Let $p$ and $q$ be odd primes such that (1) if $x^p + y^p + z^p \equiv 0 \pmod q$ then $x, y$ or $z \equiv 0 \pmod q$; (2) the class $[p]$ is not a $p$-th power in $\mathbb{Z}_q$. Then case I of FLT is true for exponent $p$. --/
theorem thm_11_8 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hp_odd : Odd p) (hq_odd : Odd q) :
  (∀ x y z : ZMod q, x^p + y^p + z^p = 0 → x = 0 ∨ y = 0 ∨ z = 0) →
  (¬∃ a : ZMod q, a^p = (p : ZMod q)) →
  ¬∃ x y z : ℤ, x^p + y^p = z^p ∧ ¬(p : ℤ) ∣ (x * y * z) := by sorry
