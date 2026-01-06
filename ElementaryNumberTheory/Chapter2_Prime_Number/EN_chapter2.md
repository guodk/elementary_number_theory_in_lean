# Elementary Number Theory - Formalization Plan
**Source:** Gareth A. Jones and J. Mary Jones, Springer Undergraduate Mathematics Series.

## Preamble & Context
This document contains the natural language statements of theorems from Chapter 2.
**Note:** While Chapter 1 focused on Integers ($\mathbb{Z}$), Prime number theory in Mathlib is primarily developed over Natural Numbers ($\mathbb{N}$). We will generally use `Nat` for this chapter.

**Imports needed for this chapter:**
- `Mathlib.Data.Nat.Prime`
- `Mathlib.Data.Nat.Factors`
- `Mathlib.Data.Real.Irrational`
- `Mathlib.NumberTheory.Primes.InfinitelyMany`

---

# Chapter 2: Prime Numbers

## 2.1 Prime numbers and prime-power factorisations

### Definition: Prime Number
**Statement:** An integer $p > 1$ is prime if the only positive divisors of $p$ are 1 and $p$.
* **Formalization Hint:** Use `Nat.Prime`.

### Lemma 2.1
**Statement:** Let $p$ be prime, and let $a$ and $b$ be any integers.
(a) Either $p$ divides $a$, or $a$ and $p$ are coprime.
(b) If $p$ divides $ab$, then $p$ divides $a$ or $p$ divides $b$ (Euclid's Lemma for Primes).
* **Formalization Hint:** (b) is `Nat.Prime.dvd_mul`.

### Corollary 2.2
**Statement:** If $p$ is prime and $p$ divides $a_1 \dots a_k$, then $p$ divides $a_i$ for some $i$.

### Theorem 2.3 (Fundamental Theorem of Arithmetic)
**Statement:** Each integer $n > 1$ has a prime-power factorisation $n = p_1^{e_1} \dots p_k^{e_k}$, where $p_1, \dots, p_k$ are distinct primes and $e_i$ are positive integers. This factorisation is unique, apart from permutations of the factors.
* **Formalization Hint:** Mathlib has `Nat.factors` (list of prime factors) and `Nat.factorization` (finsupp from primes to exponents). The uniqueness is `Nat.factors_unique`.

### Lemma 2.4
**Statement:** If $a_1, \dots, a_r$ are mutually coprime positive integers, and their product $a_1 \dots a_r$ is an $m$-th power ($m \ge 2$), then each $a_i$ is an $m$-th power.

### Corollary 2.5
**Statement:** If a positive integer $m$ is not a perfect square, then $\sqrt{m}$ is irrational.
* **Formalization Hint:** Use `Irrational` from `Mathlib.Data.Real.Irrational`.

## 2.2 Distribution of primes

### Theorem 2.6 (Euclid's Theorem)
**Statement:** There are infinitely many primes.
* **Formalization Hint:** `Set.Infinite {p | Nat.Prime p}` or `Nat.exists_infinite_primes`.

### Corollary 2.7
**Statement:** The $n$-th prime $p_n$ satisfies $p_n \le 2^{2^{n-1}}$ for all $n \ge 1$.

### Theorem 2.9
**Statement:** There are infinitely many primes of the form $4q + 3$.
* **Formalization Hint:** `Set.Infinite {p | p.Prime ∧ p % 4 = 3}`.

### Theorem 2.10 (Dirichlet's Theorem)
**Statement:** If $a$ and $b$ are coprime integers, then there are infinitely many primes of the form $aq + b$.
* **Formalization Hint:** This is a major theorem (`Mathlib.NumberTheory.DirichletTheorem`), usually stated as `Set.Infinite {p | p.Prime ∧ p % a = b}` given `gcd a b = 1`.

## 2.3 Fermat and Mersenne primes

### Lemma 2.11
**Statement:** If $2^m + 1$ is prime, then $m = 2^n$ for some integer $n \ge 0$.
* **Formalization Hint:** Relates to Fermat numbers.

### Lemma 2.12
**Statement:** Distinct Fermat numbers $F_n = 2^{2^n} + 1$ are mutually coprime.

### Theorem 2.13
**Statement:** If $m > 1$ and $a^m - 1$ is prime, then $a = 2$ and $m$ is prime.
* **Formalization Hint:** Relates to Mersenne primes.

## 2.4 Primality-testing and factorisation

### Lemma 2.14
**Statement:** An integer $n > 1$ is composite if and only if it is divisible by some prime $p \le \sqrt{n}$.
* **Formalization Hint:** `Nat.prime_def_le_sqrt`.