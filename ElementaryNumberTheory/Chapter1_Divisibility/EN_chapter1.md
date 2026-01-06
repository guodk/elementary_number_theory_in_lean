# Elementary Number Theory - Formalization Plan
**Source:** Gareth A. Jones and J. Mary Jones, Springer Undergraduate Mathematics Series.

## Preamble & Context
This document contains the natural language statements of theorems from Chapter 1. The goal is to translate these into Lean 4 statements using `Mathlib`.

**Imports needed for this chapter:**
- `Mathlib.Data.Int.Basic`
- `Mathlib.Data.Int.Lemmas`
- `Mathlib.Data.Nat.Gcd`
- `Mathlib.Algebra.Group.Defs`

---

# Chapter 1: Divisibility

## 1.1 Divisors

### Theorem 1.1 (The Division Algorithm)
**Statement:** If $a$ and $b$ are integers with $b > 0$, then there is a unique pair of integers $q$ and $r$ such that $a = qb + r$ and $0 \le r < b$.
* **Formalization Hint:** Use `ExistsUnique`. In Mathlib, this relates to `Int.div` and `Int.mod`.

### Corollary 1.2 (General Division Algorithm)
**Statement:** If $a$ and $b$ are integers with $b \ne 0$, then there is a unique pair of integers $q$ and $r$ such that $a = qb + r$ and $0 \le r < |b|$.

### Definition: Divisibility
**Statement:** An integer $b$ divides $a$ (written $b \mid a$) if $a = qb$ for some integer $q$.
* **Formalization Hint:** Use the standard notation `\|` in Lean.

### Theorem 1.3
**Statement:**
(a) If $c$ divides $a_1, \dots, a_k$, then $c$ divides $a_1 u_1 + \dots + a_k u_k$ for all integers $u_1, \dots, u_k$.
(b) $a \mid b$ and $b \mid a$ if and only if $a = \pm b$.
* **Formalization Hint:** For (b), note that in Lean `Int.associated_iff_eq_or_eq_neg`.

### Corollary 1.4
**Statement:** If $c$ divides $a$ and $b$, then $c$ divides $au + bv$ for all integers $u$ and $v$.

### Definition: Greatest Common Divisor (GCD)
**Statement:** Let $a$ and $b$ be integers, not both 0. The greatest common divisor $d = \gcd(a, b)$ is the unique integer satisfying:
1. $d \mid a$ and $d \mid b$.
2. If $c \mid a$ and $c \mid b$, then $c \le d$.
* **Formalization Hint:** Map this to `Int.gcd`.

### Lemma 1.5
**Statement:** If $a = qb + r$, then $\gcd(a, b) = \gcd(b, r)$.
* **Formalization Hint:** This is the basis of the Euclidean Algorithm.

### Theorem 1.6 (Euclid's Algorithm Result)
**Statement:** In the Euclidean algorithm calculation, the greatest common divisor $d$ is equal to the last non-zero remainder $r_{n-1}$.
* **Formalization Hint:** This implies that the recursive calculation of GCD terminates and computes the correct value.

## 1.2 Bezout's Identity

### Theorem 1.7 (Bezout's Identity)
**Statement:** If $a$ and $b$ are integers (not both 0), then there exist integers $u$ and $v$ such that $\gcd(a, b) = au + bv$.

### Theorem 1.8
**Statement:** Let $a$ and $b$ be integers (not both 0) with greatest common divisor $d$. Then an integer $c$ has the form $ax + by$ for some $x, y \in \mathbb{Z}$ if and only if $c$ is a multiple of $d$. In particular, $d$ is the least positive integer of the form $ax + by$.

### Corollary 1.9
**Statement:** Two integers $a$ and $b$ are coprime if and only if there exist integers $x$ and $y$ such that $ax + by = 1$.
* **Formalization Hint:** Coprime means `Int.gcd a b = 1`.

### Corollary 1.10
**Statement:** If $\gcd(a, b) = d$, then $\gcd(ma, mb) = m \cdot d$ for every integer $m > 0$, and $\gcd(a/d, b/d) = 1$.

### Corollary 1.11
**Statement:** Let $a$ and $b$ be coprime integers.
(a) If $a \mid c$ and $b \mid c$, then $ab \mid c$.
(b) If $a \mid bc$, then $a \mid c$ (Euclid's Lemma).

## 1.3 Least Common Multiples

### Definition: Least Common Multiple (LCM)
**Statement:** The least common multiple $l = \text{lcm}(a, b)$ of non-zero integers $a, b$ is the unique positive integer satisfying:
1. $a \mid l$ and $b \mid l$.
2. If $a \mid c$ and $b \mid c$ with $c > 0$, then $l \le c$.

### Theorem 1.12
**Statement:** Let $a$ and $b$ be positive integers. Then $\gcd(a, b) \cdot \text{lcm}(a, b) = ab$.

## 1.4 Linear Diophantine Equations

### Theorem 1.13
**Statement:** Let $a, b, c$ be integers with $a, b$ not both 0, and let $d = \gcd(a, b)$. Then the equation $ax + by = c$ has an integer solution $x, y$ if and only if $d$ divides $c$.
If $d \mid c$, then there are infinitely many solutions. If $(x_0, y_0)$ is a particular solution, the general solution is given by:
$$x = x_0 + \frac{b}{d}n, \quad y = y_0 - \frac{a}{d}n \quad (n \in \mathbb{Z})$$