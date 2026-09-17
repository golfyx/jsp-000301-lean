/-
Copyright (c) 2026 golfyx. Formalization of a classical counterexample.

JSP-000301 / the first yes-no question of Erdős problem #365:

  If two consecutive positive integers are powerful, must at least one be a
  perfect square?

The catalog already records the negative answer via Golomb's pair
12167 = 23³, 12168 = 2³ · 3² · 13². This file machine-checks that pair.
Mathematical discovery remains with Golomb (1970); this development claims
only the formalization.
-/

namespace JSP000301

/-! ## Definitions matching the catalog review note -/

/-- A prime is an integer `p ≥ 2` whose only positive divisors are `1` and `p`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ n, n ∣ p → n = 1 ∨ n = p

/-- A powerful number has exponent at least two in every prime factor. -/
def Powerful (n : Nat) : Prop :=
  0 < n ∧ ∀ p, IsPrime p → p ∣ n → p * p ∣ n

def IsSquare (n : Nat) : Prop :=
  ∃ k, k * k = n

/-- The catalog yes/no question: consecutive powerful numbers force a square. -/
def Question : Prop :=
  ∀ n, Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)

/-! ## Primality of the four primes that appear -/

theorem isPrime_of_fin (p : Nat) (hp : 2 ≤ p)
    (h : ∀ n : Fin p, n.val ∣ p → n.val = 1) : IsPrime p := by
  refine ⟨hp, ?_⟩
  intro n hd
  have ppos : 0 < p := Nat.lt_of_lt_of_le (by decide : 0 < 2) hp
  have nle : n ≤ p := Nat.le_of_dvd ppos hd
  rcases Nat.lt_or_eq_of_le nle with hlt | rfl
  · exact Or.inl (h ⟨n, hlt⟩ hd)
  · exact Or.inr rfl

theorem prime_2 : IsPrime 2 :=
  isPrime_of_fin 2 (by decide) (by decide)

theorem prime_3 : IsPrime 3 :=
  isPrime_of_fin 3 (by decide) (by decide)

theorem prime_13 : IsPrime 13 :=
  isPrime_of_fin 13 (by decide) (by decide)

theorem prime_23 : IsPrime 23 :=
  isPrime_of_fin 23 (by decide) (by decide)

/-! ## Euclid's lemma from the core gcd library -/

theorem gcd_eq_one_or_self {p a : Nat} (hp : IsPrime p) :
    Nat.gcd p a = 1 ∨ Nat.gcd p a = p := by
  have hdiv : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  cases hp.2 (Nat.gcd p a) hdiv with
  | inl h1 => exact Or.inl h1
  | inr hp' => exact Or.inr hp'

theorem not_dvd_one {p : Nat} (hp : IsPrime p) : ¬ p ∣ 1 := by
  intro h
  have : p ≤ 1 := Nat.le_of_dvd (by decide) h
  have : 2 ≤ p := hp.1
  omega

theorem prime_dvd_prime {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (h : p ∣ q) : p = q := by
  cases hq.2 p h with
  | inl h1 =>
    have : 2 ≤ p := hp.1
    omega
  | inr hq' => exact hq'

theorem prime_dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  rcases gcd_eq_one_or_self (a := a) hp with h1 | hp'
  · exact Or.inr ((Nat.coprime_iff_gcd_eq_one.mpr h1).dvd_of_dvd_mul_left h)
  · exact Or.inl (hp' ▸ Nat.gcd_dvd_right p a)

theorem prime_dvd_pow {p a n : Nat} (hp : IsPrime p) (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
    rw [Nat.pow_zero] at h
    exact (not_dvd_one hp h).elim
  | succ n ih =>
    rw [Nat.pow_succ] at h
    rcases prime_dvd_mul hp h with hpow | ha
    · exact ih hpow
    · exact ha

/-! ## Arithmetic of the Golomb pair -/

theorem eq_12167 : 23 ^ 3 = 12167 := by decide
theorem eq_12168 : 2 ^ 3 * 3 ^ 2 * 13 ^ 2 = 12168 := by decide
theorem sq_110 : 110 * 110 = 12100 := by decide
theorem sq_111 : 111 * 111 = 12321 := by decide

theorem twenty_three_sq_dvd : 23 * 23 ∣ 12167 := ⟨23, by decide⟩

theorem two_sq_dvd : 2 * 2 ∣ 12168 := ⟨3042, by decide⟩

theorem three_sq_dvd : 3 * 3 ∣ 12168 := ⟨1352, by decide⟩

theorem thirteen_sq_dvd : 13 * 13 ∣ 12168 := ⟨72, by decide⟩

theorem prime_dvd_12167 {p : Nat} (hp : IsPrime p) (h : p ∣ 12167) : p = 23 := by
  have : p ∣ 23 ^ 3 := eq_12167 ▸ h
  have : p ∣ 23 := prime_dvd_pow hp this
  exact prime_dvd_prime hp prime_23 this

theorem prime_dvd_12168 {p : Nat} (hp : IsPrime p) (h : p ∣ 12168) :
    p = 2 ∨ p = 3 ∨ p = 13 := by
  have : p ∣ 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := eq_12168 ▸ h
  rcases prime_dvd_mul hp this with h23 | h13
  · rcases prime_dvd_mul hp h23 with h2 | h3
    · exact Or.inl (prime_dvd_prime hp prime_2 (prime_dvd_pow hp h2))
    · exact Or.inr (Or.inl (prime_dvd_prime hp prime_3 (prime_dvd_pow hp h3)))
  · exact Or.inr (Or.inr (prime_dvd_prime hp prime_13 (prime_dvd_pow hp h13)))

theorem powerful_12167 : Powerful 12167 := by
  refine ⟨by decide, ?_⟩
  intro p hp hd
  have := prime_dvd_12167 hp hd
  subst this
  exact twenty_three_sq_dvd

theorem powerful_12168 : Powerful 12168 := by
  refine ⟨by decide, ?_⟩
  intro p hp hd
  rcases prime_dvd_12168 hp hd with h | h | h
  · subst h; exact two_sq_dvd
  · subst h; exact three_sq_dvd
  · subst h; exact thirteen_sq_dvd

theorem not_square_of_between {n k : Nat}
    (hlo : k * k < n) (hhi : n < (k + 1) * (k + 1)) : ¬ IsSquare n := by
  rintro ⟨m, hm⟩
  have : m ≤ k ∨ k + 1 ≤ m := by omega
  cases this with
  | inl hmle =>
    have : m * m ≤ k * k := Nat.mul_le_mul hmle hmle
    omega
  | inr hmge =>
    have : (k + 1) * (k + 1) ≤ m * m := Nat.mul_le_mul hmge hmge
    omega

theorem not_square_12167 : ¬ IsSquare 12167 :=
  not_square_of_between (k := 110) (by decide) (by decide)

theorem not_square_12168 : ¬ IsSquare 12168 :=
  not_square_of_between (k := 110) (by decide) (by decide)

/-! ## Main theorems -/

/-- Explicit Golomb witness. -/
theorem golomb_pair :
    Powerful 12167 ∧ Powerful 12168 ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 ∧
      12168 = 12167 + 1 :=
  ⟨powerful_12167, powerful_12168, not_square_12167, not_square_12168, by decide⟩

/-- Existence form of the catalog disproof. -/
theorem jsp_000301 :
    ∃ n, Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) :=
  ⟨12167, powerful_12167, by
    simpa using powerful_12168, not_square_12167, by
    simpa using not_square_12168⟩

/-- Direct negation of the catalog yes/no question. -/
theorem question_false : ¬ Question := by
  intro h
  have := h 12167 powerful_12167 (by simpa using powerful_12168)
  rcases this with hsq | hsq
  · exact not_square_12167 hsq
  · exact not_square_12168 (by simpa using hsq)

end JSP000301
