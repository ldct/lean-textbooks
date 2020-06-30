-- Graham, Knuth, Patashnik
-- Concrete Mathematics

import tactic
import data.real.basic
import data.num.basic

-- Chapter 1
def T_hanoi : ℕ → ℤ
| nat.zero     := 0
| (nat.succ x) := (2* T_hanoi x) + 1

example : T_hanoi 10 = 2^10 - 1 :=
begin
  repeat { rw T_hanoi },
  comp_val
end

example (n : ℕ) : T_hanoi n = 2^n - 1 :=
begin
  induction n,
  comp_val,
  rw T_hanoi,
  rw n_ih,
  rw pow_succ,
  ring,
end

def L_steiner : ℕ → ℕ
| 0            := 0
| (x+1)        := (L_steiner x) + x + 1

example : L_steiner 1 = 1 :=
begin
  repeat { rw L_steiner },
end

-- I copied this proof from mathlib/big_operators.lean; however there it is stated using ∑ notation

lemma twice_steiner_closed (n : ℕ) : L_steiner n * 2 = n*(n+1) :=
begin
  induction n,
  norm_num,
  rw L_steiner,
  rw L_steiner,
  rw add_mul,
  rw add_mul,
  rw n_ih,
  rw nat.succ_eq_add_one,
  ring,
end

lemma steiner_closed (n : ℕ) : L_steiner n = n*(n+1) / 2 :=
begin
  rw ← twice_steiner_closed,
  have two_pos : 2 > 0,
  comp_val,
  rw @nat.mul_div_cancel (L_steiner n) 2 two_pos,
end

-- 1.3 The Josephus Problem
-- We take equation 1.8 as the definition of the function J:
--    J(2*n)   = 2*J(n) - 1
--    J(2*n+1) = 2*J(n) + 1
-- Actually, the real definition of J works on lists of naturals, e.g. to derive the even case of eqn 1.8 we say that J [1, 2, ... 2n] = J [1, 3, 5 ... 2n - 1]. 
-- It seems rather inconvenient to write a function ℕ → ℤ directly, so we use structural recursion on pos_num

def J_joseph₁ : pos_num → ℤ
| 1 := 1
| (pos_num.bit0 n) := 2*(J_joseph₁ n) - 1     -- J(2*n)   = 2*J(n) - 1
| (pos_num.bit1 n) := 2*(J_joseph₁ n) + 1     -- J(2*n+1) = 2*J(n) + 1

def J_joseph : ℕ → ℤ
| 0 := 0
| (n+1) := J_joseph₁ (n:num).succ'

lemma J_joseph_even (n : ℕ) (h : n ≥ 1) : J_joseph(2*n) = 2*J_joseph(n) - 1 :=
  sorry

-- todo: this needs n ≥ 1
lemma J_joseph_odd (n : ℕ) : J_joseph(2*n + 1) = 2*J_joseph(n) + 1 :=
  sorry

example : J_joseph 100 = 73 :=
begin
  comp_val,
end

-- lemma statement by Kevin Buzzard

def is_even (n : ℕ) := ∃ a, n = 2 * a

def is_odd (n : ℕ) := ∃ b, n = 2 * b + 1

lemma even_or_odd (n : ℕ) : is_even(n) ∨ is_odd(n) :=
begin
  induction n,
  left,
  use 0,
  linarith,
  cases n_ih,
  right,
  cases n_ih with a h_a,
  use a,
  rw nat.succ_eq_add_one,
  rw h_a,
  cases n_ih with a h_a,
  left,
  use a+1,
  rw nat.succ_eq_add_one,
  rw h_a,
  ring,
end

lemma pow_pos2 ( m: ℕ ) : 2^m ≥ 1 :=
begin
  induction m,
  rw nat.pow_zero,
  linarith,
  rw nat.pow_succ,
  linarith,
end

-- Closed form of J for perfect powers of 2
theorem J_pow_2 (m : ℕ) : J_joseph(2 ^ m) = 1 :=
begin
  induction m,
  rw nat.pow_zero,
  comp_val,
  rw nat.pow_succ,
  rw nat.mul_comm,
  rw J_joseph_even,
  rw m_ih,
  comp_val,
  -- 2 ^ m_n > 1
  exact pow_pos2 m_n,
end

lemma bdd (m : ℕ) : (m < 1) → m = 0 :=
begin
  exact nat.sub_eq_zero_of_le,
end

-- Kevin Buzzard
lemma lt_mul_cancel (n m k : ℕ) : (k*m + 1 < k*n) → (m < n) :=
begin
  intro h,
  refine lt_of_mul_lt_mul_left _ (show 0 ≤ k, by linarith),
  refine lt_trans _ h,
  omega,
end

-- eqn 1.9
-- If we imagine J to be defined as a function of two variables m and l, with l < 2^m, and draw the DP table for calculating J via the recurrence (each row representing m fixed and l varying), we treat each cell as depending on the entire previous row
-- There is a slick proof in the margin that probably requires us to work with J defined on lists in order to relate J(m, l) and J(m, l+1). Once related we can prove it using induction on l and J_pow_2.
lemma J_closed (m l : ℕ) : (l < 2^m) → J_joseph(2^m + l) = 2*l + 1 :=
begin
  induction m generalizing l, -- draw the DP table!
  intro h,
  simp at h,
  have h2 := bdd l h,
  rw h2,
  comp_val,
  -- inductive step
  rw nat.pow_succ,
  have key := even_or_odd l,
  cases key,
  -- l even
  cases key with w h_w,
  rw h_w,
  intro h,
  rw mul_comm,
  rw ← nat.left_distrib,
  rw J_joseph_even,
  ring at h,
  have two_pos : 0 < 2,
  comp_val,
  have h := (mul_lt_mul_left two_pos).mp h,
  specialize m_ih w,
  rw m_ih h,
  rw int.distrib_left, -- why isn't this called left_distrib?
  rw int.coe_nat_mul,
  ring,
  have h2 := pow_pos2 m_n,
  linarith,
  -- l odd
  cases key with w h_w,
  rw h_w,
  intro h,
  rw mul_comm,
  rw ← add_assoc _ _ 1,
  rw ← nat.left_distrib,
  rw J_joseph_odd,
  rw mul_comm _ 2 at h,
  have h := lt_mul_cancel (2 ^ m_n) w 2 h,
  specialize m_ih w,
  rw m_ih h,
  ring,
  rw int.coe_nat_add,
  rw int.coe_nat_mul,
  ring,
end

-- alternative closed form using mathlib functions, by Mario Carneiro
def J_joseph₂ (n : ℕ) : ℤ := (2 * n + 1) - (2 ^ nat.size n : ℕ)

-- knuth generalizes J here and considers iterating it until it reaches its fixpoint. This involves considering it as acting on binary digits.

-- Chapter 5

#reduce nat.choose 5 2

-- 5.3 is equivalent to choose_symm from mathlib

-- 5.4



-- Chapter 6

-- From TPIL

def fib : ℕ → ℤ 
| 0     := 0
| 1     := 1
| (n+2) := fib (n+1) + fib n

lemma helper (n : ℕ) : (-1:ℤ)^(n+2) = (-1) * (-1)^(n+1) :=
begin
  exact rfl,
end

theorem cassini (n : ℕ) : (n > 0) → (fib (n+1)) * (fib (n-1)) - (fib (n)) ^ 2 = (-1)^n :=
begin
  cases n,
  intro h,
  linarith,
  -- now n is replaced by nat.succ n
  induction n,
  -- the base case has actual content now
  intro h,
  simp,
  rw fib,
  rw fib,
  rw fib,
  norm_num,
  -- inductive case
  intro h,
  have p : nat.succ n_n > 0,
  exact nat.succ_pos n_n,
  have n_ih := n_ih p,
  rw nat.succ_eq_add_one at n_ih,
  rw nat.succ_eq_add_one,
  rw nat.succ_eq_add_one,
  simp,
  simp at n_ih,
  -- we express everything in terms of F_n and F_{n+1}
  have h2 : fib (n_n+2) = fib (n_n+1) + fib n_n,
  rw fib,
  have h3 : fib (n_n+3) = fib (n_n+2) + fib (n_n + 1),
  rw fib,
  rw h3,
  rw h2,
  rw h2 at n_ih,
  ring,
  have helper := helper n_n,
  rw helper,
  ring,
  rw ← n_ih,
  ring,
end

theorem k_future (n k : ℕ) : (k > 0) → fib (n+k) = (fib k)*(fib (n+1)) + (fib (k-1))*(fib n) :=
begin
  cases k,
  intro h,
  linarith,
  intro h,
  induction k generalizing n,
  rw fib,
  simp,
  rw fib,
  simp,
  -- inductive
  have p : nat.succ k_n > 0,
  exact nat.succ_pos k_n,
  have k_ih := k_ih p,
  rw nat.succ_eq_add_one at k_ih,
  repeat { rw nat.succ_eq_add_one },
  simp,
  simp at k_ih,
  rw ← add_assoc,
  specialize k_ih (n+1),
  ring at k_ih,
  rw ← add_assoc at k_ih,
  rw k_ih,
  simp,
  rw fib,
  rw nat.succ_eq_add_one,
  rw fib,
  rw nat.succ_eq_add_one,
  ring,  
end

lemma dichotomy (a : ℕ) : a > 0 ∨ a = 0 :=
begin
  have h := nat.eq_zero_or_pos a,
  exact or.swap h,
end

-- 6.110
theorem f_div ( n k : ℕ) : fib n ∣ fib (k*n) :=
begin 
  induction k,
  simp,
  rw fib,
  exact dvd_zero (fib n),

  have key := dichotomy (n*k_n),
  cases key,

  -- case 1
  have h := k_future n (k_n*n) _,
  rw nat.succ_eq_add_one,
  ring,
  rw add_comm,
  rw mul_comm,
  rw h,
  cases k_ih,
  rw k_ih_h,
  use (k_ih_w * fib (n + 1)) + fib (k_n * n - 1),
  ring,
  rw mul_comm,
  
  -- case 2
  exact key,
  rw nat.succ_eq_add_one,
  ring,
  rw key,
  simp,
end

-- exercise 27
example (m n : ℕ) : int.gcd (fib m) (fib n) = nat.gcd m n := 
begin
  sorry
end

-- todo: converse of f_div

-- matijasevich's lemma
example (m n : ℕ) (h : n > 2): (fib n)^2 ∣ fib m ↔ (n:ℤ)*(fib n) ∣ (m:ℤ) := sorry

-- todo: Zeckendorf's theorem states that every positive integer can be represented uniquely as the sum of one or more distinct Fibonacci numbers in such a way that the sum does not include any two consecutive Fibonacci numbers.
-- looks hard