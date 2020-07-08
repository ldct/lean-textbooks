-- Graham, Knuth, Patashnik
-- Concrete Mathematics

import tactic
import data.real.basic
import data.num.basic

lemma l1 (x y : ℝ) : 0 ≤ x^2-2*x*y + y^2 :=
begin
  have h1 : 0 ≤ (x - y)^2,
  exact pow_two_nonneg (x - y),
  ring SOP at h1,
  ring at h1,
  ring,
  exact h1,
end

example (a b : ℝ) : a ≤ b → 0 ≤ b - a :=
begin
  exact sub_nonneg.mpr,
end

-- CSI, two variable case
-- todo: use sqrt?
theorem csi_two_variable (a1 a2 b1 b2 : ℝ) : (a1*b1 + a2*b2)^2 ≤ (a1^2 + a2^2)*(b1^2 + b2^2) :=
begin
  have h1 := l1 (a1*b2) (a2*b1),
  rw ← sub_nonneg,
  ring SOP at h1,
  ring SOP at h1,
  ring SOP,
  ring SOP,
  ring SOP,
  exact h1,
end