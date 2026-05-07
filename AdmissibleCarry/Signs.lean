import Mathlib

/-!
# Three-valued signs

This file contains the finite sign type used to encode signed differences of
subset sums in the admissible-carry construction.
-/

namespace AdmissibleCarry

inductive Sign3 where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr

namespace Sign3

def sgn : Sign3 → Int
  | neg => -1
  | zero => 0
  | pos => 1

def opp : Sign3 → Sign3
  | neg => pos
  | zero => zero
  | pos => neg

def defect : Sign3 → Nat
  | neg => 2
  | zero => 1
  | pos => 0

@[simp] theorem sgn_neg : sgn neg = -1 := rfl
@[simp] theorem sgn_zero : sgn zero = 0 := rfl
@[simp] theorem sgn_pos : sgn pos = 1 := rfl
@[simp] theorem opp_neg : opp neg = pos := rfl
@[simp] theorem opp_zero : opp zero = zero := rfl
@[simp] theorem opp_pos : opp pos = neg := rfl
@[simp] theorem defect_neg : defect neg = 2 := rfl
@[simp] theorem defect_zero : defect zero = 1 := rfl
@[simp] theorem defect_pos : defect pos = 0 := rfl

@[simp] theorem opp_opp (s : Sign3) : opp (opp s) = s := by
  cases s <;> rfl

@[simp] theorem sgn_opp (s : Sign3) : sgn (opp s) = -sgn s := by
  cases s <;> norm_num [sgn, opp]

@[simp] theorem defect_eq_one_sub_sgn (s : Sign3) :
    (defect s : Int) = 1 - sgn s := by
  cases s <;> norm_num [defect, sgn]

end Sign3

end AdmissibleCarry
