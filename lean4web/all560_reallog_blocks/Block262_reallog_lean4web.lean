/-
Self-contained Lean4Web paste file.
Block 262 real-log V_i(y) > 0 check for the M=1.817475 candidate.

This file includes the rational kernel, the generated block data,
and the Mathlib Real.log bridge.  The final #check lines expose
the block-level theorem whose type contains `0 < block...V y`.

This is still only a block-level reduced-certificate check: it
does not formalize the outer reduction from the original #1038
problem, and the theorem excludes the singular atom locations.
-/

import Mathlib


/-!
# Rational box kernel for #1038 finite-atom checks

This file is deliberately Mathlib-free.  It does not prove the analytic
`Real.log` bridge.  It proves the finite arithmetic part that should later be
connected to `Real.log` by a Mathlib file, following the Hua Xu certificate
architecture.
-/

namespace Erdos1038Lean

def ratAbs (x : Rat) : Rat :=
  if x < 0 then -x else x

def atanhLowerRat : Nat -> Rat -> Rat
  | 0, _ => 0
  | n + 1, t => atanhLowerRat n t + 2 * t ^ (2 * n + 1) / (2 * n + 1)

def atanhUpperRat (n : Nat) (t : Rat) : Rat :=
  atanhLowerRat n t + 2 * t ^ (2 * n + 1) / (1 - t ^ 2)

def tInv (d : Rat) : Rat := (1 - d) / (1 + d)

def tSelf (d : Rat) : Rat := (d - 1) / (d + 1)

def logInvLowerRat (nPos nNeg : Nat) (d : Rat) : Rat :=
  if d < 1 then
    atanhLowerRat nPos (tInv d)
  else
    -atanhUpperRat nNeg (tSelf d)

structure RatBox where
  w1 : Rat
  w2 : Rat
  w3 : Rat
  w4 : Rat
  s1 : Rat
  s2 : Rat
  s3 : Rat
  s4 : Rat
  L : Rat
  R : Rat
  D0 : Rat
  D1 : Rat
  D2 : Rat
  D3 : Rat
  D4 : Rat
  LB : Rat
  deriving DecidableEq, Repr

def RatBox.computedLower (b : RatBox) (nPos nNeg : Nat := 150) : Rat :=
  logInvLowerRat nPos nNeg b.D0
  + b.w1 * logInvLowerRat nPos nNeg b.D1
  + b.w2 * logInvLowerRat nPos nNeg b.D2
  + b.w3 * logInvLowerRat nPos nNeg b.D3
  + b.w4 * logInvLowerRat nPos nNeg b.D4

def RatBox.validFastBool (b : RatBox) : Bool :=
  decide (
    0 <= b.w1 /\ 0 <= b.w2 /\ 0 <= b.w3 /\ 0 <= b.w4 /\
    b.L <= b.R /\
    0 < b.D0 /\ 0 < b.D1 /\ 0 < b.D2 /\ 0 < b.D3 /\ 0 < b.D4 /\
    0 < b.LB /\
    ratAbs (b.L - 0) <= b.D0 /\ ratAbs (b.R - 0) <= b.D0 /\
    ratAbs (b.L - b.s1) <= b.D1 /\ ratAbs (b.R - b.s1) <= b.D1 /\
    ratAbs (b.L - b.s2) <= b.D2 /\ ratAbs (b.R - b.s2) <= b.D2 /\
    ratAbs (b.L - b.s3) <= b.D3 /\ ratAbs (b.R - b.s3) <= b.D3 /\
    ratAbs (b.L - b.s4) <= b.D4 /\ ratAbs (b.R - b.s4) <= b.D4)

def RatBox.validComputedBool (b : RatBox) (nPos nNeg : Nat := 150) : Bool :=
  b.validFastBool && decide (b.LB = b.computedLower nPos nNeg)

def RatBox.validComputedPositiveBool (b : RatBox) (nPos nNeg : Nat := 150) : Bool :=
  b.validFastBool && decide (0 < b.computedLower nPos nNeg)

def allBoxesFastValid (boxes : List RatBox) : Bool :=
  boxes.all (fun b => b.validFastBool)

def allBoxesComputedValid (boxes : List RatBox) (nPos nNeg : Nat := 150) : Bool :=
  boxes.all (fun b => b.validComputedBool nPos nNeg)

def allBoxesComputedPositiveValid (boxes : List RatBox) (nPos nNeg : Nat := 150) : Bool :=
  boxes.all (fun b => b.validComputedPositiveBool nPos nNeg)

def allBoxesValid (boxes : List RatBox) : Bool :=
  allBoxesComputedPositiveValid boxes 150 150

def coversFromBool : List RatBox -> Rat -> Rat -> Bool
  | [], _lo, _hi => false
  | [b], lo, hi => decide (b.L <= lo /\ hi <= b.R)
  | b :: b' :: bs, lo, hi =>
      decide (b.L <= lo /\ lo <= b.R) && coversFromBool (b' :: bs) b.R hi

def boxCount (xs : List RatBox) : Nat := xs.length

def worstLower? (boxes : List RatBox) : Option Rat :=
  match boxes.map (fun b => b.LB) with
  | [] => none
  | x :: xs => some (xs.foldl min x)

end Erdos1038Lean


/-!
# Real-log bridge for rational boxes

This file starts the Mathlib layer connecting the exact rational box checks to
actual logarithmic potentials over `ℝ`.

The pure certificate files check each `RatBox` by exact rational arithmetic.
Here we prove the reusable analytic bridge for one rational box: if Lean has
checked a positive computed rational lower bound, then the corresponding
five-term real logarithmic potential is positive on the box, away from the
singular atom locations.
-/

namespace Erdos1038Lean

noncomputable section

open Finset Set

lemma bool_left_of_and_eq_true {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

lemma bool_right_of_and_eq_true {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

def atanhLowerReal (n : Nat) (t : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * (i : ℝ) + 1))

def atanhUpperReal (n : Nat) (t : ℝ) : ℝ :=
  atanhLowerReal n t + 2 * t ^ (2 * n + 1) / (1 - t ^ 2)

lemma atanhLowerRat_cast (n : Nat) (t : Rat) :
    ((atanhLowerRat n t : Rat) : ℝ) = atanhLowerReal n (t : ℝ) := by
  induction n with
  | zero =>
      simp [atanhLowerRat, atanhLowerReal]
  | succ n ih =>
      rw [atanhLowerRat]
      simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
      rw [ih]
      simp [atanhLowerReal, Finset.sum_range_succ]
      ring

lemma atanhUpperRat_cast (n : Nat) (t : Rat) :
    ((atanhUpperRat n t : Rat) : ℝ) = atanhUpperReal n (t : ℝ) := by
  simp [atanhUpperRat, atanhUpperReal, atanhLowerRat_cast]

lemma atanhLowerRat_le_log_of_mobius
    (r t : Rat) (n : Nat)
    (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hr : (r : ℝ) = (1 + (t : ℝ)) / (1 - (t : ℝ))) :
    ((atanhLowerRat n t : Rat) : ℝ) ≤ Real.log (r : ℝ) := by
  have h := Real.sum_range_le_log_div ht0 ht1 n
  rw [atanhLowerRat_cast]
  unfold atanhLowerReal
  rw [hr]
  nlinarith

lemma log_le_atanhUpperRat_of_mobius
    (r t : Rat) (n : Nat)
    (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hr : (r : ℝ) = (1 + (t : ℝ)) / (1 - (t : ℝ))) :
    Real.log (r : ℝ) ≤ ((atanhUpperRat n t : Rat) : ℝ) := by
  have h := Real.log_div_le_sum_range_add ht0 ht1 n
  rw [atanhUpperRat_cast]
  unfold atanhUpperReal atanhLowerReal
  rw [hr]
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.log ((1 + (t : ℝ)) / (1 - (t : ℝ)))
        = 2 * (1 / 2 * Real.log ((1 + (t : ℝ)) / (1 - (t : ℝ)))) := by ring
    _ ≤ 2 * (∑ i ∈ Finset.range n,
          (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)
        + (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2)) := h2
    _ = 2 * ∑ i ∈ Finset.range n,
          (t : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)
        + 2 * (t : ℝ) ^ (2 * n + 1) / (1 - (t : ℝ) ^ 2) := by ring

lemma tInv_cast_eq (d : Rat) :
    (tInv d : ℝ) = (1 - (d : ℝ)) / (1 + (d : ℝ)) := by
  unfold tInv
  norm_num

lemma tSelf_cast_eq (d : Rat) :
    (tSelf d : ℝ) = ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
  unfold tSelf
  norm_num

lemma logInvLowerRat_le_log_inv (nPos nNeg : Nat) (d : Rat) (hd : 0 < d) :
    ((logInvLowerRat nPos nNeg d : Rat) : ℝ) ≤ Real.log ((d : ℝ)⁻¹) := by
  by_cases hlt : d < 1
  · simp [logInvLowerRat, hlt]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hltR : (d : ℝ) < 1 := by exact_mod_cast hlt
    have htEq := tInv_cast_eq d
    have hden : 0 < 1 + (d : ℝ) := by positivity
    have ht0 : 0 ≤ (tInv d : ℝ) := by
      rw [htEq]
      exact div_nonneg (sub_nonneg.mpr hltR.le) hden.le
    have ht1 : (tInv d : ℝ) < 1 := by
      rw [htEq]
      field_simp [hden.ne']
      linarith
    have hr : ((1 / d : Rat) : ℝ) =
        (1 + (tInv d : ℝ)) / (1 - (tInv d : ℝ)) := by
      rw [htEq]
      norm_num
      field_simp [show (d : ℝ) ≠ 0 by positivity, hden.ne']
      ring
    simpa using atanhLowerRat_le_log_of_mobius (1 / d) (tInv d) nPos ht0 ht1 hr
  · simp [logInvLowerRat, hlt]
    have hge : (1 : Rat) ≤ d := le_of_not_gt hlt
    have hgeR : (1 : ℝ) ≤ d := by exact_mod_cast hge
    have htEq := tSelf_cast_eq d
    have hden : 0 < (d : ℝ) + 1 := by positivity
    have ht0 : 0 ≤ (tSelf d : ℝ) := by
      rw [htEq]
      exact div_nonneg (sub_nonneg.mpr hgeR) hden.le
    have ht1 : (tSelf d : ℝ) < 1 := by
      rw [htEq]
      field_simp [hden.ne']
      linarith
    have hr : (d : ℝ) =
        (1 + (tSelf d : ℝ)) / (1 - (tSelf d : ℝ)) := by
      rw [htEq]
      field_simp [hden.ne']
      ring
    exact log_le_atanhUpperRat_of_mobius d (tSelf d) nNeg ht0 ht1 hr

lemma logInvLowerRat_le_log_actual_inv
    (nPos nNeg : Nat) (d : Rat) {actual : ℝ}
    (hd : 0 < d) (hactual : 0 < actual) (hle : actual ≤ (d : ℝ)) :
    ((logInvLowerRat nPos nNeg d : Rat) : ℝ) ≤ Real.log actual⁻¹ := by
  have hbase := logInvLowerRat_le_log_inv nPos nNeg d hd
  have hdinv : ((d : ℝ)⁻¹) ≤ actual⁻¹ := by
    exact (inv_le_inv₀ (by exact_mod_cast hd : (0 : ℝ) < d) hactual).2 hle
  exact hbase.trans (Real.log_le_log (inv_pos.mpr (by exact_mod_cast hd)) hdinv)

lemma ratAbs_cast (x : Rat) :
    ((ratAbs x : Rat) : ℝ) = |(x : ℝ)| := by
  unfold ratAbs
  by_cases hx : x < 0
  · simp [hx]
    have hxR : (x : ℝ) < 0 := by exact_mod_cast hx
    rw [abs_of_neg hxR]
  · simp [hx]
    have hxR : 0 ≤ (x : ℝ) := by exact_mod_cast le_of_not_gt hx
    rw [abs_of_nonneg hxR]

lemma real_abs_bound_of_ratAbs {x D : Rat}
    (h : ratAbs x ≤ D) :
    |(x : ℝ)| ≤ (D : ℝ) := by
  have hc : ((ratAbs x : Rat) : ℝ) ≤ (D : ℝ) := by exact_mod_cast h
  simpa [ratAbs_cast] using hc

lemma abs_sub_le_of_box_endpoints
    {L R p D y : ℝ}
    (hy : y ∈ Icc L R)
    (hL : |L - p| ≤ D)
    (hR : |R - p| ≤ D) :
    |y - p| ≤ D := by
  rw [abs_sub_le_iff] at hL hR ⊢
  constructor <;> linarith [hy.1, hy.2, hL.1, hL.2, hR.1, hR.2]

def RatBox.realPotential (b : RatBox) (y : ℝ) : ℝ :=
    Real.log (|y|)⁻¹
  + (b.w1 : ℝ) * Real.log (|y - (b.s1 : ℝ)|)⁻¹
  + (b.w2 : ℝ) * Real.log (|y - (b.s2 : ℝ)|)⁻¹
  + (b.w3 : ℝ) * Real.log (|y - (b.s3 : ℝ)|)⁻¹
  + (b.w4 : ℝ) * Real.log (|y - (b.s4 : ℝ)|)⁻¹

def ratPotential
    (w1 w2 w3 w4 s1 s2 s3 s4 : Rat) (y : ℝ) : ℝ :=
    Real.log (|y|)⁻¹
  + (w1 : ℝ) * Real.log (|y - (s1 : ℝ)|)⁻¹
  + (w2 : ℝ) * Real.log (|y - (s2 : ℝ)|)⁻¹
  + (w3 : ℝ) * Real.log (|y - (s3 : ℝ)|)⁻¹
  + (w4 : ℝ) * Real.log (|y - (s4 : ℝ)|)⁻¹

def RatBox.sameParamsBool
    (b : RatBox) (w1 w2 w3 w4 s1 s2 s3 s4 : Rat) : Bool :=
  decide (
    b.w1 = w1 /\ b.w2 = w2 /\ b.w3 = w3 /\ b.w4 = w4 /\
    b.s1 = s1 /\ b.s2 = s2 /\ b.s3 = s3 /\ b.s4 = s4)

def allBoxesSameParams
    (boxes : List RatBox) (w1 w2 w3 w4 s1 s2 s3 s4 : Rat) : Bool :=
  boxes.all (fun b => b.sameParamsBool w1 w2 w3 w4 s1 s2 s3 s4)

lemma RatBox.sameParamsBool_eq_true_iff
    (b : RatBox) (w1 w2 w3 w4 s1 s2 s3 s4 : Rat) :
    b.sameParamsBool w1 w2 w3 w4 s1 s2 s3 s4 = true ↔
      b.w1 = w1 /\ b.w2 = w2 /\ b.w3 = w3 /\ b.w4 = w4 /\
      b.s1 = s1 /\ b.s2 = s2 /\ b.s3 = s3 /\ b.s4 = s4 := by
  unfold RatBox.sameParamsBool
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

lemma RatBox.realPotential_eq_ratPotential_of_sameParams
    {b : RatBox} {w1 w2 w3 w4 s1 s2 s3 s4 : Rat}
    (h : b.sameParamsBool w1 w2 w3 w4 s1 s2 s3 s4 = true) :
    b.realPotential = ratPotential w1 w2 w3 w4 s1 s2 s3 s4 := by
  rcases (b.sameParamsBool_eq_true_iff w1 w2 w3 w4 s1 s2 s3 s4).mp h with
    ⟨hw1, hw2, hw3, hw4, hs1, hs2, hs3, hs4⟩
  funext y
  simp [RatBox.realPotential, ratPotential, hw1, hw2, hw3, hw4, hs1, hs2, hs3, hs4]

lemma sameParamsBool_of_mem_allBoxesSameParams
    {boxes : List RatBox} {b : RatBox} {w1 w2 w3 w4 s1 s2 s3 s4 : Rat}
    (hparams : allBoxesSameParams boxes w1 w2 w3 w4 s1 s2 s3 s4 = true)
    (hb : b ∈ boxes) :
    b.sameParamsBool w1 w2 w3 w4 s1 s2 s3 s4 = true := by
  unfold allBoxesSameParams at hparams
  exact List.all_eq_true.mp hparams b hb

lemma RatBox.computedLower_le_realPotential
    (b : RatBox) (nPos nNeg : Nat) {y : ℝ}
    (hw1 : 0 ≤ (b.w1 : ℝ))
    (hw2 : 0 ≤ (b.w2 : ℝ))
    (hw3 : 0 ≤ (b.w3 : ℝ))
    (hw4 : 0 ≤ (b.w4 : ℝ))
    (hD0 : 0 < b.D0) (hD1 : 0 < b.D1) (hD2 : 0 < b.D2)
    (hD3 : 0 < b.D3) (hD4 : 0 < b.D4)
    (hy0 : 0 < |y|)
    (hy1 : 0 < |y - (b.s1 : ℝ)|)
    (hy2 : 0 < |y - (b.s2 : ℝ)|)
    (hy3 : 0 < |y - (b.s3 : ℝ)|)
    (hy4 : 0 < |y - (b.s4 : ℝ)|)
    (hb0 : |y| ≤ (b.D0 : ℝ))
    (hb1 : |y - (b.s1 : ℝ)| ≤ (b.D1 : ℝ))
    (hb2 : |y - (b.s2 : ℝ)| ≤ (b.D2 : ℝ))
    (hb3 : |y - (b.s3 : ℝ)| ≤ (b.D3 : ℝ))
    (hb4 : |y - (b.s4 : ℝ)| ≤ (b.D4 : ℝ)) :
    ((b.computedLower nPos nNeg : Rat) : ℝ) ≤ b.realPotential y := by
  have h0 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D0 hD0 hy0 hb0
  have h1 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D1 hD1 hy1 hb1
  have h2 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D2 hD2 hy2 hb2
  have h3 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D3 hD3 hy3 hb3
  have h4 := logInvLowerRat_le_log_actual_inv nPos nNeg b.D4 hD4 hy4 hb4
  have h1w :
      (b.w1 : ℝ) * ((logInvLowerRat nPos nNeg b.D1 : Rat) : ℝ)
        ≤ (b.w1 : ℝ) * Real.log (|y - (b.s1 : ℝ)|)⁻¹ :=
    mul_le_mul_of_nonneg_left h1 hw1
  have h2w :
      (b.w2 : ℝ) * ((logInvLowerRat nPos nNeg b.D2 : Rat) : ℝ)
        ≤ (b.w2 : ℝ) * Real.log (|y - (b.s2 : ℝ)|)⁻¹ :=
    mul_le_mul_of_nonneg_left h2 hw2
  have h3w :
      (b.w3 : ℝ) * ((logInvLowerRat nPos nNeg b.D3 : Rat) : ℝ)
        ≤ (b.w3 : ℝ) * Real.log (|y - (b.s3 : ℝ)|)⁻¹ :=
    mul_le_mul_of_nonneg_left h3 hw3
  have h4w :
      (b.w4 : ℝ) * ((logInvLowerRat nPos nNeg b.D4 : Rat) : ℝ)
        ≤ (b.w4 : ℝ) * Real.log (|y - (b.s4 : ℝ)|)⁻¹ :=
    mul_le_mul_of_nonneg_left h4 hw4
  calc
    ((b.computedLower nPos nNeg : Rat) : ℝ)
        = ((logInvLowerRat nPos nNeg b.D0 : Rat) : ℝ)
          + (b.w1 : ℝ) * ((logInvLowerRat nPos nNeg b.D1 : Rat) : ℝ)
          + (b.w2 : ℝ) * ((logInvLowerRat nPos nNeg b.D2 : Rat) : ℝ)
          + (b.w3 : ℝ) * ((logInvLowerRat nPos nNeg b.D3 : Rat) : ℝ)
          + (b.w4 : ℝ) * ((logInvLowerRat nPos nNeg b.D4 : Rat) : ℝ) := by
            simp [RatBox.computedLower]
    _ ≤ Real.log (|y|)⁻¹
          + (b.w1 : ℝ) * Real.log (|y - (b.s1 : ℝ)|)⁻¹
          + (b.w2 : ℝ) * Real.log (|y - (b.s2 : ℝ)|)⁻¹
          + (b.w3 : ℝ) * Real.log (|y - (b.s3 : ℝ)|)⁻¹
          + (b.w4 : ℝ) * Real.log (|y - (b.s4 : ℝ)|)⁻¹ := by
            nlinarith
    _ = b.realPotential y := by
            simp [RatBox.realPotential]

lemma RatBox.validFastBool_eq_true_iff (b : RatBox) :
    b.validFastBool = true ↔
      0 ≤ b.w1 ∧ 0 ≤ b.w2 ∧ 0 ≤ b.w3 ∧ 0 ≤ b.w4 ∧
      b.L ≤ b.R ∧
      0 < b.D0 ∧ 0 < b.D1 ∧ 0 < b.D2 ∧ 0 < b.D3 ∧ 0 < b.D4 ∧
      0 < b.LB ∧
      ratAbs (b.L - 0) ≤ b.D0 ∧ ratAbs (b.R - 0) ≤ b.D0 ∧
      ratAbs (b.L - b.s1) ≤ b.D1 ∧ ratAbs (b.R - b.s1) ≤ b.D1 ∧
      ratAbs (b.L - b.s2) ≤ b.D2 ∧ ratAbs (b.R - b.s2) ≤ b.D2 ∧
      ratAbs (b.L - b.s3) ≤ b.D3 ∧ ratAbs (b.R - b.s3) ≤ b.D3 ∧
      ratAbs (b.L - b.s4) ≤ b.D4 ∧ ratAbs (b.R - b.s4) ≤ b.D4 := by
  unfold RatBox.validFastBool
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

lemma RatBox.validComputedPositiveBool_eq_true_iff
    (b : RatBox) (nPos nNeg : Nat) :
    b.validComputedPositiveBool nPos nNeg = true ↔
      b.validFastBool = true ∧ 0 < b.computedLower nPos nNeg := by
  unfold RatBox.validComputedPositiveBool
  constructor
  · intro h
    by_cases hfast : b.validFastBool = true
    · constructor
      · exact hfast
      · rw [hfast] at h
        simp at h
        exact h
    · have hfastFalse : b.validFastBool = false := by
        cases hb : b.validFastBool <;> simp_all
      rw [hfastFalse] at h
      simp at h
  · intro h
    rw [h.1]
    simp [decide_eq_true h.2]

lemma validComputedPositiveBool_of_mem_allBoxesValid
    {boxes : List RatBox} {b : RatBox}
    (hboxes : allBoxesValid boxes = true)
    (hb : b ∈ boxes) :
    b.validComputedPositiveBool 150 150 = true := by
  unfold allBoxesValid allBoxesComputedPositiveValid at hboxes
  exact List.all_eq_true.mp hboxes b hb

lemma exists_mem_box_of_coversFromBool
    {boxes : List RatBox} {lo hi : Rat}
    (hcovers : coversFromBool boxes lo hi = true)
    {y : ℝ} (hy : y ∈ Icc (lo : ℝ) (hi : ℝ)) :
    ∃ b ∈ boxes, y ∈ Icc (b.L : ℝ) (b.R : ℝ) := by
  induction boxes generalizing lo with
  | nil =>
      simp [coversFromBool] at hcovers
  | cons b bs ih =>
      cases bs with
      | nil =>
          have hprop : b.L ≤ lo ∧ hi ≤ b.R := by
            have hdec : decide (b.L ≤ lo ∧ hi ≤ b.R) = true := by
              simpa [coversFromBool] using hcovers
            exact of_decide_eq_true hdec
          rcases hprop with ⟨hbL, hhiR⟩
          refine ⟨b, by simp, ?_⟩
          constructor
          · have hbLR : (b.L : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hbL
            linarith [hbLR, hy.1]
          · have hhiRR : (hi : ℝ) ≤ (b.R : ℝ) := by exact_mod_cast hhiR
            linarith [hhiRR, hy.2]
      | cons b' bs =>
          have hbool :
              decide (b.L ≤ lo ∧ lo ≤ b.R) &&
                  coversFromBool (b' :: bs) b.R hi = true := by
            simpa [coversFromBool] using hcovers
          have hheadBool : decide (b.L ≤ lo ∧ lo ≤ b.R) = true := by
            cases h : decide (b.L ≤ lo ∧ lo ≤ b.R) <;> simp [h] at hbool ⊢
          have hrest : coversFromBool (b' :: bs) b.R hi = true := by
            cases h : decide (b.L ≤ lo ∧ lo ≤ b.R) <;> simp [h] at hbool
            exact hbool
          have hhead : b.L ≤ lo ∧ lo ≤ b.R := of_decide_eq_true hheadBool
          rcases hhead with ⟨hbL, _hloR⟩
          by_cases hyR : y ≤ (b.R : ℝ)
          · refine ⟨b, by simp, ?_⟩
            constructor
            · have hbLR : (b.L : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hbL
              linarith [hbLR, hy.1]
            · exact hyR
          · have hbRy : (b.R : ℝ) ≤ y := le_of_lt (lt_of_not_ge hyR)
            have hy' : y ∈ Icc (b.R : ℝ) (hi : ℝ) := ⟨hbRy, hy.2⟩
            rcases ih hrest hy' with ⟨b'', hb''mem, hby⟩
            exact ⟨b'', by simp [hb''mem], hby⟩

theorem RatBox.realPotential_pos_of_validComputedPositive
    {b : RatBox} {nPos nNeg : Nat} {y : ℝ}
    (hvalid : b.validComputedPositiveBool nPos nNeg = true)
    (hy : y ∈ Icc (b.L : ℝ) (b.R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (b.s1 : ℝ))
    (hy2ne : y ≠ (b.s2 : ℝ))
    (hy3ne : y ≠ (b.s3 : ℝ))
    (hy4ne : y ≠ (b.s4 : ℝ)) :
    0 < b.realPotential y := by
  rcases (RatBox.validComputedPositiveBool_eq_true_iff b nPos nNeg).mp hvalid with
    ⟨hfast, hcomp⟩
  rcases (RatBox.validFastBool_eq_true_iff b).mp hfast with
    ⟨hw1, hw2, hw3, hw4, _hLR,
      hD0, hD1, hD2, hD3, hD4, _hLB,
      hL0, hR0, hL1, hR1, hL2, hR2, hL3, hR3, hL4, hR4⟩
  have hb0 : |y| ≤ (b.D0 : ℝ) := by
    simpa using abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := 0) (D := (b.D0 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL0)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR0)
  have hb1 : |y - (b.s1 : ℝ)| ≤ (b.D1 : ℝ) :=
    abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := (b.s1 : ℝ)) (D := (b.D1 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL1)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR1)
  have hb2 : |y - (b.s2 : ℝ)| ≤ (b.D2 : ℝ) :=
    abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := (b.s2 : ℝ)) (D := (b.D2 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL2)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR2)
  have hb3 : |y - (b.s3 : ℝ)| ≤ (b.D3 : ℝ) :=
    abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := (b.s3 : ℝ)) (D := (b.D3 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL3)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR3)
  have hb4 : |y - (b.s4 : ℝ)| ≤ (b.D4 : ℝ) :=
    abs_sub_le_of_box_endpoints
      (L := (b.L : ℝ)) (R := (b.R : ℝ)) (p := (b.s4 : ℝ)) (D := (b.D4 : ℝ)) hy
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hL4)
      (by simpa [Rat.cast_sub] using real_abs_bound_of_ratAbs hR4)
  have hle := b.computedLower_le_realPotential nPos nNeg
    (by exact_mod_cast hw1) (by exact_mod_cast hw2)
    (by exact_mod_cast hw3) (by exact_mod_cast hw4)
    hD0 hD1 hD2 hD3 hD4
    (abs_pos.mpr hy0ne)
    (abs_pos.mpr (sub_ne_zero.mpr hy1ne))
    (abs_pos.mpr (sub_ne_zero.mpr hy2ne))
    (abs_pos.mpr (sub_ne_zero.mpr hy3ne))
    (abs_pos.mpr (sub_ne_zero.mpr hy4ne))
    hb0 hb1 hb2 hb3 hb4
  have hcompR : (0 : ℝ) < ((b.computedLower nPos nNeg : Rat) : ℝ) := by
    exact_mod_cast hcomp
  exact hcompR.trans_le hle

theorem RatBox.realPotential_pos_of_mem_allBoxesValid
    {boxes : List RatBox} {b : RatBox} {y : ℝ}
    (hboxes : allBoxesValid boxes = true)
    (hb : b ∈ boxes)
    (hy : y ∈ Icc (b.L : ℝ) (b.R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (b.s1 : ℝ))
    (hy2ne : y ≠ (b.s2 : ℝ))
    (hy3ne : y ≠ (b.s3 : ℝ))
    (hy4ne : y ≠ (b.s4 : ℝ)) :
    0 < b.realPotential y := by
  exact RatBox.realPotential_pos_of_validComputedPositive
    (validComputedPositiveBool_of_mem_allBoxesValid hboxes hb)
    hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem exists_box_realPotential_pos_of_allBoxesValid_and_covers
    {boxes : List RatBox} {lo hi : Rat} {y : ℝ}
    (hboxes : allBoxesValid boxes = true)
    (hcovers : coversFromBool boxes lo hi = true)
    (hy : y ∈ Icc (lo : ℝ) (hi : ℝ)) :
    ∃ b ∈ boxes, y ∈ Icc (b.L : ℝ) (b.R : ℝ) ∧
      (y ≠ 0 →
       y ≠ (b.s1 : ℝ) →
       y ≠ (b.s2 : ℝ) →
       y ≠ (b.s3 : ℝ) →
       y ≠ (b.s4 : ℝ) →
       0 < b.realPotential y) := by
  rcases exists_mem_box_of_coversFromBool hcovers hy with ⟨b, hb, hby⟩
  refine ⟨b, hb, hby, ?_⟩
  intro hy0 hy1 hy2 hy3 hy4
  exact b.realPotential_pos_of_mem_allBoxesValid hboxes hb hby hy0 hy1 hy2 hy3 hy4

theorem ratPotential_pos_of_allBoxesValid_covers_sameParams
    {boxes : List RatBox} {lo hi w1 w2 w3 w4 s1 s2 s3 s4 : Rat} {y : ℝ}
    (hboxes : allBoxesValid boxes = true)
    (hcovers : coversFromBool boxes lo hi = true)
    (hparams : allBoxesSameParams boxes w1 w2 w3 w4 s1 s2 s3 s4 = true)
    (hy : y ∈ Icc (lo : ℝ) (hi : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (s1 : ℝ))
    (hy2ne : y ≠ (s2 : ℝ))
    (hy3ne : y ≠ (s3 : ℝ))
    (hy4ne : y ≠ (s4 : ℝ)) :
    0 < ratPotential w1 w2 w3 w4 s1 s2 s3 s4 y := by
  rcases exists_mem_box_of_coversFromBool hcovers hy with ⟨b, hb, hby⟩
  have hbparams := sameParamsBool_of_mem_allBoxesSameParams hparams hb
  rcases (b.sameParamsBool_eq_true_iff w1 w2 w3 w4 s1 s2 s3 s4).mp hbparams with
    ⟨hw1, hw2, hw3, hw4, hs1, hs2, hs3, hs4⟩
  have hbpos : 0 < b.realPotential y := by
    exact b.realPotential_pos_of_mem_allBoxesValid hboxes hb hby
      hy0ne
      (by simpa [hs1] using hy1ne)
      (by simpa [hs2] using hy2ne)
      (by simpa [hs3] using hy3ne)
      (by simpa [hs4] using hy4ne)
  simpa [RatBox.realPotential, ratPotential, hw1, hw2, hw3, hw4, hs1, hs2, hs3, hs4] using hbpos

end

end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block262

def block262LeftL : Rat := ((38303042410714285827 : Rat) / 50000000000000000000)
def block262LeftR : Rat := ((19156408482142857199 : Rat) / 25000000000000000000)
def block262RightL : Rat := ((88303042410714285827 : Rat) / 50000000000000000000)
def block262RightR : Rat := ((69156408482142857199 : Rat) / 25000000000000000000)

def block262LeftBoxes : List RatBox := [
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((38303042410714285827 : Rat) / 50000000000000000000), R := ((19156408482142857199 : Rat) / 25000000000000000000), D0 := ((19156408482142857199 : Rat) / 25000000000000000000), D1 := ((52570712589285714173 : Rat) / 50000000000000000000), D2 := ((89593707589285714173 : Rat) / 50000000000000000000), D3 := ((48872375714285714179 : Rat) / 25000000000000000000), D4 := ((100921486339285709173 : Rat) / 50000000000000000000), LB := ((25138368591990853 : Rat) / 10000000000000000000) }
]

def block262LeftCertificate : Bool :=
  allBoxesValid block262LeftBoxes &&
  coversFromBool block262LeftBoxes block262LeftL block262LeftR

theorem block262LeftCertificate_eq_true :
    block262LeftCertificate = true := by
  native_decide

def block262RightChunk000 : List RatBox := [
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((88303042410714285827 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((2570712589285714173 : Rat) / 50000000000000000000), D2 := ((39593707589285714173 : Rat) / 50000000000000000000), D3 := ((23872375714285714179 : Rat) / 25000000000000000000), D4 := ((50921486339285709173 : Rat) / 50000000000000000000), LB := ((837629000909733 : Rat) / 400000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((61642658448459 : Rat) / 400000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((9717963249880959 : Rat) / 100000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((4406933392857142837 : Rat) / 10000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((30349958087803233 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3944145955357142837 : Rat) / 10000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((4109763236535273 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((2690592074055989 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((3249964799107142837 : Rat) / 10000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((975410959784509 : Rat) / 100000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((3134267939732142837 : Rat) / 10000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((2490499140757373 : Rat) / 1250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((3018571080357142837 : Rat) / 10000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((6247779057300777 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((2960722650669642837 : Rat) / 10000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((821666059063187 : Rat) / 250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2902874220982142837 : Rat) / 10000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((1283012918253959 : Rat) / 2000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2845025791294642837 : Rat) / 10000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((230077132496633 : Rat) / 62500000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((2816101576450892837 : Rat) / 10000000000000000000), D4 := ((3451448558593749 : Rat) / 10000000000000000), LB := ((2632805151832479 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2787177361607142837 : Rat) / 10000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((836945652090193 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((2758253146763392837 : Rat) / 10000000000000000000), D4 := ((3393600128906249 : Rat) / 10000000000000000), LB := ((161406037288081 : Rat) / 200000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2729328931919642837 : Rat) / 10000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((218435015811487 : Rat) / 6250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2700404717075892837 : Rat) / 10000000000000000000), D4 := ((3335751699218749 : Rat) / 10000000000000000), LB := ((1994282658301663 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((2685942609654017837 : Rat) / 10000000000000000000), D4 := ((1660644795898437 : Rat) / 5000000000000000), LB := ((8448687608200653 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2671480502232142837 : Rat) / 10000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((1763562963599443 : Rat) / 1250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((2657018394810267837 : Rat) / 10000000000000000000), D4 := ((823091344238281 : Rat) / 2500000000000000), LB := ((11580570777333377 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((2642556287388392837 : Rat) / 10000000000000000000), D4 := ((3277903269531249 : Rat) / 10000000000000000), LB := ((465905590250483 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((2628094179966517837 : Rat) / 10000000000000000000), D4 := ((1631720581054687 : Rat) / 5000000000000000), LB := ((1831462123804313 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2613632072544642837 : Rat) / 10000000000000000000), D4 := ((3248979054687499 : Rat) / 10000000000000000), LB := ((5608699220805147 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((2599169965122767837 : Rat) / 10000000000000000000), D4 := ((404314618408203 : Rat) / 1250000000000000), LB := ((41717901287824377 : Rat) / 100000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((2523065653 : Rat) / 1024000000), D0 := ((2523065653 : Rat) / 1024000000), D1 := ((3309855753 : Rat) / 5120000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((2584707857700892837 : Rat) / 10000000000000000000), D4 := ((3220054839843749 : Rat) / 10000000000000000), LB := ((15102335343378237 : Rat) / 50000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2523065653 : Rat) / 1024000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((96259787 : Rat) / 1024000000), D3 := ((2570245750279017837 : Rat) / 10000000000000000000), D4 := ((1602796366210937 : Rat) / 5000000000000000), LB := ((540077104864041 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((12630137463 : Rat) / 5120000000), D0 := ((12630137463 : Rat) / 5120000000), D1 := ((3324664951 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((249552952828031 : Rat) / 1562500000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12630137463 : Rat) / 5120000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((466489737 : Rat) / 5120000000), D3 := ((2541321535435267837 : Rat) / 10000000000000000000), D4 := ((794167129394531 : Rat) / 2500000000000000), LB := ((13370444422812489 : Rat) / 100000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((12644946661 : Rat) / 5120000000), D0 := ((12644946661 : Rat) / 5120000000), D1 := ((3339474149 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((2526859428013392837 : Rat) / 10000000000000000000), D4 := ((3162206410156249 : Rat) / 10000000000000000), LB := ((13863882695630547 : Rat) / 100000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12644946661 : Rat) / 5120000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 5120000000), D3 := ((2512397320591517837 : Rat) / 10000000000000000000), D4 := ((1573872151367187 : Rat) / 5000000000000000), LB := ((875914113770207 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((632617563 : Rat) / 256000000), R := ((12659755859 : Rat) / 5120000000), D0 := ((12659755859 : Rat) / 5120000000), D1 := ((3354283347 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((2497935213169642837 : Rat) / 10000000000000000000), D4 := ((3133282195312499 : Rat) / 10000000000000000), LB := ((4880671124637137 : Rat) / 20000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12659755859 : Rat) / 5120000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((436871341 : Rat) / 5120000000), D3 := ((2483473105747767837 : Rat) / 10000000000000000000), D4 := ((48731563873291 : Rat) / 156250000000000), LB := ((6918430495662653 : Rat) / 20000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((12674565057 : Rat) / 5120000000), D0 := ((12674565057 : Rat) / 5120000000), D1 := ((673818509 : Rat) / 1024000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((2469010998325892837 : Rat) / 10000000000000000000), D4 := ((3104357980468749 : Rat) / 10000000000000000), LB := ((1204032008849977 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12674565057 : Rat) / 5120000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((422062143 : Rat) / 5120000000), D3 := ((2454548890904017837 : Rat) / 10000000000000000000), D4 := ((1544947936523437 : Rat) / 5000000000000000), LB := ((6519114402474963 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((2537874851 : Rat) / 1024000000), D0 := ((2537874851 : Rat) / 1024000000), D1 := ((3383901743 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((2440086783482142837 : Rat) / 10000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((8576620601583179 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2537874851 : Rat) / 1024000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((81450589 : Rat) / 1024000000), D3 := ((2425624676060267837 : Rat) / 10000000000000000000), D4 := ((765242914550781 : Rat) / 2500000000000000), LB := ((5498763517841343 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((12704183453 : Rat) / 5120000000), D0 := ((12704183453 : Rat) / 5120000000), D1 := ((3398710941 : Rat) / 5120000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((2411162568638392837 : Rat) / 10000000000000000000), D4 := ((3046509550781249 : Rat) / 10000000000000000), LB := ((6895589607753133 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12704183453 : Rat) / 5120000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((392443747 : Rat) / 5120000000), D3 := ((2396700461216517837 : Rat) / 10000000000000000000), D4 := ((1516023721679687 : Rat) / 5000000000000000), LB := ((8483710793743063 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((12718992651 : Rat) / 5120000000), D0 := ((12718992651 : Rat) / 5120000000), D1 := ((3413520139 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((2382238353794642837 : Rat) / 10000000000000000000), D4 := ((3017585335937499 : Rat) / 10000000000000000), LB := ((5134158639904761 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12718992651 : Rat) / 5120000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((377634549 : Rat) / 5120000000), D3 := ((2367776246372767837 : Rat) / 10000000000000000000), D4 := ((375390403564453 : Rat) / 1250000000000000), LB := ((24509775096929753 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((2353314138950892837 : Rat) / 10000000000000000000), D4 := ((2988661121093749 : Rat) / 10000000000000000), LB := ((18510858005318237 : Rat) / 50000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((2324389924107142837 : Rat) / 10000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((13865727866236577 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((2295465709263392837 : Rat) / 10000000000000000000), D4 := ((2930812691406249 : Rat) / 10000000000000000), LB := ((646183482918717 : Rat) / 250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((2266541494419642837 : Rat) / 10000000000000000000), D4 := ((2901888476562499 : Rat) / 10000000000000000), LB := ((99419298753671 : Rat) / 25000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((2237617279575892837 : Rat) / 10000000000000000000), D4 := ((2872964261718749 : Rat) / 10000000000000000), LB := ((1394093488267873 : Rat) / 250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((2208693064732142837 : Rat) / 10000000000000000000), D4 := ((2844040046874999 : Rat) / 10000000000000000), LB := ((6153686291354571 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((2150844635044642837 : Rat) / 10000000000000000000), D4 := ((2786191617187499 : Rat) / 10000000000000000), LB := ((6885340888529087 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((553499625212267 : Rat) / 200000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1977299345982142837 : Rat) / 10000000000000000000), D4 := ((2612646328124999 : Rat) / 10000000000000000), LB := ((9302870682483193 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((25445922425369957 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((3475973108542019 : Rat) / 100000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((21477089681712913 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((12587463722686307 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((2636664577768129 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((1668052366589285713903 : Rat) / 640000000000000000000), D0 := ((1668052366589285713903 : Rat) / 640000000000000000000), D1 := ((504868302589285713903 : Rat) / 640000000000000000000), D2 := ((30973966589285713903 : Rat) / 640000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((1898330329826791 : Rat) / 250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1668052366589285713903 : Rat) / 640000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((14671878910714285533 : Rat) / 128000000000000000000), D4 := ((114021601410714222097 : Rat) / 640000000000000000000), LB := ((5202354883516017 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((3115839045617977 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((110761183874999936423 : Rat) / 640000000000000000000), LB := ((1321539833844157 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((669503238910714285533 : Rat) / 256000000000000000000), D0 := ((669503238910714285533 : Rat) / 256000000000000000000), D1 := ((204229613310714285533 : Rat) / 256000000000000000000), D2 := ((14671878910714285533 : Rat) / 256000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((834901199377059 : Rat) / 250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((669503238910714285533 : Rat) / 256000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((135307327732142855471 : Rat) / 1280000000000000000000), D4 := ((43326348289285688867 : Rat) / 256000000000000000000), LB := ((6625510875470919 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((3350776612089285713339 : Rat) / 1280000000000000000000), D0 := ((3350776612089285713339 : Rat) / 1280000000000000000000), D1 := ((1024408484089285713339 : Rat) / 1280000000000000000000), D2 := ((76619812089285713339 : Rat) / 1280000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((2537896961951943 : Rat) / 1250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3350776612089285713339 : Rat) / 1280000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((132046910196428569797 : Rat) / 1280000000000000000000), D4 := ((213371323910714158661 : Rat) / 1280000000000000000000), LB := ((739620896229691 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((996392273188637 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((210110906374999872987 : Rat) / 1280000000000000000000), LB := ((181655082413237 : Rat) / 312500000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((182490548548389 : Rat) / 781250000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((6716225103089285712211 : Rat) / 2560000000000000000000), D0 := ((6716225103089285712211 : Rat) / 2560000000000000000000), D1 := ((2063488847089285712211 : Rat) / 2560000000000000000000), D2 := ((167911503089285712211 : Rat) / 2560000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((206850488839285587313 : Rat) / 1280000000000000000000), LB := ((8064217478907093 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6716225103089285712211 : Rat) / 2560000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((249421941482142854061 : Rat) / 2560000000000000000000), D4 := ((412070768910714031789 : Rat) / 2560000000000000000000), LB := ((7451385789978629 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((1343897104124999999577 : Rat) / 512000000000000000000), D0 := ((1343897104124999999577 : Rat) / 512000000000000000000), D1 := ((413349852924999999577 : Rat) / 512000000000000000000), D2 := ((34234384124999999577 : Rat) / 512000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((692283506890233 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1343897104124999999577 : Rat) / 512000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((246161523946428568387 : Rat) / 2560000000000000000000), D4 := ((81762070274999949223 : Rat) / 512000000000000000000), LB := ((809814875077277 : Rat) / 625000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((12236842058118563 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((405549933839285460441 : Rat) / 2560000000000000000000), LB := ((1460638497896103 : Rat) / 1250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((1130191958939139 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((402289516303571174767 : Rat) / 2560000000000000000000), LB := ((5543709129692681 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((5520901227204847 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((399029098767856889093 : Rat) / 2560000000000000000000), LB := ((11165327298835737 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((5729152119259631 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((395768681232142603419 : Rat) / 2560000000000000000000), LB := ((11921100771073861 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((3138535061756459 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((78501652739285663549 : Rat) / 512000000000000000000), LB := ((6678950870108377 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((3583229996714267 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((389247846160714032071 : Rat) / 2560000000000000000000), LB := ((15479785392058243 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((12461708440254793 : Rat) / 100000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((1129550838096273 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((2121515359148063 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((13157100215220041 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((1158724171802291 : Rat) / 625000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((24642719132882407 : Rat) / 10000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((3147664993420729 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((1192407978639759 : Rat) / 1250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((13662945723922487 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((4822225900827357 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((7926090245821901 : Rat) / 5000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((3781916732399221 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((2168844509224971 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((499785728432931 : Rat) / 20000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((17641023579656523 : Rat) / 500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((1488766635865297 : Rat) / 10000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((274360610803571428583 : Rat) / 100000000000000000000), D0 := ((274360610803571428583 : Rat) / 100000000000000000000), D1 := ((92613100803571428583 : Rat) / 100000000000000000000), D2 := ((18567110803571428583 : Rat) / 100000000000000000000), D3 := ((2265023125000000213 : Rat) / 100000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((2610549591620899 : Rat) / 25000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((274360610803571428583 : Rat) / 100000000000000000000), R := ((550986244732142857379 : Rat) / 200000000000000000000), D0 := ((550986244732142857379 : Rat) / 200000000000000000000), D1 := ((187491224732142857379 : Rat) / 200000000000000000000), D2 := ((39399244732142857379 : Rat) / 200000000000000000000), D3 := ((6795069375000000639 : Rat) / 200000000000000000000), D4 := ((4088446696428561417 : Rat) / 100000000000000000000), LB := ((30609612929300423 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((550986244732142857379 : Rat) / 200000000000000000000), R := ((1104237512589285714971 : Rat) / 400000000000000000000), D0 := ((1104237512589285714971 : Rat) / 400000000000000000000), D1 := ((377247472589285714971 : Rat) / 400000000000000000000), D2 := ((81063512589285714971 : Rat) / 400000000000000000000), D3 := ((15855161875000001491 : Rat) / 400000000000000000000), D4 := ((5911870267857122621 : Rat) / 200000000000000000000), LB := ((9789966313556109 : Rat) / 1000000000000000000) }
]

def block262RightChunk000L : Rat := ((88303042410714285827 : Rat) / 50000000000000000000)
def block262RightChunk000R : Rat := ((1104237512589285714971 : Rat) / 400000000000000000000)

def block262RightChunk000Certificate : Bool :=
  allBoxesValid block262RightChunk000 &&
  coversFromBool block262RightChunk000 block262RightChunk000L block262RightChunk000R

theorem block262RightChunk000Certificate_eq_true :
    block262RightChunk000Certificate = true := by
  native_decide

def block262RightChunk001 : List RatBox := [
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1104237512589285714971 : Rat) / 400000000000000000000), R := ((442148009660714286031 : Rat) / 160000000000000000000), D0 := ((442148009660714286031 : Rat) / 160000000000000000000), D1 := ((151351993660714286031 : Rat) / 160000000000000000000), D2 := ((32878409660714286031 : Rat) / 160000000000000000000), D3 := ((6795069375000000639 : Rat) / 160000000000000000000), D4 := ((9558717410714245029 : Rat) / 400000000000000000000), LB := ((1015192738675369 : Rat) / 250000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((442148009660714286031 : Rat) / 160000000000000000000), R := ((4423745119732142860523 : Rat) / 1600000000000000000000), D0 := ((4423745119732142860523 : Rat) / 1600000000000000000000), D1 := ((1515784959732142860523 : Rat) / 1600000000000000000000), D2 := ((331049119732142860523 : Rat) / 1600000000000000000000), D3 := ((70215716875000006603 : Rat) / 1600000000000000000000), D4 := ((3370482339285697969 : Rat) / 160000000000000000000), LB := ((6833676465023003 : Rat) / 2500000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4423745119732142860523 : Rat) / 1600000000000000000000), R := ((8849755262589285721259 : Rat) / 3200000000000000000000), D0 := ((8849755262589285721259 : Rat) / 3200000000000000000000), D1 := ((3033834942589285721259 : Rat) / 3200000000000000000000), D2 := ((664363262589285721259 : Rat) / 3200000000000000000000), D3 := ((142696456875000013419 : Rat) / 3200000000000000000000), D4 := ((31439800267856979477 : Rat) / 1600000000000000000000), LB := ((2541897280483457 : Rat) / 1000000000000000000) },
  { w1 := ((8984027938798961 : Rat) / 10000000000000000), w2 := ((1831059357642667 : Rat) / 25000000000000000), w3 := ((4989145111655751 : Rat) / 25000000000000000), w4 := ((6006731754926947 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8849755262589285721259 : Rat) / 3200000000000000000000), R := ((69156408482142857199 : Rat) / 25000000000000000000), D0 := ((69156408482142857199 : Rat) / 25000000000000000000), D1 := ((23719530982142857199 : Rat) / 25000000000000000000), D2 := ((5208033482142857199 : Rat) / 25000000000000000000), D3 := ((2265023125000000213 : Rat) / 50000000000000000000), D4 := ((60614577410713958741 : Rat) / 3200000000000000000000), LB := ((53377331192761 : Rat) / 125000000000000000) }
]

def block262RightChunk001L : Rat := ((1104237512589285714971 : Rat) / 400000000000000000000)
def block262RightChunk001R : Rat := ((69156408482142857199 : Rat) / 25000000000000000000)

def block262RightChunk001Certificate : Bool :=
  allBoxesValid block262RightChunk001 &&
  coversFromBool block262RightChunk001 block262RightChunk001L block262RightChunk001R

theorem block262RightChunk001Certificate_eq_true :
    block262RightChunk001Certificate = true := by
  native_decide

def block262RightChainCertificate : Bool :=
  decide (
    block262RightL = ((88303042410714285827 : Rat) / 50000000000000000000) /\
    ((1104237512589285714971 : Rat) / 400000000000000000000) = ((1104237512589285714971 : Rat) / 400000000000000000000) /\
    ((69156408482142857199 : Rat) / 25000000000000000000) = block262RightR)

theorem block262RightChainCertificate_eq_true :
    block262RightChainCertificate = true := by
  native_decide

def block262LeftBoxCount : Nat := boxCount block262LeftBoxes
def block262RightBoxCount : Nat := 104

def block262_rational_certificate : Prop :=
    block262LeftCertificate = true /\
    block262RightChainCertificate = true /\
    block262RightChunk000Certificate = true /\
    block262RightChunk001Certificate = true

theorem block262_rational_certificate_proof :
    block262_rational_certificate := by
  exact ⟨block262LeftCertificate_eq_true, block262RightChainCertificate_eq_true, block262RightChunk000Certificate_eq_true, block262RightChunk001Certificate_eq_true⟩

end Block262
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block262

open Set

def block262W1 : Rat := ((8984027938798961 : Rat) / 10000000000000000)
def block262W2 : Rat := ((1831059357642667 : Rat) / 25000000000000000)
def block262W3 : Rat := ((4989145111655751 : Rat) / 25000000000000000)
def block262W4 : Rat := ((6006731754926947 : Rat) / 100000000000000000)
def block262S1 : Rat := ((18174751 : Rat) / 10000000)
def block262S2 : Rat := ((511587 : Rat) / 200000)
def block262S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block262S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block262V (y : ℝ) : ℝ :=
  ratPotential block262W1 block262W2 block262W3 block262W4 block262S1 block262S2 block262S3 block262S4 y

def block262LeftParamsCertificate : Bool :=
  allBoxesSameParams block262LeftBoxes block262W1 block262W2 block262W3 block262W4 block262S1 block262S2 block262S3 block262S4

theorem block262LeftParamsCertificate_eq_true :
    block262LeftParamsCertificate = true := by
  native_decide

theorem block262_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block262LeftL : ℝ) (block262LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block262S1 : ℝ))
    (hy2ne : y ≠ (block262S2 : ℝ))
    (hy3ne : y ≠ (block262S3 : ℝ))
    (hy4ne : y ≠ (block262S4 : ℝ)) :
    0 < block262V y := by
  have hcert := block262LeftCertificate_eq_true
  unfold block262LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block262LeftBoxes) (lo := block262LeftL) (hi := block262LeftR)
    (w1 := block262W1) (w2 := block262W2) (w3 := block262W3) (w4 := block262W4)
    (s1 := block262S1) (s2 := block262S2) (s3 := block262S3) (s4 := block262S4)
    hboxes hcover block262LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block262RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block262RightChunk000 block262W1 block262W2 block262W3 block262W4 block262S1 block262S2 block262S3 block262S4

theorem block262RightChunk000ParamsCertificate_eq_true :
    block262RightChunk000ParamsCertificate = true := by
  native_decide

theorem block262_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block262RightChunk000L : ℝ) (block262RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block262S1 : ℝ))
    (hy2ne : y ≠ (block262S2 : ℝ))
    (hy3ne : y ≠ (block262S3 : ℝ))
    (hy4ne : y ≠ (block262S4 : ℝ)) :
    0 < block262V y := by
  have hcert := block262RightChunk000Certificate_eq_true
  unfold block262RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block262RightChunk000) (lo := block262RightChunk000L) (hi := block262RightChunk000R)
    (w1 := block262W1) (w2 := block262W2) (w3 := block262W3) (w4 := block262W4)
    (s1 := block262S1) (s2 := block262S2) (s3 := block262S3) (s4 := block262S4)
    hboxes hcover block262RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block262RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block262RightChunk001 block262W1 block262W2 block262W3 block262W4 block262S1 block262S2 block262S3 block262S4

theorem block262RightChunk001ParamsCertificate_eq_true :
    block262RightChunk001ParamsCertificate = true := by
  native_decide

theorem block262_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block262RightChunk001L : ℝ) (block262RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block262S1 : ℝ))
    (hy2ne : y ≠ (block262S2 : ℝ))
    (hy3ne : y ≠ (block262S3 : ℝ))
    (hy4ne : y ≠ (block262S4 : ℝ)) :
    0 < block262V y := by
  have hcert := block262RightChunk001Certificate_eq_true
  unfold block262RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block262RightChunk001) (lo := block262RightChunk001L) (hi := block262RightChunk001R)
    (w1 := block262W1) (w2 := block262W2) (w3 := block262W3) (w4 := block262W4)
    (s1 := block262S1) (s2 := block262S2) (s3 := block262S3) (s4 := block262S4)
    hboxes hcover block262RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block262_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block262RightL : ℝ) (block262RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block262S1 : ℝ))
    (hy2ne : y ≠ (block262S2 : ℝ))
    (hy3ne : y ≠ (block262S3 : ℝ))
    (hy4ne : y ≠ (block262S4 : ℝ)) :
    0 < block262V y := by
  by_cases h0 : y ≤ (block262RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block262RightChunk000L : ℝ) (block262RightChunk000R : ℝ) := by
      have hL : (block262RightChunk000L : ℝ) = (block262RightL : ℝ) := by
        norm_num [block262RightChunk000L, block262RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block262_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block262RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block262RightChunk001L : ℝ) = (block262RightChunk000R : ℝ) := by
      norm_num [block262RightChunk001L, block262RightChunk000R]
    have hR : (block262RightChunk001R : ℝ) = (block262RightR : ℝ) := by
      norm_num [block262RightChunk001R, block262RightR]
    have hyc : y ∈ Icc (block262RightChunk001L : ℝ) (block262RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block262_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block262_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block262LeftL : ℝ) (block262LeftR : ℝ) →
    y ≠ 0 → y ≠ (block262S1 : ℝ) → y ≠ (block262S2 : ℝ) →
    y ≠ (block262S3 : ℝ) → y ≠ (block262S4 : ℝ) → 0 < block262V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block262RightL : ℝ) (block262RightR : ℝ) →
    y ≠ 0 → y ≠ (block262S1 : ℝ) → y ≠ (block262S2 : ℝ) →
    y ≠ (block262S3 : ℝ) → y ≠ (block262S4 : ℝ) → 0 < block262V y)

theorem block262_reallog_certificate_proof :
    block262_reallog_certificate := by
  exact ⟨block262_left_V_pos, block262_right_V_pos⟩

end Block262
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block262.block262V
#check Erdos1038Lean.M1817475.Block262.block262_left_V_pos
#check Erdos1038Lean.M1817475.Block262.block262_right_V_pos
#check Erdos1038Lean.M1817475.Block262.block262_reallog_certificate_proof
