/-
Self-contained Lean4Web paste file.
Block 432 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block432

def block432LeftL : Rat := ((36641368303571428757 : Rat) / 50000000000000000000)
def block432LeftR : Rat := ((2290696428571428583 : Rat) / 3125000000000000000)
def block432RightL : Rat := ((86641368303571428757 : Rat) / 50000000000000000000)
def block432RightR : Rat := ((8540696428571428583 : Rat) / 3125000000000000000)

def block432LeftBoxes : List RatBox := [
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((36641368303571428757 : Rat) / 50000000000000000000), R := ((2290696428571428583 : Rat) / 3125000000000000000), D0 := ((2290696428571428583 : Rat) / 3125000000000000000), D1 := ((54232386696428571243 : Rat) / 50000000000000000000), D2 := ((91255381696428571243 : Rat) / 50000000000000000000), D3 := ((47523487321428571381 : Rat) / 25000000000000000000), D4 := ((102583160446428566243 : Rat) / 50000000000000000000), LB := ((9558188946944303 : Rat) / 5000000000000000000) }
]

def block432LeftCertificate : Bool :=
  allBoxesValid block432LeftBoxes &&
  coversFromBool block432LeftBoxes block432LeftL block432LeftR

theorem block432LeftCertificate_eq_true :
    block432LeftCertificate = true := by
  native_decide

def block432RightChunk000 : List RatBox := [
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86641368303571428757 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((4232386696428571243 : Rat) / 50000000000000000000), D2 := ((41255381696428571243 : Rat) / 50000000000000000000), D3 := ((22523487321428571381 : Rat) / 25000000000000000000), D4 := ((52583160446428566243 : Rat) / 50000000000000000000), LB := ((10358769401362697 : Rat) / 10000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((40814587946428571519 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((4675358969782607 : Rat) / 10000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((31558839196428571519 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((25149300677424203 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((22303090446428571519 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((2832619349816147 : Rat) / 50000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((19989153258928571519 : Rat) / 50000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((801590466284443 : Rat) / 100000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((17675216071428571519 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((11300399881471503 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((1481581821 : Rat) / 640000000), D0 := ((1481581821 : Rat) / 640000000), D1 := ((318397757 : Rat) / 640000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((16518247477678571519 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((490749398196013 : Rat) / 31250000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1481581821 : Rat) / 640000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((155496579 : Rat) / 640000000), D3 := ((15939763180803571519 : Rat) / 50000000000000000000), D4 := ((4695189796874999 : Rat) / 10000000000000000), LB := ((2189092837731721 : Rat) / 250000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((15361278883928571519 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((2626203099354303 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((3000186637 : Rat) / 1280000000), D0 := ((3000186637 : Rat) / 1280000000), D1 := ((673818509 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((14782794587053571519 : Rat) / 50000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((6900662900599541 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3000186637 : Rat) / 1280000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((273970163 : Rat) / 1280000000), D3 := ((14493552438616071519 : Rat) / 50000000000000000000), D4 := ((4405947648437499 : Rat) / 10000000000000000), LB := ((280731733967891 : Rat) / 62500000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((602999167 : Rat) / 256000000), D0 := ((602999167 : Rat) / 256000000), D1 := ((688627707 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14204310290178571519 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((230282736279383 : Rat) / 100000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((602999167 : Rat) / 256000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((51832193 : Rat) / 256000000), D3 := ((13915068141741071519 : Rat) / 50000000000000000000), D4 := ((4290250789062499 : Rat) / 10000000000000000), LB := ((3378014589826839 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((6052205467 : Rat) / 2560000000), D0 := ((6052205467 : Rat) / 2560000000), D1 := ((1399469211 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((13625825993303571519 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((3253314905510743 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6052205467 : Rat) / 2560000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((496108133 : Rat) / 2560000000), D3 := ((13481204919084821519 : Rat) / 50000000000000000000), D4 := ((4203478144531249 : Rat) / 10000000000000000), LB := ((613059639732589 : Rat) / 250000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((1213402933 : Rat) / 512000000), D0 := ((1213402933 : Rat) / 512000000), D1 := ((1414278409 : Rat) / 2560000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((13336583844866071519 : Rat) / 50000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((855055718066107 : Rat) / 500000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1213402933 : Rat) / 512000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((96259787 : Rat) / 512000000), D3 := ((13191962770647321519 : Rat) / 50000000000000000000), D4 := ((4145629714843749 : Rat) / 10000000000000000), LB := ((10275728102048937 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((6081823863 : Rat) / 2560000000), D0 := ((6081823863 : Rat) / 2560000000), D1 := ((1429087607 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13047341696428571519 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((2026458774552209 : Rat) / 5000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6081823863 : Rat) / 2560000000), R := ((486842093 : Rat) / 204800000), D0 := ((486842093 : Rat) / 204800000), D1 := ((2865579813 : Rat) / 5120000000), D2 := ((466489737 : Rat) / 2560000000), D3 := ((12902720622209821519 : Rat) / 50000000000000000000), D4 := ((4087781285156249 : Rat) / 10000000000000000), LB := ((10647230654003137 : Rat) / 5000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((486842093 : Rat) / 204800000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 40960000), D3 := ((12830410085100446519 : Rat) / 50000000000000000000), D4 := ((2036659588867187 : Rat) / 5000000000000000), LB := ((18671839504398463 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((12185861523 : Rat) / 5120000000), D0 := ((12185861523 : Rat) / 5120000000), D1 := ((2880389011 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((12758099547991071519 : Rat) / 50000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((16204608923267583 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12185861523 : Rat) / 5120000000), R := ((6096633061 : Rat) / 2560000000), D0 := ((6096633061 : Rat) / 2560000000), D1 := ((288779361 : Rat) / 512000000), D2 := ((910765677 : Rat) / 5120000000), D3 := ((12685789010881696519 : Rat) / 50000000000000000000), D4 := ((31596835647583 : Rat) / 78125000000000), LB := ((13893735207940183 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6096633061 : Rat) / 2560000000), R := ((12200670721 : Rat) / 5120000000), D0 := ((12200670721 : Rat) / 5120000000), D1 := ((2895198209 : Rat) / 5120000000), D2 := ((451680539 : Rat) / 2560000000), D3 := ((12613478473772321519 : Rat) / 50000000000000000000), D4 := ((4029932855468749 : Rat) / 10000000000000000), LB := ((11740205699833223 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12200670721 : Rat) / 5120000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((895956479 : Rat) / 5120000000), D3 := ((12541167936662946519 : Rat) / 50000000000000000000), D4 := ((2007735374023437 : Rat) / 5000000000000000), LB := ((9745029874195649 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((12215479919 : Rat) / 5120000000), D0 := ((12215479919 : Rat) / 5120000000), D1 := ((2910007407 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((12468857399553571519 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((7909239788959077 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12215479919 : Rat) / 5120000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((881147281 : Rat) / 5120000000), D3 := ((12396546862444196519 : Rat) / 50000000000000000000), D4 := ((996636633300781 : Rat) / 2500000000000000), LB := ((249355621891173 : Rat) / 400000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((12230289117 : Rat) / 5120000000), D0 := ((12230289117 : Rat) / 5120000000), D1 := ((584963321 : Rat) / 1024000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((12324236325334821519 : Rat) / 50000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((47200607742110823 : Rat) / 100000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12230289117 : Rat) / 5120000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((866338083 : Rat) / 5120000000), D3 := ((12251925788225446519 : Rat) / 50000000000000000000), D4 := ((1978811159179687 : Rat) / 5000000000000000), LB := ((6737706215907413 : Rat) / 20000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((2449019663 : Rat) / 1024000000), D0 := ((2449019663 : Rat) / 1024000000), D1 := ((2939625803 : Rat) / 5120000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((12179615251116071519 : Rat) / 50000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((10906973530988573 : Rat) / 50000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2449019663 : Rat) / 1024000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((170305777 : Rat) / 1024000000), D3 := ((12107304714006696519 : Rat) / 50000000000000000000), D4 := ((491087262939453 : Rat) / 1250000000000000), LB := ((5794188840767961 : Rat) / 50000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((12259907513 : Rat) / 5120000000), D0 := ((12259907513 : Rat) / 5120000000), D1 := ((2954435001 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((12034994176897321519 : Rat) / 50000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((604720145405413 : Rat) / 20000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12259907513 : Rat) / 5120000000), R := ((196217757 : Rat) / 81920000), D0 := ((196217757 : Rat) / 81920000), D1 := ((5916274601 : Rat) / 10240000000), D2 := ((836719687 : Rat) / 5120000000), D3 := ((11962683639787946519 : Rat) / 50000000000000000000), D4 := ((1949886944335937 : Rat) / 5000000000000000), LB := ((107610677243207 : Rat) / 100000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((196217757 : Rat) / 81920000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((66641391 : Rat) / 409600000), D3 := ((11926528371233259019 : Rat) / 50000000000000000000), D4 := ((7785085669921873 : Rat) / 20000000000000000), LB := ((10468518864514137 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((24542028823 : Rat) / 10240000000), D0 := ((24542028823 : Rat) / 10240000000), D1 := ((5931083799 : Rat) / 10240000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((11890373102678571519 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((1277285035686717 : Rat) / 1250000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24542028823 : Rat) / 10240000000), R := ((12274716711 : Rat) / 5120000000), D0 := ((12274716711 : Rat) / 5120000000), D1 := ((2969244199 : Rat) / 5120000000), D2 := ((1651225577 : Rat) / 10240000000), D3 := ((11854217834123884019 : Rat) / 50000000000000000000), D4 := ((7756161455078123 : Rat) / 20000000000000000), LB := ((2002101997875011 : Rat) / 2000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12274716711 : Rat) / 5120000000), R := ((24556838021 : Rat) / 10240000000), D0 := ((24556838021 : Rat) / 10240000000), D1 := ((5945892997 : Rat) / 10240000000), D2 := ((821910489 : Rat) / 5120000000), D3 := ((11818062565569196519 : Rat) / 50000000000000000000), D4 := ((967712418457031 : Rat) / 2500000000000000), LB := ((9845367722697979 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24556838021 : Rat) / 10240000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((1636416379 : Rat) / 10240000000), D3 := ((11781907297014509019 : Rat) / 50000000000000000000), D4 := ((7727237240234373 : Rat) / 20000000000000000), LB := ((9723014995929313 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((24571647219 : Rat) / 10240000000), D0 := ((24571647219 : Rat) / 10240000000), D1 := ((1192140439 : Rat) / 2048000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((11745752028459821519 : Rat) / 50000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((301362971975817 : Rat) / 312500000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24571647219 : Rat) / 10240000000), R := ((12289525909 : Rat) / 5120000000), D0 := ((12289525909 : Rat) / 5120000000), D1 := ((2984053397 : Rat) / 5120000000), D2 := ((1621607181 : Rat) / 10240000000), D3 := ((11709596759905134019 : Rat) / 50000000000000000000), D4 := ((7698313025390623 : Rat) / 20000000000000000), LB := ((9607333142535729 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12289525909 : Rat) / 5120000000), R := ((24586456417 : Rat) / 10240000000), D0 := ((24586456417 : Rat) / 10240000000), D1 := ((5975511393 : Rat) / 10240000000), D2 := ((807101291 : Rat) / 5120000000), D3 := ((11673441491350446519 : Rat) / 50000000000000000000), D4 := ((1920962729492187 : Rat) / 5000000000000000), LB := ((9614336035990989 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24586456417 : Rat) / 10240000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((1606797983 : Rat) / 10240000000), D3 := ((11637286222795759019 : Rat) / 50000000000000000000), D4 := ((7669388810546873 : Rat) / 20000000000000000), LB := ((75506191802013 : Rat) / 78125000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((4920253123 : Rat) / 2048000000), D0 := ((4920253123 : Rat) / 2048000000), D1 := ((5990320591 : Rat) / 10240000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((11601130954241071519 : Rat) / 50000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((4879436659788877 : Rat) / 5000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4920253123 : Rat) / 2048000000), R := ((12304335107 : Rat) / 5120000000), D0 := ((12304335107 : Rat) / 5120000000), D1 := ((599772519 : Rat) / 1024000000), D2 := ((318397757 : Rat) / 2048000000), D3 := ((11564975685686384019 : Rat) / 50000000000000000000), D4 := ((7640464595703123 : Rat) / 20000000000000000), LB := ((4948375431597721 : Rat) / 5000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12304335107 : Rat) / 5120000000), R := ((24616074813 : Rat) / 10240000000), D0 := ((24616074813 : Rat) / 10240000000), D1 := ((6005129789 : Rat) / 10240000000), D2 := ((792292093 : Rat) / 5120000000), D3 := ((11528820417131696519 : Rat) / 50000000000000000000), D4 := ((238312577758789 : Rat) / 625000000000000), LB := ((10078599611067773 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24616074813 : Rat) / 10240000000), R := ((6155869853 : Rat) / 2560000000), D0 := ((6155869853 : Rat) / 2560000000), D1 := ((1503133597 : Rat) / 2560000000), D2 := ((1577179587 : Rat) / 10240000000), D3 := ((11492665148577009019 : Rat) / 50000000000000000000), D4 := ((7611540380859373 : Rat) / 20000000000000000), LB := ((2576148980991573 : Rat) / 2500000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6155869853 : Rat) / 2560000000), R := ((24630884011 : Rat) / 10240000000), D0 := ((24630884011 : Rat) / 10240000000), D1 := ((6019938987 : Rat) / 10240000000), D2 := ((392443747 : Rat) / 2560000000), D3 := ((11456509880022321519 : Rat) / 50000000000000000000), D4 := ((3798539136718749 : Rat) / 10000000000000000), LB := ((132186476454247 : Rat) / 125000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24630884011 : Rat) / 10240000000), R := ((2463828861 : Rat) / 1024000000), D0 := ((2463828861 : Rat) / 1024000000), D1 := ((3013671793 : Rat) / 5120000000), D2 := ((1562370389 : Rat) / 10240000000), D3 := ((11420354611467634019 : Rat) / 50000000000000000000), D4 := ((7582616166015623 : Rat) / 20000000000000000), LB := ((217794929581297 : Rat) / 200000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2463828861 : Rat) / 1024000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((155496579 : Rat) / 1024000000), D3 := ((11384199342912946519 : Rat) / 50000000000000000000), D4 := ((1892038514648437 : Rat) / 5000000000000000), LB := ((5507345004010511 : Rat) / 200000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((12333953503 : Rat) / 5120000000), D0 := ((12333953503 : Rat) / 5120000000), D1 := ((3028480991 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((11311888805803571519 : Rat) / 50000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((5752537816385017 : Rat) / 50000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12333953503 : Rat) / 5120000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((762673697 : Rat) / 5120000000), D3 := ((11239578268694196519 : Rat) / 50000000000000000000), D4 := ((938788203613281 : Rat) / 2500000000000000), LB := ((5516357267584121 : Rat) / 25000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((12348762701 : Rat) / 5120000000), D0 := ((12348762701 : Rat) / 5120000000), D1 := ((3043290189 : Rat) / 5120000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11167267731584821519 : Rat) / 50000000000000000000), D4 := ((3740690707031249 : Rat) / 10000000000000000), LB := ((8612516859292721 : Rat) / 25000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12348762701 : Rat) / 5120000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((747864499 : Rat) / 5120000000), D3 := ((11094957194475446519 : Rat) / 50000000000000000000), D4 := ((1863114299804687 : Rat) / 5000000000000000), LB := ((48674668812392907 : Rat) / 100000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((12363571899 : Rat) / 5120000000), D0 := ((12363571899 : Rat) / 5120000000), D1 := ((3058099387 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11022646657366071519 : Rat) / 50000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((6475526310778107 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12363571899 : Rat) / 5120000000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((733055301 : Rat) / 5120000000), D3 := ((10950336120256696519 : Rat) / 50000000000000000000), D4 := ((462163048095703 : Rat) / 1250000000000000), LB := ((2067706018100239 : Rat) / 2500000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((12378381097 : Rat) / 5120000000), D0 := ((12378381097 : Rat) / 5120000000), D1 := ((614581717 : Rat) / 1024000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((10878025583147321519 : Rat) / 50000000000000000000), D4 := ((3682842277343749 : Rat) / 10000000000000000), LB := ((10255036149699193 : Rat) / 10000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12378381097 : Rat) / 5120000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((718246103 : Rat) / 5120000000), D3 := ((10805715046037946519 : Rat) / 50000000000000000000), D4 := ((1834190084960937 : Rat) / 5000000000000000), LB := ((1553734549328157 : Rat) / 1250000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((2478638059 : Rat) / 1024000000), D0 := ((2478638059 : Rat) / 1024000000), D1 := ((3087717783 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((10733404508928571519 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((369927437093541 : Rat) / 250000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2478638059 : Rat) / 1024000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1024000000), D3 := ((10661093971819196519 : Rat) / 50000000000000000000), D4 := ((909863988769531 : Rat) / 2500000000000000), LB := ((8679245953568601 : Rat) / 5000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((12407999493 : Rat) / 5120000000), D0 := ((12407999493 : Rat) / 5120000000), D1 := ((3102526981 : Rat) / 5120000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((10588783434709821519 : Rat) / 50000000000000000000), D4 := ((3624993847656249 : Rat) / 10000000000000000), LB := ((1005794649565371 : Rat) / 500000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12407999493 : Rat) / 5120000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((688627707 : Rat) / 5120000000), D3 := ((10516472897600446519 : Rat) / 50000000000000000000), D4 := ((1805265870117187 : Rat) / 5000000000000000), LB := ((1153558797870713 : Rat) / 500000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((10444162360491071519 : Rat) / 50000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((12119173302473779 : Rat) / 25000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((10299541286272321519 : Rat) / 50000000000000000000), D4 := ((3567145417968749 : Rat) / 10000000000000000), LB := ((1480630545299573 : Rat) / 1250000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10154920212053571519 : Rat) / 50000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((1966506253285677 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10010299137834821519 : Rat) / 50000000000000000000), D4 := ((3509296988281249 : Rat) / 10000000000000000), LB := ((70811869347941 : Rat) / 25000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((9865678063616071519 : Rat) / 50000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((7568386176515729 : Rat) / 2000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((9721056989397321519 : Rat) / 50000000000000000000), D4 := ((3451448558593749 : Rat) / 10000000000000000), LB := ((4823529551227307 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((9576435915178571519 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((3563881118253509 : Rat) / 2000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((9287193766741071519 : Rat) / 50000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((1086707694467743 : Rat) / 250000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((8997951618303571519 : Rat) / 50000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((1459104590332061 : Rat) / 200000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((8708709469866071519 : Rat) / 50000000000000000000), D4 := ((3248979054687499 : Rat) / 10000000000000000), LB := ((10647540339529499 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((8419467321428571519 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((6359820703634639 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((7840983024553571519 : Rat) / 50000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((15396901445306907 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((7262498727678571519 : Rat) / 50000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((2728478483887551 : Rat) / 250000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6105530133928571519 : Rat) / 50000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((10980135299218277 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((131688342946428571519 : Rat) / 50000000000000000000), D0 := ((131688342946428571519 : Rat) / 50000000000000000000), D1 := ((40814587946428571519 : Rat) / 50000000000000000000), D2 := ((3791592946428571519 : Rat) / 50000000000000000000), D3 := ((3791592946428571519 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((323643732983967 : Rat) / 4000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((131688342946428571519 : Rat) / 50000000000000000000), R := ((268339485803571428847 : Rat) / 100000000000000000000), D0 := ((268339485803571428847 : Rat) / 100000000000000000000), D1 := ((86591975803571428847 : Rat) / 100000000000000000000), D2 := ((12545985803571428847 : Rat) / 100000000000000000000), D3 := ((4962799910714285809 : Rat) / 100000000000000000000), D4 := ((7536185803571423481 : Rat) / 50000000000000000000), LB := ((4687787575235379 : Rat) / 25000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((268339485803571428847 : Rat) / 100000000000000000000), R := ((541641771517857143503 : Rat) / 200000000000000000000), D0 := ((541641771517857143503 : Rat) / 200000000000000000000), D1 := ((178146751517857143503 : Rat) / 200000000000000000000), D2 := ((30054771517857143503 : Rat) / 200000000000000000000), D3 := ((14888399732142857427 : Rat) / 200000000000000000000), D4 := ((10109571696428561153 : Rat) / 100000000000000000000), LB := ((6538919277026223 : Rat) / 100000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((541641771517857143503 : Rat) / 200000000000000000000), R := ((217649268589285714563 : Rat) / 80000000000000000000), D0 := ((217649268589285714563 : Rat) / 80000000000000000000), D1 := ((72251260589285714563 : Rat) / 80000000000000000000), D2 := ((13014468589285714563 : Rat) / 80000000000000000000), D3 := ((34739599375000000663 : Rat) / 400000000000000000000), D4 := ((15256343482142836497 : Rat) / 200000000000000000000), LB := ((26066798328583357 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((217649268589285714563 : Rat) / 80000000000000000000), R := ((2181455485803571431439 : Rat) / 800000000000000000000), D0 := ((2181455485803571431439 : Rat) / 800000000000000000000), D1 := ((727475405803571431439 : Rat) / 800000000000000000000), D2 := ((135107485803571431439 : Rat) / 800000000000000000000), D3 := ((14888399732142857427 : Rat) / 160000000000000000000), D4 := ((5109977410714277437 : Rat) / 80000000000000000000), LB := ((1184903038016577 : Rat) / 100000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2181455485803571431439 : Rat) / 800000000000000000000), R := ((4367873771517857148687 : Rat) / 1600000000000000000000), D0 := ((4367873771517857148687 : Rat) / 1600000000000000000000), D1 := ((1459913611517857148687 : Rat) / 1600000000000000000000), D2 := ((275177771517857148687 : Rat) / 1600000000000000000000), D3 := ((153846797232142860079 : Rat) / 1600000000000000000000), D4 := ((46136974196428488561 : Rat) / 800000000000000000000), LB := ((6335880803628513 : Rat) / 1000000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4367873771517857148687 : Rat) / 1600000000000000000000), R := ((8740710342946428583183 : Rat) / 3200000000000000000000), D0 := ((8740710342946428583183 : Rat) / 3200000000000000000000), D1 := ((2924790022946428583183 : Rat) / 3200000000000000000000), D2 := ((555318342946428583183 : Rat) / 3200000000000000000000), D3 := ((312656394375000005967 : Rat) / 3200000000000000000000), D4 := ((87311148482142691313 : Rat) / 1600000000000000000000), LB := ((806967061807451 : Rat) / 200000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8740710342946428583183 : Rat) / 3200000000000000000000), R := ((699455339432142858087 : Rat) / 256000000000000000000), D0 := ((699455339432142858087 : Rat) / 256000000000000000000), D1 := ((234181713832142858087 : Rat) / 256000000000000000000), D2 := ((44623979432142858087 : Rat) / 256000000000000000000), D3 := ((630275588660714297743 : Rat) / 6400000000000000000000), D4 := ((169659497053571096817 : Rat) / 3200000000000000000000), LB := ((376003508170103 : Rat) / 125000000000000000) },
  { w1 := ((6499475670188821 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((15525284718257887 : Rat) / 50000000000000000), w4 := ((3924180678367257 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131688342946428571519 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((699455339432142858087 : Rat) / 256000000000000000000), R := ((8540696428571428583 : Rat) / 3125000000000000000), D0 := ((8540696428571428583 : Rat) / 3125000000000000000), D1 := ((2861086741071428583 : Rat) / 3125000000000000000), D2 := ((547149553571428583 : Rat) / 3125000000000000000), D3 := ((4962799910714285809 : Rat) / 50000000000000000000), D4 := ((13374247767857116313 : Rat) / 256000000000000000000), LB := ((894551157397061 : Rat) / 1000000000000000000) }
]

def block432RightChunk000L : Rat := ((86641368303571428757 : Rat) / 50000000000000000000)
def block432RightChunk000R : Rat := ((8540696428571428583 : Rat) / 3125000000000000000)

def block432RightChunk000Certificate : Bool :=
  allBoxesValid block432RightChunk000 &&
  coversFromBool block432RightChunk000 block432RightChunk000L block432RightChunk000R

theorem block432RightChunk000Certificate_eq_true :
    block432RightChunk000Certificate = true := by
  native_decide

def block432RightChainCertificate : Bool :=
  decide (
    block432RightL = ((86641368303571428757 : Rat) / 50000000000000000000) /\
    ((8540696428571428583 : Rat) / 3125000000000000000) = block432RightR)

theorem block432RightChainCertificate_eq_true :
    block432RightChainCertificate = true := by
  native_decide

def block432LeftBoxCount : Nat := boxCount block432LeftBoxes
def block432RightBoxCount : Nat := 83

def block432_rational_certificate : Prop :=
    block432LeftCertificate = true /\
    block432RightChainCertificate = true /\
    block432RightChunk000Certificate = true

theorem block432_rational_certificate_proof :
    block432_rational_certificate := by
  exact ⟨block432LeftCertificate_eq_true, block432RightChainCertificate_eq_true, block432RightChunk000Certificate_eq_true⟩

end Block432
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block432

open Set

def block432W1 : Rat := ((6499475670188821 : Rat) / 10000000000000000)
def block432W2 : Rat := (0 : Rat)
def block432W3 : Rat := ((15525284718257887 : Rat) / 50000000000000000)
def block432W4 : Rat := ((3924180678367257 : Rat) / 50000000000000000)
def block432S1 : Rat := ((18174751 : Rat) / 10000000)
def block432S2 : Rat := ((511587 : Rat) / 200000)
def block432S3 : Rat := ((131688342946428571519 : Rat) / 50000000000000000000)
def block432S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block432V (y : ℝ) : ℝ :=
  ratPotential block432W1 block432W2 block432W3 block432W4 block432S1 block432S2 block432S3 block432S4 y

def block432LeftParamsCertificate : Bool :=
  allBoxesSameParams block432LeftBoxes block432W1 block432W2 block432W3 block432W4 block432S1 block432S2 block432S3 block432S4

theorem block432LeftParamsCertificate_eq_true :
    block432LeftParamsCertificate = true := by
  native_decide

theorem block432_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block432LeftL : ℝ) (block432LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block432S1 : ℝ))
    (hy2ne : y ≠ (block432S2 : ℝ))
    (hy3ne : y ≠ (block432S3 : ℝ))
    (hy4ne : y ≠ (block432S4 : ℝ)) :
    0 < block432V y := by
  have hcert := block432LeftCertificate_eq_true
  unfold block432LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block432LeftBoxes) (lo := block432LeftL) (hi := block432LeftR)
    (w1 := block432W1) (w2 := block432W2) (w3 := block432W3) (w4 := block432W4)
    (s1 := block432S1) (s2 := block432S2) (s3 := block432S3) (s4 := block432S4)
    hboxes hcover block432LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block432RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block432RightChunk000 block432W1 block432W2 block432W3 block432W4 block432S1 block432S2 block432S3 block432S4

theorem block432RightChunk000ParamsCertificate_eq_true :
    block432RightChunk000ParamsCertificate = true := by
  native_decide

theorem block432_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block432RightChunk000L : ℝ) (block432RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block432S1 : ℝ))
    (hy2ne : y ≠ (block432S2 : ℝ))
    (hy3ne : y ≠ (block432S3 : ℝ))
    (hy4ne : y ≠ (block432S4 : ℝ)) :
    0 < block432V y := by
  have hcert := block432RightChunk000Certificate_eq_true
  unfold block432RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block432RightChunk000) (lo := block432RightChunk000L) (hi := block432RightChunk000R)
    (w1 := block432W1) (w2 := block432W2) (w3 := block432W3) (w4 := block432W4)
    (s1 := block432S1) (s2 := block432S2) (s3 := block432S3) (s4 := block432S4)
    hboxes hcover block432RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block432_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block432RightL : ℝ) (block432RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block432S1 : ℝ))
    (hy2ne : y ≠ (block432S2 : ℝ))
    (hy3ne : y ≠ (block432S3 : ℝ))
    (hy4ne : y ≠ (block432S4 : ℝ)) :
    0 < block432V y := by
  have hL : (block432RightChunk000L : ℝ) = (block432RightL : ℝ) := by
    norm_num [block432RightChunk000L, block432RightL]
  have hR : (block432RightChunk000R : ℝ) = (block432RightR : ℝ) := by
    norm_num [block432RightChunk000R, block432RightR]
  have hyc : y ∈ Icc (block432RightChunk000L : ℝ) (block432RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block432_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block432_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block432LeftL : ℝ) (block432LeftR : ℝ) →
    y ≠ 0 → y ≠ (block432S1 : ℝ) → y ≠ (block432S2 : ℝ) →
    y ≠ (block432S3 : ℝ) → y ≠ (block432S4 : ℝ) → 0 < block432V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block432RightL : ℝ) (block432RightR : ℝ) →
    y ≠ 0 → y ≠ (block432S1 : ℝ) → y ≠ (block432S2 : ℝ) →
    y ≠ (block432S3 : ℝ) → y ≠ (block432S4 : ℝ) → 0 < block432V y)

theorem block432_reallog_certificate_proof :
    block432_reallog_certificate := by
  exact ⟨block432_left_V_pos, block432_right_V_pos⟩

end Block432
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block432.block432V
#check Erdos1038Lean.M1817475.Block432.block432_left_V_pos
#check Erdos1038Lean.M1817475.Block432.block432_right_V_pos
#check Erdos1038Lean.M1817475.Block432.block432_reallog_certificate_proof
