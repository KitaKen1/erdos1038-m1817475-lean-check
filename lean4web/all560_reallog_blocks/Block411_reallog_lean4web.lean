/-
Self-contained Lean4Web paste file.
Block 411 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block411

def block411LeftL : Rat := ((9211658482142857187 : Rat) / 12500000000000000000)
def block411LeftR : Rat := ((36856408482142857319 : Rat) / 50000000000000000000)
def block411RightL : Rat := ((21711658482142857187 : Rat) / 12500000000000000000)
def block411RightR : Rat := ((136856408482142857319 : Rat) / 50000000000000000000)

def block411LeftBoxes : List RatBox := [
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9211658482142857187 : Rat) / 12500000000000000000), R := ((36856408482142857319 : Rat) / 50000000000000000000), D0 := ((36856408482142857319 : Rat) / 50000000000000000000), D1 := ((13506780267857142813 : Rat) / 12500000000000000000), D2 := ((22762529017857142813 : Rat) / 12500000000000000000), D3 := ((95252240267857142753 : Rat) / 50000000000000000000), D4 := ((25594473705357141563 : Rat) / 12500000000000000000), LB := ((5433780648758657 : Rat) / 10000000000000000000) }
]

def block411LeftCertificate : Bool :=
  allBoxesValid block411LeftBoxes &&
  coversFromBool block411LeftBoxes block411LeftL block411LeftR

theorem block411LeftCertificate_eq_true :
    block411LeftCertificate = true := by
  native_decide

def block411RightChunk000 : List RatBox := [
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((21711658482142857187 : Rat) / 12500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1006780267857142813 : Rat) / 12500000000000000000), D2 := ((10262529017857142813 : Rat) / 12500000000000000000), D3 := ((45252240267857142753 : Rat) / 50000000000000000000), D4 := ((13094473705357141563 : Rat) / 12500000000000000000), LB := ((12284596977000657 : Rat) / 10000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41225119196428571501 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((356405993152651 : Rat) / 625000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((31969370446428571501 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((7813998010008603 : Rat) / 100000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((22713621696428571501 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((9526097383234677 : Rat) / 100000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((20399684508928571501 : Rat) / 50000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((7494821743841483 : Rat) / 200000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18085747321428571501 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((4362810487757573 : Rat) / 125000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((16928778727678571501 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((1481923088809127 : Rat) / 100000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((15771810133928571501 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((3703857396766791 : Rat) / 200000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((15193325837053571501 : Rat) / 50000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((272047351315767 : Rat) / 25000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14614841540178571501 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((102086711151117 : Rat) / 25000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((14036357243303571501 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((1009464430227253 : Rat) / 125000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((13747115094866071501 : Rat) / 50000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((267757614245593 : Rat) / 50000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13457872946428571501 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((2862457459442677 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((13168630797991071501 : Rat) / 50000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((12040451704389 : Rat) / 20000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((12879388649553571501 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((17052282847357589 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((12734767575334821501 : Rat) / 50000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((4939246960143473 : Rat) / 2000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((12590146501116071501 : Rat) / 50000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((1987844319767517 : Rat) / 1250000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((12445525426897321501 : Rat) / 50000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((1932879610948117 : Rat) / 2500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12300904352678571501 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((1902631308747793 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((12289525909 : Rat) / 5120000000), D0 := ((12289525909 : Rat) / 5120000000), D1 := ((2984053397 : Rat) / 5120000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((12156283278459821501 : Rat) / 50000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((17033567902281221 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12289525909 : Rat) / 5120000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((807101291 : Rat) / 5120000000), D3 := ((12083972741350446501 : Rat) / 50000000000000000000), D4 := ((1920962729492187 : Rat) / 5000000000000000), LB := ((2755289107957859 : Rat) / 2000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((12304335107 : Rat) / 5120000000), D0 := ((12304335107 : Rat) / 5120000000), D1 := ((599772519 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((12011662204241071501 : Rat) / 50000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((667641697228577 : Rat) / 625000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12304335107 : Rat) / 5120000000), R := ((6155869853 : Rat) / 2560000000), D0 := ((6155869853 : Rat) / 2560000000), D1 := ((1503133597 : Rat) / 2560000000), D2 := ((792292093 : Rat) / 5120000000), D3 := ((11939351667131696501 : Rat) / 50000000000000000000), D4 := ((238312577758789 : Rat) / 625000000000000), LB := ((3876075113625199 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6155869853 : Rat) / 2560000000), R := ((2463828861 : Rat) / 1024000000), D0 := ((2463828861 : Rat) / 1024000000), D1 := ((3013671793 : Rat) / 5120000000), D2 := ((392443747 : Rat) / 2560000000), D3 := ((11867041130022321501 : Rat) / 50000000000000000000), D4 := ((3798539136718749 : Rat) / 10000000000000000), LB := ((4987237565564351 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2463828861 : Rat) / 1024000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((155496579 : Rat) / 1024000000), D3 := ((11794730592912946501 : Rat) / 50000000000000000000), D4 := ((1892038514648437 : Rat) / 5000000000000000), LB := ((5971744674236959 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((24660502407 : Rat) / 10240000000), D0 := ((24660502407 : Rat) / 10240000000), D1 := ((6049557383 : Rat) / 10240000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((11722420055803571501 : Rat) / 50000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((11707653402892731 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24660502407 : Rat) / 10240000000), R := ((12333953503 : Rat) / 5120000000), D0 := ((12333953503 : Rat) / 5120000000), D1 := ((3028480991 : Rat) / 5120000000), D2 := ((1532751993 : Rat) / 10240000000), D3 := ((11686264787248884001 : Rat) / 50000000000000000000), D4 := ((7524767736328123 : Rat) / 20000000000000000), LB := ((658987371660669 : Rat) / 625000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12333953503 : Rat) / 5120000000), R := ((4935062321 : Rat) / 2048000000), D0 := ((4935062321 : Rat) / 2048000000), D1 := ((6064366581 : Rat) / 10240000000), D2 := ((762673697 : Rat) / 5120000000), D3 := ((11650109518694196501 : Rat) / 50000000000000000000), D4 := ((938788203613281 : Rat) / 2500000000000000), LB := ((23555804050647 : Rat) / 25000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4935062321 : Rat) / 2048000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((303588559 : Rat) / 2048000000), D3 := ((11613954250139509001 : Rat) / 50000000000000000000), D4 := ((7495843521484373 : Rat) / 20000000000000000), LB := ((8343381430828689 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((24690120803 : Rat) / 10240000000), D0 := ((24690120803 : Rat) / 10240000000), D1 := ((6079175779 : Rat) / 10240000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11577798981584821501 : Rat) / 50000000000000000000), D4 := ((3740690707031249 : Rat) / 10000000000000000), LB := ((7307136153444083 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24690120803 : Rat) / 10240000000), R := ((12348762701 : Rat) / 5120000000), D0 := ((12348762701 : Rat) / 5120000000), D1 := ((3043290189 : Rat) / 5120000000), D2 := ((1503133597 : Rat) / 10240000000), D3 := ((11541643713030134001 : Rat) / 50000000000000000000), D4 := ((7466919306640623 : Rat) / 20000000000000000), LB := ((1262749270335567 : Rat) / 2000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12348762701 : Rat) / 5120000000), R := ((24704930001 : Rat) / 10240000000), D0 := ((24704930001 : Rat) / 10240000000), D1 := ((6093984977 : Rat) / 10240000000), D2 := ((747864499 : Rat) / 5120000000), D3 := ((11505488444475446501 : Rat) / 50000000000000000000), D4 := ((1863114299804687 : Rat) / 5000000000000000), LB := ((670421799743217 : Rat) / 1250000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24704930001 : Rat) / 10240000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((1488324399 : Rat) / 10240000000), D3 := ((11469333175920759001 : Rat) / 50000000000000000000), D4 := ((7437995091796873 : Rat) / 20000000000000000), LB := ((4456184494243537 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((24719739199 : Rat) / 10240000000), D0 := ((24719739199 : Rat) / 10240000000), D1 := ((244351767 : Rat) / 409600000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11433177907366071501 : Rat) / 50000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((1796171346631903 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24719739199 : Rat) / 10240000000), R := ((12363571899 : Rat) / 5120000000), D0 := ((12363571899 : Rat) / 5120000000), D1 := ((3058099387 : Rat) / 5120000000), D2 := ((1473515201 : Rat) / 10240000000), D3 := ((11397022638811384001 : Rat) / 50000000000000000000), D4 := ((7409070876953123 : Rat) / 20000000000000000), LB := ((27720169198088007 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12363571899 : Rat) / 5120000000), R := ((24734548397 : Rat) / 10240000000), D0 := ((24734548397 : Rat) / 10240000000), D1 := ((6123603373 : Rat) / 10240000000), D2 := ((733055301 : Rat) / 5120000000), D3 := ((11360867370256696501 : Rat) / 50000000000000000000), D4 := ((462163048095703 : Rat) / 1250000000000000), LB := ((3990753985188833 : Rat) / 20000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24734548397 : Rat) / 10240000000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((1458706003 : Rat) / 10240000000), D3 := ((11324712101702009001 : Rat) / 50000000000000000000), D4 := ((7380146662109373 : Rat) / 20000000000000000), LB := ((3156486615878487 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((4949871519 : Rat) / 2048000000), D0 := ((4949871519 : Rat) / 2048000000), D1 := ((6138412571 : Rat) / 10240000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11288556833147321501 : Rat) / 50000000000000000000), D4 := ((3682842277343749 : Rat) / 10000000000000000), LB := ((1147687108686013 : Rat) / 20000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4949871519 : Rat) / 2048000000), R := ((49506119789 : Rat) / 20480000000), D0 := ((49506119789 : Rat) / 20480000000), D1 := ((12284229741 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 2048000000), D3 := ((11252401564592634001 : Rat) / 50000000000000000000), D4 := ((7351222447265623 : Rat) / 20000000000000000), LB := ((5734188534845669 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49506119789 : Rat) / 20480000000), R := ((12378381097 : Rat) / 5120000000), D0 := ((12378381097 : Rat) / 5120000000), D1 := ((614581717 : Rat) / 1024000000), D2 := ((2880389011 : Rat) / 20480000000), D3 := ((11234323930315290251 : Rat) / 50000000000000000000), D4 := ((14687982787109371 : Rat) / 40000000000000000), LB := ((5425730614650043 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12378381097 : Rat) / 5120000000), R := ((49520928987 : Rat) / 20480000000), D0 := ((49520928987 : Rat) / 20480000000), D1 := ((12299038939 : Rat) / 20480000000), D2 := ((718246103 : Rat) / 5120000000), D3 := ((11216246296037946501 : Rat) / 50000000000000000000), D4 := ((1834190084960937 : Rat) / 5000000000000000), LB := ((10256788742041 : Rat) / 20000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49520928987 : Rat) / 20480000000), R := ((24764166793 : Rat) / 10240000000), D0 := ((24764166793 : Rat) / 10240000000), D1 := ((6153221769 : Rat) / 10240000000), D2 := ((2865579813 : Rat) / 20480000000), D3 := ((11198168661760602751 : Rat) / 50000000000000000000), D4 := ((14659058572265621 : Rat) / 40000000000000000), LB := ((242110115732809 : Rat) / 500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24764166793 : Rat) / 10240000000), R := ((9907147637 : Rat) / 4096000000), D0 := ((9907147637 : Rat) / 4096000000), D1 := ((12313848137 : Rat) / 20480000000), D2 := ((1429087607 : Rat) / 10240000000), D3 := ((11180091027483259001 : Rat) / 50000000000000000000), D4 := ((7322298232421873 : Rat) / 20000000000000000), LB := ((45671770833106973 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9907147637 : Rat) / 4096000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((570154123 : Rat) / 4096000000), D3 := ((11162013393205915251 : Rat) / 50000000000000000000), D4 := ((14630134357421871 : Rat) / 40000000000000000), LB := ((2151670721242463 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((49550547383 : Rat) / 20480000000), D0 := ((49550547383 : Rat) / 20480000000), D1 := ((2465731467 : Rat) / 4096000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11143935758928571501 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((4050718286269517 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49550547383 : Rat) / 20480000000), R := ((24778975991 : Rat) / 10240000000), D0 := ((24778975991 : Rat) / 10240000000), D1 := ((6168030967 : Rat) / 10240000000), D2 := ((2835961417 : Rat) / 20480000000), D3 := ((11125858124651227751 : Rat) / 50000000000000000000), D4 := ((14601210142578121 : Rat) / 40000000000000000), LB := ((1904665319019741 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24778975991 : Rat) / 10240000000), R := ((49565356581 : Rat) / 20480000000), D0 := ((49565356581 : Rat) / 20480000000), D1 := ((12343466533 : Rat) / 20480000000), D2 := ((1414278409 : Rat) / 10240000000), D3 := ((11107780490373884001 : Rat) / 50000000000000000000), D4 := ((7293374017578123 : Rat) / 20000000000000000), LB := ((17896008256498147 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49565356581 : Rat) / 20480000000), R := ((2478638059 : Rat) / 1024000000), D0 := ((2478638059 : Rat) / 1024000000), D1 := ((3087717783 : Rat) / 5120000000), D2 := ((2821152219 : Rat) / 20480000000), D3 := ((11089702856096540251 : Rat) / 50000000000000000000), D4 := ((14572285927734371 : Rat) / 40000000000000000), LB := ((8400886526040499 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2478638059 : Rat) / 1024000000), R := ((49580165779 : Rat) / 20480000000), D0 := ((49580165779 : Rat) / 20480000000), D1 := ((12358275731 : Rat) / 20480000000), D2 := ((140687381 : Rat) / 1024000000), D3 := ((11071625221819196501 : Rat) / 50000000000000000000), D4 := ((909863988769531 : Rat) / 2500000000000000), LB := ((1576406465727681 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49580165779 : Rat) / 20480000000), R := ((24793785189 : Rat) / 10240000000), D0 := ((24793785189 : Rat) / 10240000000), D1 := ((1236568033 : Rat) / 2048000000), D2 := ((2806343021 : Rat) / 20480000000), D3 := ((11053547587541852751 : Rat) / 50000000000000000000), D4 := ((14543361712890621 : Rat) / 40000000000000000), LB := ((14783000814616587 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24793785189 : Rat) / 10240000000), R := ((49594974977 : Rat) / 20480000000), D0 := ((49594974977 : Rat) / 20480000000), D1 := ((12373084929 : Rat) / 20480000000), D2 := ((1399469211 : Rat) / 10240000000), D3 := ((11035469953264509001 : Rat) / 50000000000000000000), D4 := ((7264449802734373 : Rat) / 20000000000000000), LB := ((5543479973275367 : Rat) / 20000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49594974977 : Rat) / 20480000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((2791533823 : Rat) / 20480000000), D3 := ((11017392318987165251 : Rat) / 50000000000000000000), D4 := ((14514437498046871 : Rat) / 40000000000000000), LB := ((6495640546193629 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((1984391367 : Rat) / 819200000), D0 := ((1984391367 : Rat) / 819200000), D1 := ((12387894127 : Rat) / 20480000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((10999314684709821501 : Rat) / 50000000000000000000), D4 := ((3624993847656249 : Rat) / 10000000000000000), LB := ((6090432023132461 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1984391367 : Rat) / 819200000), R := ((24808594387 : Rat) / 10240000000), D0 := ((24808594387 : Rat) / 10240000000), D1 := ((6197649363 : Rat) / 10240000000), D2 := ((22213797 : Rat) / 163840000), D3 := ((10981237050432477751 : Rat) / 50000000000000000000), D4 := ((14485513283203121 : Rat) / 40000000000000000), LB := ((22855138454795643 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24808594387 : Rat) / 10240000000), R := ((49624593373 : Rat) / 20480000000), D0 := ((49624593373 : Rat) / 20480000000), D1 := ((496108133 : Rat) / 819200000), D2 := ((1384660013 : Rat) / 10240000000), D3 := ((10963159416155134001 : Rat) / 50000000000000000000), D4 := ((7235525587890623 : Rat) / 20000000000000000), LB := ((10731517751228631 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49624593373 : Rat) / 20480000000), R := ((12407999493 : Rat) / 5120000000), D0 := ((12407999493 : Rat) / 5120000000), D1 := ((3102526981 : Rat) / 5120000000), D2 := ((2761915427 : Rat) / 20480000000), D3 := ((10945081781877790251 : Rat) / 50000000000000000000), D4 := ((14456589068359371 : Rat) / 40000000000000000), LB := ((2523207855053243 : Rat) / 12500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12407999493 : Rat) / 5120000000), R := ((49639402571 : Rat) / 20480000000), D0 := ((49639402571 : Rat) / 20480000000), D1 := ((12417512523 : Rat) / 20480000000), D2 := ((688627707 : Rat) / 5120000000), D3 := ((10927004147600446501 : Rat) / 50000000000000000000), D4 := ((1805265870117187 : Rat) / 5000000000000000), LB := ((1902326545602101 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49639402571 : Rat) / 20480000000), R := ((4964680717 : Rat) / 2048000000), D0 := ((4964680717 : Rat) / 2048000000), D1 := ((6212458561 : Rat) / 10240000000), D2 := ((2747106229 : Rat) / 20480000000), D3 := ((10908926513323102751 : Rat) / 50000000000000000000), D4 := ((14427664853515621 : Rat) / 40000000000000000), LB := ((3595217945519813 : Rat) / 20000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4964680717 : Rat) / 2048000000), R := ((49654211769 : Rat) / 20480000000), D0 := ((49654211769 : Rat) / 20480000000), D1 := ((12432321721 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2048000000), D3 := ((10890848879045759001 : Rat) / 50000000000000000000), D4 := ((7206601373046873 : Rat) / 20000000000000000), LB := ((1704438343292647 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49654211769 : Rat) / 20480000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((2732297031 : Rat) / 20480000000), D3 := ((10872771244768415251 : Rat) / 50000000000000000000), D4 := ((14398740638671871 : Rat) / 40000000000000000), LB := ((16228395758219327 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((49669020967 : Rat) / 20480000000), D0 := ((49669020967 : Rat) / 20480000000), D1 := ((12447130919 : Rat) / 20480000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((10854693610491071501 : Rat) / 50000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((7764188653231613 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49669020967 : Rat) / 20480000000), R := ((24838212783 : Rat) / 10240000000), D0 := ((24838212783 : Rat) / 10240000000), D1 := ((6227267759 : Rat) / 10240000000), D2 := ((2717487833 : Rat) / 20480000000), D3 := ((10836615976213727751 : Rat) / 50000000000000000000), D4 := ((14369816423828121 : Rat) / 40000000000000000), LB := ((14944580106608651 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24838212783 : Rat) / 10240000000), R := ((9936766033 : Rat) / 4096000000), D0 := ((9936766033 : Rat) / 4096000000), D1 := ((12461940117 : Rat) / 20480000000), D2 := ((1355041617 : Rat) / 10240000000), D3 := ((10818538341936384001 : Rat) / 50000000000000000000), D4 := ((7177677158203123 : Rat) / 20000000000000000), LB := ((3619314405552479 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9936766033 : Rat) / 4096000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((540535727 : Rat) / 4096000000), D3 := ((10800460707659040251 : Rat) / 50000000000000000000), D4 := ((14340892208984371 : Rat) / 40000000000000000), LB := ((1765833095041143 : Rat) / 12500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((49698639363 : Rat) / 20480000000), D0 := ((49698639363 : Rat) / 20480000000), D1 := ((2495349863 : Rat) / 4096000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((10782383073381696501 : Rat) / 50000000000000000000), D4 := ((111925235168457 : Rat) / 312500000000000), LB := ((3473264470251619 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49698639363 : Rat) / 20480000000), R := ((24853021981 : Rat) / 10240000000), D0 := ((24853021981 : Rat) / 10240000000), D1 := ((6242076957 : Rat) / 10240000000), D2 := ((2687869437 : Rat) / 20480000000), D3 := ((10764305439104352751 : Rat) / 50000000000000000000), D4 := ((14311967994140621 : Rat) / 40000000000000000), LB := ((344417370144387 : Rat) / 2500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24853021981 : Rat) / 10240000000), R := ((49713448561 : Rat) / 20480000000), D0 := ((49713448561 : Rat) / 20480000000), D1 := ((12491558513 : Rat) / 20480000000), D2 := ((1340232419 : Rat) / 10240000000), D3 := ((10746227804827009001 : Rat) / 50000000000000000000), D4 := ((7148752943359373 : Rat) / 20000000000000000), LB := ((1377783482736511 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49713448561 : Rat) / 20480000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((2673060239 : Rat) / 20480000000), D3 := ((10728150170549665251 : Rat) / 50000000000000000000), D4 := ((14283043779296871 : Rat) / 40000000000000000), LB := ((694836935932891 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((49728257759 : Rat) / 20480000000), D0 := ((49728257759 : Rat) / 20480000000), D1 := ((12506367711 : Rat) / 20480000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((10710072536272321501 : Rat) / 50000000000000000000), D4 := ((3567145417968749 : Rat) / 10000000000000000), LB := ((565346749685669 : Rat) / 4000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49728257759 : Rat) / 20480000000), R := ((24867831179 : Rat) / 10240000000), D0 := ((24867831179 : Rat) / 10240000000), D1 := ((1251377231 : Rat) / 2048000000), D2 := ((2658251041 : Rat) / 20480000000), D3 := ((10691994901994977751 : Rat) / 50000000000000000000), D4 := ((14254119564453121 : Rat) / 40000000000000000), LB := ((7244444329661953 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24867831179 : Rat) / 10240000000), R := ((49743066957 : Rat) / 20480000000), D0 := ((49743066957 : Rat) / 20480000000), D1 := ((12521176909 : Rat) / 20480000000), D2 := ((1325423221 : Rat) / 10240000000), D3 := ((10673917267717634001 : Rat) / 50000000000000000000), D4 := ((7119828728515623 : Rat) / 20000000000000000), LB := ((1870332967530107 : Rat) / 12500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49743066957 : Rat) / 20480000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((2643441843 : Rat) / 20480000000), D3 := ((10655839633440290251 : Rat) / 50000000000000000000), D4 := ((14225195349609371 : Rat) / 40000000000000000), LB := ((3111052154675109 : Rat) / 20000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((9951575231 : Rat) / 4096000000), D0 := ((9951575231 : Rat) / 4096000000), D1 := ((12535986107 : Rat) / 20480000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((10637761999162946501 : Rat) / 50000000000000000000), D4 := ((1776341655273437 : Rat) / 5000000000000000), LB := ((650677922976739 : Rat) / 4000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9951575231 : Rat) / 4096000000), R := ((24882640377 : Rat) / 10240000000), D0 := ((24882640377 : Rat) / 10240000000), D1 := ((6271695353 : Rat) / 10240000000), D2 := ((525726529 : Rat) / 4096000000), D3 := ((10619684364885602751 : Rat) / 50000000000000000000), D4 := ((14196271134765621 : Rat) / 40000000000000000), LB := ((3419599099444559 : Rat) / 20000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24882640377 : Rat) / 10240000000), R := ((49772685353 : Rat) / 20480000000), D0 := ((49772685353 : Rat) / 20480000000), D1 := ((2510159061 : Rat) / 4096000000), D2 := ((1310614023 : Rat) / 10240000000), D3 := ((10601606730608259001 : Rat) / 50000000000000000000), D4 := ((7090904513671873 : Rat) / 20000000000000000), LB := ((4512168610641687 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49772685353 : Rat) / 20480000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((2613823447 : Rat) / 20480000000), D3 := ((10583529096330915251 : Rat) / 50000000000000000000), D4 := ((14167346919921871 : Rat) / 40000000000000000), LB := ((4779814467209889 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((49787494551 : Rat) / 20480000000), D0 := ((49787494551 : Rat) / 20480000000), D1 := ((12565604503 : Rat) / 20480000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10565451462053571501 : Rat) / 50000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((10155010150892513 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49787494551 : Rat) / 20480000000), R := ((995897983 : Rat) / 409600000), D0 := ((995897983 : Rat) / 409600000), D1 := ((6286504551 : Rat) / 10240000000), D2 := ((2599014249 : Rat) / 20480000000), D3 := ((10547373827776227751 : Rat) / 50000000000000000000), D4 := ((14138422705078121 : Rat) / 40000000000000000), LB := ((21621237844333951 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((995897983 : Rat) / 409600000), R := ((49802303749 : Rat) / 20480000000), D0 := ((49802303749 : Rat) / 20480000000), D1 := ((12580413701 : Rat) / 20480000000), D2 := ((51832193 : Rat) / 409600000), D3 := ((10529296193498884001 : Rat) / 50000000000000000000), D4 := ((7061980298828123 : Rat) / 20000000000000000), LB := ((11526594093611703 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49802303749 : Rat) / 20480000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((2584205051 : Rat) / 20480000000), D3 := ((10511218559221540251 : Rat) / 50000000000000000000), D4 := ((14109498490234371 : Rat) / 40000000000000000), LB := ((12303075309547107 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((49817112947 : Rat) / 20480000000), D0 := ((49817112947 : Rat) / 20480000000), D1 := ((12595222899 : Rat) / 20480000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10493140924944196501 : Rat) / 50000000000000000000), D4 := ((880939773925781 : Rat) / 2500000000000000), LB := ((657010150915821 : Rat) / 2500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49817112947 : Rat) / 20480000000), R := ((24912258773 : Rat) / 10240000000), D0 := ((24912258773 : Rat) / 10240000000), D1 := ((6301313749 : Rat) / 10240000000), D2 := ((2569395853 : Rat) / 20480000000), D3 := ((10475063290666852751 : Rat) / 50000000000000000000), D4 := ((14080574275390621 : Rat) / 40000000000000000), LB := ((2807623695554873 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24912258773 : Rat) / 10240000000), R := ((9966384429 : Rat) / 4096000000), D0 := ((9966384429 : Rat) / 4096000000), D1 := ((12610032097 : Rat) / 20480000000), D2 := ((1280995627 : Rat) / 10240000000), D3 := ((10456985656389509001 : Rat) / 50000000000000000000), D4 := ((7033056083984373 : Rat) / 20000000000000000), LB := ((3749240940042857 : Rat) / 12500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9966384429 : Rat) / 4096000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((510917331 : Rat) / 4096000000), D3 := ((10438908022112165251 : Rat) / 50000000000000000000), D4 := ((14051650060546871 : Rat) / 40000000000000000), LB := ((6406752703165819 : Rat) / 20000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((49846731343 : Rat) / 20480000000), D0 := ((49846731343 : Rat) / 20480000000), D1 := ((2524968259 : Rat) / 4096000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10420830387834821501 : Rat) / 50000000000000000000), D4 := ((3509296988281249 : Rat) / 10000000000000000), LB := ((34196032377059593 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49846731343 : Rat) / 20480000000), R := ((24927067971 : Rat) / 10240000000), D0 := ((24927067971 : Rat) / 10240000000), D1 := ((6316122947 : Rat) / 10240000000), D2 := ((2539777457 : Rat) / 20480000000), D3 := ((10402752753557477751 : Rat) / 50000000000000000000), D4 := ((14022725845703121 : Rat) / 40000000000000000), LB := ((364810232007573 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24927067971 : Rat) / 10240000000), R := ((49861540541 : Rat) / 20480000000), D0 := ((49861540541 : Rat) / 20480000000), D1 := ((12639650493 : Rat) / 20480000000), D2 := ((1266186429 : Rat) / 10240000000), D3 := ((10384675119280134001 : Rat) / 50000000000000000000), D4 := ((7004131869140623 : Rat) / 20000000000000000), LB := ((9722256688952241 : Rat) / 25000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49861540541 : Rat) / 20480000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((2524968259 : Rat) / 20480000000), D3 := ((10366597485002790251 : Rat) / 50000000000000000000), D4 := ((13993801630859371 : Rat) / 40000000000000000), LB := ((41420335494518623 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((49876349739 : Rat) / 20480000000), D0 := ((49876349739 : Rat) / 20480000000), D1 := ((12654459691 : Rat) / 20480000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10348519850725446501 : Rat) / 50000000000000000000), D4 := ((1747417440429687 : Rat) / 5000000000000000), LB := ((44075243563582167 : Rat) / 100000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49876349739 : Rat) / 20480000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((2510159061 : Rat) / 20480000000), D3 := ((10330442216448102751 : Rat) / 50000000000000000000), D4 := ((13964877416015621 : Rat) / 40000000000000000), LB := ((585675585191691 : Rat) / 1250000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((49891158937 : Rat) / 20480000000), D0 := ((49891158937 : Rat) / 20480000000), D1 := ((12669268889 : Rat) / 20480000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((10312364582170759001 : Rat) / 50000000000000000000), D4 := ((6975207654296873 : Rat) / 20000000000000000), LB := ((4975704281900833 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49891158937 : Rat) / 20480000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((2495349863 : Rat) / 20480000000), D3 := ((10294286947893415251 : Rat) / 50000000000000000000), D4 := ((13935953201171871 : Rat) / 40000000000000000), LB := ((659806635903877 : Rat) / 1250000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((9981193627 : Rat) / 4096000000), D0 := ((9981193627 : Rat) / 4096000000), D1 := ((12684078087 : Rat) / 20480000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10276209313616071501 : Rat) / 50000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((2796840600632691 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9981193627 : Rat) / 4096000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((496108133 : Rat) / 4096000000), D3 := ((10258131679338727751 : Rat) / 50000000000000000000), D4 := ((13907028986328121 : Rat) / 40000000000000000), LB := ((1480354725725483 : Rat) / 2500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((10240054045061384001 : Rat) / 50000000000000000000), D4 := ((6946283439453123 : Rat) / 20000000000000000), LB := ((609900384653389 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((4994299113 : Rat) / 2048000000), D0 := ((4994299113 : Rat) / 2048000000), D1 := ((6360550541 : Rat) / 10240000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10203898776506696501 : Rat) / 50000000000000000000), D4 := ((433238833251953 : Rat) / 1250000000000000), LB := ((266698568232443 : Rat) / 2000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4994299113 : Rat) / 2048000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((244351767 : Rat) / 2048000000), D3 := ((10167743507952009001 : Rat) / 50000000000000000000), D4 := ((6917359224609373 : Rat) / 20000000000000000), LB := ((1317252398979913 : Rat) / 6250000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((24986304763 : Rat) / 10240000000), D0 := ((24986304763 : Rat) / 10240000000), D1 := ((6375359739 : Rat) / 10240000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10131588239397321501 : Rat) / 50000000000000000000), D4 := ((3451448558593749 : Rat) / 10000000000000000), LB := ((14662417633616587 : Rat) / 50000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24986304763 : Rat) / 10240000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((1206949637 : Rat) / 10240000000), D3 := ((10095432970842634001 : Rat) / 50000000000000000000), D4 := ((6888435009765623 : Rat) / 20000000000000000), LB := ((1904192496769777 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((25001113961 : Rat) / 10240000000), D0 := ((25001113961 : Rat) / 10240000000), D1 := ((6390168937 : Rat) / 10240000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((10059277702287946501 : Rat) / 50000000000000000000), D4 := ((1718493225585937 : Rat) / 5000000000000000), LB := ((4735564303068457 : Rat) / 10000000000000000000) }
]

def block411RightChunk000L : Rat := ((21711658482142857187 : Rat) / 12500000000000000000)
def block411RightChunk000R : Rat := ((25001113961 : Rat) / 10240000000)

def block411RightChunk000Certificate : Bool :=
  allBoxesValid block411RightChunk000 &&
  coversFromBool block411RightChunk000 block411RightChunk000L block411RightChunk000R

theorem block411RightChunk000Certificate_eq_true :
    block411RightChunk000Certificate = true := by
  native_decide

def block411RightChunk001 : List RatBox := [
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25001113961 : Rat) / 10240000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((1192140439 : Rat) / 10240000000), D3 := ((10023122433733259001 : Rat) / 50000000000000000000), D4 := ((6859510794921873 : Rat) / 20000000000000000), LB := ((357142533578287 : Rat) / 625000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((25015923159 : Rat) / 10240000000), D0 := ((25015923159 : Rat) / 10240000000), D1 := ((1280995627 : Rat) / 2048000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((9986967165178571501 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((6744795837249351 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25015923159 : Rat) / 10240000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((1177331241 : Rat) / 10240000000), D3 := ((9950811896623884001 : Rat) / 50000000000000000000), D4 := ((6830586580078123 : Rat) / 20000000000000000), LB := ((7827375445652041 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((25030732357 : Rat) / 10240000000), D0 := ((25030732357 : Rat) / 10240000000), D1 := ((6419787333 : Rat) / 10240000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((9914656628069196501 : Rat) / 50000000000000000000), D4 := ((852015559082031 : Rat) / 2500000000000000), LB := ((8962287749559039 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((25030732357 : Rat) / 10240000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((1162522043 : Rat) / 10240000000), D3 := ((9878501359514509001 : Rat) / 50000000000000000000), D4 := ((6801662365234373 : Rat) / 20000000000000000), LB := ((10149804324374873 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((9842346090959821501 : Rat) / 50000000000000000000), D4 := ((3393600128906249 : Rat) / 10000000000000000), LB := ((5239389676565953 : Rat) / 250000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((9770035553850446501 : Rat) / 50000000000000000000), D4 := ((1689569010742187 : Rat) / 5000000000000000), LB := ((717685246090019 : Rat) / 2500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((9697725016741071501 : Rat) / 50000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((1149342949762877 : Rat) / 2000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((501651291 : Rat) / 204800000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 204800000), D3 := ((9625414479631696501 : Rat) / 50000000000000000000), D4 := ((209388362915039 : Rat) / 625000000000000), LB := ((8839817074408479 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((9553103942522321501 : Rat) / 50000000000000000000), D4 := ((3335751699218749 : Rat) / 10000000000000000), LB := ((1215242445478687 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((9480793405412946501 : Rat) / 50000000000000000000), D4 := ((1660644795898437 : Rat) / 5000000000000000), LB := ((7843485661918753 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9408482868303571501 : Rat) / 50000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((19445951759215763 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((9336172331194196501 : Rat) / 50000000000000000000), D4 := ((823091344238281 : Rat) / 2500000000000000), LB := ((2343192125145721 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9263861794084821501 : Rat) / 50000000000000000000), D4 := ((3277903269531249 : Rat) / 10000000000000000), LB := ((2820601931213043 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9119240719866071501 : Rat) / 50000000000000000000), D4 := ((3248979054687499 : Rat) / 10000000000000000), LB := ((14851284351728583 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((8974619645647321501 : Rat) / 50000000000000000000), D4 := ((3220054839843749 : Rat) / 10000000000000000), LB := ((2501222494748101 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((8829998571428571501 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((18073733091072547 : Rat) / 5000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((8685377497209821501 : Rat) / 50000000000000000000), D4 := ((3162206410156249 : Rat) / 10000000000000000), LB := ((4828166383533047 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((632617563 : Rat) / 256000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8540756422991071501 : Rat) / 50000000000000000000), D4 := ((3133282195312499 : Rat) / 10000000000000000), LB := ((916113225771821 : Rat) / 500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8251514274553571501 : Rat) / 50000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((4812716623688651 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((7962272126116071501 : Rat) / 50000000000000000000), D4 := ((3017585335937499 : Rat) / 10000000000000000), LB := ((4118728616995443 : Rat) / 500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((7673029977678571501 : Rat) / 50000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((1492030512730691 : Rat) / 400000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7094545680803571501 : Rat) / 50000000000000000000), D4 := ((2844040046874999 : Rat) / 10000000000000000), LB := ((6583551578888479 : Rat) / 500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6516061383928571501 : Rat) / 50000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((8684856343343317 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5359092790178571501 : Rat) / 50000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((1637992399926409 : Rat) / 40000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((132098874196428571501 : Rat) / 50000000000000000000), D0 := ((132098874196428571501 : Rat) / 50000000000000000000), D1 := ((41225119196428571501 : Rat) / 50000000000000000000), D2 := ((4202124196428571501 : Rat) / 50000000000000000000), D3 := ((4202124196428571501 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((1027659514584603 : Rat) / 100000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((132098874196428571501 : Rat) / 50000000000000000000), R := ((13447764133928571441 : Rat) / 5000000000000000000), D0 := ((13447764133928571441 : Rat) / 5000000000000000000), D1 := ((4360388633928571441 : Rat) / 5000000000000000000), D2 := ((658089133928571441 : Rat) / 5000000000000000000), D3 := ((2378767142857142909 : Rat) / 50000000000000000000), D4 := ((7125654553571423499 : Rat) / 50000000000000000000), LB := ((314214287050367 : Rat) / 2000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13447764133928571441 : Rat) / 5000000000000000000), R := ((271334049821428571729 : Rat) / 100000000000000000000), D0 := ((271334049821428571729 : Rat) / 100000000000000000000), D1 := ((89586539821428571729 : Rat) / 100000000000000000000), D2 := ((15540549821428571729 : Rat) / 100000000000000000000), D3 := ((7136301428571428727 : Rat) / 100000000000000000000), D4 := ((474688741071428059 : Rat) / 5000000000000000000), LB := ((12201601434826459 : Rat) / 250000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((271334049821428571729 : Rat) / 100000000000000000000), R := ((545046866785714286367 : Rat) / 200000000000000000000), D0 := ((545046866785714286367 : Rat) / 200000000000000000000), D1 := ((181551846785714286367 : Rat) / 200000000000000000000), D2 := ((33459866785714286367 : Rat) / 200000000000000000000), D3 := ((16651370000000000363 : Rat) / 200000000000000000000), D4 := ((7115007678571418271 : Rat) / 100000000000000000000), LB := ((1644073042311167 : Rat) / 100000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((545046866785714286367 : Rat) / 200000000000000000000), R := ((1092472500714285715643 : Rat) / 400000000000000000000), D0 := ((1092472500714285715643 : Rat) / 400000000000000000000), D1 := ((365482460714285715643 : Rat) / 400000000000000000000), D2 := ((69298500714285715643 : Rat) / 400000000000000000000), D3 := ((7136301428571428727 : Rat) / 80000000000000000000), D4 := ((11851248214285693633 : Rat) / 200000000000000000000), LB := ((1216963606579391 : Rat) / 200000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1092472500714285715643 : Rat) / 400000000000000000000), R := ((437464753714285714839 : Rat) / 160000000000000000000), D0 := ((437464753714285714839 : Rat) / 160000000000000000000), D1 := ((146668737714285714839 : Rat) / 160000000000000000000), D2 := ((28195153714285714839 : Rat) / 160000000000000000000), D3 := ((73741781428571430179 : Rat) / 800000000000000000000), D4 := ((21323729285714244357 : Rat) / 400000000000000000000), LB := ((26855194434292073 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((437464753714285714839 : Rat) / 160000000000000000000), R := ((4377026304285714291299 : Rat) / 1600000000000000000000), D0 := ((4377026304285714291299 : Rat) / 1600000000000000000000), D1 := ((1469066144285714291299 : Rat) / 1600000000000000000000), D2 := ((284330304285714291299 : Rat) / 1600000000000000000000), D3 := ((149862330000000003267 : Rat) / 1600000000000000000000), D4 := ((8053738285714269161 : Rat) / 160000000000000000000), LB := ((752496922776319 : Rat) / 500000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4377026304285714291299 : Rat) / 1600000000000000000000), R := ((8756431375714285725507 : Rat) / 3200000000000000000000), D0 := ((8756431375714285725507 : Rat) / 3200000000000000000000), D1 := ((2940511055714285725507 : Rat) / 3200000000000000000000), D2 := ((571039375714285725507 : Rat) / 3200000000000000000000), D3 := ((302103427142857149443 : Rat) / 3200000000000000000000), D4 := ((78158615714285548701 : Rat) / 1600000000000000000000), LB := ((10573806540464803 : Rat) / 10000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8756431375714285725507 : Rat) / 3200000000000000000000), R := ((17515241518571428593923 : Rat) / 6400000000000000000000), D0 := ((17515241518571428593923 : Rat) / 6400000000000000000000), D1 := ((5883400878571428593923 : Rat) / 6400000000000000000000), D2 := ((1144457518571428593923 : Rat) / 6400000000000000000000), D3 := ((121317124285714288359 : Rat) / 1280000000000000000000), D4 := ((153938464285713954493 : Rat) / 3200000000000000000000), LB := ((871147704886277 : Rat) / 1000000000000000000) },
  { w1 := ((715129534312677 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((179540304732359 : Rat) / 625000000000000), w4 := ((2229490332473899 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132098874196428571501 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17515241518571428593923 : Rat) / 6400000000000000000000), R := ((136856408482142857319 : Rat) / 50000000000000000000), D0 := ((136856408482142857319 : Rat) / 50000000000000000000), D1 := ((45982653482142857319 : Rat) / 50000000000000000000), D2 := ((8959658482142857319 : Rat) / 50000000000000000000), D3 := ((2378767142857142909 : Rat) / 25000000000000000000), D4 := ((305498161428570766077 : Rat) / 6400000000000000000000), LB := ((1706124745773363 : Rat) / 125000000000000000000) }
]

def block411RightChunk001L : Rat := ((25001113961 : Rat) / 10240000000)
def block411RightChunk001R : Rat := ((136856408482142857319 : Rat) / 50000000000000000000)

def block411RightChunk001Certificate : Bool :=
  allBoxesValid block411RightChunk001 &&
  coversFromBool block411RightChunk001 block411RightChunk001L block411RightChunk001R

theorem block411RightChunk001Certificate_eq_true :
    block411RightChunk001Certificate = true := by
  native_decide

def block411RightChainCertificate : Bool :=
  decide (
    block411RightL = ((21711658482142857187 : Rat) / 12500000000000000000) /\
    ((25001113961 : Rat) / 10240000000) = ((25001113961 : Rat) / 10240000000) /\
    ((136856408482142857319 : Rat) / 50000000000000000000) = block411RightR)

theorem block411RightChainCertificate_eq_true :
    block411RightChainCertificate = true := by
  native_decide

def block411LeftBoxCount : Nat := boxCount block411LeftBoxes
def block411RightBoxCount : Nat := 135

def block411_rational_certificate : Prop :=
    block411LeftCertificate = true /\
    block411RightChainCertificate = true /\
    block411RightChunk000Certificate = true /\
    block411RightChunk001Certificate = true

theorem block411_rational_certificate_proof :
    block411_rational_certificate := by
  exact ⟨block411LeftCertificate_eq_true, block411RightChainCertificate_eq_true, block411RightChunk000Certificate_eq_true, block411RightChunk001Certificate_eq_true⟩

end Block411
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block411

open Set

def block411W1 : Rat := ((715129534312677 : Rat) / 1000000000000000)
def block411W2 : Rat := (0 : Rat)
def block411W3 : Rat := ((179540304732359 : Rat) / 625000000000000)
def block411W4 : Rat := ((2229490332473899 : Rat) / 25000000000000000)
def block411S1 : Rat := ((18174751 : Rat) / 10000000)
def block411S2 : Rat := ((511587 : Rat) / 200000)
def block411S3 : Rat := ((132098874196428571501 : Rat) / 50000000000000000000)
def block411S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block411V (y : ℝ) : ℝ :=
  ratPotential block411W1 block411W2 block411W3 block411W4 block411S1 block411S2 block411S3 block411S4 y

def block411LeftParamsCertificate : Bool :=
  allBoxesSameParams block411LeftBoxes block411W1 block411W2 block411W3 block411W4 block411S1 block411S2 block411S3 block411S4

theorem block411LeftParamsCertificate_eq_true :
    block411LeftParamsCertificate = true := by
  native_decide

theorem block411_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block411LeftL : ℝ) (block411LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block411S1 : ℝ))
    (hy2ne : y ≠ (block411S2 : ℝ))
    (hy3ne : y ≠ (block411S3 : ℝ))
    (hy4ne : y ≠ (block411S4 : ℝ)) :
    0 < block411V y := by
  have hcert := block411LeftCertificate_eq_true
  unfold block411LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block411LeftBoxes) (lo := block411LeftL) (hi := block411LeftR)
    (w1 := block411W1) (w2 := block411W2) (w3 := block411W3) (w4 := block411W4)
    (s1 := block411S1) (s2 := block411S2) (s3 := block411S3) (s4 := block411S4)
    hboxes hcover block411LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block411RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block411RightChunk000 block411W1 block411W2 block411W3 block411W4 block411S1 block411S2 block411S3 block411S4

theorem block411RightChunk000ParamsCertificate_eq_true :
    block411RightChunk000ParamsCertificate = true := by
  native_decide

theorem block411_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block411RightChunk000L : ℝ) (block411RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block411S1 : ℝ))
    (hy2ne : y ≠ (block411S2 : ℝ))
    (hy3ne : y ≠ (block411S3 : ℝ))
    (hy4ne : y ≠ (block411S4 : ℝ)) :
    0 < block411V y := by
  have hcert := block411RightChunk000Certificate_eq_true
  unfold block411RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block411RightChunk000) (lo := block411RightChunk000L) (hi := block411RightChunk000R)
    (w1 := block411W1) (w2 := block411W2) (w3 := block411W3) (w4 := block411W4)
    (s1 := block411S1) (s2 := block411S2) (s3 := block411S3) (s4 := block411S4)
    hboxes hcover block411RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block411RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block411RightChunk001 block411W1 block411W2 block411W3 block411W4 block411S1 block411S2 block411S3 block411S4

theorem block411RightChunk001ParamsCertificate_eq_true :
    block411RightChunk001ParamsCertificate = true := by
  native_decide

theorem block411_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block411RightChunk001L : ℝ) (block411RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block411S1 : ℝ))
    (hy2ne : y ≠ (block411S2 : ℝ))
    (hy3ne : y ≠ (block411S3 : ℝ))
    (hy4ne : y ≠ (block411S4 : ℝ)) :
    0 < block411V y := by
  have hcert := block411RightChunk001Certificate_eq_true
  unfold block411RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block411RightChunk001) (lo := block411RightChunk001L) (hi := block411RightChunk001R)
    (w1 := block411W1) (w2 := block411W2) (w3 := block411W3) (w4 := block411W4)
    (s1 := block411S1) (s2 := block411S2) (s3 := block411S3) (s4 := block411S4)
    hboxes hcover block411RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block411_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block411RightL : ℝ) (block411RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block411S1 : ℝ))
    (hy2ne : y ≠ (block411S2 : ℝ))
    (hy3ne : y ≠ (block411S3 : ℝ))
    (hy4ne : y ≠ (block411S4 : ℝ)) :
    0 < block411V y := by
  by_cases h0 : y ≤ (block411RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block411RightChunk000L : ℝ) (block411RightChunk000R : ℝ) := by
      have hL : (block411RightChunk000L : ℝ) = (block411RightL : ℝ) := by
        norm_num [block411RightChunk000L, block411RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block411_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block411RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block411RightChunk001L : ℝ) = (block411RightChunk000R : ℝ) := by
      norm_num [block411RightChunk001L, block411RightChunk000R]
    have hR : (block411RightChunk001R : ℝ) = (block411RightR : ℝ) := by
      norm_num [block411RightChunk001R, block411RightR]
    have hyc : y ∈ Icc (block411RightChunk001L : ℝ) (block411RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block411_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block411_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block411LeftL : ℝ) (block411LeftR : ℝ) →
    y ≠ 0 → y ≠ (block411S1 : ℝ) → y ≠ (block411S2 : ℝ) →
    y ≠ (block411S3 : ℝ) → y ≠ (block411S4 : ℝ) → 0 < block411V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block411RightL : ℝ) (block411RightR : ℝ) →
    y ≠ 0 → y ≠ (block411S1 : ℝ) → y ≠ (block411S2 : ℝ) →
    y ≠ (block411S3 : ℝ) → y ≠ (block411S4 : ℝ) → 0 < block411V y)

theorem block411_reallog_certificate_proof :
    block411_reallog_certificate := by
  exact ⟨block411_left_V_pos, block411_right_V_pos⟩

end Block411
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block411.block411V
#check Erdos1038Lean.M1817475.Block411.block411_left_V_pos
#check Erdos1038Lean.M1817475.Block411.block411_right_V_pos
#check Erdos1038Lean.M1817475.Block411.block411_reallog_certificate_proof
