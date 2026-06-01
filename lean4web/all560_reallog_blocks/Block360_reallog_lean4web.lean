/-
Self-contained Lean4Web paste file.
Block 360 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block360

def block360LeftL : Rat := ((37345136160714285869 : Rat) / 50000000000000000000)
def block360LeftR : Rat := ((933872767857142861 : Rat) / 1250000000000000000)
def block360RightL : Rat := ((87345136160714285869 : Rat) / 50000000000000000000)
def block360RightR : Rat := ((3433872767857142861 : Rat) / 1250000000000000000)

def block360LeftBoxes : List RatBox := [
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37345136160714285869 : Rat) / 50000000000000000000), R := ((933872767857142861 : Rat) / 1250000000000000000), D0 := ((933872767857142861 : Rat) / 1250000000000000000), D1 := ((53528618839285714131 : Rat) / 50000000000000000000), D2 := ((90551613839285714131 : Rat) / 50000000000000000000), D3 := ((47875371249999999937 : Rat) / 25000000000000000000), D4 := ((101273370267857137729 : Rat) / 50000000000000000000), LB := ((3091769442560309 : Rat) / 500000000000000000) }
]

def block360LeftCertificate : Bool :=
  allBoxesValid block360LeftBoxes &&
  coversFromBool block360LeftBoxes block360LeftL block360LeftR

theorem block360LeftCertificate_eq_true :
    block360LeftCertificate = true := by
  native_decide

def block360RightChunk000 : List RatBox := [
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87345136160714285869 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3528618839285714131 : Rat) / 50000000000000000000), D2 := ((40551613839285714131 : Rat) / 50000000000000000000), D3 := ((22875371249999999937 : Rat) / 25000000000000000000), D4 := ((51273370267857137729 : Rat) / 50000000000000000000), LB := ((17723619757826687 : Rat) / 10000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42222123660714285743 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((14421739319234123 : Rat) / 100000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23710626160714285743 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((9367087360098433 : Rat) / 100000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19082751785714285743 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((2983490779523379 : Rat) / 50000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16768814598214285743 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((4852633880707599 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14454877410714285743 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((7330359695129407 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13297908816964285743 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((2451029880435357 : Rat) / 200000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12719424520089285743 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((1214477428703821 : Rat) / 250000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12140940223214285743 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((186636367262063 : Rat) / 20000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11851698074776785743 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((6522670059640023 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11562455926339285743 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((8033743855495823 : Rat) / 2000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11273213777901785743 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((285498354391997 : Rat) / 156250000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10983971629464285743 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((5225612471031121 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10839350555245535743 : Rat) / 50000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((4405025909572757 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10694729481026785743 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((18367975759975147 : Rat) / 5000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10550108406808035743 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((606748643261229 : Rat) / 200000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10405487332589285743 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((12440340772608277 : Rat) / 5000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10260866258370535743 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((4078720694722593 : Rat) / 2000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10116245184151785743 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((1690622168161099 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9971624109933035743 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((7225452140129929 : Rat) / 5000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9827003035714285743 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((6531310508940541 : Rat) / 5000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9682381961495535743 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((12779239439726087 : Rat) / 10000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9537760887276785743 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((3410466855544303 : Rat) / 2500000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9393139813058035743 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((313905026230199 : Rat) / 200000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9248518738839285743 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((118676507145761 : Rat) / 62500000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9103897664620535743 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((2357433731631997 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8959276590401785743 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((2951233686353777 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8814655516183035743 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((9216775603273289 : Rat) / 2500000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8670034441964285743 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((2285524174644629 : Rat) / 500000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8525413367745535743 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((5612242862641337 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8380792293526785743 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((18978238309513007 : Rat) / 10000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8091550145089285743 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((2442543663338931 : Rat) / 500000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7802307996651785743 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((8674350279414433 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7513065848214285743 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((4755043845298193 : Rat) / 1250000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6934581551339285743 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((16946834120796533 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6356097254464285743 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((18802229659796943 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516786128660714285743 : Rat) / 200000000000000000000), D0 := ((516786128660714285743 : Rat) / 200000000000000000000), D1 := ((153291108660714285743 : Rat) / 200000000000000000000), D2 := ((5199128660714285743 : Rat) / 200000000000000000000), D3 := ((5199128660714285743 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((17310739800205033 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516786128660714285743 : Rat) / 200000000000000000000), R := ((260992628660714285743 : Rat) / 100000000000000000000), D0 := ((260992628660714285743 : Rat) / 100000000000000000000), D1 := ((79245118660714285743 : Rat) / 100000000000000000000), D2 := ((5199128660714285743 : Rat) / 100000000000000000000), D3 := ((15597385982142857229 : Rat) / 200000000000000000000), D4 := ((37687897053571408649 : Rat) / 200000000000000000000), LB := ((6431932344719171 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((260992628660714285743 : Rat) / 100000000000000000000), R := ((527184385982142857229 : Rat) / 200000000000000000000), D0 := ((527184385982142857229 : Rat) / 200000000000000000000), D1 := ((163689365982142857229 : Rat) / 200000000000000000000), D2 := ((15597385982142857229 : Rat) / 200000000000000000000), D3 := ((5199128660714285743 : Rat) / 100000000000000000000), D4 := ((16244384196428561453 : Rat) / 100000000000000000000), LB := ((1540491185240303 : Rat) / 50000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527184385982142857229 : Rat) / 200000000000000000000), R := ((133095878660714285743 : Rat) / 50000000000000000000), D0 := ((133095878660714285743 : Rat) / 50000000000000000000), D1 := ((42222123660714285743 : Rat) / 50000000000000000000), D2 := ((5199128660714285743 : Rat) / 50000000000000000000), D3 := ((5199128660714285743 : Rat) / 200000000000000000000), D4 := ((27289639732142837163 : Rat) / 200000000000000000000), LB := ((545120024328237 : Rat) / 5000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133095878660714285743 : Rat) / 50000000000000000000), R := ((536642546696428571669 : Rat) / 200000000000000000000), D0 := ((536642546696428571669 : Rat) / 200000000000000000000), D1 := ((173147526696428571669 : Rat) / 200000000000000000000), D2 := ((25055546696428571669 : Rat) / 200000000000000000000), D3 := ((4259032053571428697 : Rat) / 200000000000000000000), D4 := ((1104525553571427571 : Rat) / 10000000000000000000), LB := ((12978383800316573 : Rat) / 100000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((536642546696428571669 : Rat) / 200000000000000000000), R := ((270450789375000000183 : Rat) / 100000000000000000000), D0 := ((270450789375000000183 : Rat) / 100000000000000000000), D1 := ((88703279375000000183 : Rat) / 100000000000000000000), D2 := ((14657289375000000183 : Rat) / 100000000000000000000), D3 := ((4259032053571428697 : Rat) / 100000000000000000000), D4 := ((17831479017857122723 : Rat) / 200000000000000000000), LB := ((437942703300051 : Rat) / 25000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270450789375000000183 : Rat) / 100000000000000000000), R := ((1086062189553571429429 : Rat) / 400000000000000000000), D0 := ((1086062189553571429429 : Rat) / 400000000000000000000), D1 := ((359072149553571429429 : Rat) / 400000000000000000000), D2 := ((62888189553571429429 : Rat) / 400000000000000000000), D3 := ((4259032053571428697 : Rat) / 80000000000000000000), D4 := ((6786223482142847013 : Rat) / 100000000000000000000), LB := ((9465716518054501 : Rat) / 2500000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1086062189553571429429 : Rat) / 400000000000000000000), R := ((435276682232142857511 : Rat) / 160000000000000000000), D0 := ((435276682232142857511 : Rat) / 160000000000000000000), D1 := ((144480666232142857511 : Rat) / 160000000000000000000), D2 := ((26007082232142857511 : Rat) / 160000000000000000000), D3 := ((46849352589285715667 : Rat) / 800000000000000000000), D4 := ((4577172374999991871 : Rat) / 80000000000000000000), LB := ((21406686887155413 : Rat) / 5000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((435276682232142857511 : Rat) / 160000000000000000000), R := ((4357025854375000003807 : Rat) / 1600000000000000000000), D0 := ((4357025854375000003807 : Rat) / 1600000000000000000000), D1 := ((1449065694375000003807 : Rat) / 1600000000000000000000), D2 := ((264329854375000003807 : Rat) / 1600000000000000000000), D3 := ((97957737232142860031 : Rat) / 1600000000000000000000), D4 := ((41512691696428490013 : Rat) / 800000000000000000000), LB := ((33811408426313583 : Rat) / 5000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4357025854375000003807 : Rat) / 1600000000000000000000), R := ((545160610803571429063 : Rat) / 200000000000000000000), D0 := ((545160610803571429063 : Rat) / 200000000000000000000), D1 := ((181665590803571429063 : Rat) / 200000000000000000000), D2 := ((33573610803571429063 : Rat) / 200000000000000000000), D3 := ((12777096160714286091 : Rat) / 200000000000000000000), D4 := ((78766351339285551329 : Rat) / 1600000000000000000000), LB := ((658391039159667 : Rat) / 200000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545160610803571429063 : Rat) / 200000000000000000000), R := ((4365543918482142861201 : Rat) / 1600000000000000000000), D0 := ((4365543918482142861201 : Rat) / 1600000000000000000000), D1 := ((1457583758482142861201 : Rat) / 1600000000000000000000), D2 := ((272847918482142861201 : Rat) / 1600000000000000000000), D3 := ((4259032053571428697 : Rat) / 64000000000000000000), D4 := ((9313414910714265329 : Rat) / 200000000000000000000), LB := ((2564773128004849 : Rat) / 5000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4365543918482142861201 : Rat) / 1600000000000000000000), R := ((8735346869017857151099 : Rat) / 3200000000000000000000), D0 := ((8735346869017857151099 : Rat) / 3200000000000000000000), D1 := ((2919426549017857151099 : Rat) / 3200000000000000000000), D2 := ((549954869017857151099 : Rat) / 3200000000000000000000), D3 := ((217210634732142863547 : Rat) / 3200000000000000000000), D4 := ((14049657446428538787 : Rat) / 320000000000000000000), LB := ((3543931999866967 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8735346869017857151099 : Rat) / 3200000000000000000000), R := ((2184901475267857144949 : Rat) / 800000000000000000000), D0 := ((2184901475267857144949 : Rat) / 800000000000000000000), D1 := ((730921395267857144949 : Rat) / 800000000000000000000), D2 := ((138553475267857144949 : Rat) / 800000000000000000000), D3 := ((55367416696428573061 : Rat) / 800000000000000000000), D4 := ((136237542410713959173 : Rat) / 3200000000000000000000), LB := ((27332632303131987 : Rat) / 10000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2184901475267857144949 : Rat) / 800000000000000000000), R := ((8743864933125000008493 : Rat) / 3200000000000000000000), D0 := ((8743864933125000008493 : Rat) / 3200000000000000000000), D1 := ((2927944613125000008493 : Rat) / 3200000000000000000000), D2 := ((558472933125000008493 : Rat) / 3200000000000000000000), D3 := ((225728698839285720941 : Rat) / 3200000000000000000000), D4 := ((32994627589285632619 : Rat) / 800000000000000000000), LB := ((529903744329957 : Rat) / 250000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8743864933125000008493 : Rat) / 3200000000000000000000), R := ((874812396517857143719 : Rat) / 320000000000000000000), D0 := ((874812396517857143719 : Rat) / 320000000000000000000), D1 := ((293220364517857143719 : Rat) / 320000000000000000000), D2 := ((56273196517857143719 : Rat) / 320000000000000000000), D3 := ((114993865446428574819 : Rat) / 1600000000000000000000), D4 := ((127719478303571101779 : Rat) / 3200000000000000000000), LB := ((854881904374577 : Rat) / 500000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((874812396517857143719 : Rat) / 320000000000000000000), R := ((8752382997232142865887 : Rat) / 3200000000000000000000), D0 := ((8752382997232142865887 : Rat) / 3200000000000000000000), D1 := ((2936462677232142865887 : Rat) / 3200000000000000000000), D2 := ((566990997232142865887 : Rat) / 3200000000000000000000), D3 := ((46849352589285715667 : Rat) / 640000000000000000000), D4 := ((61730223124999836541 : Rat) / 1600000000000000000000), LB := ((15115108814247047 : Rat) / 10000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8752382997232142865887 : Rat) / 3200000000000000000000), R := ((1094580253660714286823 : Rat) / 400000000000000000000), D0 := ((1094580253660714286823 : Rat) / 400000000000000000000), D1 := ((367590213660714286823 : Rat) / 400000000000000000000), D2 := ((71406253660714286823 : Rat) / 400000000000000000000), D3 := ((29813224375000000879 : Rat) / 400000000000000000000), D4 := ((23840282839285648877 : Rat) / 640000000000000000000), LB := ((766900577950369 : Rat) / 500000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094580253660714286823 : Rat) / 400000000000000000000), R := ((8760901061339285723281 : Rat) / 3200000000000000000000), D0 := ((8760901061339285723281 : Rat) / 3200000000000000000000), D1 := ((2944980741339285723281 : Rat) / 3200000000000000000000), D2 := ((575509061339285723281 : Rat) / 3200000000000000000000), D3 := ((242764827053571435729 : Rat) / 3200000000000000000000), D4 := ((14367797767857101961 : Rat) / 400000000000000000000), LB := ((1786866567731471 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8760901061339285723281 : Rat) / 3200000000000000000000), R := ((4382580046696428575989 : Rat) / 1600000000000000000000), D0 := ((4382580046696428575989 : Rat) / 1600000000000000000000), D1 := ((1474619886696428575989 : Rat) / 1600000000000000000000), D2 := ((289884046696428575989 : Rat) / 1600000000000000000000), D3 := ((123511929553571432213 : Rat) / 1600000000000000000000), D4 := ((110683350089285386991 : Rat) / 3200000000000000000000), LB := ((22823983416018767 : Rat) / 10000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4382580046696428575989 : Rat) / 1600000000000000000000), R := ((350776765017857143227 : Rat) / 128000000000000000000), D0 := ((350776765017857143227 : Rat) / 128000000000000000000), D1 := ((118139952217857143227 : Rat) / 128000000000000000000), D2 := ((23361085017857143227 : Rat) / 128000000000000000000), D3 := ((251282891160714293123 : Rat) / 3200000000000000000000), D4 := ((53212159017856979147 : Rat) / 1600000000000000000000), LB := ((30337550905296107 : Rat) / 10000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((350776765017857143227 : Rat) / 128000000000000000000), R := ((2193419539375000002343 : Rat) / 800000000000000000000), D0 := ((2193419539375000002343 : Rat) / 800000000000000000000), D1 := ((739439459375000002343 : Rat) / 800000000000000000000), D2 := ((147071539375000002343 : Rat) / 800000000000000000000), D3 := ((12777096160714286091 : Rat) / 160000000000000000000), D4 := ((102165285982142529597 : Rat) / 3200000000000000000000), LB := ((4056215270062613 : Rat) / 1000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2193419539375000002343 : Rat) / 800000000000000000000), R := ((4391098110803571433383 : Rat) / 1600000000000000000000), D0 := ((4391098110803571433383 : Rat) / 1600000000000000000000), D1 := ((1483137950803571433383 : Rat) / 1600000000000000000000), D2 := ((298402110803571433383 : Rat) / 1600000000000000000000), D3 := ((132029993660714289607 : Rat) / 1600000000000000000000), D4 := ((979062539285711009 : Rat) / 32000000000000000000), LB := ((8016845648096127 : Rat) / 10000000000000000000) },
  { w1 := ((8863763323022047 : Rat) / 10000000000000000), w2 := ((2968283997052271 : Rat) / 62500000000000000), w3 := ((15170427436261683 : Rat) / 100000000000000000), w4 := ((1738420445898041 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133095878660714285743 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4391098110803571433383 : Rat) / 1600000000000000000000), R := ((3433872767857142861 : Rat) / 1250000000000000000), D0 := ((3433872767857142861 : Rat) / 1250000000000000000), D1 := ((1162028892857142861 : Rat) / 1250000000000000000), D2 := ((236454017857142861 : Rat) / 1250000000000000000), D3 := ((4259032053571428697 : Rat) / 50000000000000000000), D4 := ((44694094910714121753 : Rat) / 1600000000000000000000), LB := ((2229898044048023 : Rat) / 500000000000000000) }
]

def block360RightChunk000L : Rat := ((87345136160714285869 : Rat) / 50000000000000000000)
def block360RightChunk000R : Rat := ((3433872767857142861 : Rat) / 1250000000000000000)

def block360RightChunk000Certificate : Bool :=
  allBoxesValid block360RightChunk000 &&
  coversFromBool block360RightChunk000 block360RightChunk000L block360RightChunk000R

theorem block360RightChunk000Certificate_eq_true :
    block360RightChunk000Certificate = true := by
  native_decide

def block360RightChainCertificate : Bool :=
  decide (
    block360RightL = ((87345136160714285869 : Rat) / 50000000000000000000) /\
    ((3433872767857142861 : Rat) / 1250000000000000000) = block360RightR)

theorem block360RightChainCertificate_eq_true :
    block360RightChainCertificate = true := by
  native_decide

def block360LeftBoxCount : Nat := boxCount block360LeftBoxes
def block360RightBoxCount : Nat := 59

def block360_rational_certificate : Prop :=
    block360LeftCertificate = true /\
    block360RightChainCertificate = true /\
    block360RightChunk000Certificate = true

theorem block360_rational_certificate_proof :
    block360_rational_certificate := by
  exact ⟨block360LeftCertificate_eq_true, block360RightChainCertificate_eq_true, block360RightChunk000Certificate_eq_true⟩

end Block360
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block360

open Set

def block360W1 : Rat := ((8863763323022047 : Rat) / 10000000000000000)
def block360W2 : Rat := ((2968283997052271 : Rat) / 62500000000000000)
def block360W3 : Rat := ((15170427436261683 : Rat) / 100000000000000000)
def block360W4 : Rat := ((1738420445898041 : Rat) / 12500000000000000)
def block360S1 : Rat := ((18174751 : Rat) / 10000000)
def block360S2 : Rat := ((511587 : Rat) / 200000)
def block360S3 : Rat := ((133095878660714285743 : Rat) / 50000000000000000000)
def block360S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block360V (y : ℝ) : ℝ :=
  ratPotential block360W1 block360W2 block360W3 block360W4 block360S1 block360S2 block360S3 block360S4 y

def block360LeftParamsCertificate : Bool :=
  allBoxesSameParams block360LeftBoxes block360W1 block360W2 block360W3 block360W4 block360S1 block360S2 block360S3 block360S4

theorem block360LeftParamsCertificate_eq_true :
    block360LeftParamsCertificate = true := by
  native_decide

theorem block360_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block360LeftL : ℝ) (block360LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block360S1 : ℝ))
    (hy2ne : y ≠ (block360S2 : ℝ))
    (hy3ne : y ≠ (block360S3 : ℝ))
    (hy4ne : y ≠ (block360S4 : ℝ)) :
    0 < block360V y := by
  have hcert := block360LeftCertificate_eq_true
  unfold block360LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block360LeftBoxes) (lo := block360LeftL) (hi := block360LeftR)
    (w1 := block360W1) (w2 := block360W2) (w3 := block360W3) (w4 := block360W4)
    (s1 := block360S1) (s2 := block360S2) (s3 := block360S3) (s4 := block360S4)
    hboxes hcover block360LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block360RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block360RightChunk000 block360W1 block360W2 block360W3 block360W4 block360S1 block360S2 block360S3 block360S4

theorem block360RightChunk000ParamsCertificate_eq_true :
    block360RightChunk000ParamsCertificate = true := by
  native_decide

theorem block360_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block360RightChunk000L : ℝ) (block360RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block360S1 : ℝ))
    (hy2ne : y ≠ (block360S2 : ℝ))
    (hy3ne : y ≠ (block360S3 : ℝ))
    (hy4ne : y ≠ (block360S4 : ℝ)) :
    0 < block360V y := by
  have hcert := block360RightChunk000Certificate_eq_true
  unfold block360RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block360RightChunk000) (lo := block360RightChunk000L) (hi := block360RightChunk000R)
    (w1 := block360W1) (w2 := block360W2) (w3 := block360W3) (w4 := block360W4)
    (s1 := block360S1) (s2 := block360S2) (s3 := block360S3) (s4 := block360S4)
    hboxes hcover block360RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block360_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block360RightL : ℝ) (block360RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block360S1 : ℝ))
    (hy2ne : y ≠ (block360S2 : ℝ))
    (hy3ne : y ≠ (block360S3 : ℝ))
    (hy4ne : y ≠ (block360S4 : ℝ)) :
    0 < block360V y := by
  have hL : (block360RightChunk000L : ℝ) = (block360RightL : ℝ) := by
    norm_num [block360RightChunk000L, block360RightL]
  have hR : (block360RightChunk000R : ℝ) = (block360RightR : ℝ) := by
    norm_num [block360RightChunk000R, block360RightR]
  have hyc : y ∈ Icc (block360RightChunk000L : ℝ) (block360RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block360_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block360_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block360LeftL : ℝ) (block360LeftR : ℝ) →
    y ≠ 0 → y ≠ (block360S1 : ℝ) → y ≠ (block360S2 : ℝ) →
    y ≠ (block360S3 : ℝ) → y ≠ (block360S4 : ℝ) → 0 < block360V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block360RightL : ℝ) (block360RightR : ℝ) →
    y ≠ 0 → y ≠ (block360S1 : ℝ) → y ≠ (block360S2 : ℝ) →
    y ≠ (block360S3 : ℝ) → y ≠ (block360S4 : ℝ) → 0 < block360V y)

theorem block360_reallog_certificate_proof :
    block360_reallog_certificate := by
  exact ⟨block360_left_V_pos, block360_right_V_pos⟩

end Block360
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block360.block360V
#check Erdos1038Lean.M1817475.Block360.block360_left_V_pos
#check Erdos1038Lean.M1817475.Block360.block360_right_V_pos
#check Erdos1038Lean.M1817475.Block360.block360_reallog_certificate_proof
