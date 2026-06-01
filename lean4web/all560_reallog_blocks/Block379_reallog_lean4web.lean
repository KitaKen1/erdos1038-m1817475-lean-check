/-
Self-contained Lean4Web paste file.
Block 379 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block379

def block379LeftL : Rat := ((1857970982142857151 : Rat) / 2500000000000000000)
def block379LeftR : Rat := ((37169194196428571591 : Rat) / 50000000000000000000)
def block379RightL : Rat := ((4357970982142857151 : Rat) / 2500000000000000000)
def block379RightR : Rat := ((137169194196428571591 : Rat) / 50000000000000000000)

def block379LeftBoxes : List RatBox := [
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1857970982142857151 : Rat) / 2500000000000000000), R := ((37169194196428571591 : Rat) / 50000000000000000000), D0 := ((37169194196428571591 : Rat) / 50000000000000000000), D1 := ((2685716767857142849 : Rat) / 2500000000000000000), D2 := ((4536866517857142849 : Rat) / 2500000000000000000), D3 := ((3822601039285714281 : Rat) / 2000000000000000000), D4 := ((50729543392857140289 : Rat) / 25000000000000000000), LB := ((3116544385067907 : Rat) / 500000000000000000) }
]

def block379LeftCertificate : Bool :=
  allBoxesValid block379LeftBoxes &&
  coversFromBool block379LeftBoxes block379LeftL block379LeftR

theorem block379LeftCertificate_eq_true :
    block379LeftCertificate = true := by
  native_decide

def block379RightChunk000 : List RatBox := [
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4357970982142857151 : Rat) / 2500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((185716767857142849 : Rat) / 2500000000000000000), D2 := ((2036866517857142849 : Rat) / 2500000000000000000), D3 := ((1822601039285714281 : Rat) / 2000000000000000000), D4 := ((25729543392857140289 : Rat) / 25000000000000000000), LB := ((817947298718159 : Rat) / 500000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8370138125000000009 : Rat) / 10000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((5578258387233277 : Rat) / 50000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4667838625000000009 : Rat) / 10000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((7348480391472657 : Rat) / 100000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3742263750000000009 : Rat) / 10000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((894656126354069 : Rat) / 20000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3279476312500000009 : Rat) / 10000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((2009424778315059 : Rat) / 50000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((3048082593750000009 : Rat) / 10000000000000000000), D4 := ((10567236886160711799 : Rat) / 25000000000000000000), LB := ((361968335913149 : Rat) / 20000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2816688875000000009 : Rat) / 10000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((1076703568785807 : Rat) / 50000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((2700992015625000009 : Rat) / 10000000000000000000), D4 := ((9699510440848211799 : Rat) / 25000000000000000000), LB := ((2649570624620029 : Rat) / 200000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2585295156250000009 : Rat) / 10000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((2974015870945909 : Rat) / 500000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2469598296875000009 : Rat) / 10000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((10305485638713141 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((2411749867187500009 : Rat) / 10000000000000000000), D4 := ((8976405069754461799 : Rat) / 25000000000000000000), LB := ((7499082349733899 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2353901437500000009 : Rat) / 10000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((4979080458949431 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((2296053007812500009 : Rat) / 10000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((172253028479721 : Rat) / 62500000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2238204578125000009 : Rat) / 10000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((8418531164218757 : Rat) / 10000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2180356148437500009 : Rat) / 10000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((4385137270341843 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((2151431933593750009 : Rat) / 10000000000000000000), D4 := ((8325610235770086799 : Rat) / 25000000000000000000), LB := ((461869696236121 : Rat) / 125000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2122507718750000009 : Rat) / 10000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((3091311532153751 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((2093583503906250009 : Rat) / 10000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((64410104848793 : Rat) / 25000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2064659289062500009 : Rat) / 10000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((430518045621453 : Rat) / 200000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2035735074218750009 : Rat) / 10000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((18223876277640993 : Rat) / 10000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2006810859375000009 : Rat) / 10000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((3971232839221489 : Rat) / 2500000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((1977886644531250009 : Rat) / 10000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((14537997017008697 : Rat) / 10000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((1948962429687500009 : Rat) / 10000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((1776770384566001 : Rat) / 1250000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((1920038214843750009 : Rat) / 10000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((7473452844761197 : Rat) / 5000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((1891114000000000009 : Rat) / 10000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((1677234608178979 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((1862189785156250009 : Rat) / 10000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((1233096752917863 : Rat) / 625000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((1833265570312500009 : Rat) / 10000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((7456519251517 : Rat) / 3125000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((1804341355468750009 : Rat) / 10000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((29212321965332577 : Rat) / 10000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((1775417140625000009 : Rat) / 10000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((2239632196375449 : Rat) / 625000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((1746492925781250009 : Rat) / 10000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((1751244977524391 : Rat) / 400000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((1717568710937500009 : Rat) / 10000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((294467316747319 : Rat) / 625000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1659720281250000009 : Rat) / 10000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((14073514436567097 : Rat) / 5000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((1601871851562500009 : Rat) / 10000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((5801313000859509 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((1544023421875000009 : Rat) / 10000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((7904214310533453 : Rat) / 100000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1428326562500000009 : Rat) / 10000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((5105460970157391 : Rat) / 500000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1312629703125000009 : Rat) / 10000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((24922039355938147 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1196932843750000009 : Rat) / 10000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((579414833400953 : Rat) / 20000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((103282939125000000009 : Rat) / 40000000000000000000), D0 := ((103282939125000000009 : Rat) / 40000000000000000000), D1 := ((30583935125000000009 : Rat) / 40000000000000000000), D2 := ((965539125000000009 : Rat) / 40000000000000000000), D3 := ((965539125000000009 : Rat) / 10000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((602321850459781 : Rat) / 15625000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((103282939125000000009 : Rat) / 40000000000000000000), R := ((52124239125000000009 : Rat) / 20000000000000000000), D0 := ((52124239125000000009 : Rat) / 20000000000000000000), D1 := ((15774737125000000009 : Rat) / 20000000000000000000), D2 := ((965539125000000009 : Rat) / 20000000000000000000), D3 := ((2896617375000000027 : Rat) / 40000000000000000000), D4 := ((38059330089285694347 : Rat) / 200000000000000000000), LB := ((3252087393013159 : Rat) / 100000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((52124239125000000009 : Rat) / 20000000000000000000), R := ((26544889125000000009 : Rat) / 10000000000000000000), D0 := ((26544889125000000009 : Rat) / 10000000000000000000), D1 := ((8370138125000000009 : Rat) / 10000000000000000000), D2 := ((965539125000000009 : Rat) / 10000000000000000000), D3 := ((965539125000000009 : Rat) / 20000000000000000000), D4 := ((16615817232142847151 : Rat) / 100000000000000000000), LB := ((14175373563785787 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((26544889125000000009 : Rat) / 10000000000000000000), R := ((267671265535714285863 : Rat) / 100000000000000000000), D0 := ((267671265535714285863 : Rat) / 100000000000000000000), D1 := ((85923755535714285863 : Rat) / 100000000000000000000), D2 := ((11877765535714285863 : Rat) / 100000000000000000000), D3 := ((2222374285714285773 : Rat) / 100000000000000000000), D4 := ((5894060803571423553 : Rat) / 50000000000000000000), LB := ((3608586020580501 : Rat) / 25000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((267671265535714285863 : Rat) / 100000000000000000000), R := ((67473409955357142909 : Rat) / 25000000000000000000), D0 := ((67473409955357142909 : Rat) / 25000000000000000000), D1 := ((22036532455357142909 : Rat) / 25000000000000000000), D2 := ((3525034955357142909 : Rat) / 25000000000000000000), D3 := ((2222374285714285773 : Rat) / 50000000000000000000), D4 := ((9565747321428561333 : Rat) / 100000000000000000000), LB := ((2638953195050231 : Rat) / 100000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((67473409955357142909 : Rat) / 25000000000000000000), R := ((108401930785714285809 : Rat) / 40000000000000000000), D0 := ((108401930785714285809 : Rat) / 40000000000000000000), D1 := ((35702926785714285809 : Rat) / 40000000000000000000), D2 := ((6084530785714285809 : Rat) / 40000000000000000000), D3 := ((2222374285714285773 : Rat) / 40000000000000000000), D4 := ((183584325892856889 : Rat) / 2500000000000000000), LB := ((250467610083413 : Rat) / 25000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((108401930785714285809 : Rat) / 40000000000000000000), R := ((1086241682142857143863 : Rat) / 400000000000000000000), D0 := ((1086241682142857143863 : Rat) / 400000000000000000000), D1 := ((359251642142857143863 : Rat) / 400000000000000000000), D2 := ((63067682142857143863 : Rat) / 400000000000000000000), D3 := ((24446117142857143503 : Rat) / 400000000000000000000), D4 := ((12464371785714265347 : Rat) / 200000000000000000000), LB := ((4512104663835087 : Rat) / 500000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1086241682142857143863 : Rat) / 400000000000000000000), R := ((2174705738571428573499 : Rat) / 800000000000000000000), D0 := ((2174705738571428573499 : Rat) / 800000000000000000000), D1 := ((720725658571428573499 : Rat) / 800000000000000000000), D2 := ((128357738571428573499 : Rat) / 800000000000000000000), D3 := ((51114608571428572779 : Rat) / 800000000000000000000), D4 := ((22706369285714244921 : Rat) / 400000000000000000000), LB := ((5330004887753703 : Rat) / 500000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2174705738571428573499 : Rat) / 800000000000000000000), R := ((272116014107142857409 : Rat) / 100000000000000000000), D0 := ((272116014107142857409 : Rat) / 100000000000000000000), D1 := ((90368504107142857409 : Rat) / 100000000000000000000), D2 := ((16322514107142857409 : Rat) / 100000000000000000000), D3 := ((6667122857142857319 : Rat) / 100000000000000000000), D4 := ((43190364285714204069 : Rat) / 800000000000000000000), LB := ((6551641592493329 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272116014107142857409 : Rat) / 100000000000000000000), R := ((435830097428571429009 : Rat) / 160000000000000000000), D0 := ((435830097428571429009 : Rat) / 160000000000000000000), D1 := ((145034081428571429009 : Rat) / 160000000000000000000), D2 := ((26560497428571429009 : Rat) / 160000000000000000000), D3 := ((2222374285714285773 : Rat) / 32000000000000000000), D4 := ((5120998749999989787 : Rat) / 100000000000000000000), LB := ((3112043061111569 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((435830097428571429009 : Rat) / 160000000000000000000), R := ((1090686430714285715409 : Rat) / 400000000000000000000), D0 := ((1090686430714285715409 : Rat) / 400000000000000000000), D1 := ((363696390714285715409 : Rat) / 400000000000000000000), D2 := ((67512430714285715409 : Rat) / 400000000000000000000), D3 := ((28890865714285715049 : Rat) / 400000000000000000000), D4 := ((38745615714285632523 : Rat) / 800000000000000000000), LB := ((9019075550417699 : Rat) / 25000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1090686430714285715409 : Rat) / 400000000000000000000), R := ((4364968097142857147409 : Rat) / 1600000000000000000000), D0 := ((4364968097142857147409 : Rat) / 1600000000000000000000), D1 := ((1457007937142857147409 : Rat) / 1600000000000000000000), D2 := ((272272097142857147409 : Rat) / 1600000000000000000000), D3 := ((117785837142857145969 : Rat) / 1600000000000000000000), D4 := ((146092965714285387 : Rat) / 3200000000000000000), LB := ((345999113079537 : Rat) / 100000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4364968097142857147409 : Rat) / 1600000000000000000000), R := ((2183595235714285716591 : Rat) / 800000000000000000000), D0 := ((2183595235714285716591 : Rat) / 800000000000000000000), D1 := ((729615155714285716591 : Rat) / 800000000000000000000), D2 := ((137247235714285716591 : Rat) / 800000000000000000000), D3 := ((60004105714285715871 : Rat) / 800000000000000000000), D4 := ((70824108571428407727 : Rat) / 1600000000000000000000), LB := ((2665186776559303 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2183595235714285716591 : Rat) / 800000000000000000000), R := ((873882569142857143791 : Rat) / 320000000000000000000), D0 := ((873882569142857143791 : Rat) / 320000000000000000000), D1 := ((292290537142857143791 : Rat) / 320000000000000000000), D2 := ((55343369142857143791 : Rat) / 320000000000000000000), D3 := ((24446117142857143503 : Rat) / 320000000000000000000), D4 := ((34300867142857060977 : Rat) / 800000000000000000000), LB := ((20680613556690597 : Rat) / 10000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((873882569142857143791 : Rat) / 320000000000000000000), R := ((546454402500000000591 : Rat) / 200000000000000000000), D0 := ((546454402500000000591 : Rat) / 200000000000000000000), D1 := ((182959382500000000591 : Rat) / 200000000000000000000), D2 := ((34867402500000000591 : Rat) / 200000000000000000000), D3 := ((15556620000000000411 : Rat) / 200000000000000000000), D4 := ((66379359999999836181 : Rat) / 1600000000000000000000), LB := ((8378612151060949 : Rat) / 5000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546454402500000000591 : Rat) / 200000000000000000000), R := ((4373857594285714290501 : Rat) / 1600000000000000000000), D0 := ((4373857594285714290501 : Rat) / 1600000000000000000000), D1 := ((1465897434285714290501 : Rat) / 1600000000000000000000), D2 := ((281161594285714290501 : Rat) / 1600000000000000000000), D3 := ((126675334285714289061 : Rat) / 1600000000000000000000), D4 := ((8019623214285693801 : Rat) / 200000000000000000000), LB := ((1496313302508101 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4373857594285714290501 : Rat) / 1600000000000000000000), R := ((2188039984285714288137 : Rat) / 800000000000000000000), D0 := ((2188039984285714288137 : Rat) / 800000000000000000000), D1 := ((734059904285714288137 : Rat) / 800000000000000000000), D2 := ((141691984285714288137 : Rat) / 800000000000000000000), D3 := ((64448854285714287417 : Rat) / 800000000000000000000), D4 := ((12386922285714252927 : Rat) / 320000000000000000000), LB := ((1539137124018819 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2188039984285714288137 : Rat) / 800000000000000000000), R := ((4378302342857142862047 : Rat) / 1600000000000000000000), D0 := ((4378302342857142862047 : Rat) / 1600000000000000000000), D1 := ((1470342182857142862047 : Rat) / 1600000000000000000000), D2 := ((285606342857142862047 : Rat) / 1600000000000000000000), D3 := ((131120082857142860607 : Rat) / 1600000000000000000000), D4 := ((29856118571428489431 : Rat) / 800000000000000000000), LB := ((1814805631321137 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4378302342857142862047 : Rat) / 1600000000000000000000), R := ((219026235857142857391 : Rat) / 80000000000000000000), D0 := ((219026235857142857391 : Rat) / 80000000000000000000), D1 := ((73628227857142857391 : Rat) / 80000000000000000000), D2 := ((14391435857142857391 : Rat) / 80000000000000000000), D3 := ((6667122857142857319 : Rat) / 80000000000000000000), D4 := ((57489862857142693089 : Rat) / 1600000000000000000000), LB := ((2335417914444471 : Rat) / 1000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((219026235857142857391 : Rat) / 80000000000000000000), R := ((4382747091428571433593 : Rat) / 1600000000000000000000), D0 := ((4382747091428571433593 : Rat) / 1600000000000000000000), D1 := ((1474786931428571433593 : Rat) / 1600000000000000000000), D2 := ((290051091428571433593 : Rat) / 1600000000000000000000), D3 := ((135564831428571432153 : Rat) / 1600000000000000000000), D4 := ((13816872142857101829 : Rat) / 400000000000000000000), LB := ((31147761399991647 : Rat) / 10000000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4382747091428571433593 : Rat) / 1600000000000000000000), R := ((2192484732857142859683 : Rat) / 800000000000000000000), D0 := ((2192484732857142859683 : Rat) / 800000000000000000000), D1 := ((738504652857142859683 : Rat) / 800000000000000000000), D2 := ((146136732857142859683 : Rat) / 800000000000000000000), D3 := ((68893602857142858963 : Rat) / 800000000000000000000), D4 := ((53045114285714121543 : Rat) / 1600000000000000000000), LB := ((208432358193833 : Rat) / 50000000000000000) },
  { w1 := ((68102128982591 : Rat) / 80000000000000), w2 := ((2919689326872981 : Rat) / 62500000000000000), w3 := ((1970474055792517 : Rat) / 12500000000000000), w4 := ((280809037636893 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26544889125000000009 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2192484732857142859683 : Rat) / 800000000000000000000), R := ((137169194196428571591 : Rat) / 50000000000000000000), D0 := ((137169194196428571591 : Rat) / 50000000000000000000), D1 := ((46295439196428571591 : Rat) / 50000000000000000000), D2 := ((9272444196428571591 : Rat) / 50000000000000000000), D3 := ((2222374285714285773 : Rat) / 25000000000000000000), D4 := ((5082273999999983577 : Rat) / 160000000000000000000), LB := ((4484609447182597 : Rat) / 5000000000000000000) }
]

def block379RightChunk000L : Rat := ((4357970982142857151 : Rat) / 2500000000000000000)
def block379RightChunk000R : Rat := ((137169194196428571591 : Rat) / 50000000000000000000)

def block379RightChunk000Certificate : Bool :=
  allBoxesValid block379RightChunk000 &&
  coversFromBool block379RightChunk000 block379RightChunk000L block379RightChunk000R

theorem block379RightChunk000Certificate_eq_true :
    block379RightChunk000Certificate = true := by
  native_decide

def block379RightChainCertificate : Bool :=
  decide (
    block379RightL = ((4357970982142857151 : Rat) / 2500000000000000000) /\
    ((137169194196428571591 : Rat) / 50000000000000000000) = block379RightR)

theorem block379RightChainCertificate_eq_true :
    block379RightChainCertificate = true := by
  native_decide

def block379LeftBoxCount : Nat := boxCount block379LeftBoxes
def block379RightBoxCount : Nat := 59

def block379_rational_certificate : Prop :=
    block379LeftCertificate = true /\
    block379RightChainCertificate = true /\
    block379RightChunk000Certificate = true

theorem block379_rational_certificate_proof :
    block379_rational_certificate := by
  exact ⟨block379LeftCertificate_eq_true, block379RightChainCertificate_eq_true, block379RightChunk000Certificate_eq_true⟩

end Block379
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block379

open Set

def block379W1 : Rat := ((68102128982591 : Rat) / 80000000000000)
def block379W2 : Rat := ((2919689326872981 : Rat) / 62500000000000000)
def block379W3 : Rat := ((1970474055792517 : Rat) / 12500000000000000)
def block379W4 : Rat := ((280809037636893 : Rat) / 2000000000000000)
def block379S1 : Rat := ((18174751 : Rat) / 10000000)
def block379S2 : Rat := ((511587 : Rat) / 200000)
def block379S3 : Rat := ((26544889125000000009 : Rat) / 10000000000000000000)
def block379S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block379V (y : ℝ) : ℝ :=
  ratPotential block379W1 block379W2 block379W3 block379W4 block379S1 block379S2 block379S3 block379S4 y

def block379LeftParamsCertificate : Bool :=
  allBoxesSameParams block379LeftBoxes block379W1 block379W2 block379W3 block379W4 block379S1 block379S2 block379S3 block379S4

theorem block379LeftParamsCertificate_eq_true :
    block379LeftParamsCertificate = true := by
  native_decide

theorem block379_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block379LeftL : ℝ) (block379LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block379S1 : ℝ))
    (hy2ne : y ≠ (block379S2 : ℝ))
    (hy3ne : y ≠ (block379S3 : ℝ))
    (hy4ne : y ≠ (block379S4 : ℝ)) :
    0 < block379V y := by
  have hcert := block379LeftCertificate_eq_true
  unfold block379LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block379LeftBoxes) (lo := block379LeftL) (hi := block379LeftR)
    (w1 := block379W1) (w2 := block379W2) (w3 := block379W3) (w4 := block379W4)
    (s1 := block379S1) (s2 := block379S2) (s3 := block379S3) (s4 := block379S4)
    hboxes hcover block379LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block379RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block379RightChunk000 block379W1 block379W2 block379W3 block379W4 block379S1 block379S2 block379S3 block379S4

theorem block379RightChunk000ParamsCertificate_eq_true :
    block379RightChunk000ParamsCertificate = true := by
  native_decide

theorem block379_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block379RightChunk000L : ℝ) (block379RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block379S1 : ℝ))
    (hy2ne : y ≠ (block379S2 : ℝ))
    (hy3ne : y ≠ (block379S3 : ℝ))
    (hy4ne : y ≠ (block379S4 : ℝ)) :
    0 < block379V y := by
  have hcert := block379RightChunk000Certificate_eq_true
  unfold block379RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block379RightChunk000) (lo := block379RightChunk000L) (hi := block379RightChunk000R)
    (w1 := block379W1) (w2 := block379W2) (w3 := block379W3) (w4 := block379W4)
    (s1 := block379S1) (s2 := block379S2) (s3 := block379S3) (s4 := block379S4)
    hboxes hcover block379RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block379_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block379RightL : ℝ) (block379RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block379S1 : ℝ))
    (hy2ne : y ≠ (block379S2 : ℝ))
    (hy3ne : y ≠ (block379S3 : ℝ))
    (hy4ne : y ≠ (block379S4 : ℝ)) :
    0 < block379V y := by
  have hL : (block379RightChunk000L : ℝ) = (block379RightL : ℝ) := by
    norm_num [block379RightChunk000L, block379RightL]
  have hR : (block379RightChunk000R : ℝ) = (block379RightR : ℝ) := by
    norm_num [block379RightChunk000R, block379RightR]
  have hyc : y ∈ Icc (block379RightChunk000L : ℝ) (block379RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block379_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block379_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block379LeftL : ℝ) (block379LeftR : ℝ) →
    y ≠ 0 → y ≠ (block379S1 : ℝ) → y ≠ (block379S2 : ℝ) →
    y ≠ (block379S3 : ℝ) → y ≠ (block379S4 : ℝ) → 0 < block379V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block379RightL : ℝ) (block379RightR : ℝ) →
    y ≠ 0 → y ≠ (block379S1 : ℝ) → y ≠ (block379S2 : ℝ) →
    y ≠ (block379S3 : ℝ) → y ≠ (block379S4 : ℝ) → 0 < block379V y)

theorem block379_reallog_certificate_proof :
    block379_reallog_certificate := by
  exact ⟨block379_left_V_pos, block379_right_V_pos⟩

end Block379
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block379.block379V
#check Erdos1038Lean.M1817475.Block379.block379_left_V_pos
#check Erdos1038Lean.M1817475.Block379.block379_right_V_pos
#check Erdos1038Lean.M1817475.Block379.block379_reallog_certificate_proof
