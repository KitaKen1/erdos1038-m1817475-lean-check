/-
Self-contained Lean4Web paste file.
Block 449 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block449

def block449LeftL : Rat := ((729504017857142861 : Rat) / 1000000000000000000)
def block449LeftR : Rat := ((36484975446428571621 : Rat) / 50000000000000000000)
def block449RightL : Rat := ((1729504017857142861 : Rat) / 1000000000000000000)
def block449RightR : Rat := ((136484975446428571621 : Rat) / 50000000000000000000)

def block449LeftBoxes : List RatBox := [
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((729504017857142861 : Rat) / 1000000000000000000), R := ((36484975446428571621 : Rat) / 50000000000000000000), D0 := ((36484975446428571621 : Rat) / 50000000000000000000), D1 := ((1087971082142857139 : Rat) / 1000000000000000000), D2 := ((1828430982142857139 : Rat) / 1000000000000000000), D3 := ((18976161446428571411 : Rat) / 10000000000000000000), D4 := ((2054986557142857039 : Rat) / 1000000000000000000), LB := ((3158201643534489 : Rat) / 1000000000000000000) }
]

def block449LeftCertificate : Bool :=
  allBoxesValid block449LeftBoxes &&
  coversFromBool block449LeftBoxes block449LeftL block449LeftR

theorem block449LeftCertificate_eq_true :
    block449LeftCertificate = true := by
  native_decide

def block449RightChunk000 : List RatBox := [
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1729504017857142861 : Rat) / 1000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((87971082142857139 : Rat) / 1000000000000000000), D2 := ((828430982142857139 : Rat) / 1000000000000000000), D3 := ((8976161446428571411 : Rat) / 10000000000000000000), D4 := ((1054986557142857039 : Rat) / 1000000000000000000), LB := ((4468801608550831 : Rat) / 5000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8096450625000000021 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((9758443760823389 : Rat) / 25000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((33522361 : Rat) / 16000000), D0 := ((33522361 : Rat) / 16000000), D1 := ((22213797 : Rat) / 80000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((6245300875000000021 : Rat) / 10000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((4046232996918383 : Rat) / 20000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33522361 : Rat) / 16000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 16000000), D3 := ((5319726000000000021 : Rat) / 10000000000000000000), D4 := ((6893430124999999 : Rat) / 10000000000000000), LB := ((24082515117649847 : Rat) / 500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4394151125000000021 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((29723942266891873 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((722279413 : Rat) / 320000000), D0 := ((722279413 : Rat) / 320000000), D1 := ((140687381 : Rat) / 320000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((3931363687500000021 : Rat) / 10000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((1467967470253723 : Rat) / 50000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((722279413 : Rat) / 320000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((96259787 : Rat) / 320000000), D3 := ((3699969968750000021 : Rat) / 10000000000000000000), D4 := ((5273674093749999 : Rat) / 10000000000000000), LB := ((11408180872185453 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((1466772623 : Rat) / 640000000), D0 := ((1466772623 : Rat) / 640000000), D1 := ((303588559 : Rat) / 640000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3468576250000000021 : Rat) / 10000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((7996377365442113 : Rat) / 500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1466772623 : Rat) / 640000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((170305777 : Rat) / 640000000), D3 := ((3352879390625000021 : Rat) / 10000000000000000000), D4 := ((4926583515624999 : Rat) / 10000000000000000), LB := ((1165197524805023 : Rat) / 125000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((1481581821 : Rat) / 640000000), D0 := ((1481581821 : Rat) / 640000000), D1 := ((318397757 : Rat) / 640000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((3237182531250000021 : Rat) / 10000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((862163706000011 : Rat) / 250000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1481581821 : Rat) / 640000000), R := ((2970568241 : Rat) / 1280000000), D0 := ((2970568241 : Rat) / 1280000000), D1 := ((644200113 : Rat) / 1280000000), D2 := ((155496579 : Rat) / 640000000), D3 := ((3121485671875000021 : Rat) / 10000000000000000000), D4 := ((4695189796874999 : Rat) / 10000000000000000), LB := ((15476124694233373 : Rat) / 2000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2970568241 : Rat) / 1280000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((303588559 : Rat) / 1280000000), D3 := ((3063637242187500021 : Rat) / 10000000000000000000), D4 := ((4637341367187499 : Rat) / 10000000000000000), LB := ((5435028650018513 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((2985377439 : Rat) / 1280000000), D0 := ((2985377439 : Rat) / 1280000000), D1 := ((659009311 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3005788812500000021 : Rat) / 10000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((418068247098489 : Rat) / 125000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2985377439 : Rat) / 1280000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((288779361 : Rat) / 1280000000), D3 := ((2947940382812500021 : Rat) / 10000000000000000000), D4 := ((4521644507812499 : Rat) / 10000000000000000), LB := ((7348590340803887 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((239718747 : Rat) / 102400000), D0 := ((239718747 : Rat) / 102400000), D1 := ((1340232419 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((2890091953125000021 : Rat) / 10000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((871166266014331 : Rat) / 200000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((239718747 : Rat) / 102400000), R := ((3000186637 : Rat) / 1280000000), D0 := ((3000186637 : Rat) / 1280000000), D1 := ((673818509 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 102400000), D3 := ((2861167738281250021 : Rat) / 10000000000000000000), D4 := ((4434871863281249 : Rat) / 10000000000000000), LB := ((17958304734867897 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3000186637 : Rat) / 1280000000), R := ((6007777873 : Rat) / 2560000000), D0 := ((6007777873 : Rat) / 2560000000), D1 := ((1355041617 : Rat) / 2560000000), D2 := ((273970163 : Rat) / 1280000000), D3 := ((2832243523437500021 : Rat) / 10000000000000000000), D4 := ((4405947648437499 : Rat) / 10000000000000000), LB := ((5767847569304499 : Rat) / 2000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6007777873 : Rat) / 2560000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((540535727 : Rat) / 2560000000), D3 := ((2803319308593750021 : Rat) / 10000000000000000000), D4 := ((4377023433593749 : Rat) / 10000000000000000), LB := ((11165763323411869 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((6022587071 : Rat) / 2560000000), D0 := ((6022587071 : Rat) / 2560000000), D1 := ((273970163 : Rat) / 512000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((2774395093750000021 : Rat) / 10000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((3279812096876139 : Rat) / 2000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6022587071 : Rat) / 2560000000), R := ((602999167 : Rat) / 256000000), D0 := ((602999167 : Rat) / 256000000), D1 := ((688627707 : Rat) / 1280000000), D2 := ((525726529 : Rat) / 2560000000), D3 := ((2745470878906250021 : Rat) / 10000000000000000000), D4 := ((4319175003906249 : Rat) / 10000000000000000), LB := ((5523844479646753 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((602999167 : Rat) / 256000000), R := ((6037396269 : Rat) / 2560000000), D0 := ((6037396269 : Rat) / 2560000000), D1 := ((1384660013 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 256000000), D3 := ((2716546664062500021 : Rat) / 10000000000000000000), D4 := ((4290250789062499 : Rat) / 10000000000000000), LB := ((3141767876279379 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6037396269 : Rat) / 2560000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((510917331 : Rat) / 2560000000), D3 := ((2687622449218750021 : Rat) / 10000000000000000000), D4 := ((4261326574218749 : Rat) / 10000000000000000), LB := ((211300825735887 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((2419401267 : Rat) / 1024000000), D0 := ((2419401267 : Rat) / 1024000000), D1 := ((2791533823 : Rat) / 5120000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((2658698234375000021 : Rat) / 10000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((1028103634153947 : Rat) / 500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2419401267 : Rat) / 1024000000), R := ((6052205467 : Rat) / 2560000000), D0 := ((6052205467 : Rat) / 2560000000), D1 := ((1399469211 : Rat) / 2560000000), D2 := ((199924173 : Rat) / 1024000000), D3 := ((2644236126953125021 : Rat) / 10000000000000000000), D4 := ((1054485062988281 : Rat) / 2500000000000000), LB := ((9479260926139113 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6052205467 : Rat) / 2560000000), R := ((12111815533 : Rat) / 5120000000), D0 := ((12111815533 : Rat) / 5120000000), D1 := ((2806343021 : Rat) / 5120000000), D2 := ((496108133 : Rat) / 2560000000), D3 := ((2629774019531250021 : Rat) / 10000000000000000000), D4 := ((4203478144531249 : Rat) / 10000000000000000), LB := ((8753965210463281 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12111815533 : Rat) / 5120000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((984811667 : Rat) / 5120000000), D3 := ((2615311912109375021 : Rat) / 10000000000000000000), D4 := ((2094508018554687 : Rat) / 5000000000000000), LB := ((8105610939572287 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((12126624731 : Rat) / 5120000000), D0 := ((12126624731 : Rat) / 5120000000), D1 := ((2821152219 : Rat) / 5120000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((2600849804687500021 : Rat) / 10000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((117729220692647 : Rat) / 78125000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12126624731 : Rat) / 5120000000), R := ((1213402933 : Rat) / 512000000), D0 := ((1213402933 : Rat) / 512000000), D1 := ((1414278409 : Rat) / 2560000000), D2 := ((970002469 : Rat) / 5120000000), D3 := ((2586387697265625021 : Rat) / 10000000000000000000), D4 := ((520011477783203 : Rat) / 1250000000000000), LB := ((1760406309816321 : Rat) / 1250000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1213402933 : Rat) / 512000000), R := ((12141433929 : Rat) / 5120000000), D0 := ((12141433929 : Rat) / 5120000000), D1 := ((2835961417 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 512000000), D3 := ((2571925589843750021 : Rat) / 10000000000000000000), D4 := ((4145629714843749 : Rat) / 10000000000000000), LB := ((1325393885261747 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12141433929 : Rat) / 5120000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((955193271 : Rat) / 5120000000), D3 := ((2557463482421875021 : Rat) / 10000000000000000000), D4 := ((2065583803710937 : Rat) / 5000000000000000), LB := ((12582413409160317 : Rat) / 10000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((12156243127 : Rat) / 5120000000), D0 := ((12156243127 : Rat) / 5120000000), D1 := ((570154123 : Rat) / 1024000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2543001375000000021 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((6034852186502203 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12156243127 : Rat) / 5120000000), R := ((6081823863 : Rat) / 2560000000), D0 := ((6081823863 : Rat) / 2560000000), D1 := ((1429087607 : Rat) / 2560000000), D2 := ((940384073 : Rat) / 5120000000), D3 := ((2528539267578125021 : Rat) / 10000000000000000000), D4 := ((1025560848144531 : Rat) / 2500000000000000), LB := ((2929216150160327 : Rat) / 2500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6081823863 : Rat) / 2560000000), R := ((486842093 : Rat) / 204800000), D0 := ((486842093 : Rat) / 204800000), D1 := ((2865579813 : Rat) / 5120000000), D2 := ((466489737 : Rat) / 2560000000), D3 := ((2514077160156250021 : Rat) / 10000000000000000000), D4 := ((4087781285156249 : Rat) / 10000000000000000), LB := ((1440621254849353 : Rat) / 1250000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((486842093 : Rat) / 204800000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 40960000), D3 := ((2499615052734375021 : Rat) / 10000000000000000000), D4 := ((2036659588867187 : Rat) / 5000000000000000), LB := ((114951201967671 : Rat) / 100000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((12185861523 : Rat) / 5120000000), D0 := ((12185861523 : Rat) / 5120000000), D1 := ((2880389011 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((2485152945312500021 : Rat) / 10000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((5814219316555569 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12185861523 : Rat) / 5120000000), R := ((6096633061 : Rat) / 2560000000), D0 := ((6096633061 : Rat) / 2560000000), D1 := ((288779361 : Rat) / 512000000), D2 := ((910765677 : Rat) / 5120000000), D3 := ((2470690837890625021 : Rat) / 10000000000000000000), D4 := ((31596835647583 : Rat) / 78125000000000), LB := ((2385214691426607 : Rat) / 2000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6096633061 : Rat) / 2560000000), R := ((12200670721 : Rat) / 5120000000), D0 := ((12200670721 : Rat) / 5120000000), D1 := ((2895198209 : Rat) / 5120000000), D2 := ((451680539 : Rat) / 2560000000), D3 := ((2456228730468750021 : Rat) / 10000000000000000000), D4 := ((4029932855468749 : Rat) / 10000000000000000), LB := ((774324865355459 : Rat) / 625000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12200670721 : Rat) / 5120000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((895956479 : Rat) / 5120000000), D3 := ((2441766623046875021 : Rat) / 10000000000000000000), D4 := ((2007735374023437 : Rat) / 5000000000000000), LB := ((6509505287896067 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((12215479919 : Rat) / 5120000000), D0 := ((12215479919 : Rat) / 5120000000), D1 := ((2910007407 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((2427304515625000021 : Rat) / 10000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((6908368286854469 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12215479919 : Rat) / 5120000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((881147281 : Rat) / 5120000000), D3 := ((2412842408203125021 : Rat) / 10000000000000000000), D4 := ((996636633300781 : Rat) / 2500000000000000), LB := ((739181374045661 : Rat) / 500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((12230289117 : Rat) / 5120000000), D0 := ((12230289117 : Rat) / 5120000000), D1 := ((584963321 : Rat) / 1024000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((2398380300781250021 : Rat) / 10000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((3184192447530737 : Rat) / 2000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12230289117 : Rat) / 5120000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((866338083 : Rat) / 5120000000), D3 := ((2383918193359375021 : Rat) / 10000000000000000000), D4 := ((1978811159179687 : Rat) / 5000000000000000), LB := ((17230047684752559 : Rat) / 10000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((2449019663 : Rat) / 1024000000), D0 := ((2449019663 : Rat) / 1024000000), D1 := ((2939625803 : Rat) / 5120000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((2369456085937500021 : Rat) / 10000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((187122191841807 : Rat) / 100000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2449019663 : Rat) / 1024000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((170305777 : Rat) / 1024000000), D3 := ((2354993978515625021 : Rat) / 10000000000000000000), D4 := ((491087262939453 : Rat) / 1250000000000000), LB := ((4073768251837917 : Rat) / 2000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((2340531871093750021 : Rat) / 10000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((355914941254417 : Rat) / 3125000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2311607656250000021 : Rat) / 10000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((5419251534574537 : Rat) / 10000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((2282683441406250021 : Rat) / 10000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((1302462961843831 : Rat) / 1250000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((6155869853 : Rat) / 2560000000), D0 := ((6155869853 : Rat) / 2560000000), D1 := ((1503133597 : Rat) / 2560000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((2253759226562500021 : Rat) / 10000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((8076298026202383 : Rat) / 5000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6155869853 : Rat) / 2560000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((392443747 : Rat) / 2560000000), D3 := ((2224835011718750021 : Rat) / 10000000000000000000), D4 := ((3798539136718749 : Rat) / 10000000000000000), LB := ((2263078840060523 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2195910796875000021 : Rat) / 10000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((7466928852504079 : Rat) / 2500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((2166986582031250021 : Rat) / 10000000000000000000), D4 := ((3740690707031249 : Rat) / 10000000000000000), LB := ((7575483056141863 : Rat) / 2000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((2138062367187500021 : Rat) / 10000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((5784035974099877 : Rat) / 10000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2080213937500000021 : Rat) / 10000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((203964294980851 : Rat) / 78125000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((2022365507812500021 : Rat) / 10000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((1244216676792833 : Rat) / 250000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((1964517078125000021 : Rat) / 10000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((7691175322212543 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((1906668648437500021 : Rat) / 10000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((5384730772954177 : Rat) / 500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((1848820218750000021 : Rat) / 10000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((6387213150694723 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((1733123359375000021 : Rat) / 10000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((7319106963172263 : Rat) / 500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((1617426500000000021 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((239207997065137 : Rat) / 25000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1386032781250000021 : Rat) / 10000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((1133966771386673 : Rat) / 31250000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1154639062500000021 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((22703577278139833 : Rat) / 500000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((26271201625000000021 : Rat) / 10000000000000000000), D0 := ((26271201625000000021 : Rat) / 10000000000000000000), D1 := ((8096450625000000021 : Rat) / 10000000000000000000), D2 := ((691851625000000021 : Rat) / 10000000000000000000), D3 := ((691851625000000021 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((59047547124863 : Rat) / 400000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26271201625000000021 : Rat) / 10000000000000000000), R := ((133920491785714285863 : Rat) / 50000000000000000000), D0 := ((133920491785714285863 : Rat) / 50000000000000000000), D1 := ((43046736785714285863 : Rat) / 50000000000000000000), D2 := ((6023741785714285863 : Rat) / 50000000000000000000), D3 := ((1282241830357142879 : Rat) / 25000000000000000000), D4 := ((1573704124999998979 : Rat) / 10000000000000000000), LB := ((5385380371032019 : Rat) / 25000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((133920491785714285863 : Rat) / 50000000000000000000), R := ((67601366808035714371 : Rat) / 25000000000000000000), D0 := ((67601366808035714371 : Rat) / 25000000000000000000), D1 := ((22164489308035714371 : Rat) / 25000000000000000000), D2 := ((3652991808035714371 : Rat) / 25000000000000000000), D3 := ((3846725491071428637 : Rat) / 50000000000000000000), D4 := ((5304036964285709137 : Rat) / 50000000000000000000), LB := ((1006250787977403 : Rat) / 12500000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67601366808035714371 : Rat) / 25000000000000000000), R := ((271687709062500000363 : Rat) / 100000000000000000000), D0 := ((271687709062500000363 : Rat) / 100000000000000000000), D1 := ((89940199062500000363 : Rat) / 100000000000000000000), D2 := ((15894209062500000363 : Rat) / 100000000000000000000), D3 := ((8975692812500000153 : Rat) / 100000000000000000000), D4 := ((2010897566964283129 : Rat) / 25000000000000000000), LB := ((347767599884897 : Rat) / 10000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((271687709062500000363 : Rat) / 100000000000000000000), R := ((108931531991071428721 : Rat) / 40000000000000000000), D0 := ((108931531991071428721 : Rat) / 40000000000000000000), D1 := ((36232527991071428721 : Rat) / 40000000000000000000), D2 := ((6614131991071428721 : Rat) / 40000000000000000000), D3 := ((3846725491071428637 : Rat) / 40000000000000000000), D4 := ((6761348437499989637 : Rat) / 100000000000000000000), LB := ((1065203674519977 : Rat) / 62500000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((108931531991071428721 : Rat) / 40000000000000000000), R := ((1090597561741071430089 : Rat) / 400000000000000000000), D0 := ((1090597561741071430089 : Rat) / 400000000000000000000), D1 := ((363607521741071430089 : Rat) / 400000000000000000000), D2 := ((67423561741071430089 : Rat) / 400000000000000000000), D3 := ((39749496741071429249 : Rat) / 400000000000000000000), D4 := ((2448091008928567279 : Rat) / 40000000000000000000), LB := ((9623756126128591 : Rat) / 1000000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1090597561741071430089 : Rat) / 400000000000000000000), R := ((2182477365312500003057 : Rat) / 800000000000000000000), D0 := ((2182477365312500003057 : Rat) / 800000000000000000000), D1 := ((728497285312500003057 : Rat) / 800000000000000000000), D2 := ((136129365312500003057 : Rat) / 800000000000000000000), D3 := ((80781235312500001377 : Rat) / 800000000000000000000), D4 := ((23198668258928529911 : Rat) / 400000000000000000000), LB := ((631858842905389 : Rat) / 100000000000000000) },
  { w1 := ((1200458340865571 : Rat) / 2000000000000000), w2 := (0 : Rat), w3 := ((3317463944587981 : Rat) / 10000000000000000), w4 := ((6780793405623121 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26271201625000000021 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2182477365312500003057 : Rat) / 800000000000000000000), R := ((136484975446428571621 : Rat) / 50000000000000000000), D0 := ((136484975446428571621 : Rat) / 50000000000000000000), D1 := ((45611220446428571621 : Rat) / 50000000000000000000), D2 := ((8588225446428571621 : Rat) / 50000000000000000000), D3 := ((1282241830357142879 : Rat) / 12500000000000000000), D4 := ((45115094687499916943 : Rat) / 800000000000000000000), LB := ((13515665374320973 : Rat) / 10000000000000000000) }
]

def block449RightChunk000L : Rat := ((1729504017857142861 : Rat) / 1000000000000000000)
def block449RightChunk000R : Rat := ((136484975446428571621 : Rat) / 50000000000000000000)

def block449RightChunk000Certificate : Bool :=
  allBoxesValid block449RightChunk000 &&
  coversFromBool block449RightChunk000 block449RightChunk000L block449RightChunk000R

theorem block449RightChunk000Certificate_eq_true :
    block449RightChunk000Certificate = true := by
  native_decide

def block449RightChainCertificate : Bool :=
  decide (
    block449RightL = ((1729504017857142861 : Rat) / 1000000000000000000) /\
    ((136484975446428571621 : Rat) / 50000000000000000000) = block449RightR)

theorem block449RightChainCertificate_eq_true :
    block449RightChainCertificate = true := by
  native_decide

def block449LeftBoxCount : Nat := boxCount block449LeftBoxes
def block449RightBoxCount : Nat := 69

def block449_rational_certificate : Prop :=
    block449LeftCertificate = true /\
    block449RightChainCertificate = true /\
    block449RightChunk000Certificate = true

theorem block449_rational_certificate_proof :
    block449_rational_certificate := by
  exact ⟨block449LeftCertificate_eq_true, block449RightChainCertificate_eq_true, block449RightChunk000Certificate_eq_true⟩

end Block449
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block449

open Set

def block449W1 : Rat := ((1200458340865571 : Rat) / 2000000000000000)
def block449W2 : Rat := (0 : Rat)
def block449W3 : Rat := ((3317463944587981 : Rat) / 10000000000000000)
def block449W4 : Rat := ((6780793405623121 : Rat) / 100000000000000000)
def block449S1 : Rat := ((18174751 : Rat) / 10000000)
def block449S2 : Rat := ((511587 : Rat) / 200000)
def block449S3 : Rat := ((26271201625000000021 : Rat) / 10000000000000000000)
def block449S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block449V (y : ℝ) : ℝ :=
  ratPotential block449W1 block449W2 block449W3 block449W4 block449S1 block449S2 block449S3 block449S4 y

def block449LeftParamsCertificate : Bool :=
  allBoxesSameParams block449LeftBoxes block449W1 block449W2 block449W3 block449W4 block449S1 block449S2 block449S3 block449S4

theorem block449LeftParamsCertificate_eq_true :
    block449LeftParamsCertificate = true := by
  native_decide

theorem block449_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block449LeftL : ℝ) (block449LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block449S1 : ℝ))
    (hy2ne : y ≠ (block449S2 : ℝ))
    (hy3ne : y ≠ (block449S3 : ℝ))
    (hy4ne : y ≠ (block449S4 : ℝ)) :
    0 < block449V y := by
  have hcert := block449LeftCertificate_eq_true
  unfold block449LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block449LeftBoxes) (lo := block449LeftL) (hi := block449LeftR)
    (w1 := block449W1) (w2 := block449W2) (w3 := block449W3) (w4 := block449W4)
    (s1 := block449S1) (s2 := block449S2) (s3 := block449S3) (s4 := block449S4)
    hboxes hcover block449LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block449RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block449RightChunk000 block449W1 block449W2 block449W3 block449W4 block449S1 block449S2 block449S3 block449S4

theorem block449RightChunk000ParamsCertificate_eq_true :
    block449RightChunk000ParamsCertificate = true := by
  native_decide

theorem block449_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block449RightChunk000L : ℝ) (block449RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block449S1 : ℝ))
    (hy2ne : y ≠ (block449S2 : ℝ))
    (hy3ne : y ≠ (block449S3 : ℝ))
    (hy4ne : y ≠ (block449S4 : ℝ)) :
    0 < block449V y := by
  have hcert := block449RightChunk000Certificate_eq_true
  unfold block449RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block449RightChunk000) (lo := block449RightChunk000L) (hi := block449RightChunk000R)
    (w1 := block449W1) (w2 := block449W2) (w3 := block449W3) (w4 := block449W4)
    (s1 := block449S1) (s2 := block449S2) (s3 := block449S3) (s4 := block449S4)
    hboxes hcover block449RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block449_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block449RightL : ℝ) (block449RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block449S1 : ℝ))
    (hy2ne : y ≠ (block449S2 : ℝ))
    (hy3ne : y ≠ (block449S3 : ℝ))
    (hy4ne : y ≠ (block449S4 : ℝ)) :
    0 < block449V y := by
  have hL : (block449RightChunk000L : ℝ) = (block449RightL : ℝ) := by
    norm_num [block449RightChunk000L, block449RightL]
  have hR : (block449RightChunk000R : ℝ) = (block449RightR : ℝ) := by
    norm_num [block449RightChunk000R, block449RightR]
  have hyc : y ∈ Icc (block449RightChunk000L : ℝ) (block449RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block449_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block449_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block449LeftL : ℝ) (block449LeftR : ℝ) →
    y ≠ 0 → y ≠ (block449S1 : ℝ) → y ≠ (block449S2 : ℝ) →
    y ≠ (block449S3 : ℝ) → y ≠ (block449S4 : ℝ) → 0 < block449V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block449RightL : ℝ) (block449RightR : ℝ) →
    y ≠ 0 → y ≠ (block449S1 : ℝ) → y ≠ (block449S2 : ℝ) →
    y ≠ (block449S3 : ℝ) → y ≠ (block449S4 : ℝ) → 0 < block449V y)

theorem block449_reallog_certificate_proof :
    block449_reallog_certificate := by
  exact ⟨block449_left_V_pos, block449_right_V_pos⟩

end Block449
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block449.block449V
#check Erdos1038Lean.M1817475.Block449.block449_left_V_pos
#check Erdos1038Lean.M1817475.Block449.block449_right_V_pos
#check Erdos1038Lean.M1817475.Block449.block449_reallog_certificate_proof
