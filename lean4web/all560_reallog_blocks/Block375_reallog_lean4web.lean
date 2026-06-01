/-
Self-contained Lean4Web paste file.
Block 375 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block375

def block375LeftL : Rat := ((4649814732142857163 : Rat) / 6250000000000000000)
def block375LeftR : Rat := ((297666339285714287 : Rat) / 400000000000000000)
def block375RightL : Rat := ((10899814732142857163 : Rat) / 6250000000000000000)
def block375RightR : Rat := ((1097666339285714287 : Rat) / 400000000000000000)

def block375LeftBoxes : List RatBox := [
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4649814732142857163 : Rat) / 6250000000000000000), R := ((297666339285714287 : Rat) / 400000000000000000), D0 := ((297666339285714287 : Rat) / 400000000000000000), D1 := ((6709404642857142837 : Rat) / 6250000000000000000), D2 := ((11337279017857142837 : Rat) / 6250000000000000000), D3 := ((95604124196428571309 : Rat) / 50000000000000000000), D4 := ((50709994285714283147 : Rat) / 25000000000000000000), LB := ((3102813948141603 : Rat) / 500000000000000000) }
]

def block375LeftCertificate : Bool :=
  allBoxesValid block375LeftBoxes &&
  coversFromBool block375LeftBoxes block375LeftL block375LeftR

theorem block375LeftCertificate_eq_true :
    block375LeftCertificate = true := by
  native_decide

def block375RightChunk000 : List RatBox := [
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((10899814732142857163 : Rat) / 6250000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((459404642857142837 : Rat) / 6250000000000000000), D2 := ((5087279017857142837 : Rat) / 6250000000000000000), D3 := ((45604124196428571309 : Rat) / 50000000000000000000), D4 := ((25709994285714283147 : Rat) / 25000000000000000000), LB := ((16640101610140123 : Rat) / 10000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41928887053571428613 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((2959598871569027 : Rat) / 25000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23417389553571428613 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((3883966829320539 : Rat) / 50000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18789515178571428613 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((23909872432272647 : Rat) / 500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16475577991071428613 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((5336633241859047 : Rat) / 125000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((15318609397321428613 : Rat) / 50000000000000000000), D4 := ((10567236886160711799 : Rat) / 25000000000000000000), LB := ((20144042461260517 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14161640803571428613 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((10792623755817021 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13004672209821428613 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((7205259087711607 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12426187912946428613 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((7018900173988707 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11847703616071428613 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((2909310829059611 : Rat) / 500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11558461467633928613 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((34703860268178177 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11269219319196428613 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((3574127684511999 : Rat) / 2500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10979977170758928613 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((9757950433346041 : Rat) / 2000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10835356096540178613 : Rat) / 50000000000000000000), D4 := ((8325610235770086799 : Rat) / 25000000000000000000), LB := ((515502854142983 : Rat) / 125000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10690735022321428613 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((2159484141173 : Rat) / 625000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10546113948102678613 : Rat) / 50000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((7186533924271321 : Rat) / 2500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10401492873883928613 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((23846712713682383 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10256871799665178613 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((19878415895311363 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10112250725446428613 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((3373591990637137 : Rat) / 2000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9967629651227678613 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((14844009560756877 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9823008577008928613 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((2767475363051053 : Rat) / 2000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9678387502790178613 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((1388124640978483 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9533766428571428613 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((15011433468337387 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9389145354352678613 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((3453336015929287 : Rat) / 2000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9244524280133928613 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((1034449896584827 : Rat) / 500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9099903205915178613 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((2532406618265287 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8955282131696428613 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((15610847960842583 : Rat) / 5000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8810661057477678613 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((19218187716721763 : Rat) / 5000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8666039983258928613 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((4702791419949531 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8521418909040178613 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((2853110422650823 : Rat) / 500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8376797834821428613 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((404753136708863 : Rat) / 200000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8087555686383928613 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((1213928807192989 : Rat) / 250000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7798313537946428613 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((4201956690878597 : Rat) / 500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7509071389508928613 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((12766989685301683 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7219829241071428613 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((435623671910941 : Rat) / 50000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6641344944196428613 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((23067270957580377 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6062860647321428613 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((2661546087959371 : Rat) / 100000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516492892053571428613 : Rat) / 200000000000000000000), D0 := ((516492892053571428613 : Rat) / 200000000000000000000), D1 := ((152997872053571428613 : Rat) / 200000000000000000000), D2 := ((4905892053571428613 : Rat) / 200000000000000000000), D3 := ((4905892053571428613 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((1693454626376799 : Rat) / 50000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516492892053571428613 : Rat) / 200000000000000000000), R := ((260699392053571428613 : Rat) / 100000000000000000000), D0 := ((260699392053571428613 : Rat) / 100000000000000000000), D1 := ((78951882053571428613 : Rat) / 100000000000000000000), D2 := ((4905892053571428613 : Rat) / 100000000000000000000), D3 := ((14717676160714285839 : Rat) / 200000000000000000000), D4 := ((37981133660714265779 : Rat) / 200000000000000000000), LB := ((26957137198248687 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((260699392053571428613 : Rat) / 100000000000000000000), R := ((132802642053571428613 : Rat) / 50000000000000000000), D0 := ((132802642053571428613 : Rat) / 50000000000000000000), D1 := ((41928887053571428613 : Rat) / 50000000000000000000), D2 := ((4905892053571428613 : Rat) / 50000000000000000000), D3 := ((4905892053571428613 : Rat) / 100000000000000000000), D4 := ((16537620803571418583 : Rat) / 100000000000000000000), LB := ((109325121800701 : Rat) / 15625000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((132802642053571428613 : Rat) / 50000000000000000000), R := ((267808109285714285857 : Rat) / 100000000000000000000), D0 := ((267808109285714285857 : Rat) / 100000000000000000000), D1 := ((86060599285714285857 : Rat) / 100000000000000000000), D2 := ((12014609285714285857 : Rat) / 100000000000000000000), D3 := ((2202825178571428631 : Rat) / 100000000000000000000), D4 := ((1163172874999998997 : Rat) / 10000000000000000000), LB := ((1416684561156089 : Rat) / 10000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((267808109285714285857 : Rat) / 100000000000000000000), R := ((33751366808035714311 : Rat) / 12500000000000000000), D0 := ((33751366808035714311 : Rat) / 12500000000000000000), D1 := ((11032928058035714311 : Rat) / 12500000000000000000), D2 := ((1777179308035714311 : Rat) / 12500000000000000000), D3 := ((2202825178571428631 : Rat) / 50000000000000000000), D4 := ((9428903571428561339 : Rat) / 100000000000000000000), LB := ((2473476859358331 : Rat) / 100000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((33751366808035714311 : Rat) / 12500000000000000000), R := ((542224694107142857607 : Rat) / 200000000000000000000), D0 := ((542224694107142857607 : Rat) / 200000000000000000000), D1 := ((178729674107142857607 : Rat) / 200000000000000000000), D2 := ((30637694107142857607 : Rat) / 200000000000000000000), D3 := ((2202825178571428631 : Rat) / 40000000000000000000), D4 := ((1806519598214283177 : Rat) / 25000000000000000000), LB := ((1103448268937289 : Rat) / 125000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((542224694107142857607 : Rat) / 200000000000000000000), R := ((217330442678571428769 : Rat) / 80000000000000000000), D0 := ((217330442678571428769 : Rat) / 80000000000000000000), D1 := ((71932434678571428769 : Rat) / 80000000000000000000), D2 := ((12695642678571428769 : Rat) / 80000000000000000000), D3 := ((24231076964285714941 : Rat) / 400000000000000000000), D4 := ((2449866321428567357 : Rat) / 40000000000000000000), LB := ((4047664597809947 : Rat) / 500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((217330442678571428769 : Rat) / 80000000000000000000), R := ((2175507251964285716321 : Rat) / 800000000000000000000), D0 := ((2175507251964285716321 : Rat) / 800000000000000000000), D1 := ((721527171964285716321 : Rat) / 800000000000000000000), D2 := ((129159251964285716321 : Rat) / 800000000000000000000), D3 := ((50664979107142858513 : Rat) / 800000000000000000000), D4 := ((22295838035714244939 : Rat) / 400000000000000000000), LB := ((2470099475567769 : Rat) / 250000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2175507251964285716321 : Rat) / 800000000000000000000), R := ((272213759642857143119 : Rat) / 100000000000000000000), D0 := ((272213759642857143119 : Rat) / 100000000000000000000), D1 := ((90466249642857143119 : Rat) / 100000000000000000000), D2 := ((16420259642857143119 : Rat) / 100000000000000000000), D3 := ((6608475535714285893 : Rat) / 100000000000000000000), D4 := ((42388850892857061247 : Rat) / 800000000000000000000), LB := ((2943366864275293 : Rat) / 500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272213759642857143119 : Rat) / 100000000000000000000), R := ((2179912902321428573583 : Rat) / 800000000000000000000), D0 := ((2179912902321428573583 : Rat) / 800000000000000000000), D1 := ((725932822321428573583 : Rat) / 800000000000000000000), D2 := ((133564902321428573583 : Rat) / 800000000000000000000), D3 := ((2202825178571428631 : Rat) / 32000000000000000000), D4 := ((5023253214285704077 : Rat) / 100000000000000000000), LB := ((2565924349149873 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2179912902321428573583 : Rat) / 800000000000000000000), R := ((4362028629821428575797 : Rat) / 1600000000000000000000), D0 := ((4362028629821428575797 : Rat) / 1600000000000000000000), D1 := ((1454068469821428575797 : Rat) / 1600000000000000000000), D2 := ((269332629821428575797 : Rat) / 1600000000000000000000), D3 := ((112344084107142860181 : Rat) / 1600000000000000000000), D4 := ((7596640107142840797 : Rat) / 160000000000000000000), LB := ((258286114337547 : Rat) / 50000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4362028629821428575797 : Rat) / 1600000000000000000000), R := ((1091057863750000001107 : Rat) / 400000000000000000000), D0 := ((1091057863750000001107 : Rat) / 400000000000000000000), D1 := ((364067823750000001107 : Rat) / 400000000000000000000), D2 := ((67883863750000001107 : Rat) / 400000000000000000000), D3 := ((28636727321428572203 : Rat) / 400000000000000000000), D4 := ((73763575892856979339 : Rat) / 1600000000000000000000), LB := ((1014586002566667 : Rat) / 250000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1091057863750000001107 : Rat) / 400000000000000000000), R := ((4366434280178571433059 : Rat) / 1600000000000000000000), D0 := ((4366434280178571433059 : Rat) / 1600000000000000000000), D1 := ((1458474120178571433059 : Rat) / 1600000000000000000000), D2 := ((273738280178571433059 : Rat) / 1600000000000000000000), D3 := ((116749734464285717443 : Rat) / 1600000000000000000000), D4 := ((17890187678571387677 : Rat) / 400000000000000000000), LB := ((3139100978091891 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4366434280178571433059 : Rat) / 1600000000000000000000), R := ((436863710535714286169 : Rat) / 160000000000000000000), D0 := ((436863710535714286169 : Rat) / 160000000000000000000), D1 := ((146067694535714286169 : Rat) / 160000000000000000000), D2 := ((27594110535714286169 : Rat) / 160000000000000000000), D3 := ((59476279821428573037 : Rat) / 800000000000000000000), D4 := ((69357925535714122077 : Rat) / 1600000000000000000000), LB := ((150848980236859 : Rat) / 62500000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((436863710535714286169 : Rat) / 160000000000000000000), R := ((4370839930535714290321 : Rat) / 1600000000000000000000), D0 := ((4370839930535714290321 : Rat) / 1600000000000000000000), D1 := ((1462879770535714290321 : Rat) / 1600000000000000000000), D2 := ((278143930535714290321 : Rat) / 1600000000000000000000), D3 := ((24231076964285714941 : Rat) / 320000000000000000000), D4 := ((33577550178571346723 : Rat) / 800000000000000000000), LB := ((18882596459394163 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4370839930535714290321 : Rat) / 1600000000000000000000), R := ((546630344464285714869 : Rat) / 200000000000000000000), D0 := ((546630344464285714869 : Rat) / 200000000000000000000), D1 := ((183135324464285714869 : Rat) / 200000000000000000000), D2 := ((35043344464285714869 : Rat) / 200000000000000000000), D3 := ((15419776250000000417 : Rat) / 200000000000000000000), D4 := ((12990455035714252963 : Rat) / 320000000000000000000), LB := ((7852828726966077 : Rat) / 5000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546630344464285714869 : Rat) / 200000000000000000000), R := ((4375245580892857147583 : Rat) / 1600000000000000000000), D0 := ((4375245580892857147583 : Rat) / 1600000000000000000000), D1 := ((1467285420892857147583 : Rat) / 1600000000000000000000), D2 := ((282549580892857147583 : Rat) / 1600000000000000000000), D3 := ((125561035178571431967 : Rat) / 1600000000000000000000), D4 := ((7843681249999979523 : Rat) / 200000000000000000000), LB := ((14690187512798603 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4375245580892857147583 : Rat) / 1600000000000000000000), R := ((2188724203035714288107 : Rat) / 800000000000000000000), D0 := ((2188724203035714288107 : Rat) / 800000000000000000000), D1 := ((734744123035714288107 : Rat) / 800000000000000000000), D2 := ((142376203035714288107 : Rat) / 800000000000000000000), D3 := ((63881930178571430299 : Rat) / 800000000000000000000), D4 := ((60546624821428407553 : Rat) / 1600000000000000000000), LB := ((7966738474494417 : Rat) / 5000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2188724203035714288107 : Rat) / 800000000000000000000), R := ((875930246250000000969 : Rat) / 320000000000000000000), D0 := ((875930246250000000969 : Rat) / 320000000000000000000), D1 := ((294338214250000000969 : Rat) / 320000000000000000000), D2 := ((57391046250000000969 : Rat) / 320000000000000000000), D3 := ((129966685535714289229 : Rat) / 1600000000000000000000), D4 := ((29171899821428489461 : Rat) / 800000000000000000000), LB := ((610828978369303 : Rat) / 312500000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((875930246250000000969 : Rat) / 320000000000000000000), R := ((1095463514107142858369 : Rat) / 400000000000000000000), D0 := ((1095463514107142858369 : Rat) / 400000000000000000000), D1 := ((368473474107142858369 : Rat) / 400000000000000000000), D2 := ((72289514107142858369 : Rat) / 400000000000000000000), D3 := ((6608475535714285893 : Rat) / 80000000000000000000), D4 := ((56140974464285550291 : Rat) / 1600000000000000000000), LB := ((25655964020051547 : Rat) / 10000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1095463514107142858369 : Rat) / 400000000000000000000), R := ((4384056881607142862107 : Rat) / 1600000000000000000000), D0 := ((4384056881607142862107 : Rat) / 1600000000000000000000), D1 := ((1476096721607142862107 : Rat) / 1600000000000000000000), D2 := ((291360881607142862107 : Rat) / 1600000000000000000000), D3 := ((134372335892857146491 : Rat) / 1600000000000000000000), D4 := ((2696907464285706083 : Rat) / 80000000000000000000), LB := ((1720317455235043 : Rat) / 500000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4384056881607142862107 : Rat) / 1600000000000000000000), R := ((2193129853392857145369 : Rat) / 800000000000000000000), D0 := ((2193129853392857145369 : Rat) / 800000000000000000000), D1 := ((739149773392857145369 : Rat) / 800000000000000000000), D2 := ((146781853392857145369 : Rat) / 800000000000000000000), D3 := ((68287580535714287561 : Rat) / 800000000000000000000), D4 := ((51735324107142693029 : Rat) / 1600000000000000000000), LB := ((4596299235193613 : Rat) / 1000000000000000000) },
  { w1 := ((8586168311867867 : Rat) / 10000000000000000), w2 := ((4677473788702693 : Rat) / 100000000000000000), w3 := ((15661859488264807 : Rat) / 100000000000000000), w4 := ((8749679626733 : Rat) / 62500000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132802642053571428613 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2193129853392857145369 : Rat) / 800000000000000000000), R := ((1097666339285714287 : Rat) / 400000000000000000), D0 := ((1097666339285714287 : Rat) / 400000000000000000), D1 := ((370676299285714287 : Rat) / 400000000000000000), D2 := ((74492339285714287 : Rat) / 400000000000000000), D3 := ((2202825178571428631 : Rat) / 25000000000000000000), D4 := ((24766249464285632199 : Rat) / 800000000000000000000), LB := ((7297812248127089 : Rat) / 5000000000000000000) }
]

def block375RightChunk000L : Rat := ((10899814732142857163 : Rat) / 6250000000000000000)
def block375RightChunk000R : Rat := ((1097666339285714287 : Rat) / 400000000000000000)

def block375RightChunk000Certificate : Bool :=
  allBoxesValid block375RightChunk000 &&
  coversFromBool block375RightChunk000 block375RightChunk000L block375RightChunk000R

theorem block375RightChunk000Certificate_eq_true :
    block375RightChunk000Certificate = true := by
  native_decide

def block375RightChainCertificate : Bool :=
  decide (
    block375RightL = ((10899814732142857163 : Rat) / 6250000000000000000) /\
    ((1097666339285714287 : Rat) / 400000000000000000) = block375RightR)

theorem block375RightChainCertificate_eq_true :
    block375RightChainCertificate = true := by
  native_decide

def block375LeftBoxCount : Nat := boxCount block375LeftBoxes
def block375RightBoxCount : Nat := 60

def block375_rational_certificate : Prop :=
    block375LeftCertificate = true /\
    block375RightChainCertificate = true /\
    block375RightChunk000Certificate = true

theorem block375_rational_certificate_proof :
    block375_rational_certificate := by
  exact ⟨block375LeftCertificate_eq_true, block375RightChainCertificate_eq_true, block375RightChunk000Certificate_eq_true⟩

end Block375
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block375

open Set

def block375W1 : Rat := ((8586168311867867 : Rat) / 10000000000000000)
def block375W2 : Rat := ((4677473788702693 : Rat) / 100000000000000000)
def block375W3 : Rat := ((15661859488264807 : Rat) / 100000000000000000)
def block375W4 : Rat := ((8749679626733 : Rat) / 62500000000000)
def block375S1 : Rat := ((18174751 : Rat) / 10000000)
def block375S2 : Rat := ((511587 : Rat) / 200000)
def block375S3 : Rat := ((132802642053571428613 : Rat) / 50000000000000000000)
def block375S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block375V (y : ℝ) : ℝ :=
  ratPotential block375W1 block375W2 block375W3 block375W4 block375S1 block375S2 block375S3 block375S4 y

def block375LeftParamsCertificate : Bool :=
  allBoxesSameParams block375LeftBoxes block375W1 block375W2 block375W3 block375W4 block375S1 block375S2 block375S3 block375S4

theorem block375LeftParamsCertificate_eq_true :
    block375LeftParamsCertificate = true := by
  native_decide

theorem block375_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block375LeftL : ℝ) (block375LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block375S1 : ℝ))
    (hy2ne : y ≠ (block375S2 : ℝ))
    (hy3ne : y ≠ (block375S3 : ℝ))
    (hy4ne : y ≠ (block375S4 : ℝ)) :
    0 < block375V y := by
  have hcert := block375LeftCertificate_eq_true
  unfold block375LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block375LeftBoxes) (lo := block375LeftL) (hi := block375LeftR)
    (w1 := block375W1) (w2 := block375W2) (w3 := block375W3) (w4 := block375W4)
    (s1 := block375S1) (s2 := block375S2) (s3 := block375S3) (s4 := block375S4)
    hboxes hcover block375LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block375RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block375RightChunk000 block375W1 block375W2 block375W3 block375W4 block375S1 block375S2 block375S3 block375S4

theorem block375RightChunk000ParamsCertificate_eq_true :
    block375RightChunk000ParamsCertificate = true := by
  native_decide

theorem block375_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block375RightChunk000L : ℝ) (block375RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block375S1 : ℝ))
    (hy2ne : y ≠ (block375S2 : ℝ))
    (hy3ne : y ≠ (block375S3 : ℝ))
    (hy4ne : y ≠ (block375S4 : ℝ)) :
    0 < block375V y := by
  have hcert := block375RightChunk000Certificate_eq_true
  unfold block375RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block375RightChunk000) (lo := block375RightChunk000L) (hi := block375RightChunk000R)
    (w1 := block375W1) (w2 := block375W2) (w3 := block375W3) (w4 := block375W4)
    (s1 := block375S1) (s2 := block375S2) (s3 := block375S3) (s4 := block375S4)
    hboxes hcover block375RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block375_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block375RightL : ℝ) (block375RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block375S1 : ℝ))
    (hy2ne : y ≠ (block375S2 : ℝ))
    (hy3ne : y ≠ (block375S3 : ℝ))
    (hy4ne : y ≠ (block375S4 : ℝ)) :
    0 < block375V y := by
  have hL : (block375RightChunk000L : ℝ) = (block375RightL : ℝ) := by
    norm_num [block375RightChunk000L, block375RightL]
  have hR : (block375RightChunk000R : ℝ) = (block375RightR : ℝ) := by
    norm_num [block375RightChunk000R, block375RightR]
  have hyc : y ∈ Icc (block375RightChunk000L : ℝ) (block375RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block375_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block375_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block375LeftL : ℝ) (block375LeftR : ℝ) →
    y ≠ 0 → y ≠ (block375S1 : ℝ) → y ≠ (block375S2 : ℝ) →
    y ≠ (block375S3 : ℝ) → y ≠ (block375S4 : ℝ) → 0 < block375V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block375RightL : ℝ) (block375RightR : ℝ) →
    y ≠ 0 → y ≠ (block375S1 : ℝ) → y ≠ (block375S2 : ℝ) →
    y ≠ (block375S3 : ℝ) → y ≠ (block375S4 : ℝ) → 0 < block375V y)

theorem block375_reallog_certificate_proof :
    block375_reallog_certificate := by
  exact ⟨block375_left_V_pos, block375_right_V_pos⟩

end Block375
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block375.block375V
#check Erdos1038Lean.M1817475.Block375.block375_left_V_pos
#check Erdos1038Lean.M1817475.Block375.block375_right_V_pos
#check Erdos1038Lean.M1817475.Block375.block375_reallog_certificate_proof
