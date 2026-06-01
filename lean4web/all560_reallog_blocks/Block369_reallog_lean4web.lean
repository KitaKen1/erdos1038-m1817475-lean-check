/-
Self-contained Lean4Web paste file.
Block 369 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block369

def block369LeftL : Rat := ((3725716517857142873 : Rat) / 5000000000000000000)
def block369LeftR : Rat := ((37266939732142857301 : Rat) / 50000000000000000000)
def block369RightL : Rat := ((8725716517857142873 : Rat) / 5000000000000000000)
def block369RightR : Rat := ((137266939732142857301 : Rat) / 50000000000000000000)

def block369LeftBoxes : List RatBox := [
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3725716517857142873 : Rat) / 5000000000000000000), R := ((37266939732142857301 : Rat) / 50000000000000000000), D0 := ((37266939732142857301 : Rat) / 50000000000000000000), D1 := ((5361658982142857127 : Rat) / 5000000000000000000), D2 := ((9063958482142857127 : Rat) / 5000000000000000000), D3 := ((19132554303571428547 : Rat) / 10000000000000000000), D4 := ((25340335312499998717 : Rat) / 12500000000000000000), LB := ((247249764506271 : Rat) / 40000000000000000) }
]

def block369LeftCertificate : Bool :=
  allBoxesValid block369LeftBoxes &&
  coversFromBool block369LeftBoxes block369LeftL block369LeftR

theorem block369LeftCertificate_eq_true :
    block369LeftCertificate = true := by
  native_decide

def block369RightChunk000 : List RatBox := [
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8725716517857142873 : Rat) / 5000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((361658982142857127 : Rat) / 5000000000000000000), D2 := ((4063958482142857127 : Rat) / 5000000000000000000), D3 := ((9132554303571428547 : Rat) / 10000000000000000000), D4 := ((12840335312499998717 : Rat) / 12500000000000000000), LB := ((17057926046783287 : Rat) / 10000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8409236339285714293 : Rat) / 10000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((2566101687047443 : Rat) / 20000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4706936839285714293 : Rat) / 10000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((523694858497111 : Rat) / 6250000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3781361964285714293 : Rat) / 10000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((1308213807804669 : Rat) / 25000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3318574526785714293 : Rat) / 10000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((1854477701562377 : Rat) / 40000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((3087180808035714293 : Rat) / 10000000000000000000), D4 := ((10567236886160711799 : Rat) / 25000000000000000000), LB := ((578760608362457 : Rat) / 25000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2855787089285714293 : Rat) / 10000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((213774796576513 : Rat) / 62500000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2624393370535714293 : Rat) / 10000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((17733974618237 : Rat) / 1953125000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2508696511160714293 : Rat) / 10000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((223016441472057 : Rat) / 100000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2392999651785714293 : Rat) / 10000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((7097021861192099 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((2335151222098214293 : Rat) / 10000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((4570154277602073 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2277302792410714293 : Rat) / 10000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((5872885279085971 : Rat) / 2500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2219454362723214293 : Rat) / 10000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((1117661171082529 : Rat) / 2500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2161605933035714293 : Rat) / 10000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((2028809002330087 : Rat) / 500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((2132681718191964293 : Rat) / 10000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((676798568245629 : Rat) / 200000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2103757503348214293 : Rat) / 10000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((2800415477455881 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2074833288504464293 : Rat) / 10000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((115467645400201 : Rat) / 50000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2045909073660714293 : Rat) / 10000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((19134488442596187 : Rat) / 10000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((2016984858816964293 : Rat) / 10000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((8077705403004981 : Rat) / 5000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((1988060643973214293 : Rat) / 10000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((1418681228728541 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((1959136429129464293 : Rat) / 10000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((2652314461314531 : Rat) / 2000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((1930212214285714293 : Rat) / 10000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((13415191480410649 : Rat) / 10000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((1901287999441964293 : Rat) / 10000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((1835761043171083 : Rat) / 1250000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((1872363784598214293 : Rat) / 10000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((4278985588433773 : Rat) / 2500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((1843439569754464293 : Rat) / 10000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((20750092328231107 : Rat) / 10000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((1814515354910714293 : Rat) / 10000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((6409500448793931 : Rat) / 2500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((1785591140066964293 : Rat) / 10000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((1591690274762969 : Rat) / 500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((1756666925223214293 : Rat) / 10000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((1969847755821569 : Rat) / 500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((1727742710379464293 : Rat) / 10000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((9678597442108583 : Rat) / 2000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1698818495535714293 : Rat) / 10000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((5031409913851259 : Rat) / 5000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((1640970065848214293 : Rat) / 10000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((4532139504868811 : Rat) / 1250000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((1583121636160714293 : Rat) / 10000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((34784433629723027 : Rat) / 5000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((1525273206473214293 : Rat) / 10000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((2774555480606837 : Rat) / 250000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1467424776785714293 : Rat) / 10000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((3364641203258467 : Rat) / 500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1351727917410714293 : Rat) / 10000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((2577322926169523 : Rat) / 125000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1236031058035714293 : Rat) / 10000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((2940313158309029 : Rat) / 125000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((103322037339285714293 : Rat) / 40000000000000000000), D0 := ((103322037339285714293 : Rat) / 40000000000000000000), D1 := ((30623033339285714293 : Rat) / 40000000000000000000), D2 := ((1004637339285714293 : Rat) / 40000000000000000000), D3 := ((1004637339285714293 : Rat) / 10000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((1362696320657629 : Rat) / 50000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((103322037339285714293 : Rat) / 40000000000000000000), R := ((52163337339285714293 : Rat) / 20000000000000000000), D0 := ((52163337339285714293 : Rat) / 20000000000000000000), D1 := ((15813835339285714293 : Rat) / 20000000000000000000), D2 := ((1004637339285714293 : Rat) / 20000000000000000000), D3 := ((3013912017857142879 : Rat) / 40000000000000000000), D4 := ((37863839017857122927 : Rat) / 200000000000000000000), LB := ((18725759892149973 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((52163337339285714293 : Rat) / 20000000000000000000), R := ((105331312017857142879 : Rat) / 40000000000000000000), D0 := ((105331312017857142879 : Rat) / 40000000000000000000), D1 := ((32632308017857142879 : Rat) / 40000000000000000000), D2 := ((3013912017857142879 : Rat) / 40000000000000000000), D3 := ((1004637339285714293 : Rat) / 20000000000000000000), D4 := ((16420326160714275731 : Rat) / 100000000000000000000), LB := ((2271253230988271 : Rat) / 50000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((105331312017857142879 : Rat) / 40000000000000000000), R := ((26583987339285714293 : Rat) / 10000000000000000000), D0 := ((26583987339285714293 : Rat) / 10000000000000000000), D1 := ((8409236339285714293 : Rat) / 10000000000000000000), D2 := ((1004637339285714293 : Rat) / 10000000000000000000), D3 := ((1004637339285714293 : Rat) / 40000000000000000000), D4 := ((27817465624999979997 : Rat) / 200000000000000000000), LB := ((12639219570231697 : Rat) / 100000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((26583987339285714293 : Rat) / 10000000000000000000), R := ((33501671863839285731 : Rat) / 12500000000000000000), D0 := ((33501671863839285731 : Rat) / 12500000000000000000), D1 := ((10783233113839285731 : Rat) / 12500000000000000000), D2 := ((1527484363839285731 : Rat) / 12500000000000000000), D3 := ((1086750758928571459 : Rat) / 50000000000000000000), D4 := ((5698569732142852133 : Rat) / 50000000000000000000), LB := ((1712420802885739 : Rat) / 12500000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((33501671863839285731 : Rat) / 12500000000000000000), R := ((135093438214285714383 : Rat) / 50000000000000000000), D0 := ((135093438214285714383 : Rat) / 50000000000000000000), D1 := ((44219683214285714383 : Rat) / 50000000000000000000), D2 := ((7196688214285714383 : Rat) / 50000000000000000000), D3 := ((1086750758928571459 : Rat) / 25000000000000000000), D4 := ((2305909486607140337 : Rat) / 25000000000000000000), LB := ((4378582839633649 : Rat) / 200000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((135093438214285714383 : Rat) / 50000000000000000000), R := ((10850945087500000009 : Rat) / 4000000000000000000), D0 := ((10850945087500000009 : Rat) / 4000000000000000000), D1 := ((3581044687500000009 : Rat) / 4000000000000000000), D2 := ((619205087500000009 : Rat) / 4000000000000000000), D3 := ((1086750758928571459 : Rat) / 20000000000000000000), D4 := ((705013642857141843 : Rat) / 10000000000000000000), LB := ((6824393395238049 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((10850945087500000009 : Rat) / 4000000000000000000), R := ((543634005133928571909 : Rat) / 200000000000000000000), D0 := ((543634005133928571909 : Rat) / 200000000000000000000), D1 := ((180138985133928571909 : Rat) / 200000000000000000000), D2 := ((32047005133928571909 : Rat) / 200000000000000000000), D3 := ((11954258348214286049 : Rat) / 200000000000000000000), D4 := ((5963385669642846971 : Rat) / 100000000000000000000), LB := ((1312311071448069 : Rat) / 200000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((543634005133928571909 : Rat) / 200000000000000000000), R := ((1088354761026785715277 : Rat) / 400000000000000000000), D0 := ((1088354761026785715277 : Rat) / 400000000000000000000), D1 := ((361364721026785715277 : Rat) / 400000000000000000000), D2 := ((65180761026785715277 : Rat) / 400000000000000000000), D3 := ((24995267455357143557 : Rat) / 400000000000000000000), D4 := ((10840020580357122483 : Rat) / 200000000000000000000), LB := ((8611637898975233 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1088354761026785715277 : Rat) / 400000000000000000000), R := ((68090094486607142921 : Rat) / 25000000000000000000), D0 := ((68090094486607142921 : Rat) / 25000000000000000000), D1 := ((22653216986607142921 : Rat) / 25000000000000000000), D2 := ((4141719486607142921 : Rat) / 25000000000000000000), D3 := ((3260252276785714377 : Rat) / 50000000000000000000), D4 := ((20593290401785673507 : Rat) / 400000000000000000000), LB := ((4819061142550873 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((68090094486607142921 : Rat) / 25000000000000000000), R := ((218105652508928571639 : Rat) / 80000000000000000000), D0 := ((218105652508928571639 : Rat) / 80000000000000000000), D1 := ((72707644508928571639 : Rat) / 80000000000000000000), D2 := ((13470852508928571639 : Rat) / 80000000000000000000), D3 := ((1086750758928571459 : Rat) / 16000000000000000000), D4 := ((609579363839284439 : Rat) / 12500000000000000000), LB := ((17059819013272581 : Rat) / 10000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((218105652508928571639 : Rat) / 80000000000000000000), R := ((2182143275848214287849 : Rat) / 800000000000000000000), D0 := ((2182143275848214287849 : Rat) / 800000000000000000000), D1 := ((728163195848214287849 : Rat) / 800000000000000000000), D2 := ((135795275848214287849 : Rat) / 800000000000000000000), D3 := ((55424288705357144409 : Rat) / 800000000000000000000), D4 := ((18419788883928530589 : Rat) / 400000000000000000000), LB := ((2234486328855173 : Rat) / 500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2182143275848214287849 : Rat) / 800000000000000000000), R := ((545807506651785714827 : Rat) / 200000000000000000000), D0 := ((545807506651785714827 : Rat) / 200000000000000000000), D1 := ((182312486651785714827 : Rat) / 200000000000000000000), D2 := ((34220506651785714827 : Rat) / 200000000000000000000), D3 := ((14127759866071428967 : Rat) / 200000000000000000000), D4 := ((35752827008928489719 : Rat) / 800000000000000000000), LB := ((34749162388045263 : Rat) / 10000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545807506651785714827 : Rat) / 200000000000000000000), R := ((2184316777366071430767 : Rat) / 800000000000000000000), D0 := ((2184316777366071430767 : Rat) / 800000000000000000000), D1 := ((730336697366071430767 : Rat) / 800000000000000000000), D2 := ((137968777366071430767 : Rat) / 800000000000000000000), D3 := ((57597790223214287327 : Rat) / 800000000000000000000), D4 := ((1733303812499995913 : Rat) / 40000000000000000000), LB := ((26722397900731387 : Rat) / 10000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2184316777366071430767 : Rat) / 800000000000000000000), R := ((1092701764062500001113 : Rat) / 400000000000000000000), D0 := ((1092701764062500001113 : Rat) / 400000000000000000000), D1 := ((365711724062500001113 : Rat) / 400000000000000000000), D2 := ((69527764062500001113 : Rat) / 400000000000000000000), D3 := ((29342270491071429393 : Rat) / 400000000000000000000), D4 := ((33579325491071346801 : Rat) / 800000000000000000000), LB := ((20669718606554643 : Rat) / 10000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1092701764062500001113 : Rat) / 400000000000000000000), R := ((437298055776785714737 : Rat) / 160000000000000000000), D0 := ((437298055776785714737 : Rat) / 160000000000000000000), D1 := ((146502039776785714737 : Rat) / 160000000000000000000), D2 := ((28028455776785714737 : Rat) / 160000000000000000000), D3 := ((11954258348214286049 : Rat) / 160000000000000000000), D4 := ((16246287366071387671 : Rat) / 400000000000000000000), LB := ((16660713716380449 : Rat) / 10000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((437298055776785714737 : Rat) / 160000000000000000000), R := ((273447128705357143143 : Rat) / 100000000000000000000), D0 := ((273447128705357143143 : Rat) / 100000000000000000000), D1 := ((91699618705357143143 : Rat) / 100000000000000000000), D2 := ((17653628705357143143 : Rat) / 100000000000000000000), D3 := ((7607255312500000213 : Rat) / 100000000000000000000), D4 := ((31405823973214203883 : Rat) / 800000000000000000000), LB := ((5910118229701 : Rat) / 4000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((273447128705357143143 : Rat) / 100000000000000000000), R := ((2188663780401785716603 : Rat) / 800000000000000000000), D0 := ((2188663780401785716603 : Rat) / 800000000000000000000), D1 := ((734683700401785716603 : Rat) / 800000000000000000000), D2 := ((142315780401785716603 : Rat) / 800000000000000000000), D3 := ((61944793258928573163 : Rat) / 800000000000000000000), D4 := ((3789884151785704053 : Rat) / 100000000000000000000), LB := ((604196847710603 : Rat) / 400000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2188663780401785716603 : Rat) / 800000000000000000000), R := ((1094875265580357144031 : Rat) / 400000000000000000000), D0 := ((1094875265580357144031 : Rat) / 400000000000000000000), D1 := ((367885225580357144031 : Rat) / 400000000000000000000), D2 := ((71701265580357144031 : Rat) / 400000000000000000000), D3 := ((31515772008928572311 : Rat) / 400000000000000000000), D4 := ((5846464491071412193 : Rat) / 160000000000000000000), LB := ((443851444233867 : Rat) / 250000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094875265580357144031 : Rat) / 400000000000000000000), R := ((2190837281919642859521 : Rat) / 800000000000000000000), D0 := ((2190837281919642859521 : Rat) / 800000000000000000000), D1 := ((736857201919642859521 : Rat) / 800000000000000000000), D2 := ((144489281919642859521 : Rat) / 800000000000000000000), D3 := ((64118294776785716081 : Rat) / 800000000000000000000), D4 := ((14072785848214244753 : Rat) / 400000000000000000000), LB := ((1142097272656739 : Rat) / 500000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190837281919642859521 : Rat) / 800000000000000000000), R := ((109596201633928571549 : Rat) / 40000000000000000000), D0 := ((109596201633928571549 : Rat) / 40000000000000000000), D1 := ((36897197633928571549 : Rat) / 40000000000000000000), D2 := ((7278801633928571549 : Rat) / 40000000000000000000), D3 := ((3260252276785714377 : Rat) / 40000000000000000000), D4 := ((27058820937499918047 : Rat) / 800000000000000000000), LB := ((3050472559773143 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((109596201633928571549 : Rat) / 40000000000000000000), R := ((2193010783437500002439 : Rat) / 800000000000000000000), D0 := ((2193010783437500002439 : Rat) / 800000000000000000000), D1 := ((739030703437500002439 : Rat) / 800000000000000000000), D2 := ((146662783437500002439 : Rat) / 800000000000000000000), D3 := ((66291796294642858999 : Rat) / 800000000000000000000), D4 := ((6493017544642836647 : Rat) / 200000000000000000000), LB := ((1635920902985899 : Rat) / 400000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2193010783437500002439 : Rat) / 800000000000000000000), R := ((1097048767098214286949 : Rat) / 400000000000000000000), D0 := ((1097048767098214286949 : Rat) / 400000000000000000000), D1 := ((370058727098214286949 : Rat) / 400000000000000000000), D2 := ((73874767098214286949 : Rat) / 400000000000000000000), D3 := ((33689273526785715229 : Rat) / 400000000000000000000), D4 := ((24885319419642775129 : Rat) / 800000000000000000000), LB := ((5420009381570001 : Rat) / 1000000000000000000) },
  { w1 := ((4346453091963343 : Rat) / 5000000000000000), w2 := ((4713951059812557 : Rat) / 100000000000000000), w3 := ((3866768956438603 : Rat) / 25000000000000000), w4 := ((3489423322919047 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26583987339285714293 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1097048767098214286949 : Rat) / 400000000000000000000), R := ((137266939732142857301 : Rat) / 50000000000000000000), D0 := ((137266939732142857301 : Rat) / 50000000000000000000), D1 := ((46393184732142857301 : Rat) / 50000000000000000000), D2 := ((9370189732142857301 : Rat) / 50000000000000000000), D3 := ((1086750758928571459 : Rat) / 12500000000000000000), D4 := ((2379856866071420367 : Rat) / 80000000000000000000), LB := ((2514257890051441 : Rat) / 1000000000000000000) }
]

def block369RightChunk000L : Rat := ((8725716517857142873 : Rat) / 5000000000000000000)
def block369RightChunk000R : Rat := ((137266939732142857301 : Rat) / 50000000000000000000)

def block369RightChunk000Certificate : Bool :=
  allBoxesValid block369RightChunk000 &&
  coversFromBool block369RightChunk000 block369RightChunk000L block369RightChunk000R

theorem block369RightChunk000Certificate_eq_true :
    block369RightChunk000Certificate = true := by
  native_decide

def block369RightChainCertificate : Bool :=
  decide (
    block369RightL = ((8725716517857142873 : Rat) / 5000000000000000000) /\
    ((137266939732142857301 : Rat) / 50000000000000000000) = block369RightR)

theorem block369RightChainCertificate_eq_true :
    block369RightChainCertificate = true := by
  native_decide

def block369LeftBoxCount : Nat := boxCount block369LeftBoxes
def block369RightBoxCount : Nat := 60

def block369_rational_certificate : Prop :=
    block369LeftCertificate = true /\
    block369RightChainCertificate = true /\
    block369RightChunk000Certificate = true

theorem block369_rational_certificate_proof :
    block369_rational_certificate := by
  exact ⟨block369LeftCertificate_eq_true, block369RightChainCertificate_eq_true, block369RightChunk000Certificate_eq_true⟩

end Block369
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block369

open Set

def block369W1 : Rat := ((4346453091963343 : Rat) / 5000000000000000)
def block369W2 : Rat := ((4713951059812557 : Rat) / 100000000000000000)
def block369W3 : Rat := ((3866768956438603 : Rat) / 25000000000000000)
def block369W4 : Rat := ((3489423322919047 : Rat) / 25000000000000000)
def block369S1 : Rat := ((18174751 : Rat) / 10000000)
def block369S2 : Rat := ((511587 : Rat) / 200000)
def block369S3 : Rat := ((26583987339285714293 : Rat) / 10000000000000000000)
def block369S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block369V (y : ℝ) : ℝ :=
  ratPotential block369W1 block369W2 block369W3 block369W4 block369S1 block369S2 block369S3 block369S4 y

def block369LeftParamsCertificate : Bool :=
  allBoxesSameParams block369LeftBoxes block369W1 block369W2 block369W3 block369W4 block369S1 block369S2 block369S3 block369S4

theorem block369LeftParamsCertificate_eq_true :
    block369LeftParamsCertificate = true := by
  native_decide

theorem block369_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block369LeftL : ℝ) (block369LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block369S1 : ℝ))
    (hy2ne : y ≠ (block369S2 : ℝ))
    (hy3ne : y ≠ (block369S3 : ℝ))
    (hy4ne : y ≠ (block369S4 : ℝ)) :
    0 < block369V y := by
  have hcert := block369LeftCertificate_eq_true
  unfold block369LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block369LeftBoxes) (lo := block369LeftL) (hi := block369LeftR)
    (w1 := block369W1) (w2 := block369W2) (w3 := block369W3) (w4 := block369W4)
    (s1 := block369S1) (s2 := block369S2) (s3 := block369S3) (s4 := block369S4)
    hboxes hcover block369LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block369RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block369RightChunk000 block369W1 block369W2 block369W3 block369W4 block369S1 block369S2 block369S3 block369S4

theorem block369RightChunk000ParamsCertificate_eq_true :
    block369RightChunk000ParamsCertificate = true := by
  native_decide

theorem block369_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block369RightChunk000L : ℝ) (block369RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block369S1 : ℝ))
    (hy2ne : y ≠ (block369S2 : ℝ))
    (hy3ne : y ≠ (block369S3 : ℝ))
    (hy4ne : y ≠ (block369S4 : ℝ)) :
    0 < block369V y := by
  have hcert := block369RightChunk000Certificate_eq_true
  unfold block369RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block369RightChunk000) (lo := block369RightChunk000L) (hi := block369RightChunk000R)
    (w1 := block369W1) (w2 := block369W2) (w3 := block369W3) (w4 := block369W4)
    (s1 := block369S1) (s2 := block369S2) (s3 := block369S3) (s4 := block369S4)
    hboxes hcover block369RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block369_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block369RightL : ℝ) (block369RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block369S1 : ℝ))
    (hy2ne : y ≠ (block369S2 : ℝ))
    (hy3ne : y ≠ (block369S3 : ℝ))
    (hy4ne : y ≠ (block369S4 : ℝ)) :
    0 < block369V y := by
  have hL : (block369RightChunk000L : ℝ) = (block369RightL : ℝ) := by
    norm_num [block369RightChunk000L, block369RightL]
  have hR : (block369RightChunk000R : ℝ) = (block369RightR : ℝ) := by
    norm_num [block369RightChunk000R, block369RightR]
  have hyc : y ∈ Icc (block369RightChunk000L : ℝ) (block369RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block369_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block369_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block369LeftL : ℝ) (block369LeftR : ℝ) →
    y ≠ 0 → y ≠ (block369S1 : ℝ) → y ≠ (block369S2 : ℝ) →
    y ≠ (block369S3 : ℝ) → y ≠ (block369S4 : ℝ) → 0 < block369V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block369RightL : ℝ) (block369RightR : ℝ) →
    y ≠ 0 → y ≠ (block369S1 : ℝ) → y ≠ (block369S2 : ℝ) →
    y ≠ (block369S3 : ℝ) → y ≠ (block369S4 : ℝ) → 0 < block369V y)

theorem block369_reallog_certificate_proof :
    block369_reallog_certificate := by
  exact ⟨block369_left_V_pos, block369_right_V_pos⟩

end Block369
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block369.block369V
#check Erdos1038Lean.M1817475.Block369.block369_left_V_pos
#check Erdos1038Lean.M1817475.Block369.block369_right_V_pos
#check Erdos1038Lean.M1817475.Block369.block369_reallog_certificate_proof
