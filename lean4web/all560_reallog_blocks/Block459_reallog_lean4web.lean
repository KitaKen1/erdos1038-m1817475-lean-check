/-
Self-contained Lean4Web paste file.
Block 459 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block459

def block459LeftL : Rat := ((1818872767857142867 : Rat) / 2500000000000000000)
def block459LeftR : Rat := ((36387229910714285911 : Rat) / 50000000000000000000)
def block459RightL : Rat := ((4318872767857142867 : Rat) / 2500000000000000000)
def block459RightR : Rat := ((136387229910714285911 : Rat) / 50000000000000000000)

def block459LeftBoxes : List RatBox := [
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1818872767857142867 : Rat) / 2500000000000000000), R := ((36387229910714285911 : Rat) / 50000000000000000000), D0 := ((36387229910714285911 : Rat) / 50000000000000000000), D1 := ((2724814982142857133 : Rat) / 2500000000000000000), D2 := ((4575964732142857133 : Rat) / 2500000000000000000), D3 := ((18956612339285714269 : Rat) / 10000000000000000000), D4 := ((5142353669642856883 : Rat) / 2500000000000000000), LB := ((24689589064963 : Rat) / 6250000000000000) }
]

def block459LeftCertificate : Bool :=
  allBoxesValid block459LeftBoxes &&
  coversFromBool block459LeftBoxes block459LeftL block459LeftR

theorem block459LeftCertificate_eq_true :
    block459LeftCertificate = true := by
  native_decide

def block459RightChunk000 : List RatBox := [
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4318872767857142867 : Rat) / 2500000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((224814982142857133 : Rat) / 2500000000000000000), D2 := ((2075964732142857133 : Rat) / 2500000000000000000), D3 := ((8956612339285714269 : Rat) / 10000000000000000000), D4 := ((2642353669642856883 : Rat) / 2500000000000000000), LB := ((4075572081836059 : Rat) / 5000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8057352410714285737 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((17353437409288913 : Rat) / 50000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((33522361 : Rat) / 16000000), D0 := ((33522361 : Rat) / 16000000), D1 := ((22213797 : Rat) / 80000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((6206202660714285737 : Rat) / 10000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((17299503585782197 : Rat) / 100000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33522361 : Rat) / 16000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 16000000), D3 := ((5280627785714285737 : Rat) / 10000000000000000000), D4 := ((6893430124999999 : Rat) / 10000000000000000), LB := ((894628061415967 : Rat) / 31250000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4355052910714285737 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((15622326226133739 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((722279413 : Rat) / 320000000), D0 := ((722279413 : Rat) / 320000000), D1 := ((140687381 : Rat) / 320000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((3892265473214285737 : Rat) / 10000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((113048529212061 : Rat) / 6250000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((722279413 : Rat) / 320000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((96259787 : Rat) / 320000000), D3 := ((3660871754464285737 : Rat) / 10000000000000000000), D4 := ((5273674093749999 : Rat) / 10000000000000000), LB := ((5801617872298031 : Rat) / 2500000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((1466772623 : Rat) / 640000000), D0 := ((1466772623 : Rat) / 640000000), D1 := ((303588559 : Rat) / 640000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3429478035714285737 : Rat) / 10000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((84075595443409 : Rat) / 10000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1466772623 : Rat) / 640000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((170305777 : Rat) / 640000000), D3 := ((3313781176339285737 : Rat) / 10000000000000000000), D4 := ((4926583515624999 : Rat) / 10000000000000000), LB := ((14243606896417807 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((2955759043 : Rat) / 1280000000), D0 := ((2955759043 : Rat) / 1280000000), D1 := ((125878183 : Rat) / 256000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((3198084316964285737 : Rat) / 10000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((72865294435107 : Rat) / 10000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2955759043 : Rat) / 1280000000), R := ((1481581821 : Rat) / 640000000), D0 := ((1481581821 : Rat) / 640000000), D1 := ((318397757 : Rat) / 640000000), D2 := ((318397757 : Rat) / 1280000000), D3 := ((3140235887276785737 : Rat) / 10000000000000000000), D4 := ((4753038226562499 : Rat) / 10000000000000000), LB := ((5132629607025471 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1481581821 : Rat) / 640000000), R := ((2970568241 : Rat) / 1280000000), D0 := ((2970568241 : Rat) / 1280000000), D1 := ((644200113 : Rat) / 1280000000), D2 := ((155496579 : Rat) / 640000000), D3 := ((3082387457589285737 : Rat) / 10000000000000000000), D4 := ((4695189796874999 : Rat) / 10000000000000000), LB := ((15942723008602541 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2970568241 : Rat) / 1280000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((303588559 : Rat) / 1280000000), D3 := ((3024539027901785737 : Rat) / 10000000000000000000), D4 := ((4637341367187499 : Rat) / 10000000000000000), LB := ((7285705290106803 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((5963350279 : Rat) / 2560000000), D0 := ((5963350279 : Rat) / 2560000000), D1 := ((1310614023 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((2966690598214285737 : Rat) / 10000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((110128461281323 : Rat) / 25000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5963350279 : Rat) / 2560000000), R := ((2985377439 : Rat) / 1280000000), D0 := ((2985377439 : Rat) / 1280000000), D1 := ((659009311 : Rat) / 1280000000), D2 := ((584963321 : Rat) / 2560000000), D3 := ((2937766383370535737 : Rat) / 10000000000000000000), D4 := ((4550568722656249 : Rat) / 10000000000000000), LB := ((3709825814787057 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2985377439 : Rat) / 1280000000), R := ((5978159477 : Rat) / 2560000000), D0 := ((5978159477 : Rat) / 2560000000), D1 := ((1325423221 : Rat) / 2560000000), D2 := ((288779361 : Rat) / 1280000000), D3 := ((2908842168526785737 : Rat) / 10000000000000000000), D4 := ((4521644507812499 : Rat) / 10000000000000000), LB := ((3070040853443007 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5978159477 : Rat) / 2560000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((570154123 : Rat) / 2560000000), D3 := ((2879917953683035737 : Rat) / 10000000000000000000), D4 := ((4492720292968749 : Rat) / 10000000000000000), LB := ((24862793606445707 : Rat) / 10000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((239718747 : Rat) / 102400000), D0 := ((239718747 : Rat) / 102400000), D1 := ((1340232419 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((2850993738839285737 : Rat) / 10000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((1959061366470033 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((239718747 : Rat) / 102400000), R := ((3000186637 : Rat) / 1280000000), D0 := ((3000186637 : Rat) / 1280000000), D1 := ((673818509 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 102400000), D3 := ((2822069523995535737 : Rat) / 10000000000000000000), D4 := ((4434871863281249 : Rat) / 10000000000000000), LB := ((7444659532791359 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3000186637 : Rat) / 1280000000), R := ((6007777873 : Rat) / 2560000000), D0 := ((6007777873 : Rat) / 2560000000), D1 := ((1355041617 : Rat) / 2560000000), D2 := ((273970163 : Rat) / 1280000000), D3 := ((2793145309151785737 : Rat) / 10000000000000000000), D4 := ((4405947648437499 : Rat) / 10000000000000000), LB := ((2691154590390519 : Rat) / 2500000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6007777873 : Rat) / 2560000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((540535727 : Rat) / 2560000000), D3 := ((2764221094308035737 : Rat) / 10000000000000000000), D4 := ((4377023433593749 : Rat) / 10000000000000000), LB := ((902810864879481 : Rat) / 1250000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((6022587071 : Rat) / 2560000000), D0 := ((6022587071 : Rat) / 2560000000), D1 := ((273970163 : Rat) / 512000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((2735296879464285737 : Rat) / 10000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((1067294010440277 : Rat) / 2500000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6022587071 : Rat) / 2560000000), R := ((602999167 : Rat) / 256000000), D0 := ((602999167 : Rat) / 256000000), D1 := ((688627707 : Rat) / 1280000000), D2 := ((525726529 : Rat) / 2560000000), D3 := ((2706372664620535737 : Rat) / 10000000000000000000), D4 := ((4319175003906249 : Rat) / 10000000000000000), LB := ((19112226302830243 : Rat) / 100000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((602999167 : Rat) / 256000000), R := ((6037396269 : Rat) / 2560000000), D0 := ((6037396269 : Rat) / 2560000000), D1 := ((1384660013 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 256000000), D3 := ((2677448449776785737 : Rat) / 10000000000000000000), D4 := ((4290250789062499 : Rat) / 10000000000000000), LB := ((1554594097832873 : Rat) / 100000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6037396269 : Rat) / 2560000000), R := ((12082197137 : Rat) / 5120000000), D0 := ((12082197137 : Rat) / 5120000000), D1 := ((22213797 : Rat) / 40960000), D2 := ((510917331 : Rat) / 2560000000), D3 := ((2648524234933035737 : Rat) / 10000000000000000000), D4 := ((4261326574218749 : Rat) / 10000000000000000), LB := ((2036902654952731 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12082197137 : Rat) / 5120000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((1014430063 : Rat) / 5120000000), D3 := ((2634062127511160737 : Rat) / 10000000000000000000), D4 := ((2123432233398437 : Rat) / 5000000000000000), LB := ((1998241426244267 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((2419401267 : Rat) / 1024000000), D0 := ((2419401267 : Rat) / 1024000000), D1 := ((2791533823 : Rat) / 5120000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((2619600020089285737 : Rat) / 10000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((19751175395566617 : Rat) / 10000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2419401267 : Rat) / 1024000000), R := ((6052205467 : Rat) / 2560000000), D0 := ((6052205467 : Rat) / 2560000000), D1 := ((1399469211 : Rat) / 2560000000), D2 := ((199924173 : Rat) / 1024000000), D3 := ((2605137912667410737 : Rat) / 10000000000000000000), D4 := ((1054485062988281 : Rat) / 2500000000000000), LB := ((245953651653431 : Rat) / 125000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6052205467 : Rat) / 2560000000), R := ((12111815533 : Rat) / 5120000000), D0 := ((12111815533 : Rat) / 5120000000), D1 := ((2806343021 : Rat) / 5120000000), D2 := ((496108133 : Rat) / 2560000000), D3 := ((2590675805245535737 : Rat) / 10000000000000000000), D4 := ((4203478144531249 : Rat) / 10000000000000000), LB := ((617461503619333 : Rat) / 312500000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12111815533 : Rat) / 5120000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((984811667 : Rat) / 5120000000), D3 := ((2576213697823660737 : Rat) / 10000000000000000000), D4 := ((2094508018554687 : Rat) / 5000000000000000), LB := ((999981443474643 : Rat) / 500000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((12126624731 : Rat) / 5120000000), D0 := ((12126624731 : Rat) / 5120000000), D1 := ((2821152219 : Rat) / 5120000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((2561751590401785737 : Rat) / 10000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((10199961114588131 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12126624731 : Rat) / 5120000000), R := ((1213402933 : Rat) / 512000000), D0 := ((1213402933 : Rat) / 512000000), D1 := ((1414278409 : Rat) / 2560000000), D2 := ((970002469 : Rat) / 5120000000), D3 := ((2547289482979910737 : Rat) / 10000000000000000000), D4 := ((520011477783203 : Rat) / 1250000000000000), LB := ((20960718788890983 : Rat) / 10000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1213402933 : Rat) / 512000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((96259787 : Rat) / 512000000), D3 := ((2532827375558035737 : Rat) / 10000000000000000000), D4 := ((4145629714843749 : Rat) / 10000000000000000), LB := ((67076946802129 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((6081823863 : Rat) / 2560000000), D0 := ((6081823863 : Rat) / 2560000000), D1 := ((1429087607 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2503903160714285737 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((26896499984632033 : Rat) / 100000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6081823863 : Rat) / 2560000000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((466489737 : Rat) / 2560000000), D3 := ((2474978945870535737 : Rat) / 10000000000000000000), D4 := ((4087781285156249 : Rat) / 10000000000000000), LB := ((2683914519562361 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((6096633061 : Rat) / 2560000000), D0 := ((6096633061 : Rat) / 2560000000), D1 := ((288779361 : Rat) / 512000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((2446054731026785737 : Rat) / 10000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((4357477674648419 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6096633061 : Rat) / 2560000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((451680539 : Rat) / 2560000000), D3 := ((2417130516183035737 : Rat) / 10000000000000000000), D4 := ((4029932855468749 : Rat) / 10000000000000000), LB := ((79631862434999 : Rat) / 62500000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((2388206301339285737 : Rat) / 10000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((2182095589871513 : Rat) / 1250000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((2359282086495535737 : Rat) / 10000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((11436460774313477 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((2330357871651785737 : Rat) / 10000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((14500506768555903 : Rat) / 5000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((2301433656808035737 : Rat) / 10000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((3585298691794407 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2272509441964285737 : Rat) / 10000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((750822188715361 : Rat) / 2500000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((2214661012276785737 : Rat) / 10000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((5187406350803201 : Rat) / 2500000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2156812582589285737 : Rat) / 10000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((831994409488887 : Rat) / 200000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((2098964152901785737 : Rat) / 10000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((6567517736323983 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2041115723214285737 : Rat) / 10000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((15061528137649827 : Rat) / 10000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((1925418863839285737 : Rat) / 10000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((1634414424579883 : Rat) / 200000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((1809722004464285737 : Rat) / 10000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((13603203999962427 : Rat) / 10000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((1578328285714285737 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((93781259181561 : Rat) / 4000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1346934566964285737 : Rat) / 10000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((2706140562262871 : Rat) / 50000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1115540848214285737 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((1379872267421203 : Rat) / 20000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((26232103410714285737 : Rat) / 10000000000000000000), D0 := ((26232103410714285737 : Rat) / 10000000000000000000), D1 := ((8057352410714285737 : Rat) / 10000000000000000000), D2 := ((652753410714285737 : Rat) / 10000000000000000000), D3 := ((652753410714285737 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((767423449567717 : Rat) / 4000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26232103410714285737 : Rat) / 10000000000000000000), R := ((66886936741071428649 : Rat) / 25000000000000000000), D0 := ((66886936741071428649 : Rat) / 25000000000000000000), D1 := ((21450059241071428649 : Rat) / 25000000000000000000), D2 := ((2938561741071428649 : Rat) / 25000000000000000000), D3 := ((2613356428571428613 : Rat) / 50000000000000000000), D4 := ((1612802339285713263 : Rat) / 10000000000000000000), LB := ((23352129028677787 : Rat) / 100000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((66886936741071428649 : Rat) / 25000000000000000000), R := ((270161103392857143209 : Rat) / 100000000000000000000), D0 := ((270161103392857143209 : Rat) / 100000000000000000000), D1 := ((88413593392857143209 : Rat) / 100000000000000000000), D2 := ((14367603392857143209 : Rat) / 100000000000000000000), D3 := ((7840069285714285839 : Rat) / 100000000000000000000), D4 := ((2725327633928568851 : Rat) / 25000000000000000000), LB := ((9026205581313987 : Rat) / 100000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((270161103392857143209 : Rat) / 100000000000000000000), R := ((542935563214285715031 : Rat) / 200000000000000000000), D0 := ((542935563214285715031 : Rat) / 200000000000000000000), D1 := ((179440543214285715031 : Rat) / 200000000000000000000), D2 := ((31348563214285715031 : Rat) / 200000000000000000000), D3 := ((18293495000000000291 : Rat) / 200000000000000000000), D4 := ((8287954107142846791 : Rat) / 100000000000000000000), LB := ((2018778451422111 : Rat) / 50000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((542935563214285715031 : Rat) / 200000000000000000000), R := ((43539379314285714347 : Rat) / 16000000000000000000), D0 := ((43539379314285714347 : Rat) / 16000000000000000000), D1 := ((14459777714285714347 : Rat) / 16000000000000000000), D2 := ((2612419314285714347 : Rat) / 16000000000000000000), D3 := ((7840069285714285839 : Rat) / 80000000000000000000), D4 := ((13962551785714264969 : Rat) / 200000000000000000000), LB := ((10184346977240133 : Rat) / 500000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43539379314285714347 : Rat) / 16000000000000000000), R := ((2179582322142857145963 : Rat) / 800000000000000000000), D0 := ((2179582322142857145963 : Rat) / 800000000000000000000), D1 := ((725602242142857145963 : Rat) / 800000000000000000000), D2 := ((133234322142857145963 : Rat) / 800000000000000000000), D3 := ((81014049285714287003 : Rat) / 800000000000000000000), D4 := ((1012469885714284053 : Rat) / 16000000000000000000), LB := ((11722967830111897 : Rat) / 1000000000000000000) },
  { w1 := ((2860061216691561 : Rat) / 5000000000000000), w2 := (0 : Rat), w3 := ((3454752121055683 : Rat) / 10000000000000000), w4 := ((6051430260822989 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26232103410714285737 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2179582322142857145963 : Rat) / 800000000000000000000), R := ((136387229910714285911 : Rat) / 50000000000000000000), D0 := ((136387229910714285911 : Rat) / 50000000000000000000), D1 := ((45513474910714285911 : Rat) / 50000000000000000000), D2 := ((8490479910714285911 : Rat) / 50000000000000000000), D3 := ((2613356428571428613 : Rat) / 25000000000000000000), D4 := ((48010137857142774037 : Rat) / 800000000000000000000), LB := ((3536380734481259 : Rat) / 5000000000000000000) }
]

def block459RightChunk000L : Rat := ((4318872767857142867 : Rat) / 2500000000000000000)
def block459RightChunk000R : Rat := ((136387229910714285911 : Rat) / 50000000000000000000)

def block459RightChunk000Certificate : Bool :=
  allBoxesValid block459RightChunk000 &&
  coversFromBool block459RightChunk000 block459RightChunk000L block459RightChunk000R

theorem block459RightChunk000Certificate_eq_true :
    block459RightChunk000Certificate = true := by
  native_decide

def block459RightChainCertificate : Bool :=
  decide (
    block459RightL = ((4318872767857142867 : Rat) / 2500000000000000000) /\
    ((136387229910714285911 : Rat) / 50000000000000000000) = block459RightR)

theorem block459RightChainCertificate_eq_true :
    block459RightChainCertificate = true := by
  native_decide

def block459LeftBoxCount : Nat := boxCount block459LeftBoxes
def block459RightBoxCount : Nat := 58

def block459_rational_certificate : Prop :=
    block459LeftCertificate = true /\
    block459RightChainCertificate = true /\
    block459RightChunk000Certificate = true

theorem block459_rational_certificate_proof :
    block459_rational_certificate := by
  exact ⟨block459LeftCertificate_eq_true, block459RightChainCertificate_eq_true, block459RightChunk000Certificate_eq_true⟩

end Block459
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block459

open Set

def block459W1 : Rat := ((2860061216691561 : Rat) / 5000000000000000)
def block459W2 : Rat := (0 : Rat)
def block459W3 : Rat := ((3454752121055683 : Rat) / 10000000000000000)
def block459W4 : Rat := ((6051430260822989 : Rat) / 100000000000000000)
def block459S1 : Rat := ((18174751 : Rat) / 10000000)
def block459S2 : Rat := ((511587 : Rat) / 200000)
def block459S3 : Rat := ((26232103410714285737 : Rat) / 10000000000000000000)
def block459S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block459V (y : ℝ) : ℝ :=
  ratPotential block459W1 block459W2 block459W3 block459W4 block459S1 block459S2 block459S3 block459S4 y

def block459LeftParamsCertificate : Bool :=
  allBoxesSameParams block459LeftBoxes block459W1 block459W2 block459W3 block459W4 block459S1 block459S2 block459S3 block459S4

theorem block459LeftParamsCertificate_eq_true :
    block459LeftParamsCertificate = true := by
  native_decide

theorem block459_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block459LeftL : ℝ) (block459LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block459S1 : ℝ))
    (hy2ne : y ≠ (block459S2 : ℝ))
    (hy3ne : y ≠ (block459S3 : ℝ))
    (hy4ne : y ≠ (block459S4 : ℝ)) :
    0 < block459V y := by
  have hcert := block459LeftCertificate_eq_true
  unfold block459LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block459LeftBoxes) (lo := block459LeftL) (hi := block459LeftR)
    (w1 := block459W1) (w2 := block459W2) (w3 := block459W3) (w4 := block459W4)
    (s1 := block459S1) (s2 := block459S2) (s3 := block459S3) (s4 := block459S4)
    hboxes hcover block459LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block459RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block459RightChunk000 block459W1 block459W2 block459W3 block459W4 block459S1 block459S2 block459S3 block459S4

theorem block459RightChunk000ParamsCertificate_eq_true :
    block459RightChunk000ParamsCertificate = true := by
  native_decide

theorem block459_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block459RightChunk000L : ℝ) (block459RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block459S1 : ℝ))
    (hy2ne : y ≠ (block459S2 : ℝ))
    (hy3ne : y ≠ (block459S3 : ℝ))
    (hy4ne : y ≠ (block459S4 : ℝ)) :
    0 < block459V y := by
  have hcert := block459RightChunk000Certificate_eq_true
  unfold block459RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block459RightChunk000) (lo := block459RightChunk000L) (hi := block459RightChunk000R)
    (w1 := block459W1) (w2 := block459W2) (w3 := block459W3) (w4 := block459W4)
    (s1 := block459S1) (s2 := block459S2) (s3 := block459S3) (s4 := block459S4)
    hboxes hcover block459RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block459_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block459RightL : ℝ) (block459RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block459S1 : ℝ))
    (hy2ne : y ≠ (block459S2 : ℝ))
    (hy3ne : y ≠ (block459S3 : ℝ))
    (hy4ne : y ≠ (block459S4 : ℝ)) :
    0 < block459V y := by
  have hL : (block459RightChunk000L : ℝ) = (block459RightL : ℝ) := by
    norm_num [block459RightChunk000L, block459RightL]
  have hR : (block459RightChunk000R : ℝ) = (block459RightR : ℝ) := by
    norm_num [block459RightChunk000R, block459RightR]
  have hyc : y ∈ Icc (block459RightChunk000L : ℝ) (block459RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block459_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block459_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block459LeftL : ℝ) (block459LeftR : ℝ) →
    y ≠ 0 → y ≠ (block459S1 : ℝ) → y ≠ (block459S2 : ℝ) →
    y ≠ (block459S3 : ℝ) → y ≠ (block459S4 : ℝ) → 0 < block459V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block459RightL : ℝ) (block459RightR : ℝ) →
    y ≠ 0 → y ≠ (block459S1 : ℝ) → y ≠ (block459S2 : ℝ) →
    y ≠ (block459S3 : ℝ) → y ≠ (block459S4 : ℝ) → 0 < block459V y)

theorem block459_reallog_certificate_proof :
    block459_reallog_certificate := by
  exact ⟨block459_left_V_pos, block459_right_V_pos⟩

end Block459
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block459.block459V
#check Erdos1038Lean.M1817475.Block459.block459_left_V_pos
#check Erdos1038Lean.M1817475.Block459.block459_right_V_pos
#check Erdos1038Lean.M1817475.Block459.block459_reallog_certificate_proof
