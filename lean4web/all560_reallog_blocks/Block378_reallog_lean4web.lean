/-
Self-contained Lean4Web paste file.
Block 378 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block378

def block378LeftL : Rat := ((37169194196428571591 : Rat) / 50000000000000000000)
def block378LeftR : Rat := ((18589484375000000081 : Rat) / 25000000000000000000)
def block378RightL : Rat := ((87169194196428571591 : Rat) / 50000000000000000000)
def block378RightR : Rat := ((68589484375000000081 : Rat) / 25000000000000000000)

def block378LeftBoxes : List RatBox := [
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37169194196428571591 : Rat) / 50000000000000000000), R := ((18589484375000000081 : Rat) / 25000000000000000000), D0 := ((18589484375000000081 : Rat) / 25000000000000000000), D1 := ((53704560803571428409 : Rat) / 50000000000000000000), D2 := ((90727555803571428409 : Rat) / 50000000000000000000), D3 := ((23893700133928571399 : Rat) / 12500000000000000000), D4 := ((101449312232142852007 : Rat) / 50000000000000000000), LB := ((1245086410634777 : Rat) / 200000000000000000) }
]

def block378LeftCertificate : Bool :=
  allBoxesValid block378LeftBoxes &&
  coversFromBool block378LeftBoxes block378LeftL block378LeftR

theorem block378LeftCertificate_eq_true :
    block378LeftCertificate = true := by
  native_decide

def block378RightChunk000 : List RatBox := [
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87169194196428571591 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3704560803571428409 : Rat) / 50000000000000000000), D2 := ((40727555803571428409 : Rat) / 50000000000000000000), D3 := ((11393700133928571399 : Rat) / 12500000000000000000), D4 := ((51449312232142852007 : Rat) / 50000000000000000000), LB := ((2053111987514579 : Rat) / 1250000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41870239732142857187 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((5656063308292611 : Rat) / 50000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23358742232142857187 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((1860991411408783 : Rat) / 25000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((18730867857142857187 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((567926415205813 : Rat) / 12500000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16416930669642857187 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((10189108314537721 : Rat) / 250000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((15259962075892857187 : Rat) / 50000000000000000000), D4 := ((10567236886160711799 : Rat) / 25000000000000000000), LB := ((74245553464729 : Rat) / 4000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14102993482142857187 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((21925214376109087 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((13524509185267857187 : Rat) / 50000000000000000000), D4 := ((9699510440848211799 : Rat) / 25000000000000000000), LB := ((6792471271225023 : Rat) / 500000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12946024888392857187 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((1557631865802163 : Rat) / 250000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12367540591517857187 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((2109770416362089 : Rat) / 200000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((12078298443080357187 : Rat) / 50000000000000000000), D4 := ((8976405069754461799 : Rat) / 25000000000000000000), LB := ((7714320024754889 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11789056294642857187 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((5165942147556141 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11499814146205357187 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((2914258589277019 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11210571997767857187 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((9711055568990823 : Rat) / 10000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10921329849330357187 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((4492859668179 : Rat) / 1000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10776708775111607187 : Rat) / 50000000000000000000), D4 := ((8325610235770086799 : Rat) / 25000000000000000000), LB := ((3787857368902109 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((10632087700892857187 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((15846452934824007 : Rat) / 5000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((10487466626674107187 : Rat) / 50000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((26393593831250117 : Rat) / 10000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10342845552455357187 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((22004132353155847 : Rat) / 10000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10198224478236607187 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((927482354985007 : Rat) / 500000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10053603404017857187 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((8028524387986291 : Rat) / 5000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9908982329799107187 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((1455520755728773 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9764361255580357187 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((3518787796638681 : Rat) / 2500000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((9619740181361607187 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((457821588427023 : Rat) / 312500000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9475119107142857187 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((8158339822353783 : Rat) / 5000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9330498032924107187 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((382266202089937 : Rat) / 200000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9185876958705357187 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((2308245747764337 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9041255884486607187 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((353375982592493 : Rat) / 125000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8896634810267857187 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((17363138672370493 : Rat) / 5000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((8752013736049107187 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((8501170170371719 : Rat) / 2000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8607392661830357187 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((31945356385440493 : Rat) / 100000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8318150513392857187 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((5133944155273 : Rat) / 1953125000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8028908364955357187 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((5579867121912413 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((7739666216517857187 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((9250842695175981 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7450424068080357187 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((171756390132451 : Rat) / 12500000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7161181919642857187 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((4931729598303569 : Rat) / 500000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6582697622767857187 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((24493759539268273 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6004213325892857187 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((14214820338728007 : Rat) / 500000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516434244732142857187 : Rat) / 200000000000000000000), D0 := ((516434244732142857187 : Rat) / 200000000000000000000), D1 := ((152939224732142857187 : Rat) / 200000000000000000000), D2 := ((4847244732142857187 : Rat) / 200000000000000000000), D3 := ((4847244732142857187 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((3743711931171281 : Rat) / 100000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516434244732142857187 : Rat) / 200000000000000000000), R := ((260640744732142857187 : Rat) / 100000000000000000000), D0 := ((260640744732142857187 : Rat) / 100000000000000000000), D1 := ((78893234732142857187 : Rat) / 100000000000000000000), D2 := ((4847244732142857187 : Rat) / 100000000000000000000), D3 := ((14541734196428571561 : Rat) / 200000000000000000000), D4 := ((7607956196428567441 : Rat) / 40000000000000000000), LB := ((1559915720066779 : Rat) / 50000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((260640744732142857187 : Rat) / 100000000000000000000), R := ((132743994732142857187 : Rat) / 50000000000000000000), D0 := ((132743994732142857187 : Rat) / 50000000000000000000), D1 := ((41870239732142857187 : Rat) / 50000000000000000000), D2 := ((4847244732142857187 : Rat) / 50000000000000000000), D3 := ((4847244732142857187 : Rat) / 100000000000000000000), D4 := ((16596268124999990009 : Rat) / 100000000000000000000), LB := ((3117615700465301 : Rat) / 250000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((132743994732142857187 : Rat) / 50000000000000000000), R := ((535410952946428571723 : Rat) / 200000000000000000000), D0 := ((535410952946428571723 : Rat) / 200000000000000000000), D1 := ((171915932946428571723 : Rat) / 200000000000000000000), D2 := ((23823952946428571723 : Rat) / 200000000000000000000), D3 := ((177398960714285719 : Rat) / 8000000000000000000), D4 := ((5874511696428566411 : Rat) / 50000000000000000000), LB := ((7190200218576931 : Rat) / 50000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((535410952946428571723 : Rat) / 200000000000000000000), R := ((269922963482142857349 : Rat) / 100000000000000000000), D0 := ((269922963482142857349 : Rat) / 100000000000000000000), D1 := ((88175453482142857349 : Rat) / 100000000000000000000), D2 := ((14129463482142857349 : Rat) / 100000000000000000000), D3 := ((177398960714285719 : Rat) / 4000000000000000000), D4 := ((19063072767857122669 : Rat) / 200000000000000000000), LB := ((6513234468199569 : Rat) / 250000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((269922963482142857349 : Rat) / 100000000000000000000), R := ((1084126827946428572371 : Rat) / 400000000000000000000), D0 := ((1084126827946428572371 : Rat) / 400000000000000000000), D1 := ((357136787946428572371 : Rat) / 400000000000000000000), D2 := ((60952827946428572371 : Rat) / 400000000000000000000), D3 := ((177398960714285719 : Rat) / 3200000000000000000), D4 := ((7314049374999989847 : Rat) / 100000000000000000000), LB := ((4885553430973577 : Rat) / 500000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1084126827946428572371 : Rat) / 400000000000000000000), R := ((2172688629910714287717 : Rat) / 800000000000000000000), D0 := ((2172688629910714287717 : Rat) / 800000000000000000000), D1 := ((718708549910714287717 : Rat) / 800000000000000000000), D2 := ((126340629910714287717 : Rat) / 800000000000000000000), D3 := ((1951388567857142909 : Rat) / 32000000000000000000), D4 := ((24821223482142816413 : Rat) / 400000000000000000000), LB := ((8827910177654497 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2172688629910714287717 : Rat) / 800000000000000000000), R := ((4349812233839285718409 : Rat) / 1600000000000000000000), D0 := ((4349812233839285718409 : Rat) / 1600000000000000000000), D1 := ((1441852073839285718409 : Rat) / 1600000000000000000000), D2 := ((257116233839285718409 : Rat) / 1600000000000000000000), D3 := ((4080176096428571537 : Rat) / 64000000000000000000), D4 := ((45207472946428489851 : Rat) / 800000000000000000000), LB := ((16395977680229 : Rat) / 1562500000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4349812233839285718409 : Rat) / 1600000000000000000000), R := ((544280900982142857673 : Rat) / 200000000000000000000), D0 := ((544280900982142857673 : Rat) / 200000000000000000000), D1 := ((180785880982142857673 : Rat) / 200000000000000000000), D2 := ((32693900982142857673 : Rat) / 200000000000000000000), D3 := ((532196882142857157 : Rat) / 8000000000000000000), D4 := ((85979971874999836727 : Rat) / 1600000000000000000000), LB := ((6408587386409481 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((544280900982142857673 : Rat) / 200000000000000000000), R := ((4358682181875000004359 : Rat) / 1600000000000000000000), D0 := ((4358682181875000004359 : Rat) / 1600000000000000000000), D1 := ((1450722021875000004359 : Rat) / 1600000000000000000000), D2 := ((265986181875000004359 : Rat) / 1600000000000000000000), D3 := ((177398960714285719 : Rat) / 2560000000000000000), D4 := ((10193124732142836719 : Rat) / 200000000000000000000), LB := ((2993485057538603 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4358682181875000004359 : Rat) / 1600000000000000000000), R := ((2181558577946428573667 : Rat) / 800000000000000000000), D0 := ((2181558577946428573667 : Rat) / 800000000000000000000), D1 := ((727578497946428573667 : Rat) / 800000000000000000000), D2 := ((135210577946428573667 : Rat) / 800000000000000000000), D3 := ((2306186489285714347 : Rat) / 32000000000000000000), D4 := ((77110023839285550777 : Rat) / 1600000000000000000000), LB := ((2679683034303437 : Rat) / 10000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2181558577946428573667 : Rat) / 800000000000000000000), R := ((8730669285803571437643 : Rat) / 3200000000000000000000), D0 := ((8730669285803571437643 : Rat) / 3200000000000000000000), D1 := ((2914748965803571437643 : Rat) / 3200000000000000000000), D2 := ((545277285803571437643 : Rat) / 3200000000000000000000), D3 := ((9402144917857143107 : Rat) / 128000000000000000000), D4 := ((36337524910714203901 : Rat) / 800000000000000000000), LB := ((1355231365533327 : Rat) / 400000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8730669285803571437643 : Rat) / 3200000000000000000000), R := ((4367552129910714290309 : Rat) / 1600000000000000000000), D0 := ((4367552129910714290309 : Rat) / 1600000000000000000000), D1 := ((1459591969910714290309 : Rat) / 1600000000000000000000), D2 := ((274856129910714290309 : Rat) / 1600000000000000000000), D3 := ((4789771939285714413 : Rat) / 64000000000000000000), D4 := ((140915125624999672629 : Rat) / 3200000000000000000000), LB := ((26078153662088543 : Rat) / 10000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4367552129910714290309 : Rat) / 1600000000000000000000), R := ((8739539233839285723593 : Rat) / 3200000000000000000000), D0 := ((8739539233839285723593 : Rat) / 3200000000000000000000), D1 := ((2923618913839285723593 : Rat) / 3200000000000000000000), D2 := ((554147233839285723593 : Rat) / 3200000000000000000000), D3 := ((1951388567857142909 : Rat) / 25600000000000000000), D4 := ((68240075803571264827 : Rat) / 1600000000000000000000), LB := ((4051631708077541 : Rat) / 2000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8739539233839285723593 : Rat) / 3200000000000000000000), R := ((1092996775982142858321 : Rat) / 400000000000000000000), D0 := ((1092996775982142858321 : Rat) / 400000000000000000000), D1 := ((366006735982142858321 : Rat) / 400000000000000000000), D2 := ((69822775982142858321 : Rat) / 400000000000000000000), D3 := ((1241792725000000033 : Rat) / 16000000000000000000), D4 := ((132045177589285386679 : Rat) / 3200000000000000000000), LB := ((2061579643195463 : Rat) / 1250000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1092996775982142858321 : Rat) / 400000000000000000000), R := ((8748409181875000009543 : Rat) / 3200000000000000000000), D0 := ((8748409181875000009543 : Rat) / 3200000000000000000000), D1 := ((2932488861875000009543 : Rat) / 3200000000000000000000), D2 := ((563017181875000009543 : Rat) / 3200000000000000000000), D3 := ((10111740760714285983 : Rat) / 128000000000000000000), D4 := ((15951275446428530463 : Rat) / 400000000000000000000), LB := ((1857986164819983 : Rat) / 1250000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8748409181875000009543 : Rat) / 3200000000000000000000), R := ((4376422077946428576259 : Rat) / 1600000000000000000000), D0 := ((4376422077946428576259 : Rat) / 1600000000000000000000), D1 := ((1468461917946428576259 : Rat) / 1600000000000000000000), D2 := ((283726077946428576259 : Rat) / 1600000000000000000000), D3 := ((5144569860714285851 : Rat) / 64000000000000000000), D4 := ((123175229553571100729 : Rat) / 3200000000000000000000), LB := ((15465936902744337 : Rat) / 10000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4376422077946428576259 : Rat) / 1600000000000000000000), R := ((8757279129910714295493 : Rat) / 3200000000000000000000), D0 := ((8757279129910714295493 : Rat) / 3200000000000000000000), D1 := ((2941358809910714295493 : Rat) / 3200000000000000000000), D2 := ((571887129910714295493 : Rat) / 3200000000000000000000), D3 := ((10466538682142857421 : Rat) / 128000000000000000000), D4 := ((59370127767856978877 : Rat) / 1600000000000000000000), LB := ((1840603492838877 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8757279129910714295493 : Rat) / 3200000000000000000000), R := ((2190428525982142859617 : Rat) / 800000000000000000000), D0 := ((2190428525982142859617 : Rat) / 800000000000000000000), D1 := ((736448445982142859617 : Rat) / 800000000000000000000), D2 := ((144080525982142859617 : Rat) / 800000000000000000000), D3 := ((532196882142857157 : Rat) / 6400000000000000000), D4 := ((114305281517856814779 : Rat) / 3200000000000000000000), LB := ((2975811087730651 : Rat) / 1250000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190428525982142859617 : Rat) / 800000000000000000000), R := ((8766149077946428581443 : Rat) / 3200000000000000000000), D0 := ((8766149077946428581443 : Rat) / 3200000000000000000000), D1 := ((2950228757946428581443 : Rat) / 3200000000000000000000), D2 := ((580757077946428581443 : Rat) / 3200000000000000000000), D3 := ((10821336603571428859 : Rat) / 128000000000000000000), D4 := ((27467576874999917951 : Rat) / 800000000000000000000), LB := ((31806847615243883 : Rat) / 10000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8766149077946428581443 : Rat) / 3200000000000000000000), R := ((4385292025982142862209 : Rat) / 1600000000000000000000), D0 := ((4385292025982142862209 : Rat) / 1600000000000000000000), D1 := ((1477331865982142862209 : Rat) / 1600000000000000000000), D2 := ((292596025982142862209 : Rat) / 1600000000000000000000), D3 := ((5499367782142857289 : Rat) / 64000000000000000000), D4 := ((105435333482142528829 : Rat) / 3200000000000000000000), LB := ((4256656715299123 : Rat) / 1000000000000000000) },
  { w1 := ((8529503642159403 : Rat) / 10000000000000000), w2 := ((2337050573264133 : Rat) / 50000000000000000), w3 := ((1574457332453511 : Rat) / 10000000000000000), w4 := ((14025114540471553 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132743994732142857187 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4385292025982142862209 : Rat) / 1600000000000000000000), R := ((68589484375000000081 : Rat) / 25000000000000000000), D0 := ((68589484375000000081 : Rat) / 25000000000000000000), D1 := ((23152606875000000081 : Rat) / 25000000000000000000), D2 := ((4641109375000000081 : Rat) / 25000000000000000000), D3 := ((177398960714285719 : Rat) / 2000000000000000000), D4 := ((50500179732142692927 : Rat) / 1600000000000000000000), LB := ((5071844814890647 : Rat) / 5000000000000000000) }
]

def block378RightChunk000L : Rat := ((87169194196428571591 : Rat) / 50000000000000000000)
def block378RightChunk000R : Rat := ((68589484375000000081 : Rat) / 25000000000000000000)

def block378RightChunk000Certificate : Bool :=
  allBoxesValid block378RightChunk000 &&
  coversFromBool block378RightChunk000 block378RightChunk000L block378RightChunk000R

theorem block378RightChunk000Certificate_eq_true :
    block378RightChunk000Certificate = true := by
  native_decide

def block378RightChainCertificate : Bool :=
  decide (
    block378RightL = ((87169194196428571591 : Rat) / 50000000000000000000) /\
    ((68589484375000000081 : Rat) / 25000000000000000000) = block378RightR)

theorem block378RightChainCertificate_eq_true :
    block378RightChainCertificate = true := by
  native_decide

def block378LeftBoxCount : Nat := boxCount block378LeftBoxes
def block378RightBoxCount : Nat := 60

def block378_rational_certificate : Prop :=
    block378LeftCertificate = true /\
    block378RightChainCertificate = true /\
    block378RightChunk000Certificate = true

theorem block378_rational_certificate_proof :
    block378_rational_certificate := by
  exact ⟨block378LeftCertificate_eq_true, block378RightChainCertificate_eq_true, block378RightChunk000Certificate_eq_true⟩

end Block378
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block378

open Set

def block378W1 : Rat := ((8529503642159403 : Rat) / 10000000000000000)
def block378W2 : Rat := ((2337050573264133 : Rat) / 50000000000000000)
def block378W3 : Rat := ((1574457332453511 : Rat) / 10000000000000000)
def block378W4 : Rat := ((14025114540471553 : Rat) / 100000000000000000)
def block378S1 : Rat := ((18174751 : Rat) / 10000000)
def block378S2 : Rat := ((511587 : Rat) / 200000)
def block378S3 : Rat := ((132743994732142857187 : Rat) / 50000000000000000000)
def block378S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block378V (y : ℝ) : ℝ :=
  ratPotential block378W1 block378W2 block378W3 block378W4 block378S1 block378S2 block378S3 block378S4 y

def block378LeftParamsCertificate : Bool :=
  allBoxesSameParams block378LeftBoxes block378W1 block378W2 block378W3 block378W4 block378S1 block378S2 block378S3 block378S4

theorem block378LeftParamsCertificate_eq_true :
    block378LeftParamsCertificate = true := by
  native_decide

theorem block378_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block378LeftL : ℝ) (block378LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block378S1 : ℝ))
    (hy2ne : y ≠ (block378S2 : ℝ))
    (hy3ne : y ≠ (block378S3 : ℝ))
    (hy4ne : y ≠ (block378S4 : ℝ)) :
    0 < block378V y := by
  have hcert := block378LeftCertificate_eq_true
  unfold block378LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block378LeftBoxes) (lo := block378LeftL) (hi := block378LeftR)
    (w1 := block378W1) (w2 := block378W2) (w3 := block378W3) (w4 := block378W4)
    (s1 := block378S1) (s2 := block378S2) (s3 := block378S3) (s4 := block378S4)
    hboxes hcover block378LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block378RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block378RightChunk000 block378W1 block378W2 block378W3 block378W4 block378S1 block378S2 block378S3 block378S4

theorem block378RightChunk000ParamsCertificate_eq_true :
    block378RightChunk000ParamsCertificate = true := by
  native_decide

theorem block378_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block378RightChunk000L : ℝ) (block378RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block378S1 : ℝ))
    (hy2ne : y ≠ (block378S2 : ℝ))
    (hy3ne : y ≠ (block378S3 : ℝ))
    (hy4ne : y ≠ (block378S4 : ℝ)) :
    0 < block378V y := by
  have hcert := block378RightChunk000Certificate_eq_true
  unfold block378RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block378RightChunk000) (lo := block378RightChunk000L) (hi := block378RightChunk000R)
    (w1 := block378W1) (w2 := block378W2) (w3 := block378W3) (w4 := block378W4)
    (s1 := block378S1) (s2 := block378S2) (s3 := block378S3) (s4 := block378S4)
    hboxes hcover block378RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block378_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block378RightL : ℝ) (block378RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block378S1 : ℝ))
    (hy2ne : y ≠ (block378S2 : ℝ))
    (hy3ne : y ≠ (block378S3 : ℝ))
    (hy4ne : y ≠ (block378S4 : ℝ)) :
    0 < block378V y := by
  have hL : (block378RightChunk000L : ℝ) = (block378RightL : ℝ) := by
    norm_num [block378RightChunk000L, block378RightL]
  have hR : (block378RightChunk000R : ℝ) = (block378RightR : ℝ) := by
    norm_num [block378RightChunk000R, block378RightR]
  have hyc : y ∈ Icc (block378RightChunk000L : ℝ) (block378RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block378_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block378_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block378LeftL : ℝ) (block378LeftR : ℝ) →
    y ≠ 0 → y ≠ (block378S1 : ℝ) → y ≠ (block378S2 : ℝ) →
    y ≠ (block378S3 : ℝ) → y ≠ (block378S4 : ℝ) → 0 < block378V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block378RightL : ℝ) (block378RightR : ℝ) →
    y ≠ 0 → y ≠ (block378S1 : ℝ) → y ≠ (block378S2 : ℝ) →
    y ≠ (block378S3 : ℝ) → y ≠ (block378S4 : ℝ) → 0 < block378V y)

theorem block378_reallog_certificate_proof :
    block378_reallog_certificate := by
  exact ⟨block378_left_V_pos, block378_right_V_pos⟩

end Block378
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block378.block378V
#check Erdos1038Lean.M1817475.Block378.block378_left_V_pos
#check Erdos1038Lean.M1817475.Block378.block378_right_V_pos
#check Erdos1038Lean.M1817475.Block378.block378_reallog_certificate_proof
