/-
Self-contained Lean4Web paste file.
Block 354 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block354

def block354LeftL : Rat := ((7480756696428571459 : Rat) / 10000000000000000000)
def block354LeftR : Rat := ((18706779017857142933 : Rat) / 25000000000000000000)
def block354RightL : Rat := ((17480756696428571459 : Rat) / 10000000000000000000)
def block354RightR : Rat := ((68706779017857142933 : Rat) / 25000000000000000000)

def block354LeftBoxes : List RatBox := [
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((7480756696428571459 : Rat) / 10000000000000000000), R := ((18706779017857142933 : Rat) / 25000000000000000000), D0 := ((18706779017857142933 : Rat) / 25000000000000000000), D1 := ((10693994303571428541 : Rat) / 10000000000000000000), D2 := ((18098593303571428541 : Rat) / 10000000000000000000), D3 := ((958093898214285713 : Rat) / 500000000000000000), D4 := ((101214722946428566303 : Rat) / 50000000000000000000), LB := ((776511753238467 : Rat) / 125000000000000000) }
]

def block354LeftCertificate : Bool :=
  allBoxesValid block354LeftBoxes &&
  coversFromBool block354LeftBoxes block354LeftL block354LeftR

theorem block354LeftCertificate_eq_true :
    block354LeftCertificate = true := by
  native_decide

def block354RightChunk000 : List RatBox := [
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((17480756696428571459 : Rat) / 10000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((693994303571428541 : Rat) / 10000000000000000000), D2 := ((8098593303571428541 : Rat) / 10000000000000000000), D3 := ((458093898214285713 : Rat) / 500000000000000000), D4 := ((51214722946428566303 : Rat) / 50000000000000000000), LB := ((18186263384101469 : Rat) / 10000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8467883660714285719 : Rat) / 10000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((77621718090139 : Rat) / 500000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4765584160714285719 : Rat) / 10000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((10057164424211519 : Rat) / 100000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3840009285714285719 : Rat) / 10000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((648348598414717 : Rat) / 10000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3377221848214285719 : Rat) / 10000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((8609641120602071 : Rat) / 1000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2914434410714285719 : Rat) / 10000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((5074617409958723 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2683040691964285719 : Rat) / 10000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((1821751371872321 : Rat) / 125000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2567343832589285719 : Rat) / 10000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((3401197891530733 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2451646973214285719 : Rat) / 10000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((11252018231902583 : Rat) / 100000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2335950113839285719 : Rat) / 10000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((5306422499264579 : Rat) / 1000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2278101684151785719 : Rat) / 10000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((14600926902978567 : Rat) / 5000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2220253254464285719 : Rat) / 10000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((1077994581204049 : Rat) / 1250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2162404824776785719 : Rat) / 10000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((2210331382161951 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2133480609933035719 : Rat) / 10000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((9197716913698431 : Rat) / 2500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2104556395089285719 : Rat) / 10000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((7577510929416137 : Rat) / 2500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((2075632180245535719 : Rat) / 10000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((309896352511229 : Rat) / 125000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2046707965401785719 : Rat) / 10000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((20265517222346763 : Rat) / 10000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((2017783750558035719 : Rat) / 10000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((838172703768833 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((1988859535714285719 : Rat) / 10000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((7160042697777619 : Rat) / 5000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((1959935320870535719 : Rat) / 10000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((3243214039010331 : Rat) / 2500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((1931011106026785719 : Rat) / 10000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((255248619268561 : Rat) / 200000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((1902086891183035719 : Rat) / 10000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((6866545441017863 : Rat) / 5000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((1873162676339285719 : Rat) / 10000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((7966598631059807 : Rat) / 5000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((1844238461495535719 : Rat) / 10000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((19415736946767903 : Rat) / 10000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((1815314246651785719 : Rat) / 10000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((24238967004411027 : Rat) / 10000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((1786390031808035719 : Rat) / 10000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((1904198880437781 : Rat) / 625000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1757465816964285719 : Rat) / 10000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((19085817040872949 : Rat) / 5000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((1728541602120535719 : Rat) / 10000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((2371582126265051 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((1699617387276785719 : Rat) / 10000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((862050675933479 : Rat) / 1000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((1641768957589285719 : Rat) / 10000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((722446386760589 : Rat) / 200000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((1583920527901785719 : Rat) / 10000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((1789513522431313 : Rat) / 250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1526072098214285719 : Rat) / 10000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((19401041634116711 : Rat) / 10000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1410375238839285719 : Rat) / 10000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1819945686297831 : Rat) / 125000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1294678379464285719 : Rat) / 10000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((7834321654018553 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((103380684660714285719 : Rat) / 40000000000000000000), D0 := ((103380684660714285719 : Rat) / 40000000000000000000), D1 := ((30681680660714285719 : Rat) / 40000000000000000000), D2 := ((1063284660714285719 : Rat) / 40000000000000000000), D3 := ((1063284660714285719 : Rat) / 10000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((5397577086352967 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((103380684660714285719 : Rat) / 40000000000000000000), R := ((207824653982142857157 : Rat) / 80000000000000000000), D0 := ((207824653982142857157 : Rat) / 80000000000000000000), D1 := ((62426645982142857157 : Rat) / 80000000000000000000), D2 := ((3189853982142857157 : Rat) / 80000000000000000000), D3 := ((3189853982142857157 : Rat) / 40000000000000000000), D4 := ((37570602410714265797 : Rat) / 200000000000000000000), LB := ((6490500125068871 : Rat) / 200000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((207824653982142857157 : Rat) / 80000000000000000000), R := ((52221984660714285719 : Rat) / 20000000000000000000), D0 := ((52221984660714285719 : Rat) / 20000000000000000000), D1 := ((15872482660714285719 : Rat) / 20000000000000000000), D2 := ((1063284660714285719 : Rat) / 20000000000000000000), D3 := ((1063284660714285719 : Rat) / 16000000000000000000), D4 := ((69824781517857102999 : Rat) / 400000000000000000000), LB := ((18009874581539617 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((52221984660714285719 : Rat) / 20000000000000000000), R := ((105507253982142857157 : Rat) / 40000000000000000000), D0 := ((105507253982142857157 : Rat) / 40000000000000000000), D1 := ((32808249982142857157 : Rat) / 40000000000000000000), D2 := ((3189853982142857157 : Rat) / 40000000000000000000), D3 := ((1063284660714285719 : Rat) / 20000000000000000000), D4 := ((16127089553571418601 : Rat) / 100000000000000000000), LB := ((5366945705742393 : Rat) / 250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((105507253982142857157 : Rat) / 40000000000000000000), R := ((26642634660714285719 : Rat) / 10000000000000000000), D0 := ((26642634660714285719 : Rat) / 10000000000000000000), D1 := ((8467883660714285719 : Rat) / 10000000000000000000), D2 := ((1063284660714285719 : Rat) / 10000000000000000000), D3 := ((1063284660714285719 : Rat) / 40000000000000000000), D4 := ((26937755803571408607 : Rat) / 200000000000000000000), LB := ((1225711561349313 : Rat) / 12500000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((26642634660714285719 : Rat) / 10000000000000000000), R := ((537053077946428571651 : Rat) / 200000000000000000000), D0 := ((537053077946428571651 : Rat) / 200000000000000000000), D1 := ((173558057946428571651 : Rat) / 200000000000000000000), D2 := ((25466077946428571651 : Rat) / 200000000000000000000), D3 := ((4200384732142857271 : Rat) / 200000000000000000000), D4 := ((5405333124999995003 : Rat) / 50000000000000000000), LB := ((12544507199429283 : Rat) / 100000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((537053077946428571651 : Rat) / 200000000000000000000), R := ((270626731339285714461 : Rat) / 100000000000000000000), D0 := ((270626731339285714461 : Rat) / 100000000000000000000), D1 := ((88879221339285714461 : Rat) / 100000000000000000000), D2 := ((14833231339285714461 : Rat) / 100000000000000000000), D3 := ((4200384732142857271 : Rat) / 100000000000000000000), D4 := ((17420947767857122741 : Rat) / 200000000000000000000), LB := ((14872090411122751 : Rat) / 1000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270626731339285714461 : Rat) / 100000000000000000000), R := ((217341462017857143023 : Rat) / 80000000000000000000), D0 := ((217341462017857143023 : Rat) / 80000000000000000000), D1 := ((71943454017857143023 : Rat) / 80000000000000000000), D2 := ((12706662017857143023 : Rat) / 80000000000000000000), D3 := ((4200384732142857271 : Rat) / 80000000000000000000), D4 := ((1322056303571426547 : Rat) / 20000000000000000000), LB := ((19610626558798083 : Rat) / 10000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((217341462017857143023 : Rat) / 80000000000000000000), R := ((2177615004910714287501 : Rat) / 800000000000000000000), D0 := ((2177615004910714287501 : Rat) / 800000000000000000000), D1 := ((723634924910714287501 : Rat) / 800000000000000000000), D2 := ((131267004910714287501 : Rat) / 800000000000000000000), D3 := ((46204232053571429981 : Rat) / 800000000000000000000), D4 := ((22240741339285673669 : Rat) / 400000000000000000000), LB := ((3666988119667633 : Rat) / 1250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2177615004910714287501 : Rat) / 800000000000000000000), R := ((4359430394553571432273 : Rat) / 1600000000000000000000), D0 := ((4359430394553571432273 : Rat) / 1600000000000000000000), D1 := ((1451470234553571432273 : Rat) / 1600000000000000000000), D2 := ((266734394553571432273 : Rat) / 1600000000000000000000), D3 := ((96608848839285717233 : Rat) / 1600000000000000000000), D4 := ((40281097946428490067 : Rat) / 800000000000000000000), LB := ((2845429516135617 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4359430394553571432273 : Rat) / 1600000000000000000000), R := ((545453847410714286193 : Rat) / 200000000000000000000), D0 := ((545453847410714286193 : Rat) / 200000000000000000000), D1 := ((181958827410714286193 : Rat) / 200000000000000000000), D2 := ((33866847410714286193 : Rat) / 200000000000000000000), D3 := ((12601154196428571813 : Rat) / 200000000000000000000), D4 := ((76361811160714122863 : Rat) / 1600000000000000000000), LB := ((2426159261519567 : Rat) / 1000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545453847410714286193 : Rat) / 200000000000000000000), R := ((8731461943303571436359 : Rat) / 3200000000000000000000), D0 := ((8731461943303571436359 : Rat) / 3200000000000000000000), D1 := ((2915541623303571436359 : Rat) / 3200000000000000000000), D2 := ((546069943303571436359 : Rat) / 3200000000000000000000), D3 := ((205818851875000006279 : Rat) / 3200000000000000000000), D4 := ((9020178303571408199 : Rat) / 200000000000000000000), LB := ((1257757943825391 : Rat) / 250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8731461943303571436359 : Rat) / 3200000000000000000000), R := ((873566232803571429363 : Rat) / 320000000000000000000), D0 := ((873566232803571429363 : Rat) / 320000000000000000000), D1 := ((291974200803571429363 : Rat) / 320000000000000000000), D2 := ((55027032803571429363 : Rat) / 320000000000000000000), D3 := ((4200384732142857271 : Rat) / 64000000000000000000), D4 := ((140122468124999673913 : Rat) / 3200000000000000000000), LB := ((988880434164563 : Rat) / 250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((873566232803571429363 : Rat) / 320000000000000000000), R := ((8739862712767857150901 : Rat) / 3200000000000000000000), D0 := ((8739862712767857150901 : Rat) / 3200000000000000000000), D1 := ((2923942392767857150901 : Rat) / 3200000000000000000000), D2 := ((554470712767857150901 : Rat) / 3200000000000000000000), D3 := ((214219621339285720821 : Rat) / 3200000000000000000000), D4 := ((67961041696428408321 : Rat) / 1600000000000000000000), LB := ((767371831548333 : Rat) / 250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8739862712767857150901 : Rat) / 3200000000000000000000), R := ((2186015774375000002043 : Rat) / 800000000000000000000), D0 := ((2186015774375000002043 : Rat) / 800000000000000000000), D1 := ((732035694375000002043 : Rat) / 800000000000000000000), D2 := ((139667774375000002043 : Rat) / 800000000000000000000), D3 := ((54605001517857144523 : Rat) / 800000000000000000000), D4 := ((131721698660713959371 : Rat) / 3200000000000000000000), LB := ((1189186863603503 : Rat) / 500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2186015774375000002043 : Rat) / 800000000000000000000), R := ((8748263482232142865443 : Rat) / 3200000000000000000000), D0 := ((8748263482232142865443 : Rat) / 3200000000000000000000), D1 := ((2932343162232142865443 : Rat) / 3200000000000000000000), D2 := ((562871482232142865443 : Rat) / 3200000000000000000000), D3 := ((222620390803571435363 : Rat) / 3200000000000000000000), D4 := ((1275213139285711021 : Rat) / 32000000000000000000), LB := ((18885211236041033 : Rat) / 10000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8748263482232142865443 : Rat) / 3200000000000000000000), R := ((4376231933482142861357 : Rat) / 1600000000000000000000), D0 := ((4376231933482142861357 : Rat) / 1600000000000000000000), D1 := ((1468271773482142861357 : Rat) / 1600000000000000000000), D2 := ((283535933482142861357 : Rat) / 1600000000000000000000), D3 := ((113410387767857146317 : Rat) / 1600000000000000000000), D4 := ((123320929196428244829 : Rat) / 3200000000000000000000), LB := ((8036283376660347 : Rat) / 5000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4376231933482142861357 : Rat) / 1600000000000000000000), R := ((1751332850339285715997 : Rat) / 640000000000000000000), D0 := ((1751332850339285715997 : Rat) / 640000000000000000000), D1 := ((588148786339285715997 : Rat) / 640000000000000000000), D2 := ((114254450339285715997 : Rat) / 640000000000000000000), D3 := ((46204232053571429981 : Rat) / 640000000000000000000), D4 := ((59560272232142693779 : Rat) / 1600000000000000000000), LB := ((15430050845096077 : Rat) / 10000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1751332850339285715997 : Rat) / 640000000000000000000), R := ((1095108079553571429657 : Rat) / 400000000000000000000), D0 := ((1095108079553571429657 : Rat) / 400000000000000000000), D1 := ((368118039553571429657 : Rat) / 400000000000000000000), D2 := ((71934079553571429657 : Rat) / 400000000000000000000), D3 := ((29402693125000000897 : Rat) / 400000000000000000000), D4 := ((114920159732142530287 : Rat) / 3200000000000000000000), LB := ((4263553656557867 : Rat) / 2500000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1095108079553571429657 : Rat) / 400000000000000000000), R := ((8765065021160714294527 : Rat) / 3200000000000000000000), D0 := ((8765065021160714294527 : Rat) / 3200000000000000000000), D1 := ((2949144701160714294527 : Rat) / 3200000000000000000000), D2 := ((579673021160714294527 : Rat) / 3200000000000000000000), D3 := ((239421929732142864447 : Rat) / 3200000000000000000000), D4 := ((13839971874999959127 : Rat) / 400000000000000000000), LB := ((1315969509378713 : Rat) / 625000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8765065021160714294527 : Rat) / 3200000000000000000000), R := ((4384632702946428575899 : Rat) / 1600000000000000000000), D0 := ((4384632702946428575899 : Rat) / 1600000000000000000000), D1 := ((1476672542946428575899 : Rat) / 1600000000000000000000), D2 := ((291936702946428575899 : Rat) / 1600000000000000000000), D3 := ((121811157232142860859 : Rat) / 1600000000000000000000), D4 := ((21303878053571363149 : Rat) / 640000000000000000000), LB := ((689005742608953 : Rat) / 250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4384632702946428575899 : Rat) / 1600000000000000000000), R := ((8773465790625000009069 : Rat) / 3200000000000000000000), D0 := ((8773465790625000009069 : Rat) / 3200000000000000000000), D1 := ((2957545470625000009069 : Rat) / 3200000000000000000000), D2 := ((588073790625000009069 : Rat) / 3200000000000000000000), D3 := ((247822699196428578989 : Rat) / 3200000000000000000000), D4 := ((51159502767856979237 : Rat) / 1600000000000000000000), LB := ((367128231298397 : Rat) / 100000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8773465790625000009069 : Rat) / 3200000000000000000000), R := ((438883308767857143317 : Rat) / 160000000000000000000), D0 := ((438883308767857143317 : Rat) / 160000000000000000000), D1 := ((148087292767857143317 : Rat) / 160000000000000000000), D2 := ((29613708767857143317 : Rat) / 160000000000000000000), D3 := ((12601154196428571813 : Rat) / 160000000000000000000), D4 := ((98118620803571101203 : Rat) / 3200000000000000000000), LB := ((1216969094585657 : Rat) / 250000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((438883308767857143317 : Rat) / 160000000000000000000), R := ((4393033472410714290441 : Rat) / 1600000000000000000000), D0 := ((4393033472410714290441 : Rat) / 1600000000000000000000), D1 := ((1485073312410714290441 : Rat) / 1600000000000000000000), D2 := ((300337472410714290441 : Rat) / 1600000000000000000000), D3 := ((130211926696428575401 : Rat) / 1600000000000000000000), D4 := ((23479559017857060983 : Rat) / 800000000000000000000), LB := ((9212510351504777 : Rat) / 5000000000000000000) },
  { w1 := ((8981828514220107 : Rat) / 10000000000000000), w2 := ((4755536156841607 : Rat) / 100000000000000000), w3 := ((15001305437149837 : Rat) / 100000000000000000), w4 := ((1732450594830973 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26642634660714285719 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4393033472410714290441 : Rat) / 1600000000000000000000), R := ((68706779017857142933 : Rat) / 25000000000000000000), D0 := ((68706779017857142933 : Rat) / 25000000000000000000), D1 := ((23269901517857142933 : Rat) / 25000000000000000000), D2 := ((4758404017857142933 : Rat) / 25000000000000000000), D3 := ((4200384732142857271 : Rat) / 50000000000000000000), D4 := ((8551746660714252939 : Rat) / 320000000000000000000), LB := ((1182754059865787 : Rat) / 200000000000000000) }
]

def block354RightChunk000L : Rat := ((17480756696428571459 : Rat) / 10000000000000000000)
def block354RightChunk000R : Rat := ((68706779017857142933 : Rat) / 25000000000000000000)

def block354RightChunk000Certificate : Bool :=
  allBoxesValid block354RightChunk000 &&
  coversFromBool block354RightChunk000 block354RightChunk000L block354RightChunk000R

theorem block354RightChunk000Certificate_eq_true :
    block354RightChunk000Certificate = true := by
  native_decide

def block354RightChainCertificate : Bool :=
  decide (
    block354RightL = ((17480756696428571459 : Rat) / 10000000000000000000) /\
    ((68706779017857142933 : Rat) / 25000000000000000000) = block354RightR)

theorem block354RightChainCertificate_eq_true :
    block354RightChainCertificate = true := by
  native_decide

def block354LeftBoxCount : Nat := boxCount block354LeftBoxes
def block354RightBoxCount : Nat := 59

def block354_rational_certificate : Prop :=
    block354LeftCertificate = true /\
    block354RightChainCertificate = true /\
    block354RightChunk000Certificate = true

theorem block354_rational_certificate_proof :
    block354_rational_certificate := by
  exact ⟨block354LeftCertificate_eq_true, block354RightChainCertificate_eq_true, block354RightChunk000Certificate_eq_true⟩

end Block354
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block354

open Set

def block354W1 : Rat := ((8981828514220107 : Rat) / 10000000000000000)
def block354W2 : Rat := ((4755536156841607 : Rat) / 100000000000000000)
def block354W3 : Rat := ((15001305437149837 : Rat) / 100000000000000000)
def block354W4 : Rat := ((1732450594830973 : Rat) / 12500000000000000)
def block354S1 : Rat := ((18174751 : Rat) / 10000000)
def block354S2 : Rat := ((511587 : Rat) / 200000)
def block354S3 : Rat := ((26642634660714285719 : Rat) / 10000000000000000000)
def block354S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block354V (y : ℝ) : ℝ :=
  ratPotential block354W1 block354W2 block354W3 block354W4 block354S1 block354S2 block354S3 block354S4 y

def block354LeftParamsCertificate : Bool :=
  allBoxesSameParams block354LeftBoxes block354W1 block354W2 block354W3 block354W4 block354S1 block354S2 block354S3 block354S4

theorem block354LeftParamsCertificate_eq_true :
    block354LeftParamsCertificate = true := by
  native_decide

theorem block354_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block354LeftL : ℝ) (block354LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block354S1 : ℝ))
    (hy2ne : y ≠ (block354S2 : ℝ))
    (hy3ne : y ≠ (block354S3 : ℝ))
    (hy4ne : y ≠ (block354S4 : ℝ)) :
    0 < block354V y := by
  have hcert := block354LeftCertificate_eq_true
  unfold block354LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block354LeftBoxes) (lo := block354LeftL) (hi := block354LeftR)
    (w1 := block354W1) (w2 := block354W2) (w3 := block354W3) (w4 := block354W4)
    (s1 := block354S1) (s2 := block354S2) (s3 := block354S3) (s4 := block354S4)
    hboxes hcover block354LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block354RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block354RightChunk000 block354W1 block354W2 block354W3 block354W4 block354S1 block354S2 block354S3 block354S4

theorem block354RightChunk000ParamsCertificate_eq_true :
    block354RightChunk000ParamsCertificate = true := by
  native_decide

theorem block354_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block354RightChunk000L : ℝ) (block354RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block354S1 : ℝ))
    (hy2ne : y ≠ (block354S2 : ℝ))
    (hy3ne : y ≠ (block354S3 : ℝ))
    (hy4ne : y ≠ (block354S4 : ℝ)) :
    0 < block354V y := by
  have hcert := block354RightChunk000Certificate_eq_true
  unfold block354RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block354RightChunk000) (lo := block354RightChunk000L) (hi := block354RightChunk000R)
    (w1 := block354W1) (w2 := block354W2) (w3 := block354W3) (w4 := block354W4)
    (s1 := block354S1) (s2 := block354S2) (s3 := block354S3) (s4 := block354S4)
    hboxes hcover block354RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block354_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block354RightL : ℝ) (block354RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block354S1 : ℝ))
    (hy2ne : y ≠ (block354S2 : ℝ))
    (hy3ne : y ≠ (block354S3 : ℝ))
    (hy4ne : y ≠ (block354S4 : ℝ)) :
    0 < block354V y := by
  have hL : (block354RightChunk000L : ℝ) = (block354RightL : ℝ) := by
    norm_num [block354RightChunk000L, block354RightL]
  have hR : (block354RightChunk000R : ℝ) = (block354RightR : ℝ) := by
    norm_num [block354RightChunk000R, block354RightR]
  have hyc : y ∈ Icc (block354RightChunk000L : ℝ) (block354RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block354_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block354_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block354LeftL : ℝ) (block354LeftR : ℝ) →
    y ≠ 0 → y ≠ (block354S1 : ℝ) → y ≠ (block354S2 : ℝ) →
    y ≠ (block354S3 : ℝ) → y ≠ (block354S4 : ℝ) → 0 < block354V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block354RightL : ℝ) (block354RightR : ℝ) →
    y ≠ 0 → y ≠ (block354S1 : ℝ) → y ≠ (block354S2 : ℝ) →
    y ≠ (block354S3 : ℝ) → y ≠ (block354S4 : ℝ) → 0 < block354V y)

theorem block354_reallog_certificate_proof :
    block354_reallog_certificate := by
  exact ⟨block354_left_V_pos, block354_right_V_pos⟩

end Block354
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block354.block354V
#check Erdos1038Lean.M1817475.Block354.block354_left_V_pos
#check Erdos1038Lean.M1817475.Block354.block354_right_V_pos
#check Erdos1038Lean.M1817475.Block354.block354_reallog_certificate_proof
