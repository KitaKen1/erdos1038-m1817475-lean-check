/-
Self-contained Lean4Web paste file.
Block 13 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block013

def block013LeftL : Rat := ((20368453125000000003 : Rat) / 25000000000000000000)
def block013LeftR : Rat := ((40746680803571428577 : Rat) / 50000000000000000000)
def block013RightL : Rat := ((45368453125000000003 : Rat) / 25000000000000000000)
def block013RightR : Rat := ((140746680803571428577 : Rat) / 50000000000000000000)

def block013LeftBoxes : List RatBox := [
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((20368453125000000003 : Rat) / 25000000000000000000), R := ((40746680803571428577 : Rat) / 50000000000000000000), D0 := ((40746680803571428577 : Rat) / 50000000000000000000), D1 := ((25068424374999999997 : Rat) / 25000000000000000000), D2 := ((43579921874999999997 : Rat) / 25000000000000000000), D3 := ((46506933749999999997 : Rat) / 25000000000000000000), D4 := ((50416757678571426017 : Rat) / 25000000000000000000), LB := ((23163021129636863 : Rat) / 10000000000000000000) }
]

def block013LeftCertificate : Bool :=
  allBoxesValid block013LeftBoxes &&
  coversFromBool block013LeftBoxes block013LeftL block013LeftR

theorem block013LeftCertificate_eq_true :
    block013LeftCertificate = true := by
  native_decide

def block013RightChunk000 : List RatBox := [
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((45368453125000000003 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((68424374999999997 : Rat) / 25000000000000000000), D2 := ((18579921874999999997 : Rat) / 25000000000000000000), D3 := ((21506933749999999997 : Rat) / 25000000000000000000), D4 := ((25416757678571426017 : Rat) / 25000000000000000000), LB := ((9988819932866761 : Rat) / 200000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((1267416665178571301 : Rat) / 1250000000000000000), LB := ((1667046189256829 : Rat) / 1000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((341841790178571301 : Rat) / 1250000000000000000), LB := ((1361924348491471 : Rat) / 2000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((274497454553571428577 : Rat) / 100000000000000000000), D0 := ((274497454553571428577 : Rat) / 100000000000000000000), D1 := ((92749944553571428577 : Rat) / 100000000000000000000), D2 := ((18703954553571428577 : Rat) / 100000000000000000000), D3 := ((6995907053571428577 : Rat) / 100000000000000000000), D4 := ((195491196428571301 : Rat) / 1250000000000000000), LB := ((5814936503619317 : Rat) / 50000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((274497454553571428577 : Rat) / 100000000000000000000), R := ((220997145053571428577 : Rat) / 80000000000000000000), D0 := ((220997145053571428577 : Rat) / 80000000000000000000), D1 := ((75599137053571428577 : Rat) / 80000000000000000000), D2 := ((16362345053571428577 : Rat) / 80000000000000000000), D3 := ((6995907053571428577 : Rat) / 80000000000000000000), D4 := ((8643388660714275503 : Rat) / 100000000000000000000), LB := ((2466896982015529 : Rat) / 25000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((220997145053571428577 : Rat) / 80000000000000000000), R := ((2216967357589285714347 : Rat) / 800000000000000000000), D0 := ((2216967357589285714347 : Rat) / 800000000000000000000), D1 := ((762987277589285714347 : Rat) / 800000000000000000000), D2 := ((170619357589285714347 : Rat) / 800000000000000000000), D3 := ((76954977589285714347 : Rat) / 800000000000000000000), D4 := ((5515529517857134687 : Rat) / 80000000000000000000), LB := ((7307467460337869 : Rat) / 100000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2216967357589285714347 : Rat) / 800000000000000000000), R := ((555990816160714285731 : Rat) / 200000000000000000000), D0 := ((555990816160714285731 : Rat) / 200000000000000000000), D1 := ((192495796160714285731 : Rat) / 200000000000000000000), D2 := ((44403816160714285731 : Rat) / 200000000000000000000), D3 := ((20987721160714285731 : Rat) / 200000000000000000000), D4 := ((48159388124999918293 : Rat) / 800000000000000000000), LB := ((2518524424736901 : Rat) / 100000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((555990816160714285731 : Rat) / 200000000000000000000), R := ((178196897453571428577 : Rat) / 64000000000000000000), D0 := ((178196897453571428577 : Rat) / 64000000000000000000), D1 := ((61878491053571428577 : Rat) / 64000000000000000000), D2 := ((14489057453571428577 : Rat) / 64000000000000000000), D3 := ((6995907053571428577 : Rat) / 64000000000000000000), D4 := ((10290870267857122429 : Rat) / 200000000000000000000), LB := ((1210560274876099 : Rat) / 50000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((178196897453571428577 : Rat) / 64000000000000000000), R := ((2230959171696428571501 : Rat) / 800000000000000000000), D0 := ((2230959171696428571501 : Rat) / 800000000000000000000), D1 := ((776979091696428571501 : Rat) / 800000000000000000000), D2 := ((184611171696428571501 : Rat) / 800000000000000000000), D3 := ((90946791696428571501 : Rat) / 800000000000000000000), D4 := ((15066211017857110171 : Rat) / 320000000000000000000), LB := ((6063648209451711 : Rat) / 1000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2230959171696428571501 : Rat) / 800000000000000000000), R := ((8930832593839285714581 : Rat) / 3200000000000000000000), D0 := ((8930832593839285714581 : Rat) / 3200000000000000000000), D1 := ((3114912273839285714581 : Rat) / 3200000000000000000000), D2 := ((745440593839285714581 : Rat) / 3200000000000000000000), D3 := ((370783073839285714581 : Rat) / 3200000000000000000000), D4 := ((34167574017857061139 : Rat) / 800000000000000000000), LB := ((5283828802793211 : Rat) / 500000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8930832593839285714581 : Rat) / 3200000000000000000000), R := ((4468914250446428571579 : Rat) / 1600000000000000000000), D0 := ((4468914250446428571579 : Rat) / 1600000000000000000000), D1 := ((1560954090446428571579 : Rat) / 1600000000000000000000), D2 := ((376218250446428571579 : Rat) / 1600000000000000000000), D3 := ((188889490446428571579 : Rat) / 1600000000000000000000), D4 := ((129674389017856815979 : Rat) / 3200000000000000000000), LB := ((4597845691343 : Rat) / 1250000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4468914250446428571579 : Rat) / 1600000000000000000000), R := ((17882652908839285714893 : Rat) / 6400000000000000000000), D0 := ((17882652908839285714893 : Rat) / 6400000000000000000000), D1 := ((6250812268839285714893 : Rat) / 6400000000000000000000), D2 := ((1511868908839285714893 : Rat) / 6400000000000000000000), D3 := ((762553868839285714893 : Rat) / 6400000000000000000000), D4 := ((61339240982142693701 : Rat) / 1600000000000000000000), LB := ((7681458749785541 : Rat) / 1000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17882652908839285714893 : Rat) / 6400000000000000000000), R := ((1788964881589285714347 : Rat) / 640000000000000000000), D0 := ((1788964881589285714347 : Rat) / 640000000000000000000), D1 := ((625780817589285714347 : Rat) / 640000000000000000000), D2 := ((151886481589285714347 : Rat) / 640000000000000000000), D3 := ((76954977589285714347 : Rat) / 640000000000000000000), D4 := ((238361056874999346227 : Rat) / 6400000000000000000000), LB := ((4940421994680699 : Rat) / 1000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1788964881589285714347 : Rat) / 640000000000000000000), R := ((17896644722946428572047 : Rat) / 6400000000000000000000), D0 := ((17896644722946428572047 : Rat) / 6400000000000000000000), D1 := ((6264804082946428572047 : Rat) / 6400000000000000000000), D2 := ((1525860722946428572047 : Rat) / 6400000000000000000000), D3 := ((776545682946428572047 : Rat) / 6400000000000000000000), D4 := ((4627302996428558353 : Rat) / 128000000000000000000), LB := ((303726553378153 : Rat) / 125000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17896644722946428572047 : Rat) / 6400000000000000000000), R := ((1118977539375000000039 : Rat) / 400000000000000000000), D0 := ((1118977539375000000039 : Rat) / 400000000000000000000), D1 := ((391987499375000000039 : Rat) / 400000000000000000000), D2 := ((95803539375000000039 : Rat) / 400000000000000000000), D3 := ((48971349375000000039 : Rat) / 400000000000000000000), D4 := ((224369242767856489073 : Rat) / 6400000000000000000000), LB := ((8154093464735057 : Rat) / 50000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1118977539375000000039 : Rat) / 400000000000000000000), R := ((1432571086682142857193 : Rat) / 512000000000000000000), D0 := ((1432571086682142857193 : Rat) / 512000000000000000000), D1 := ((502023835482142857193 : Rat) / 512000000000000000000), D2 := ((122908366682142857193 : Rat) / 512000000000000000000), D3 := ((62963163482142857193 : Rat) / 512000000000000000000), D4 := ((13585833482142816281 : Rat) / 400000000000000000000), LB := ((15951101050224459 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1432571086682142857193 : Rat) / 512000000000000000000), R := ((17910636537053571429201 : Rat) / 6400000000000000000000), D0 := ((17910636537053571429201 : Rat) / 6400000000000000000000), D1 := ((6278795897053571429201 : Rat) / 6400000000000000000000), D2 := ((1539852537053571429201 : Rat) / 6400000000000000000000), D3 := ((790537497053571429201 : Rat) / 6400000000000000000000), D4 := ((85550152874999738483 : Rat) / 2560000000000000000000), LB := ((11427007809696743 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17910636537053571429201 : Rat) / 6400000000000000000000), R := ((35828268981160714286979 : Rat) / 12800000000000000000000), D0 := ((35828268981160714286979 : Rat) / 12800000000000000000000), D1 := ((12564587701160714286979 : Rat) / 12800000000000000000000), D2 := ((3086700981160714286979 : Rat) / 12800000000000000000000), D3 := ((1588070901160714286979 : Rat) / 12800000000000000000000), D4 := ((210377428660713631919 : Rat) / 6400000000000000000000), LB := ((14514304386170629 : Rat) / 10000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35828268981160714286979 : Rat) / 12800000000000000000000), R := ((8958816222053571428889 : Rat) / 3200000000000000000000), D0 := ((8958816222053571428889 : Rat) / 3200000000000000000000), D1 := ((3142895902053571428889 : Rat) / 3200000000000000000000), D2 := ((773424222053571428889 : Rat) / 3200000000000000000000), D3 := ((398766702053571428889 : Rat) / 3200000000000000000000), D4 := ((413758950267855835261 : Rat) / 12800000000000000000000), LB := ((863235037806831 : Rat) / 1250000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8958816222053571428889 : Rat) / 3200000000000000000000), R := ((35842260795267857144133 : Rat) / 12800000000000000000000), D0 := ((35842260795267857144133 : Rat) / 12800000000000000000000), D1 := ((12578579515267857144133 : Rat) / 12800000000000000000000), D2 := ((3100692795267857144133 : Rat) / 12800000000000000000000), D3 := ((1602062715267857144133 : Rat) / 12800000000000000000000), D4 := ((101690760803571101671 : Rat) / 3200000000000000000000), LB := ((26361978820999 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35842260795267857144133 : Rat) / 12800000000000000000000), R := ((71691517497589285716843 : Rat) / 25600000000000000000000), D0 := ((71691517497589285716843 : Rat) / 25600000000000000000000), D1 := ((25164154937589285716843 : Rat) / 25600000000000000000000), D2 := ((6208381497589285716843 : Rat) / 25600000000000000000000), D3 := ((3211121337589285716843 : Rat) / 25600000000000000000000), D4 := ((399767136160712978107 : Rat) / 12800000000000000000000), LB := ((4774590576165083 : Rat) / 2500000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71691517497589285716843 : Rat) / 25600000000000000000000), R := ((3584925670232142857271 : Rat) / 1280000000000000000000), D0 := ((3584925670232142857271 : Rat) / 1280000000000000000000), D1 := ((1258557542232142857271 : Rat) / 1280000000000000000000), D2 := ((310768870232142857271 : Rat) / 1280000000000000000000), D3 := ((160905862232142857271 : Rat) / 1280000000000000000000), D4 := ((792538365267854527637 : Rat) / 25600000000000000000000), LB := ((2044520436725733 : Rat) / 1250000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3584925670232142857271 : Rat) / 1280000000000000000000), R := ((71705509311696428573997 : Rat) / 25600000000000000000000), D0 := ((71705509311696428573997 : Rat) / 25600000000000000000000), D1 := ((25178146751696428573997 : Rat) / 25600000000000000000000), D2 := ((6222373311696428573997 : Rat) / 25600000000000000000000), D3 := ((3225113151696428573997 : Rat) / 25600000000000000000000), D4 := ((39277122910714154953 : Rat) / 1280000000000000000000), LB := ((6909582900772593 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71705509311696428573997 : Rat) / 25600000000000000000000), R := ((35856252609375000001287 : Rat) / 12800000000000000000000), D0 := ((35856252609375000001287 : Rat) / 12800000000000000000000), D1 := ((12592571329375000001287 : Rat) / 12800000000000000000000), D2 := ((3114684609375000001287 : Rat) / 12800000000000000000000), D3 := ((1616054529375000001287 : Rat) / 12800000000000000000000), D4 := ((778546551160711670483 : Rat) / 25600000000000000000000), LB := ((5745457564438339 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35856252609375000001287 : Rat) / 12800000000000000000000), R := ((71719501125803571431151 : Rat) / 25600000000000000000000), D0 := ((71719501125803571431151 : Rat) / 25600000000000000000000), D1 := ((25192138565803571431151 : Rat) / 25600000000000000000000), D2 := ((6236365125803571431151 : Rat) / 25600000000000000000000), D3 := ((3239104965803571431151 : Rat) / 25600000000000000000000), D4 := ((385775322053570120953 : Rat) / 12800000000000000000000), LB := ((9375053503094533 : Rat) / 10000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71719501125803571431151 : Rat) / 25600000000000000000000), R := ((4482906064553571428733 : Rat) / 1600000000000000000000), D0 := ((4482906064553571428733 : Rat) / 1600000000000000000000), D1 := ((1574945904553571428733 : Rat) / 1600000000000000000000), D2 := ((390210064553571428733 : Rat) / 1600000000000000000000), D3 := ((202881304553571428733 : Rat) / 1600000000000000000000), D4 := ((764554737053568813329 : Rat) / 25600000000000000000000), LB := ((7475322580057231 : Rat) / 10000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4482906064553571428733 : Rat) / 1600000000000000000000), R := ((14346698587982142857661 : Rat) / 5120000000000000000000), D0 := ((14346698587982142857661 : Rat) / 5120000000000000000000), D1 := ((5041226075982142857661 : Rat) / 5120000000000000000000), D2 := ((1250071387982142857661 : Rat) / 5120000000000000000000), D3 := ((650619355982142857661 : Rat) / 5120000000000000000000), D4 := ((47347426874999836547 : Rat) / 1600000000000000000000), LB := ((5795567307186333 : Rat) / 10000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((14346698587982142857661 : Rat) / 5120000000000000000000), R := ((35870244423482142858441 : Rat) / 12800000000000000000000), D0 := ((35870244423482142858441 : Rat) / 12800000000000000000000), D1 := ((12606563143482142858441 : Rat) / 12800000000000000000000), D2 := ((3128676423482142858441 : Rat) / 12800000000000000000000), D3 := ((1630046343482142858441 : Rat) / 12800000000000000000000), D4 := ((30022516917857038247 : Rat) / 1024000000000000000000), LB := ((4339739756508143 : Rat) / 10000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35870244423482142858441 : Rat) / 12800000000000000000000), R := ((71747484754017857145459 : Rat) / 25600000000000000000000), D0 := ((71747484754017857145459 : Rat) / 25600000000000000000000), D1 := ((25220122194017857145459 : Rat) / 25600000000000000000000), D2 := ((6264348754017857145459 : Rat) / 25600000000000000000000), D3 := ((3267088594017857145459 : Rat) / 25600000000000000000000), D4 := ((371783507946427263799 : Rat) / 12800000000000000000000), LB := ((1555951568489311 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71747484754017857145459 : Rat) / 25600000000000000000000), R := ((17938620165267857143509 : Rat) / 6400000000000000000000), D0 := ((17938620165267857143509 : Rat) / 6400000000000000000000), D1 := ((6306779525267857143509 : Rat) / 6400000000000000000000), D2 := ((1567836165267857143509 : Rat) / 6400000000000000000000), D3 := ((818521125267857143509 : Rat) / 6400000000000000000000), D4 := ((736571108839283099021 : Rat) / 25600000000000000000000), LB := ((10581179982682709 : Rat) / 50000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17938620165267857143509 : Rat) / 6400000000000000000000), R := ((71761476568125000002613 : Rat) / 25600000000000000000000), D0 := ((71761476568125000002613 : Rat) / 25600000000000000000000), D1 := ((25234114008125000002613 : Rat) / 25600000000000000000000), D2 := ((6278340568125000002613 : Rat) / 25600000000000000000000), D3 := ((3281080408125000002613 : Rat) / 25600000000000000000000), D4 := ((182393800446427917611 : Rat) / 6400000000000000000000), LB := ((3392591561290903 : Rat) / 25000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71761476568125000002613 : Rat) / 25600000000000000000000), R := ((7176847247517857143119 : Rat) / 2560000000000000000000), D0 := ((7176847247517857143119 : Rat) / 2560000000000000000000), D1 := ((2524110991517857143119 : Rat) / 2560000000000000000000), D2 := ((628533647517857143119 : Rat) / 2560000000000000000000), D3 := ((328807631517857143119 : Rat) / 2560000000000000000000), D4 := ((722579294732140241867 : Rat) / 25600000000000000000000), LB := ((419363833043529 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((7176847247517857143119 : Rat) / 2560000000000000000000), R := ((71775468382232142859767 : Rat) / 25600000000000000000000), D0 := ((71775468382232142859767 : Rat) / 25600000000000000000000), D1 := ((25248105822232142859767 : Rat) / 25600000000000000000000), D2 := ((6292332382232142859767 : Rat) / 25600000000000000000000), D3 := ((3295072222232142859767 : Rat) / 25600000000000000000000), D4 := ((71558338767856881329 : Rat) / 2560000000000000000000), LB := ((2829304805807009 : Rat) / 50000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71775468382232142859767 : Rat) / 25600000000000000000000), R := ((8972808036160714286043 : Rat) / 3200000000000000000000), D0 := ((8972808036160714286043 : Rat) / 3200000000000000000000), D1 := ((3156887716160714286043 : Rat) / 3200000000000000000000), D2 := ((787416036160714286043 : Rat) / 3200000000000000000000), D3 := ((412758516160714286043 : Rat) / 3200000000000000000000), D4 := ((708587480624997384713 : Rat) / 25600000000000000000000), LB := ((5431226208030271 : Rat) / 100000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8972808036160714286043 : Rat) / 3200000000000000000000), R := ((71789460196339285716921 : Rat) / 25600000000000000000000), D0 := ((71789460196339285716921 : Rat) / 25600000000000000000000), D1 := ((25262097636339285716921 : Rat) / 25600000000000000000000), D2 := ((6306324196339285716921 : Rat) / 25600000000000000000000), D3 := ((3309064036339285716921 : Rat) / 25600000000000000000000), D4 := ((87698946696428244517 : Rat) / 3200000000000000000000), LB := ((7753383554209847 : Rat) / 100000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71789460196339285716921 : Rat) / 25600000000000000000000), R := ((35898228051696428572749 : Rat) / 12800000000000000000000), D0 := ((35898228051696428572749 : Rat) / 12800000000000000000000), D1 := ((12634546771696428572749 : Rat) / 12800000000000000000000), D2 := ((3156660051696428572749 : Rat) / 12800000000000000000000), D3 := ((1658029971696428572749 : Rat) / 12800000000000000000000), D4 := ((694595666517854527559 : Rat) / 25600000000000000000000), LB := ((6337395348759989 : Rat) / 50000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35898228051696428572749 : Rat) / 12800000000000000000000), R := ((2872138080417857142963 : Rat) / 1024000000000000000000), D0 := ((2872138080417857142963 : Rat) / 1024000000000000000000), D1 := ((1011043578017857142963 : Rat) / 1024000000000000000000), D2 := ((252812640417857142963 : Rat) / 1024000000000000000000), D3 := ((132922234017857142963 : Rat) / 1024000000000000000000), D4 := ((343799879732141549491 : Rat) / 12800000000000000000000), LB := ((20246667408896357 : Rat) / 100000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2872138080417857142963 : Rat) / 1024000000000000000000), R := ((17952611979375000000663 : Rat) / 6400000000000000000000), D0 := ((17952611979375000000663 : Rat) / 6400000000000000000000), D1 := ((6320771339375000000663 : Rat) / 6400000000000000000000), D2 := ((1581827979375000000663 : Rat) / 6400000000000000000000), D3 := ((832512939375000000663 : Rat) / 6400000000000000000000), D4 := ((136120770482142334081 : Rat) / 5120000000000000000000), LB := ((6104361193348673 : Rat) / 20000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17952611979375000000663 : Rat) / 6400000000000000000000), R := ((71817443824553571431229 : Rat) / 25600000000000000000000), D0 := ((71817443824553571431229 : Rat) / 25600000000000000000000), D1 := ((25290081264553571431229 : Rat) / 25600000000000000000000), D2 := ((6334307824553571431229 : Rat) / 25600000000000000000000), D3 := ((3337047664553571431229 : Rat) / 25600000000000000000000), D4 := ((168401986339285060457 : Rat) / 6400000000000000000000), LB := ((10888659032368131 : Rat) / 25000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71817443824553571431229 : Rat) / 25600000000000000000000), R := ((35912219865803571429903 : Rat) / 12800000000000000000000), D0 := ((35912219865803571429903 : Rat) / 12800000000000000000000), D1 := ((12648538585803571429903 : Rat) / 12800000000000000000000), D2 := ((3170651865803571429903 : Rat) / 12800000000000000000000), D3 := ((1672021785803571429903 : Rat) / 12800000000000000000000), D4 := ((666612038303568813251 : Rat) / 25600000000000000000000), LB := ((742516168714541 : Rat) / 1250000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35912219865803571429903 : Rat) / 12800000000000000000000), R := ((71831435638660714288383 : Rat) / 25600000000000000000000), D0 := ((71831435638660714288383 : Rat) / 25600000000000000000000), D1 := ((25304073078660714288383 : Rat) / 25600000000000000000000), D2 := ((6348299638660714288383 : Rat) / 25600000000000000000000), D3 := ((3351039478660714288383 : Rat) / 25600000000000000000000), D4 := ((329808065624998692337 : Rat) / 12800000000000000000000), LB := ((7811969147553111 : Rat) / 10000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71831435638660714288383 : Rat) / 25600000000000000000000), R := ((448990197160714285731 : Rat) / 160000000000000000000), D0 := ((448990197160714285731 : Rat) / 160000000000000000000), D1 := ((158194181160714285731 : Rat) / 160000000000000000000), D2 := ((39720597160714285731 : Rat) / 160000000000000000000), D3 := ((20987721160714285731 : Rat) / 160000000000000000000), D4 := ((652620224196425956097 : Rat) / 25600000000000000000000), LB := ((1247119963413007 : Rat) / 1250000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((448990197160714285731 : Rat) / 160000000000000000000), R := ((71845427452767857145537 : Rat) / 25600000000000000000000), D0 := ((71845427452767857145537 : Rat) / 25600000000000000000000), D1 := ((25318064892767857145537 : Rat) / 25600000000000000000000), D2 := ((6362291452767857145537 : Rat) / 25600000000000000000000), D3 := ((3365031292767857145537 : Rat) / 25600000000000000000000), D4 := ((4035151982142840797 : Rat) / 160000000000000000000), LB := ((12441271077469063 : Rat) / 10000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71845427452767857145537 : Rat) / 25600000000000000000000), R := ((35926211679910714287057 : Rat) / 12800000000000000000000), D0 := ((35926211679910714287057 : Rat) / 12800000000000000000000), D1 := ((12662530399910714287057 : Rat) / 12800000000000000000000), D2 := ((3184643679910714287057 : Rat) / 12800000000000000000000), D3 := ((1686013599910714287057 : Rat) / 12800000000000000000000), D4 := ((638628410089283098943 : Rat) / 25600000000000000000000), LB := ((15211275076455477 : Rat) / 10000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35926211679910714287057 : Rat) / 12800000000000000000000), R := ((71859419266875000002691 : Rat) / 25600000000000000000000), D0 := ((71859419266875000002691 : Rat) / 25600000000000000000000), D1 := ((25332056706875000002691 : Rat) / 25600000000000000000000), D2 := ((6376283266875000002691 : Rat) / 25600000000000000000000), D3 := ((3379023106875000002691 : Rat) / 25600000000000000000000), D4 := ((315816251517855835183 : Rat) / 12800000000000000000000), LB := ((1829355417773959 : Rat) / 1000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((71859419266875000002691 : Rat) / 25600000000000000000000), R := ((17966603793482142857817 : Rat) / 6400000000000000000000), D0 := ((17966603793482142857817 : Rat) / 6400000000000000000000), D1 := ((6334763153482142857817 : Rat) / 6400000000000000000000), D2 := ((1595819793482142857817 : Rat) / 6400000000000000000000), D3 := ((846504753482142857817 : Rat) / 6400000000000000000000), D4 := ((624636595982140241789 : Rat) / 25600000000000000000000), LB := ((5423727722205507 : Rat) / 2500000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17966603793482142857817 : Rat) / 6400000000000000000000), R := ((35940203494017857144211 : Rat) / 12800000000000000000000), D0 := ((35940203494017857144211 : Rat) / 12800000000000000000000), D1 := ((12676522214017857144211 : Rat) / 12800000000000000000000), D2 := ((3198635494017857144211 : Rat) / 12800000000000000000000), D3 := ((1700005414017857144211 : Rat) / 12800000000000000000000), D4 := ((154410172232142203303 : Rat) / 6400000000000000000000), LB := ((11994575699197929 : Rat) / 250000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35940203494017857144211 : Rat) / 12800000000000000000000), R := ((8986799850267857143197 : Rat) / 3200000000000000000000), D0 := ((8986799850267857143197 : Rat) / 3200000000000000000000), D1 := ((3170879530267857143197 : Rat) / 3200000000000000000000), D2 := ((801407850267857143197 : Rat) / 3200000000000000000000), D3 := ((426750330267857143197 : Rat) / 3200000000000000000000), D4 := ((301824437410712978029 : Rat) / 12800000000000000000000), LB := ((4477900875468621 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8986799850267857143197 : Rat) / 3200000000000000000000), R := ((7190839061625000000273 : Rat) / 2560000000000000000000), D0 := ((7190839061625000000273 : Rat) / 2560000000000000000000), D1 := ((2538102805625000000273 : Rat) / 2560000000000000000000), D2 := ((642525461625000000273 : Rat) / 2560000000000000000000), D3 := ((342799445625000000273 : Rat) / 2560000000000000000000), D4 := ((73707132589285387363 : Rat) / 3200000000000000000000), LB := ((470671514039539 : Rat) / 250000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((7190839061625000000273 : Rat) / 2560000000000000000000), R := ((17980595607589285714971 : Rat) / 6400000000000000000000), D0 := ((17980595607589285714971 : Rat) / 6400000000000000000000), D1 := ((6348754967589285714971 : Rat) / 6400000000000000000000), D2 := ((1609811607589285714971 : Rat) / 6400000000000000000000), D3 := ((860496567589285714971 : Rat) / 6400000000000000000000), D4 := ((2302660986428560967 : Rat) / 102400000000000000000), LB := ((3015864655551481 : Rat) / 1000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17980595607589285714971 : Rat) / 6400000000000000000000), R := ((35968187122232142858519 : Rat) / 12800000000000000000000), D0 := ((35968187122232142858519 : Rat) / 12800000000000000000000), D1 := ((12704505842232142858519 : Rat) / 12800000000000000000000), D2 := ((3226619122232142858519 : Rat) / 12800000000000000000000), D3 := ((1727989042232142858519 : Rat) / 12800000000000000000000), D4 := ((140418358124999346149 : Rat) / 6400000000000000000000), LB := ((1075542408359359 : Rat) / 250000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35968187122232142858519 : Rat) / 12800000000000000000000), R := ((4496897878660714285887 : Rat) / 1600000000000000000000), D0 := ((4496897878660714285887 : Rat) / 1600000000000000000000), D1 := ((1588937718660714285887 : Rat) / 1600000000000000000000), D2 := ((404201878660714285887 : Rat) / 1600000000000000000000), D3 := ((216873118660714285887 : Rat) / 1600000000000000000000), D4 := ((273840809196427263721 : Rat) / 12800000000000000000000), LB := ((11498376910273 : Rat) / 2000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4496897878660714285887 : Rat) / 1600000000000000000000), R := ((143956699373571428577 : Rat) / 51200000000000000000), D0 := ((143956699373571428577 : Rat) / 51200000000000000000), D1 := ((50901974253571428577 : Rat) / 51200000000000000000), D2 := ((12990427373571428577 : Rat) / 51200000000000000000), D3 := ((6995907053571428577 : Rat) / 51200000000000000000), D4 := ((33355612767856979393 : Rat) / 1600000000000000000000), LB := ((11973140625510803 : Rat) / 5000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((143956699373571428577 : Rat) / 51200000000000000000), R := ((9000791664375000000351 : Rat) / 3200000000000000000000), D0 := ((9000791664375000000351 : Rat) / 3200000000000000000000), D1 := ((3184871344375000000351 : Rat) / 3200000000000000000000), D2 := ((815399664375000000351 : Rat) / 3200000000000000000000), D3 := ((440742144375000000351 : Rat) / 3200000000000000000000), D4 := ((25285308803571297799 : Rat) / 1280000000000000000000), LB := ((6174472961947841 : Rat) / 1000000000000000000) },
  { w1 := ((4342612687605687 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((12730352082081897 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((9000791664375000000351 : Rat) / 3200000000000000000000), R := ((140746680803571428577 : Rat) / 50000000000000000000), D0 := ((140746680803571428577 : Rat) / 50000000000000000000), D1 := ((49872925803571428577 : Rat) / 50000000000000000000), D2 := ((12849930803571428577 : Rat) / 50000000000000000000), D3 := ((6995907053571428577 : Rat) / 50000000000000000000), D4 := ((59715318482142530209 : Rat) / 3200000000000000000000), LB := ((260613836417789 : Rat) / 312500000000000000) }
]

def block013RightChunk000L : Rat := ((45368453125000000003 : Rat) / 25000000000000000000)
def block013RightChunk000R : Rat := ((140746680803571428577 : Rat) / 50000000000000000000)

def block013RightChunk000Certificate : Bool :=
  allBoxesValid block013RightChunk000 &&
  coversFromBool block013RightChunk000 block013RightChunk000L block013RightChunk000R

theorem block013RightChunk000Certificate_eq_true :
    block013RightChunk000Certificate = true := by
  native_decide

def block013RightChainCertificate : Bool :=
  decide (
    block013RightL = ((45368453125000000003 : Rat) / 25000000000000000000) /\
    ((140746680803571428577 : Rat) / 50000000000000000000) = block013RightR)

theorem block013RightChainCertificate_eq_true :
    block013RightChainCertificate = true := by
  native_decide

def block013LeftBoxCount : Nat := boxCount block013LeftBoxes
def block013RightBoxCount : Nat := 55

def block013_rational_certificate : Prop :=
    block013LeftCertificate = true /\
    block013RightChainCertificate = true /\
    block013RightChunk000Certificate = true

theorem block013_rational_certificate_proof :
    block013_rational_certificate := by
  exact ⟨block013LeftCertificate_eq_true, block013RightChainCertificate_eq_true, block013RightChunk000Certificate_eq_true⟩

end Block013
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block013

open Set

def block013W1 : Rat := ((4342612687605687 : Rat) / 500000000000000)
def block013W2 : Rat := (0 : Rat)
def block013W3 : Rat := (0 : Rat)
def block013W4 : Rat := ((12730352082081897 : Rat) / 50000000000000000)
def block013S1 : Rat := ((18174751 : Rat) / 10000000)
def block013S2 : Rat := ((511587 : Rat) / 200000)
def block013S3 : Rat := ((107000619 : Rat) / 40000000)
def block013S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block013V (y : ℝ) : ℝ :=
  ratPotential block013W1 block013W2 block013W3 block013W4 block013S1 block013S2 block013S3 block013S4 y

def block013LeftParamsCertificate : Bool :=
  allBoxesSameParams block013LeftBoxes block013W1 block013W2 block013W3 block013W4 block013S1 block013S2 block013S3 block013S4

theorem block013LeftParamsCertificate_eq_true :
    block013LeftParamsCertificate = true := by
  native_decide

theorem block013_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block013LeftL : ℝ) (block013LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block013S1 : ℝ))
    (hy2ne : y ≠ (block013S2 : ℝ))
    (hy3ne : y ≠ (block013S3 : ℝ))
    (hy4ne : y ≠ (block013S4 : ℝ)) :
    0 < block013V y := by
  have hcert := block013LeftCertificate_eq_true
  unfold block013LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block013LeftBoxes) (lo := block013LeftL) (hi := block013LeftR)
    (w1 := block013W1) (w2 := block013W2) (w3 := block013W3) (w4 := block013W4)
    (s1 := block013S1) (s2 := block013S2) (s3 := block013S3) (s4 := block013S4)
    hboxes hcover block013LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block013RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block013RightChunk000 block013W1 block013W2 block013W3 block013W4 block013S1 block013S2 block013S3 block013S4

theorem block013RightChunk000ParamsCertificate_eq_true :
    block013RightChunk000ParamsCertificate = true := by
  native_decide

theorem block013_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block013RightChunk000L : ℝ) (block013RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block013S1 : ℝ))
    (hy2ne : y ≠ (block013S2 : ℝ))
    (hy3ne : y ≠ (block013S3 : ℝ))
    (hy4ne : y ≠ (block013S4 : ℝ)) :
    0 < block013V y := by
  have hcert := block013RightChunk000Certificate_eq_true
  unfold block013RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block013RightChunk000) (lo := block013RightChunk000L) (hi := block013RightChunk000R)
    (w1 := block013W1) (w2 := block013W2) (w3 := block013W3) (w4 := block013W4)
    (s1 := block013S1) (s2 := block013S2) (s3 := block013S3) (s4 := block013S4)
    hboxes hcover block013RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block013_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block013RightL : ℝ) (block013RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block013S1 : ℝ))
    (hy2ne : y ≠ (block013S2 : ℝ))
    (hy3ne : y ≠ (block013S3 : ℝ))
    (hy4ne : y ≠ (block013S4 : ℝ)) :
    0 < block013V y := by
  have hL : (block013RightChunk000L : ℝ) = (block013RightL : ℝ) := by
    norm_num [block013RightChunk000L, block013RightL]
  have hR : (block013RightChunk000R : ℝ) = (block013RightR : ℝ) := by
    norm_num [block013RightChunk000R, block013RightR]
  have hyc : y ∈ Icc (block013RightChunk000L : ℝ) (block013RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block013_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block013_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block013LeftL : ℝ) (block013LeftR : ℝ) →
    y ≠ 0 → y ≠ (block013S1 : ℝ) → y ≠ (block013S2 : ℝ) →
    y ≠ (block013S3 : ℝ) → y ≠ (block013S4 : ℝ) → 0 < block013V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block013RightL : ℝ) (block013RightR : ℝ) →
    y ≠ 0 → y ≠ (block013S1 : ℝ) → y ≠ (block013S2 : ℝ) →
    y ≠ (block013S3 : ℝ) → y ≠ (block013S4 : ℝ) → 0 < block013V y)

theorem block013_reallog_certificate_proof :
    block013_reallog_certificate := by
  exact ⟨block013_left_V_pos, block013_right_V_pos⟩

end Block013
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block013.block013V
#check Erdos1038Lean.M1817475.Block013.block013_left_V_pos
#check Erdos1038Lean.M1817475.Block013.block013_right_V_pos
#check Erdos1038Lean.M1817475.Block013.block013_reallog_certificate_proof
