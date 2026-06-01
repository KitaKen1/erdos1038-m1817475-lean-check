/-
Self-contained Lean4Web paste file.
Block 23 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block023

def block023LeftL : Rat := ((5079895089285714287 : Rat) / 6250000000000000000)
def block023LeftR : Rat := ((40648935267857142867 : Rat) / 50000000000000000000)
def block023RightL : Rat := ((11329895089285714287 : Rat) / 6250000000000000000)
def block023RightR : Rat := ((140648935267857142867 : Rat) / 50000000000000000000)

def block023LeftBoxes : List RatBox := [
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5079895089285714287 : Rat) / 6250000000000000000), R := ((40648935267857142867 : Rat) / 50000000000000000000), D0 := ((40648935267857142867 : Rat) / 50000000000000000000), D1 := ((6279324285714285713 : Rat) / 6250000000000000000), D2 := ((10907198660714285713 : Rat) / 6250000000000000000), D3 := ((11638951629464285713 : Rat) / 6250000000000000000), D4 := ((385099093889508909 : Rat) / 195312500000000000), LB := ((4033159075116921 : Rat) / 5000000000000000000) }
]

def block023LeftCertificate : Bool :=
  allBoxesValid block023LeftBoxes &&
  coversFromBool block023LeftBoxes block023LeftL block023LeftR

theorem block023LeftCertificate_eq_true :
    block023LeftCertificate = true := by
  native_decide

def block023RightChunk000 : List RatBox := [
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((11329895089285714287 : Rat) / 6250000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((29324285714285713 : Rat) / 6250000000000000000), D2 := ((4657198660714285713 : Rat) / 6250000000000000000), D3 := ((5388951629464285713 : Rat) / 6250000000000000000), D4 := ((189786593889508909 : Rat) / 195312500000000000), LB := ((11602847411012519 : Rat) / 1000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((1493130528640663 : Rat) / 1000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((19492417 : Rat) / 40000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((6261365054433283 : Rat) / 10000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((6043909 : Rat) / 20000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((18245770883098533 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((413952819 : Rat) / 160000000), D0 := ((413952819 : Rat) / 160000000), D1 := ((123156803 : Rat) / 160000000), D2 := ((4683219 : Rat) / 160000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((925798796494659 : Rat) / 12500000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((413952819 : Rat) / 160000000), R := ((209318019 : Rat) / 80000000), D0 := ((209318019 : Rat) / 80000000), D1 := ((63920011 : Rat) / 80000000), D2 := ((4683219 : Rat) / 80000000), D3 := ((14049657 : Rat) / 160000000), D4 := ((1972854562499999 : Rat) / 10000000000000000), LB := ((8770153197376479 : Rat) / 500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209318019 : Rat) / 80000000), R := ((168391059 : Rat) / 64000000), D0 := ((168391059 : Rat) / 64000000), D1 := ((260363263 : Rat) / 320000000), D2 := ((4683219 : Rat) / 64000000), D3 := ((4683219 : Rat) / 80000000), D4 := ((1680153374999999 : Rat) / 10000000000000000), LB := ((8412512120595461 : Rat) / 500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168391059 : Rat) / 64000000), R := ((1688593809 : Rat) / 640000000), D0 := ((1688593809 : Rat) / 640000000), D1 := ((105081949 : Rat) / 128000000), D2 := ((51515409 : Rat) / 640000000), D3 := ((14049657 : Rat) / 320000000), D4 := ((1533802781249999 : Rat) / 10000000000000000), LB := ((4969779134882113 : Rat) / 250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1688593809 : Rat) / 640000000), R := ((423319257 : Rat) / 160000000), D0 := ((423319257 : Rat) / 160000000), D1 := ((132523241 : Rat) / 160000000), D2 := ((14049657 : Rat) / 160000000), D3 := ((4683219 : Rat) / 128000000), D4 := ((1460627484374999 : Rat) / 10000000000000000), LB := ((13688876243311 : Rat) / 1250000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423319257 : Rat) / 160000000), R := ((1697960247 : Rat) / 640000000), D0 := ((1697960247 : Rat) / 640000000), D1 := ((534776183 : Rat) / 640000000), D2 := ((60881847 : Rat) / 640000000), D3 := ((4683219 : Rat) / 160000000), D4 := ((1387452187499999 : Rat) / 10000000000000000), LB := ((1466339798149363 : Rat) / 500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697960247 : Rat) / 640000000), R := ((3400603713 : Rat) / 1280000000), D0 := ((3400603713 : Rat) / 1280000000), D1 := ((214847117 : Rat) / 256000000), D2 := ((126446913 : Rat) / 1280000000), D3 := ((14049657 : Rat) / 640000000), D4 := ((1314276890624999 : Rat) / 10000000000000000), LB := ((7197348863961617 : Rat) / 1000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3400603713 : Rat) / 1280000000), R := ((851321733 : Rat) / 320000000), D0 := ((851321733 : Rat) / 320000000), D1 := ((269729701 : Rat) / 320000000), D2 := ((32782533 : Rat) / 320000000), D3 := ((4683219 : Rat) / 256000000), D4 := ((1277689242187499 : Rat) / 10000000000000000), LB := ((63004024761509 : Rat) / 15625000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((851321733 : Rat) / 320000000), R := ((3409970151 : Rat) / 1280000000), D0 := ((3409970151 : Rat) / 1280000000), D1 := ((1083602023 : Rat) / 1280000000), D2 := ((135813351 : Rat) / 1280000000), D3 := ((4683219 : Rat) / 320000000), D4 := ((1241101593749999 : Rat) / 10000000000000000), LB := ((5741725195377301 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3409970151 : Rat) / 1280000000), R := ((6824623521 : Rat) / 2560000000), D0 := ((6824623521 : Rat) / 2560000000), D1 := ((434377453 : Rat) / 512000000), D2 := ((276309921 : Rat) / 2560000000), D3 := ((14049657 : Rat) / 1280000000), D4 := ((1204513945312499 : Rat) / 10000000000000000), LB := ((4158244346110673 : Rat) / 1000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6824623521 : Rat) / 2560000000), R := ((341465337 : Rat) / 128000000), D0 := ((341465337 : Rat) / 128000000), D1 := ((544142621 : Rat) / 640000000), D2 := ((14049657 : Rat) / 128000000), D3 := ((4683219 : Rat) / 512000000), D4 := ((1186220121093749 : Rat) / 10000000000000000), LB := ((7419987398701311 : Rat) / 2500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((341465337 : Rat) / 128000000), R := ((6833989959 : Rat) / 2560000000), D0 := ((6833989959 : Rat) / 2560000000), D1 := ((2181253703 : Rat) / 2560000000), D2 := ((285676359 : Rat) / 2560000000), D3 := ((4683219 : Rat) / 640000000), D4 := ((1167926296874999 : Rat) / 10000000000000000), LB := ((18572957763217657 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6833989959 : Rat) / 2560000000), R := ((3419336589 : Rat) / 1280000000), D0 := ((3419336589 : Rat) / 1280000000), D1 := ((1092968461 : Rat) / 1280000000), D2 := ((145179789 : Rat) / 1280000000), D3 := ((14049657 : Rat) / 2560000000), D4 := ((1149632472656249 : Rat) / 10000000000000000), LB := ((8282644777899417 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3419336589 : Rat) / 1280000000), R := ((547281183 : Rat) / 204800000), D0 := ((547281183 : Rat) / 204800000), D1 := ((4376557063 : Rat) / 5120000000), D2 := ((4683219 : Rat) / 40960000), D3 := ((4683219 : Rat) / 1280000000), D4 := ((1131338648437499 : Rat) / 10000000000000000), LB := ((3330893984680311 : Rat) / 1250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((547281183 : Rat) / 204800000), R := ((6843356397 : Rat) / 2560000000), D0 := ((6843356397 : Rat) / 2560000000), D1 := ((2190620141 : Rat) / 2560000000), D2 := ((295042797 : Rat) / 2560000000), D3 := ((14049657 : Rat) / 5120000000), D4 := ((280547934082031 : Rat) / 2500000000000000), LB := ((4443209409766391 : Rat) / 2000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6843356397 : Rat) / 2560000000), R := ((13691396013 : Rat) / 5120000000), D0 := ((13691396013 : Rat) / 5120000000), D1 := ((4385923501 : Rat) / 5120000000), D2 := ((594768813 : Rat) / 5120000000), D3 := ((4683219 : Rat) / 2560000000), D4 := ((1113044824218749 : Rat) / 10000000000000000), LB := ((9001782152004423 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13691396013 : Rat) / 5120000000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 5120000000), D4 := ((551948956054687 : Rat) / 5000000000000000), LB := ((3503201476930673 : Rat) / 2500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107000619 : Rat) / 40000000), R := ((3425114558999999999 : Rat) / 1280000000000000000), D0 := ((3425114558999999999 : Rat) / 1280000000000000000), D1 := ((1098746430999999999 : Rat) / 1280000000000000000), D2 := ((150957758999999999 : Rat) / 1280000000000000000), D3 := ((1094750999999999 : Rat) / 1280000000000000000), D4 := ((1094750999999999 : Rat) / 10000000000000000), LB := ((6023857989527759 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3425114558999999999 : Rat) / 1280000000000000000), R := ((1713104654999999999 : Rat) / 640000000000000000), D0 := ((1713104654999999999 : Rat) / 640000000000000000), D1 := ((549920590999999999 : Rat) / 640000000000000000), D2 := ((76026254999999999 : Rat) / 640000000000000000), D3 := ((1094750999999999 : Rat) / 640000000000000000), D4 := ((139033376999999873 : Rat) / 1280000000000000000), LB := ((4365598892983047 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1713104654999999999 : Rat) / 640000000000000000), R := ((3427304060999999997 : Rat) / 1280000000000000000), D0 := ((3427304060999999997 : Rat) / 1280000000000000000), D1 := ((1100935932999999997 : Rat) / 1280000000000000000), D2 := ((153147260999999997 : Rat) / 1280000000000000000), D3 := ((3284252999999997 : Rat) / 1280000000000000000), D4 := ((68969312999999937 : Rat) / 640000000000000000), LB := ((702113073813293 : Rat) / 1250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3427304060999999997 : Rat) / 1280000000000000000), R := ((857099702999999999 : Rat) / 320000000000000000), D0 := ((857099702999999999 : Rat) / 320000000000000000), D1 := ((275507670999999999 : Rat) / 320000000000000000), D2 := ((38560502999999999 : Rat) / 320000000000000000), D3 := ((1094750999999999 : Rat) / 320000000000000000), D4 := ((1094750999999999 : Rat) / 10240000000000000), LB := ((169227323725471 : Rat) / 625000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((857099702999999999 : Rat) / 320000000000000000), R := ((685898712599999999 : Rat) / 256000000000000000), D0 := ((685898712599999999 : Rat) / 256000000000000000), D1 := ((220625086999999999 : Rat) / 256000000000000000), D2 := ((31067352599999999 : Rat) / 256000000000000000), D3 := ((1094750999999999 : Rat) / 256000000000000000), D4 := ((33937280999999969 : Rat) / 320000000000000000), LB := ((6265063057231401 : Rat) / 10000000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((685898712599999999 : Rat) / 256000000000000000), R := ((6860081876999999989 : Rat) / 2560000000000000000), D0 := ((6860081876999999989 : Rat) / 2560000000000000000), D1 := ((2207345620999999989 : Rat) / 2560000000000000000), D2 := ((311768276999999989 : Rat) / 2560000000000000000), D3 := ((12042260999999989 : Rat) / 2560000000000000000), D4 := ((134654372999999877 : Rat) / 1280000000000000000), LB := ((1042067827388471 : Rat) / 1000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6860081876999999989 : Rat) / 2560000000000000000), R := ((1715294156999999997 : Rat) / 640000000000000000), D0 := ((1715294156999999997 : Rat) / 640000000000000000), D1 := ((552110092999999997 : Rat) / 640000000000000000), D2 := ((78215756999999997 : Rat) / 640000000000000000), D3 := ((3284252999999997 : Rat) / 640000000000000000), D4 := ((53642798999999951 : Rat) / 512000000000000000), LB := ((4624776511261697 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1715294156999999997 : Rat) / 640000000000000000), R := ((6862271378999999987 : Rat) / 2560000000000000000), D0 := ((6862271378999999987 : Rat) / 2560000000000000000), D1 := ((2209535122999999987 : Rat) / 2560000000000000000), D2 := ((313957778999999987 : Rat) / 2560000000000000000), D3 := ((14231762999999987 : Rat) / 2560000000000000000), D4 := ((66779810999999939 : Rat) / 640000000000000000), LB := ((1626455667246507 : Rat) / 2000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6862271378999999987 : Rat) / 2560000000000000000), R := ((3431683064999999993 : Rat) / 1280000000000000000), D0 := ((3431683064999999993 : Rat) / 1280000000000000000), D1 := ((1105314936999999993 : Rat) / 1280000000000000000), D2 := ((157526264999999993 : Rat) / 1280000000000000000), D3 := ((7663256999999993 : Rat) / 1280000000000000000), D4 := ((266024492999999757 : Rat) / 2560000000000000000), LB := ((7069242761448269 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3431683064999999993 : Rat) / 1280000000000000000), R := ((1372892176199999997 : Rat) / 512000000000000000), D0 := ((1372892176199999997 : Rat) / 512000000000000000), D1 := ((442344924999999997 : Rat) / 512000000000000000), D2 := ((63229456199999997 : Rat) / 512000000000000000), D3 := ((3284252999999997 : Rat) / 512000000000000000), D4 := ((132464870999999879 : Rat) / 1280000000000000000), LB := ((6060839729319367 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1372892176199999997 : Rat) / 512000000000000000), R := ((429097226999999999 : Rat) / 160000000000000000), D0 := ((429097226999999999 : Rat) / 160000000000000000), D1 := ((138301210999999999 : Rat) / 160000000000000000), D2 := ((19827626999999999 : Rat) / 160000000000000000), D3 := ((1094750999999999 : Rat) / 160000000000000000), D4 := ((263834990999999759 : Rat) / 2560000000000000000), LB := ((1021493527310291 : Rat) / 2000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((429097226999999999 : Rat) / 160000000000000000), R := ((6866650382999999983 : Rat) / 2560000000000000000), D0 := ((6866650382999999983 : Rat) / 2560000000000000000), D1 := ((2213914126999999983 : Rat) / 2560000000000000000), D2 := ((318336782999999983 : Rat) / 2560000000000000000), D3 := ((18610766999999983 : Rat) / 2560000000000000000), D4 := ((3284252999999997 : Rat) / 32000000000000000), LB := ((42095299277877807 : Rat) / 100000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6866650382999999983 : Rat) / 2560000000000000000), R := ((3433872566999999991 : Rat) / 1280000000000000000), D0 := ((3433872566999999991 : Rat) / 1280000000000000000), D1 := ((1107504438999999991 : Rat) / 1280000000000000000), D2 := ((159715766999999991 : Rat) / 1280000000000000000), D3 := ((9852758999999991 : Rat) / 1280000000000000000), D4 := ((261645488999999761 : Rat) / 2560000000000000000), LB := ((1683717589897049 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3433872566999999991 : Rat) / 1280000000000000000), R := ((6868839884999999981 : Rat) / 2560000000000000000), D0 := ((6868839884999999981 : Rat) / 2560000000000000000), D1 := ((2216103628999999981 : Rat) / 2560000000000000000), D2 := ((320526284999999981 : Rat) / 2560000000000000000), D3 := ((20800268999999981 : Rat) / 2560000000000000000), D4 := ((130275368999999881 : Rat) / 1280000000000000000), LB := ((5163194374755431 : Rat) / 20000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6868839884999999981 : Rat) / 2560000000000000000), R := ((343496731799999999 : Rat) / 128000000000000000), D0 := ((343496731799999999 : Rat) / 128000000000000000), D1 := ((110859918999999999 : Rat) / 128000000000000000), D2 := ((16081051799999999 : Rat) / 128000000000000000), D3 := ((1094750999999999 : Rat) / 128000000000000000), D4 := ((259455986999999763 : Rat) / 2560000000000000000), LB := ((18524350510551457 : Rat) / 100000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((343496731799999999 : Rat) / 128000000000000000), R := ((6871029386999999979 : Rat) / 2560000000000000000), D0 := ((6871029386999999979 : Rat) / 2560000000000000000), D1 := ((2218293130999999979 : Rat) / 2560000000000000000), D2 := ((322715786999999979 : Rat) / 2560000000000000000), D3 := ((22989770999999979 : Rat) / 2560000000000000000), D4 := ((64590308999999941 : Rat) / 640000000000000000), LB := ((5901866333857253 : Rat) / 50000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6871029386999999979 : Rat) / 2560000000000000000), R := ((3436062068999999989 : Rat) / 1280000000000000000), D0 := ((3436062068999999989 : Rat) / 1280000000000000000), D1 := ((1109693940999999989 : Rat) / 1280000000000000000), D2 := ((161905268999999989 : Rat) / 1280000000000000000), D3 := ((12042260999999989 : Rat) / 1280000000000000000), D4 := ((51453296999999953 : Rat) / 512000000000000000), LB := ((2829209086097073 : Rat) / 50000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3436062068999999989 : Rat) / 1280000000000000000), R := ((6873218888999999977 : Rat) / 2560000000000000000), D0 := ((6873218888999999977 : Rat) / 2560000000000000000), D1 := ((2220482632999999977 : Rat) / 2560000000000000000), D2 := ((324905288999999977 : Rat) / 2560000000000000000), D3 := ((25179272999999977 : Rat) / 2560000000000000000), D4 := ((128085866999999883 : Rat) / 1280000000000000000), LB := ((18552530807181 : Rat) / 20000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6873218888999999977 : Rat) / 2560000000000000000), R := ((13747532528999999953 : Rat) / 5120000000000000000), D0 := ((13747532528999999953 : Rat) / 5120000000000000000), D1 := ((4442060016999999953 : Rat) / 5120000000000000000), D2 := ((650905328999999953 : Rat) / 5120000000000000000), D3 := ((51453296999999953 : Rat) / 5120000000000000000), D4 := ((255076982999999767 : Rat) / 2560000000000000000), LB := ((370493580437517 : Rat) / 625000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13747532528999999953 : Rat) / 5120000000000000000), R := ((859289204999999997 : Rat) / 320000000000000000), D0 := ((859289204999999997 : Rat) / 320000000000000000), D1 := ((277697172999999997 : Rat) / 320000000000000000), D2 := ((40750004999999997 : Rat) / 320000000000000000), D3 := ((3284252999999997 : Rat) / 320000000000000000), D4 := ((101811842999999907 : Rat) / 1024000000000000000), LB := ((2849706075798153 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((859289204999999997 : Rat) / 320000000000000000), R := ((13749722030999999951 : Rat) / 5120000000000000000), D0 := ((13749722030999999951 : Rat) / 5120000000000000000), D1 := ((4444249518999999951 : Rat) / 5120000000000000000), D2 := ((653094830999999951 : Rat) / 5120000000000000000), D3 := ((53642798999999951 : Rat) / 5120000000000000000), D4 := ((31747778999999971 : Rat) / 320000000000000000), LB := ((2742848789197283 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13749722030999999951 : Rat) / 5120000000000000000), R := ((275016335639999999 : Rat) / 102400000000000000), D0 := ((275016335639999999 : Rat) / 102400000000000000), D1 := ((88906885399999999 : Rat) / 102400000000000000), D2 := ((13083791639999999 : Rat) / 102400000000000000), D3 := ((1094750999999999 : Rat) / 102400000000000000), D4 := ((506869712999999537 : Rat) / 5120000000000000000), LB := ((5286810361756489 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((275016335639999999 : Rat) / 102400000000000000), R := ((13751911532999999949 : Rat) / 5120000000000000000), D0 := ((13751911532999999949 : Rat) / 5120000000000000000), D1 := ((4446439020999999949 : Rat) / 5120000000000000000), D2 := ((655284332999999949 : Rat) / 5120000000000000000), D3 := ((55832300999999949 : Rat) / 5120000000000000000), D4 := ((252887480999999769 : Rat) / 2560000000000000000), LB := ((5102807669481457 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13751911532999999949 : Rat) / 5120000000000000000), R := ((3438251570999999987 : Rat) / 1280000000000000000), D0 := ((3438251570999999987 : Rat) / 1280000000000000000), D1 := ((1111883442999999987 : Rat) / 1280000000000000000), D2 := ((164094770999999987 : Rat) / 1280000000000000000), D3 := ((14231762999999987 : Rat) / 1280000000000000000), D4 := ((504680210999999539 : Rat) / 5120000000000000000), LB := ((2466873522975477 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3438251570999999987 : Rat) / 1280000000000000000), R := ((13754101034999999947 : Rat) / 5120000000000000000), D0 := ((13754101034999999947 : Rat) / 5120000000000000000), D1 := ((4448628522999999947 : Rat) / 5120000000000000000), D2 := ((657473834999999947 : Rat) / 5120000000000000000), D3 := ((58021802999999947 : Rat) / 5120000000000000000), D4 := ((25179272999999977 : Rat) / 256000000000000000), LB := ((597460801935179 : Rat) / 1250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13754101034999999947 : Rat) / 5120000000000000000), R := ((6877597892999999973 : Rat) / 2560000000000000000), D0 := ((6877597892999999973 : Rat) / 2560000000000000000), D1 := ((2224861636999999973 : Rat) / 2560000000000000000), D2 := ((329284292999999973 : Rat) / 2560000000000000000), D3 := ((29558276999999973 : Rat) / 2560000000000000000), D4 := ((502490708999999541 : Rat) / 5120000000000000000), LB := ((9281368171054627 : Rat) / 20000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6877597892999999973 : Rat) / 2560000000000000000), R := ((2751258107399999989 : Rat) / 1024000000000000000), D0 := ((2751258107399999989 : Rat) / 1024000000000000000), D1 := ((890163604999999989 : Rat) / 1024000000000000000), D2 := ((131932667399999989 : Rat) / 1024000000000000000), D3 := ((12042260999999989 : Rat) / 1024000000000000000), D4 := ((250697978999999771 : Rat) / 2560000000000000000), LB := ((180671950004907 : Rat) / 400000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2751258107399999989 : Rat) / 1024000000000000000), R := ((1719673160999999993 : Rat) / 640000000000000000), D0 := ((1719673160999999993 : Rat) / 640000000000000000), D1 := ((556489096999999993 : Rat) / 640000000000000000), D2 := ((82594760999999993 : Rat) / 640000000000000000), D3 := ((7663256999999993 : Rat) / 640000000000000000), D4 := ((500301206999999543 : Rat) / 5120000000000000000), LB := ((4408089493168621 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1719673160999999993 : Rat) / 640000000000000000), R := ((13758480038999999943 : Rat) / 5120000000000000000), D0 := ((13758480038999999943 : Rat) / 5120000000000000000), D1 := ((4453007526999999943 : Rat) / 5120000000000000000), D2 := ((661852838999999943 : Rat) / 5120000000000000000), D3 := ((62400806999999943 : Rat) / 5120000000000000000), D4 := ((62400806999999943 : Rat) / 640000000000000000), LB := ((172584631676731 : Rat) / 400000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13758480038999999943 : Rat) / 5120000000000000000), R := ((6879787394999999971 : Rat) / 2560000000000000000), D0 := ((6879787394999999971 : Rat) / 2560000000000000000), D1 := ((2227051138999999971 : Rat) / 2560000000000000000), D2 := ((331473794999999971 : Rat) / 2560000000000000000), D3 := ((31747778999999971 : Rat) / 2560000000000000000), D4 := ((99622340999999909 : Rat) / 1024000000000000000), LB := ((8472875040723693 : Rat) / 20000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6879787394999999971 : Rat) / 2560000000000000000), R := ((13760669540999999941 : Rat) / 5120000000000000000), D0 := ((13760669540999999941 : Rat) / 5120000000000000000), D1 := ((4455197028999999941 : Rat) / 5120000000000000000), D2 := ((664042340999999941 : Rat) / 5120000000000000000), D3 := ((64590308999999941 : Rat) / 5120000000000000000), D4 := ((248508476999999773 : Rat) / 2560000000000000000), LB := ((166944598110641 : Rat) / 400000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13760669540999999941 : Rat) / 5120000000000000000), R := ((688088214599999997 : Rat) / 256000000000000000), D0 := ((688088214599999997 : Rat) / 256000000000000000), D1 := ((222814588999999997 : Rat) / 256000000000000000), D2 := ((33256854599999997 : Rat) / 256000000000000000), D3 := ((3284252999999997 : Rat) / 256000000000000000), D4 := ((495922202999999547 : Rat) / 5120000000000000000), LB := ((41262087671478653 : Rat) / 100000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((688088214599999997 : Rat) / 256000000000000000), R := ((13762859042999999939 : Rat) / 5120000000000000000), D0 := ((13762859042999999939 : Rat) / 5120000000000000000), D1 := ((4457386530999999939 : Rat) / 5120000000000000000), D2 := ((666231842999999939 : Rat) / 5120000000000000000), D3 := ((66779810999999939 : Rat) / 5120000000000000000), D4 := ((123706862999999887 : Rat) / 1280000000000000000), LB := ((5117850061135687 : Rat) / 12500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13762859042999999939 : Rat) / 5120000000000000000), R := ((6881976896999999969 : Rat) / 2560000000000000000), D0 := ((6881976896999999969 : Rat) / 2560000000000000000), D1 := ((2229240640999999969 : Rat) / 2560000000000000000), D2 := ((333663296999999969 : Rat) / 2560000000000000000), D3 := ((33937280999999969 : Rat) / 2560000000000000000), D4 := ((493732700999999549 : Rat) / 5120000000000000000), LB := ((40778902943472417 : Rat) / 100000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6881976896999999969 : Rat) / 2560000000000000000), R := ((13765048544999999937 : Rat) / 5120000000000000000), D0 := ((13765048544999999937 : Rat) / 5120000000000000000), D1 := ((4459576032999999937 : Rat) / 5120000000000000000), D2 := ((668421344999999937 : Rat) / 5120000000000000000), D3 := ((68969312999999937 : Rat) / 5120000000000000000), D4 := ((9852758999999991 : Rat) / 102400000000000000), LB := ((20385507071984943 : Rat) / 50000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13765048544999999937 : Rat) / 5120000000000000000), R := ((215095988999999999 : Rat) / 80000000000000000), D0 := ((215095988999999999 : Rat) / 80000000000000000), D1 := ((69697980999999999 : Rat) / 80000000000000000), D2 := ((10461188999999999 : Rat) / 80000000000000000), D3 := ((1094750999999999 : Rat) / 80000000000000000), D4 := ((491543198999999551 : Rat) / 5120000000000000000), LB := ((1278742418199183 : Rat) / 3125000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((215095988999999999 : Rat) / 80000000000000000), R := ((2753447609399999987 : Rat) / 1024000000000000000), D0 := ((2753447609399999987 : Rat) / 1024000000000000000), D1 := ((892353106999999987 : Rat) / 1024000000000000000), D2 := ((134122169399999987 : Rat) / 1024000000000000000), D3 := ((14231762999999987 : Rat) / 1024000000000000000), D4 := ((7663256999999993 : Rat) / 80000000000000000), LB := ((1030644004266501 : Rat) / 2500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2753447609399999987 : Rat) / 1024000000000000000), R := ((6884166398999999967 : Rat) / 2560000000000000000), D0 := ((6884166398999999967 : Rat) / 2560000000000000000), D1 := ((2231430142999999967 : Rat) / 2560000000000000000), D2 := ((335852798999999967 : Rat) / 2560000000000000000), D3 := ((36126782999999967 : Rat) / 2560000000000000000), D4 := ((489353696999999553 : Rat) / 5120000000000000000), LB := ((521120678479009 : Rat) / 1250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6884166398999999967 : Rat) / 2560000000000000000), R := ((13769427548999999933 : Rat) / 5120000000000000000), D0 := ((13769427548999999933 : Rat) / 5120000000000000000), D1 := ((4463955036999999933 : Rat) / 5120000000000000000), D2 := ((672800348999999933 : Rat) / 5120000000000000000), D3 := ((73348316999999933 : Rat) / 5120000000000000000), D4 := ((244129472999999777 : Rat) / 2560000000000000000), LB := ((4231207577070073 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13769427548999999933 : Rat) / 5120000000000000000), R := ((3442630574999999983 : Rat) / 1280000000000000000), D0 := ((3442630574999999983 : Rat) / 1280000000000000000), D1 := ((1116262446999999983 : Rat) / 1280000000000000000), D2 := ((168473774999999983 : Rat) / 1280000000000000000), D3 := ((18610766999999983 : Rat) / 1280000000000000000), D4 := ((97432838999999911 : Rat) / 1024000000000000000), LB := ((21546832523766657 : Rat) / 50000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3442630574999999983 : Rat) / 1280000000000000000), R := ((13771617050999999931 : Rat) / 5120000000000000000), D0 := ((13771617050999999931 : Rat) / 5120000000000000000), D1 := ((4466144538999999931 : Rat) / 5120000000000000000), D2 := ((674989850999999931 : Rat) / 5120000000000000000), D3 := ((75537818999999931 : Rat) / 5120000000000000000), D4 := ((121517360999999889 : Rat) / 1280000000000000000), LB := ((44035066881642493 : Rat) / 100000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13771617050999999931 : Rat) / 5120000000000000000), R := ((1377271180199999993 : Rat) / 512000000000000000), D0 := ((1377271180199999993 : Rat) / 512000000000000000), D1 := ((446723928999999993 : Rat) / 512000000000000000), D2 := ((67608460199999993 : Rat) / 512000000000000000), D3 := ((7663256999999993 : Rat) / 512000000000000000), D4 := ((484974692999999557 : Rat) / 5120000000000000000), LB := ((22568465229283463 : Rat) / 50000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1377271180199999993 : Rat) / 512000000000000000), R := ((13773806552999999929 : Rat) / 5120000000000000000), D0 := ((13773806552999999929 : Rat) / 5120000000000000000), D1 := ((4468334040999999929 : Rat) / 5120000000000000000), D2 := ((677179352999999929 : Rat) / 5120000000000000000), D3 := ((77727320999999929 : Rat) / 5120000000000000000), D4 := ((241939970999999779 : Rat) / 2560000000000000000), LB := ((2899994338515649 : Rat) / 6250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13773806552999999929 : Rat) / 5120000000000000000), R := ((1721862662999999991 : Rat) / 640000000000000000), D0 := ((1721862662999999991 : Rat) / 640000000000000000), D1 := ((558678598999999991 : Rat) / 640000000000000000), D2 := ((84784262999999991 : Rat) / 640000000000000000), D3 := ((9852758999999991 : Rat) / 640000000000000000), D4 := ((482785190999999559 : Rat) / 5120000000000000000), LB := ((4782466188555379 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1721862662999999991 : Rat) / 640000000000000000), R := ((13775996054999999927 : Rat) / 5120000000000000000), D0 := ((13775996054999999927 : Rat) / 5120000000000000000), D1 := ((4470523542999999927 : Rat) / 5120000000000000000), D2 := ((679368854999999927 : Rat) / 5120000000000000000), D3 := ((79916822999999927 : Rat) / 5120000000000000000), D4 := ((12042260999999989 : Rat) / 128000000000000000), LB := ((2470592526532811 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13775996054999999927 : Rat) / 5120000000000000000), R := ((6888545402999999963 : Rat) / 2560000000000000000), D0 := ((6888545402999999963 : Rat) / 2560000000000000000), D1 := ((2235809146999999963 : Rat) / 2560000000000000000), D2 := ((340231802999999963 : Rat) / 2560000000000000000), D3 := ((40505786999999963 : Rat) / 2560000000000000000), D4 := ((480595688999999561 : Rat) / 5120000000000000000), LB := ((31976339119201 : Rat) / 62500000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6888545402999999963 : Rat) / 2560000000000000000), R := ((551127422279999997 : Rat) / 204800000000000000), D0 := ((551127422279999997 : Rat) / 204800000000000000), D1 := ((178908521799999997 : Rat) / 204800000000000000), D2 := ((27262334279999997 : Rat) / 204800000000000000), D3 := ((3284252999999997 : Rat) / 204800000000000000), D4 := ((239750468999999781 : Rat) / 2560000000000000000), LB := ((1061524198419983 : Rat) / 2000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((551127422279999997 : Rat) / 204800000000000000), R := ((3444820076999999981 : Rat) / 1280000000000000000), D0 := ((3444820076999999981 : Rat) / 1280000000000000000), D1 := ((1118451948999999981 : Rat) / 1280000000000000000), D2 := ((170663276999999981 : Rat) / 1280000000000000000), D3 := ((20800268999999981 : Rat) / 1280000000000000000), D4 := ((478406186999999563 : Rat) / 5120000000000000000), LB := ((220618916142179 : Rat) / 400000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3444820076999999981 : Rat) / 1280000000000000000), R := ((13780375058999999923 : Rat) / 5120000000000000000), D0 := ((13780375058999999923 : Rat) / 5120000000000000000), D1 := ((4474902546999999923 : Rat) / 5120000000000000000), D2 := ((683747858999999923 : Rat) / 5120000000000000000), D3 := ((84295826999999923 : Rat) / 5120000000000000000), D4 := ((119327858999999891 : Rat) / 1280000000000000000), LB := ((2869919057478243 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13780375058999999923 : Rat) / 5120000000000000000), R := ((6890734904999999961 : Rat) / 2560000000000000000), D0 := ((6890734904999999961 : Rat) / 2560000000000000000), D1 := ((2237998648999999961 : Rat) / 2560000000000000000), D2 := ((342421304999999961 : Rat) / 2560000000000000000), D3 := ((42695288999999961 : Rat) / 2560000000000000000), D4 := ((95243336999999913 : Rat) / 1024000000000000000), LB := ((5980785222251539 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6890734904999999961 : Rat) / 2560000000000000000), R := ((13782564560999999921 : Rat) / 5120000000000000000), D0 := ((13782564560999999921 : Rat) / 5120000000000000000), D1 := ((4477092048999999921 : Rat) / 5120000000000000000), D2 := ((685937360999999921 : Rat) / 5120000000000000000), D3 := ((86485328999999921 : Rat) / 5120000000000000000), D4 := ((237560966999999783 : Rat) / 2560000000000000000), LB := ((3119191650093889 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((13782564560999999921 : Rat) / 5120000000000000000), R := ((172295741399999999 : Rat) / 64000000000000000), D0 := ((172295741399999999 : Rat) / 64000000000000000), D1 := ((55977334999999999 : Rat) / 64000000000000000), D2 := ((8587901399999999 : Rat) / 64000000000000000), D3 := ((1094750999999999 : Rat) / 64000000000000000), D4 := ((474027182999999567 : Rat) / 5120000000000000000), LB := ((6512701906711271 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((172295741399999999 : Rat) / 64000000000000000), R := ((6892924406999999959 : Rat) / 2560000000000000000), D0 := ((6892924406999999959 : Rat) / 2560000000000000000), D1 := ((2240188150999999959 : Rat) / 2560000000000000000), D2 := ((344610806999999959 : Rat) / 2560000000000000000), D3 := ((44884790999999959 : Rat) / 2560000000000000000), D4 := ((29558276999999973 : Rat) / 320000000000000000), LB := ((871761236367341 : Rat) / 20000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6892924406999999959 : Rat) / 2560000000000000000), R := ((3447009578999999979 : Rat) / 1280000000000000000), D0 := ((3447009578999999979 : Rat) / 1280000000000000000), D1 := ((1120641450999999979 : Rat) / 1280000000000000000), D2 := ((172852778999999979 : Rat) / 1280000000000000000), D3 := ((22989770999999979 : Rat) / 1280000000000000000), D4 := ((47074292999999957 : Rat) / 512000000000000000), LB := ((10716023028456423 : Rat) / 100000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3447009578999999979 : Rat) / 1280000000000000000), R := ((6895113908999999957 : Rat) / 2560000000000000000), D0 := ((6895113908999999957 : Rat) / 2560000000000000000), D1 := ((2242377652999999957 : Rat) / 2560000000000000000), D2 := ((346800308999999957 : Rat) / 2560000000000000000), D3 := ((47074292999999957 : Rat) / 2560000000000000000), D4 := ((117138356999999893 : Rat) / 1280000000000000000), LB := ((17753365248240893 : Rat) / 100000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6895113908999999957 : Rat) / 2560000000000000000), R := ((1724052164999999989 : Rat) / 640000000000000000), D0 := ((1724052164999999989 : Rat) / 640000000000000000), D1 := ((560868100999999989 : Rat) / 640000000000000000), D2 := ((86973764999999989 : Rat) / 640000000000000000), D3 := ((12042260999999989 : Rat) / 640000000000000000), D4 := ((233181962999999787 : Rat) / 2560000000000000000), LB := ((2547661676740587 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1724052164999999989 : Rat) / 640000000000000000), R := ((1379460682199999991 : Rat) / 512000000000000000), D0 := ((1379460682199999991 : Rat) / 512000000000000000), D1 := ((448913430999999991 : Rat) / 512000000000000000), D2 := ((69797962199999991 : Rat) / 512000000000000000), D3 := ((9852758999999991 : Rat) / 512000000000000000), D4 := ((58021802999999947 : Rat) / 640000000000000000), LB := ((3389164400710021 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1379460682199999991 : Rat) / 512000000000000000), R := ((3449199080999999977 : Rat) / 1280000000000000000), D0 := ((3449199080999999977 : Rat) / 1280000000000000000), D1 := ((1122830952999999977 : Rat) / 1280000000000000000), D2 := ((175042280999999977 : Rat) / 1280000000000000000), D3 := ((25179272999999977 : Rat) / 1280000000000000000), D4 := ((230992460999999789 : Rat) / 2560000000000000000), LB := ((4300439744278073 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3449199080999999977 : Rat) / 1280000000000000000), R := ((6899492912999999953 : Rat) / 2560000000000000000), D0 := ((6899492912999999953 : Rat) / 2560000000000000000), D1 := ((2246756656999999953 : Rat) / 2560000000000000000), D2 := ((351179312999999953 : Rat) / 2560000000000000000), D3 := ((51453296999999953 : Rat) / 2560000000000000000), D4 := ((22989770999999979 : Rat) / 256000000000000000), LB := ((5282091319948057 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6899492912999999953 : Rat) / 2560000000000000000), R := ((431286728999999997 : Rat) / 160000000000000000), D0 := ((431286728999999997 : Rat) / 160000000000000000), D1 := ((140490712999999997 : Rat) / 160000000000000000), D2 := ((22017128999999997 : Rat) / 160000000000000000), D3 := ((3284252999999997 : Rat) / 160000000000000000), D4 := ((228802958999999791 : Rat) / 2560000000000000000), LB := ((791841433569751 : Rat) / 1250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((431286728999999997 : Rat) / 160000000000000000), R := ((6901682414999999951 : Rat) / 2560000000000000000), D0 := ((6901682414999999951 : Rat) / 2560000000000000000), D1 := ((2248946158999999951 : Rat) / 2560000000000000000), D2 := ((353368814999999951 : Rat) / 2560000000000000000), D3 := ((53642798999999951 : Rat) / 2560000000000000000), D4 := ((14231762999999987 : Rat) / 160000000000000000), LB := ((7458981426511357 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6901682414999999951 : Rat) / 2560000000000000000), R := ((138055543319999999 : Rat) / 51200000000000000), D0 := ((138055543319999999 : Rat) / 51200000000000000), D1 := ((45000818199999999 : Rat) / 51200000000000000), D2 := ((7089271319999999 : Rat) / 51200000000000000), D3 := ((1094750999999999 : Rat) / 51200000000000000), D4 := ((226613456999999793 : Rat) / 2560000000000000000), LB := ((4327735748611561 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((138055543319999999 : Rat) / 51200000000000000), R := ((6903871916999999949 : Rat) / 2560000000000000000), D0 := ((6903871916999999949 : Rat) / 2560000000000000000), D1 := ((2251135660999999949 : Rat) / 2560000000000000000), D2 := ((355558316999999949 : Rat) / 2560000000000000000), D3 := ((55832300999999949 : Rat) / 2560000000000000000), D4 := ((112759352999999897 : Rat) / 1280000000000000000), LB := ((1984968245290597 : Rat) / 2000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6903871916999999949 : Rat) / 2560000000000000000), R := ((1726241666999999987 : Rat) / 640000000000000000), D0 := ((1726241666999999987 : Rat) / 640000000000000000), D1 := ((563057602999999987 : Rat) / 640000000000000000), D2 := ((89163266999999987 : Rat) / 640000000000000000), D3 := ((14231762999999987 : Rat) / 640000000000000000), D4 := ((44884790999999959 : Rat) / 512000000000000000), LB := ((22007303871357 : Rat) / 19531250000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1726241666999999987 : Rat) / 640000000000000000), R := ((3453578084999999973 : Rat) / 1280000000000000000), D0 := ((3453578084999999973 : Rat) / 1280000000000000000), D1 := ((1127209956999999973 : Rat) / 1280000000000000000), D2 := ((179421284999999973 : Rat) / 1280000000000000000), D3 := ((29558276999999973 : Rat) / 1280000000000000000), D4 := ((55832300999999949 : Rat) / 640000000000000000), LB := ((41425911284209 : Rat) / 19531250000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3453578084999999973 : Rat) / 1280000000000000000), R := ((863668208999999993 : Rat) / 320000000000000000), D0 := ((863668208999999993 : Rat) / 320000000000000000), D1 := ((282076176999999993 : Rat) / 320000000000000000), D2 := ((45129008999999993 : Rat) / 320000000000000000), D3 := ((7663256999999993 : Rat) / 320000000000000000), D4 := ((110569850999999899 : Rat) / 1280000000000000000), LB := ((3091880271318681 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((863668208999999993 : Rat) / 320000000000000000), R := ((3455767586999999971 : Rat) / 1280000000000000000), D0 := ((3455767586999999971 : Rat) / 1280000000000000000), D1 := ((1129399458999999971 : Rat) / 1280000000000000000), D2 := ((181610786999999971 : Rat) / 1280000000000000000), D3 := ((31747778999999971 : Rat) / 1280000000000000000), D4 := ((1094750999999999 : Rat) / 12800000000000000), LB := ((1616857395438931 : Rat) / 2500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3455767586999999971 : Rat) / 1280000000000000000), R := ((345686233799999997 : Rat) / 128000000000000000), D0 := ((345686233799999997 : Rat) / 128000000000000000), D1 := ((113049420999999997 : Rat) / 128000000000000000), D2 := ((18270553799999997 : Rat) / 128000000000000000), D3 := ((3284252999999997 : Rat) / 128000000000000000), D4 := ((108380348999999901 : Rat) / 1280000000000000000), LB := ((1015349233555063 : Rat) / 1000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((345686233799999997 : Rat) / 128000000000000000), R := ((3457957088999999969 : Rat) / 1280000000000000000), D0 := ((3457957088999999969 : Rat) / 1280000000000000000), D1 := ((1131588960999999969 : Rat) / 1280000000000000000), D2 := ((183800288999999969 : Rat) / 1280000000000000000), D3 := ((33937280999999969 : Rat) / 1280000000000000000), D4 := ((53642798999999951 : Rat) / 640000000000000000), LB := ((3538968972099099 : Rat) / 2500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3457957088999999969 : Rat) / 1280000000000000000), R := ((108095369999999999 : Rat) / 40000000000000000), D0 := ((108095369999999999 : Rat) / 40000000000000000), D1 := ((35396365999999999 : Rat) / 40000000000000000), D2 := ((5777969999999999 : Rat) / 40000000000000000), D3 := ((1094750999999999 : Rat) / 40000000000000000), D4 := ((106190846999999903 : Rat) / 1280000000000000000), LB := ((739222708283771 : Rat) / 400000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((108095369999999999 : Rat) / 40000000000000000), R := ((3460146590999999967 : Rat) / 1280000000000000000), D0 := ((3460146590999999967 : Rat) / 1280000000000000000), D1 := ((1133778462999999967 : Rat) / 1280000000000000000), D2 := ((185989790999999967 : Rat) / 1280000000000000000), D3 := ((36126782999999967 : Rat) / 1280000000000000000), D4 := ((3284252999999997 : Rat) / 40000000000000000), LB := ((2313374283010039 : Rat) / 1000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3460146590999999967 : Rat) / 1280000000000000000), R := ((1730620670999999983 : Rat) / 640000000000000000), D0 := ((1730620670999999983 : Rat) / 640000000000000000), D1 := ((567436606999999983 : Rat) / 640000000000000000), D2 := ((93542270999999983 : Rat) / 640000000000000000), D3 := ((18610766999999983 : Rat) / 640000000000000000), D4 := ((20800268999999981 : Rat) / 256000000000000000), LB := ((14060885859376593 : Rat) / 5000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1730620670999999983 : Rat) / 640000000000000000), R := ((865857710999999991 : Rat) / 320000000000000000), D0 := ((865857710999999991 : Rat) / 320000000000000000), D1 := ((284265678999999991 : Rat) / 320000000000000000), D2 := ((47318510999999991 : Rat) / 320000000000000000), D3 := ((9852758999999991 : Rat) / 320000000000000000), D4 := ((51453296999999953 : Rat) / 640000000000000000), LB := ((8319516382491177 : Rat) / 10000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((865857710999999991 : Rat) / 320000000000000000), R := ((1732810172999999981 : Rat) / 640000000000000000), D0 := ((1732810172999999981 : Rat) / 640000000000000000), D1 := ((569626108999999981 : Rat) / 640000000000000000), D2 := ((95731772999999981 : Rat) / 640000000000000000), D3 := ((20800268999999981 : Rat) / 640000000000000000), D4 := ((25179272999999977 : Rat) / 320000000000000000), LB := ((5018580921073157 : Rat) / 2500000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1732810172999999981 : Rat) / 640000000000000000), R := ((86695246199999999 : Rat) / 32000000000000000), D0 := ((86695246199999999 : Rat) / 32000000000000000), D1 := ((28536042999999999 : Rat) / 32000000000000000), D2 := ((4841326199999999 : Rat) / 32000000000000000), D3 := ((1094750999999999 : Rat) / 32000000000000000), D4 := ((9852758999999991 : Rat) / 128000000000000000), LB := ((332790557166851 : Rat) / 100000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86695246199999999 : Rat) / 32000000000000000), R := ((1734999674999999979 : Rat) / 640000000000000000), D0 := ((1734999674999999979 : Rat) / 640000000000000000), D1 := ((571815610999999979 : Rat) / 640000000000000000), D2 := ((97921274999999979 : Rat) / 640000000000000000), D3 := ((22989770999999979 : Rat) / 640000000000000000), D4 := ((12042260999999989 : Rat) / 160000000000000000), LB := ((1199864788759747 : Rat) / 250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1734999674999999979 : Rat) / 640000000000000000), R := ((868047212999999989 : Rat) / 320000000000000000), D0 := ((868047212999999989 : Rat) / 320000000000000000), D1 := ((286455180999999989 : Rat) / 320000000000000000), D2 := ((49508012999999989 : Rat) / 320000000000000000), D3 := ((12042260999999989 : Rat) / 320000000000000000), D4 := ((47074292999999957 : Rat) / 640000000000000000), LB := ((1285720680202207 : Rat) / 200000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((868047212999999989 : Rat) / 320000000000000000), R := ((217285490999999997 : Rat) / 80000000000000000), D0 := ((217285490999999997 : Rat) / 80000000000000000), D1 := ((71887482999999997 : Rat) / 80000000000000000), D2 := ((12650690999999997 : Rat) / 80000000000000000), D3 := ((3284252999999997 : Rat) / 80000000000000000), D4 := ((22989770999999979 : Rat) / 320000000000000000), LB := ((3246399204702599 : Rat) / 1000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((217285490999999997 : Rat) / 80000000000000000), R := ((870236714999999987 : Rat) / 320000000000000000), D0 := ((870236714999999987 : Rat) / 320000000000000000), D1 := ((288644682999999987 : Rat) / 320000000000000000), D2 := ((51697514999999987 : Rat) / 320000000000000000), D3 := ((14231762999999987 : Rat) / 320000000000000000), D4 := ((1094750999999999 : Rat) / 16000000000000000), LB := ((7375267236974681 : Rat) / 1000000000000000000) }
]

def block023RightChunk000L : Rat := ((11329895089285714287 : Rat) / 6250000000000000000)
def block023RightChunk000R : Rat := ((870236714999999987 : Rat) / 320000000000000000)

def block023RightChunk000Certificate : Bool :=
  allBoxesValid block023RightChunk000 &&
  coversFromBool block023RightChunk000 block023RightChunk000L block023RightChunk000R

theorem block023RightChunk000Certificate_eq_true :
    block023RightChunk000Certificate = true := by
  native_decide

def block023RightChunk001 : List RatBox := [
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((870236714999999987 : Rat) / 320000000000000000), R := ((435665732999999993 : Rat) / 160000000000000000), D0 := ((435665732999999993 : Rat) / 160000000000000000), D1 := ((144869716999999993 : Rat) / 160000000000000000), D2 := ((26396132999999993 : Rat) / 160000000000000000), D3 := ((7663256999999993 : Rat) / 160000000000000000), D4 := ((20800268999999981 : Rat) / 320000000000000000), LB := ((12259591759267607 : Rat) / 1000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((435665732999999993 : Rat) / 160000000000000000), R := ((54595060499999999 : Rat) / 20000000000000000), D0 := ((54595060499999999 : Rat) / 20000000000000000), D1 := ((18245558499999999 : Rat) / 20000000000000000), D2 := ((3436360499999999 : Rat) / 20000000000000000), D3 := ((1094750999999999 : Rat) / 20000000000000000), D4 := ((9852758999999991 : Rat) / 160000000000000000), LB := ((8153683700836911 : Rat) / 1000000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54595060499999999 : Rat) / 20000000000000000), R := ((43894998599999999 : Rat) / 16000000000000000), D0 := ((43894998599999999 : Rat) / 16000000000000000), D1 := ((14815396999999999 : Rat) / 16000000000000000), D2 := ((2968038599999999 : Rat) / 16000000000000000), D3 := ((1094750999999999 : Rat) / 16000000000000000), D4 := ((1094750999999999 : Rat) / 20000000000000000), LB := ((780779802005499 : Rat) / 250000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43894998599999999 : Rat) / 16000000000000000), R := ((110284871999999997 : Rat) / 40000000000000000), D0 := ((110284871999999997 : Rat) / 40000000000000000), D1 := ((37585867999999997 : Rat) / 40000000000000000), D2 := ((7967471999999997 : Rat) / 40000000000000000), D3 := ((3284252999999997 : Rat) / 40000000000000000), D4 := ((3284252999999997 : Rat) / 80000000000000000), LB := ((5944700579361667 : Rat) / 125000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((110284871999999997 : Rat) / 40000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((1094750999999999 : Rat) / 10000000000000000), D4 := ((1094750999999999 : Rat) / 40000000000000000), LB := ((8899587393617137 : Rat) / 100000000000000000) },
  { w1 := ((456169689131047 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2880649889557893 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((140648935267857142867 : Rat) / 50000000000000000000), D0 := ((140648935267857142867 : Rat) / 50000000000000000000), D1 := ((49775180267857142867 : Rat) / 50000000000000000000), D2 := ((12752185267857142867 : Rat) / 50000000000000000000), D3 := ((6898161517857142867 : Rat) / 50000000000000000000), D4 := ((1424406517857147867 : Rat) / 50000000000000000000), LB := ((2094245705105191 : Rat) / 2000000000000000000) }
]

def block023RightChunk001L : Rat := ((870236714999999987 : Rat) / 320000000000000000)
def block023RightChunk001R : Rat := ((140648935267857142867 : Rat) / 50000000000000000000)

def block023RightChunk001Certificate : Bool :=
  allBoxesValid block023RightChunk001 &&
  coversFromBool block023RightChunk001 block023RightChunk001L block023RightChunk001R

theorem block023RightChunk001Certificate_eq_true :
    block023RightChunk001Certificate = true := by
  native_decide

def block023RightChainCertificate : Bool :=
  decide (
    block023RightL = ((11329895089285714287 : Rat) / 6250000000000000000) /\
    ((870236714999999987 : Rat) / 320000000000000000) = ((870236714999999987 : Rat) / 320000000000000000) /\
    ((140648935267857142867 : Rat) / 50000000000000000000) = block023RightR)

theorem block023RightChainCertificate_eq_true :
    block023RightChainCertificate = true := by
  native_decide

def block023LeftBoxCount : Nat := boxCount block023LeftBoxes
def block023RightBoxCount : Nat := 106

def block023_rational_certificate : Prop :=
    block023LeftCertificate = true /\
    block023RightChainCertificate = true /\
    block023RightChunk000Certificate = true /\
    block023RightChunk001Certificate = true

theorem block023_rational_certificate_proof :
    block023_rational_certificate := by
  exact ⟨block023LeftCertificate_eq_true, block023RightChainCertificate_eq_true, block023RightChunk000Certificate_eq_true, block023RightChunk001Certificate_eq_true⟩

end Block023
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block023

open Set

def block023W1 : Rat := ((456169689131047 : Rat) / 200000000000000)
def block023W2 : Rat := (0 : Rat)
def block023W3 : Rat := (0 : Rat)
def block023W4 : Rat := ((2880649889557893 : Rat) / 10000000000000000)
def block023S1 : Rat := ((18174751 : Rat) / 10000000)
def block023S2 : Rat := ((511587 : Rat) / 200000)
def block023S3 : Rat := ((107000619 : Rat) / 40000000)
def block023S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block023V (y : ℝ) : ℝ :=
  ratPotential block023W1 block023W2 block023W3 block023W4 block023S1 block023S2 block023S3 block023S4 y

def block023LeftParamsCertificate : Bool :=
  allBoxesSameParams block023LeftBoxes block023W1 block023W2 block023W3 block023W4 block023S1 block023S2 block023S3 block023S4

theorem block023LeftParamsCertificate_eq_true :
    block023LeftParamsCertificate = true := by
  native_decide

theorem block023_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block023LeftL : ℝ) (block023LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block023S1 : ℝ))
    (hy2ne : y ≠ (block023S2 : ℝ))
    (hy3ne : y ≠ (block023S3 : ℝ))
    (hy4ne : y ≠ (block023S4 : ℝ)) :
    0 < block023V y := by
  have hcert := block023LeftCertificate_eq_true
  unfold block023LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block023LeftBoxes) (lo := block023LeftL) (hi := block023LeftR)
    (w1 := block023W1) (w2 := block023W2) (w3 := block023W3) (w4 := block023W4)
    (s1 := block023S1) (s2 := block023S2) (s3 := block023S3) (s4 := block023S4)
    hboxes hcover block023LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block023RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block023RightChunk000 block023W1 block023W2 block023W3 block023W4 block023S1 block023S2 block023S3 block023S4

theorem block023RightChunk000ParamsCertificate_eq_true :
    block023RightChunk000ParamsCertificate = true := by
  native_decide

theorem block023_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block023RightChunk000L : ℝ) (block023RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block023S1 : ℝ))
    (hy2ne : y ≠ (block023S2 : ℝ))
    (hy3ne : y ≠ (block023S3 : ℝ))
    (hy4ne : y ≠ (block023S4 : ℝ)) :
    0 < block023V y := by
  have hcert := block023RightChunk000Certificate_eq_true
  unfold block023RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block023RightChunk000) (lo := block023RightChunk000L) (hi := block023RightChunk000R)
    (w1 := block023W1) (w2 := block023W2) (w3 := block023W3) (w4 := block023W4)
    (s1 := block023S1) (s2 := block023S2) (s3 := block023S3) (s4 := block023S4)
    hboxes hcover block023RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block023RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block023RightChunk001 block023W1 block023W2 block023W3 block023W4 block023S1 block023S2 block023S3 block023S4

theorem block023RightChunk001ParamsCertificate_eq_true :
    block023RightChunk001ParamsCertificate = true := by
  native_decide

theorem block023_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block023RightChunk001L : ℝ) (block023RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block023S1 : ℝ))
    (hy2ne : y ≠ (block023S2 : ℝ))
    (hy3ne : y ≠ (block023S3 : ℝ))
    (hy4ne : y ≠ (block023S4 : ℝ)) :
    0 < block023V y := by
  have hcert := block023RightChunk001Certificate_eq_true
  unfold block023RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block023RightChunk001) (lo := block023RightChunk001L) (hi := block023RightChunk001R)
    (w1 := block023W1) (w2 := block023W2) (w3 := block023W3) (w4 := block023W4)
    (s1 := block023S1) (s2 := block023S2) (s3 := block023S3) (s4 := block023S4)
    hboxes hcover block023RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block023_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block023RightL : ℝ) (block023RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block023S1 : ℝ))
    (hy2ne : y ≠ (block023S2 : ℝ))
    (hy3ne : y ≠ (block023S3 : ℝ))
    (hy4ne : y ≠ (block023S4 : ℝ)) :
    0 < block023V y := by
  by_cases h0 : y ≤ (block023RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block023RightChunk000L : ℝ) (block023RightChunk000R : ℝ) := by
      have hL : (block023RightChunk000L : ℝ) = (block023RightL : ℝ) := by
        norm_num [block023RightChunk000L, block023RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block023_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block023RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block023RightChunk001L : ℝ) = (block023RightChunk000R : ℝ) := by
      norm_num [block023RightChunk001L, block023RightChunk000R]
    have hR : (block023RightChunk001R : ℝ) = (block023RightR : ℝ) := by
      norm_num [block023RightChunk001R, block023RightR]
    have hyc : y ∈ Icc (block023RightChunk001L : ℝ) (block023RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block023_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block023_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block023LeftL : ℝ) (block023LeftR : ℝ) →
    y ≠ 0 → y ≠ (block023S1 : ℝ) → y ≠ (block023S2 : ℝ) →
    y ≠ (block023S3 : ℝ) → y ≠ (block023S4 : ℝ) → 0 < block023V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block023RightL : ℝ) (block023RightR : ℝ) →
    y ≠ 0 → y ≠ (block023S1 : ℝ) → y ≠ (block023S2 : ℝ) →
    y ≠ (block023S3 : ℝ) → y ≠ (block023S4 : ℝ) → 0 < block023V y)

theorem block023_reallog_certificate_proof :
    block023_reallog_certificate := by
  exact ⟨block023_left_V_pos, block023_right_V_pos⟩

end Block023
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block023.block023V
#check Erdos1038Lean.M1817475.Block023.block023_left_V_pos
#check Erdos1038Lean.M1817475.Block023.block023_right_V_pos
#check Erdos1038Lean.M1817475.Block023.block023_reallog_certificate_proof
