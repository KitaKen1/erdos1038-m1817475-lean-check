/-
Self-contained Lean4Web paste file.
Block 349 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block349

def block349LeftL : Rat := ((749053125000000003 : Rat) / 1000000000000000000)
def block349LeftR : Rat := ((37462430803571428721 : Rat) / 50000000000000000000)
def block349RightL : Rat := ((1749053125000000003 : Rat) / 1000000000000000000)
def block349RightR : Rat := ((137462430803571428721 : Rat) / 50000000000000000000)

def block349LeftBoxes : List RatBox := [
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((749053125000000003 : Rat) / 1000000000000000000), R := ((37462430803571428721 : Rat) / 50000000000000000000), D0 := ((37462430803571428721 : Rat) / 50000000000000000000), D1 := ((1068421974999999997 : Rat) / 1000000000000000000), D2 := ((1808881874999999997 : Rat) / 1000000000000000000), D3 := ((19171652517857142831 : Rat) / 10000000000000000000), D4 := ((12645731272321427931 : Rat) / 6250000000000000000), LB := ((6253048805566083 : Rat) / 1000000000000000000) }
]

def block349LeftCertificate : Bool :=
  allBoxesValid block349LeftBoxes &&
  coversFromBool block349LeftBoxes block349LeftL block349LeftR

theorem block349LeftCertificate_eq_true :
    block349LeftCertificate = true := by
  native_decide

def block349RightChunk000 : List RatBox := [
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1749053125000000003 : Rat) / 1000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((68421974999999997 : Rat) / 1000000000000000000), D2 := ((808881874999999997 : Rat) / 1000000000000000000), D3 := ((9171652517857142831 : Rat) / 10000000000000000000), D4 := ((6395731272321427931 : Rat) / 6250000000000000000), LB := ((4645723584895023 : Rat) / 2500000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8487432767857142861 : Rat) / 10000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((1646586061141073 : Rat) / 10000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4785133267857142861 : Rat) / 10000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((212983350987209 : Rat) / 2000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3859558392857142861 : Rat) / 10000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((6928529035629723 : Rat) / 100000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3396770955357142861 : Rat) / 10000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((11866436020503093 : Rat) / 1000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2933983517857142861 : Rat) / 10000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((6307501966186471 : Rat) / 500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2702589799107142861 : Rat) / 10000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((1661891898234577 : Rat) / 100000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2586892939732142861 : Rat) / 10000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((4265584809958617 : Rat) / 500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2471196080357142861 : Rat) / 10000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((7606284077882053 : Rat) / 5000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2355499220982142861 : Rat) / 10000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((3241893779166699 : Rat) / 500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2297650791294642861 : Rat) / 10000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((982981267401109 : Rat) / 250000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2239802361607142861 : Rat) / 10000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((8533982502509363 : Rat) / 5000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2181953931919642861 : Rat) / 10000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((1028337293171383 : Rat) / 200000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2153029717075892861 : Rat) / 10000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((4314504168533739 : Rat) / 1000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2124105502232142861 : Rat) / 10000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((7160525811147067 : Rat) / 2000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((2095181287388392861 : Rat) / 10000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((29416891947499357 : Rat) / 10000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2066257072544642861 : Rat) / 10000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((12008593061492573 : Rat) / 5000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((2037332857700892861 : Rat) / 10000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((490879512761791 : Rat) / 250000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2008408642857142861 : Rat) / 10000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((1630511246634797 : Rat) / 1000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((1979484428013392861 : Rat) / 10000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((879005112710881 : Rat) / 625000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((1950560213169642861 : Rat) / 10000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((12952391053129841 : Rat) / 10000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((1921635998325892861 : Rat) / 10000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((13013941187501321 : Rat) / 10000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((1892711783482142861 : Rat) / 10000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((14296694271841437 : Rat) / 10000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((1863787568638392861 : Rat) / 10000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((3370643484576441 : Rat) / 2000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((1834863353794642861 : Rat) / 10000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((20741326217751377 : Rat) / 10000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((1805939138950892861 : Rat) / 10000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((260248506558583 : Rat) / 100000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1777014924107142861 : Rat) / 10000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((3277455334630447 : Rat) / 1000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((1748090709263392861 : Rat) / 10000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((4106923839914567 : Rat) / 1000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((1719166494419642861 : Rat) / 10000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((8541752141924541 : Rat) / 100000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((1661318064732142861 : Rat) / 10000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((3296379272359623 : Rat) / 1250000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((1603469635044642861 : Rat) / 10000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((11958498825670849 : Rat) / 2000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1545621205357142861 : Rat) / 10000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((46903442832985087 : Rat) / 100000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1429924345982142861 : Rat) / 10000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((6325683364946419 : Rat) / 500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1314227486607142861 : Rat) / 10000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((1313406912355053 : Rat) / 100000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((103400233767857142861 : Rat) / 40000000000000000000), D0 := ((103400233767857142861 : Rat) / 40000000000000000000), D1 := ((30701229767857142861 : Rat) / 40000000000000000000), D2 := ((1082833767857142861 : Rat) / 40000000000000000000), D3 := ((1082833767857142861 : Rat) / 10000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((546345067244261 : Rat) / 100000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((103400233767857142861 : Rat) / 40000000000000000000), R := ((207883301303571428583 : Rat) / 80000000000000000000), D0 := ((207883301303571428583 : Rat) / 80000000000000000000), D1 := ((62485293303571428583 : Rat) / 80000000000000000000), D2 := ((3248501303571428583 : Rat) / 80000000000000000000), D3 := ((3248501303571428583 : Rat) / 40000000000000000000), D4 := ((37472856874999980087 : Rat) / 200000000000000000000), LB := ((13230496122972349 : Rat) / 500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((207883301303571428583 : Rat) / 80000000000000000000), R := ((52241533767857142861 : Rat) / 20000000000000000000), D0 := ((52241533767857142861 : Rat) / 20000000000000000000), D1 := ((15892031767857142861 : Rat) / 20000000000000000000), D2 := ((1082833767857142861 : Rat) / 20000000000000000000), D3 := ((1082833767857142861 : Rat) / 16000000000000000000), D4 := ((69531544910714245869 : Rat) / 400000000000000000000), LB := ((588428214817831 : Rat) / 20000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((52241533767857142861 : Rat) / 20000000000000000000), R := ((105565901303571428583 : Rat) / 40000000000000000000), D0 := ((105565901303571428583 : Rat) / 40000000000000000000), D1 := ((32866897303571428583 : Rat) / 40000000000000000000), D2 := ((3248501303571428583 : Rat) / 40000000000000000000), D3 := ((1082833767857142861 : Rat) / 20000000000000000000), D4 := ((16029344017857132891 : Rat) / 100000000000000000000), LB := ((1374392794575191 : Rat) / 100000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((105565901303571428583 : Rat) / 40000000000000000000), R := ((26662183767857142861 : Rat) / 10000000000000000000), D0 := ((26662183767857142861 : Rat) / 10000000000000000000), D1 := ((8487432767857142861 : Rat) / 10000000000000000000), D2 := ((1082833767857142861 : Rat) / 10000000000000000000), D3 := ((1082833767857142861 : Rat) / 40000000000000000000), D4 := ((26644519196428551477 : Rat) / 200000000000000000000), LB := ((4447834465614181 : Rat) / 50000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((26662183767857142861 : Rat) / 10000000000000000000), R := ((134348796830357142909 : Rat) / 50000000000000000000), D0 := ((134348796830357142909 : Rat) / 50000000000000000000), D1 := ((43475041830357142909 : Rat) / 50000000000000000000), D2 := ((6452046830357142909 : Rat) / 50000000000000000000), D3 := ((259469497767857151 : Rat) / 12500000000000000000), D4 := ((5307587589285709293 : Rat) / 50000000000000000000), LB := ((487039861052609 : Rat) / 4000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((134348796830357142909 : Rat) / 50000000000000000000), R := ((135386674821428571513 : Rat) / 50000000000000000000), D0 := ((135386674821428571513 : Rat) / 50000000000000000000), D1 := ((44512919821428571513 : Rat) / 50000000000000000000), D2 := ((7489924821428571513 : Rat) / 50000000000000000000), D3 := ((259469497767857151 : Rat) / 6250000000000000000), D4 := ((4269709598214280689 : Rat) / 50000000000000000000), LB := ((1263450815018241 : Rat) / 100000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((135386674821428571513 : Rat) / 50000000000000000000), R := ((27181122763392857163 : Rat) / 10000000000000000000), D0 := ((27181122763392857163 : Rat) / 10000000000000000000), D1 := ((9006371763392857163 : Rat) / 10000000000000000000), D2 := ((1601772763392857163 : Rat) / 10000000000000000000), D3 := ((259469497767857151 : Rat) / 5000000000000000000), D4 := ((646366321428570417 : Rat) / 10000000000000000000), LB := ((5466551186646823 : Rat) / 12500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((27181122763392857163 : Rat) / 10000000000000000000), R := ((68082541657366071483 : Rat) / 25000000000000000000), D0 := ((68082541657366071483 : Rat) / 25000000000000000000), D1 := ((22645664157366071483 : Rat) / 25000000000000000000), D2 := ((4134166657366071483 : Rat) / 25000000000000000000), D3 := ((2854164475446428661 : Rat) / 50000000000000000000), D4 := ((2712892611607137783 : Rat) / 50000000000000000000), LB := ((18288251493456809 : Rat) / 10000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((68082541657366071483 : Rat) / 25000000000000000000), R := ((272589636127232143083 : Rat) / 100000000000000000000), D0 := ((272589636127232143083 : Rat) / 100000000000000000000), D1 := ((90842126127232143083 : Rat) / 100000000000000000000), D2 := ((16796136127232143083 : Rat) / 100000000000000000000), D3 := ((5967798448660714473 : Rat) / 100000000000000000000), D4 := ((306677889229910079 : Rat) / 6250000000000000000), LB := ((2414897229546853 : Rat) / 500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272589636127232143083 : Rat) / 100000000000000000000), R := ((136424552812500000117 : Rat) / 50000000000000000000), D0 := ((136424552812500000117 : Rat) / 50000000000000000000), D1 := ((45550797812500000117 : Rat) / 50000000000000000000), D2 := ((8527802812500000117 : Rat) / 50000000000000000000), D3 := ((778408493303571453 : Rat) / 12500000000000000000), D4 := ((4647376729910704113 : Rat) / 100000000000000000000), LB := ((872493536474811 : Rat) / 500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((136424552812500000117 : Rat) / 50000000000000000000), R := ((545957680747767857619 : Rat) / 200000000000000000000), D0 := ((545957680747767857619 : Rat) / 200000000000000000000), D1 := ((182462660747767857619 : Rat) / 200000000000000000000), D2 := ((34370680747767857619 : Rat) / 200000000000000000000), D3 := ((12714005390625000399 : Rat) / 200000000000000000000), D4 := ((2193953616071423481 : Rat) / 50000000000000000000), LB := ((4494421653922331 : Rat) / 1000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545957680747767857619 : Rat) / 200000000000000000000), R := ((54621715024553571477 : Rat) / 20000000000000000000), D0 := ((54621715024553571477 : Rat) / 20000000000000000000), D1 := ((18272213024553571477 : Rat) / 20000000000000000000), D2 := ((3463015024553571477 : Rat) / 20000000000000000000), D3 := ((259469497767857151 : Rat) / 4000000000000000000), D4 := ((8516344966517836773 : Rat) / 200000000000000000000), LB := ((17588805767568827 : Rat) / 5000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((54621715024553571477 : Rat) / 20000000000000000000), R := ((546476619743303571921 : Rat) / 200000000000000000000), D0 := ((546476619743303571921 : Rat) / 200000000000000000000), D1 := ((182981599743303571921 : Rat) / 200000000000000000000), D2 := ((34889619743303571921 : Rat) / 200000000000000000000), D3 := ((13232944386160714701 : Rat) / 200000000000000000000), D4 := ((4128437734374989811 : Rat) / 100000000000000000000), LB := ((13668203057698447 : Rat) / 5000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546476619743303571921 : Rat) / 200000000000000000000), R := ((34171005577566964317 : Rat) / 12500000000000000000), D0 := ((34171005577566964317 : Rat) / 12500000000000000000), D1 := ((11452566827566964317 : Rat) / 12500000000000000000), D2 := ((2196818077566964317 : Rat) / 12500000000000000000), D3 := ((3373103470982142963 : Rat) / 50000000000000000000), D4 := ((7997405970982122471 : Rat) / 200000000000000000000), LB := ((1073952667514061 : Rat) / 500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((34171005577566964317 : Rat) / 12500000000000000000), R := ((546995558738839286223 : Rat) / 200000000000000000000), D0 := ((546995558738839286223 : Rat) / 200000000000000000000), D1 := ((183500538738839286223 : Rat) / 200000000000000000000), D2 := ((35408558738839286223 : Rat) / 200000000000000000000), D3 := ((13751883381696429003 : Rat) / 200000000000000000000), D4 := ((193448411830356633 : Rat) / 5000000000000000000), LB := ((17673449175139577 : Rat) / 10000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546995558738839286223 : Rat) / 200000000000000000000), R := ((273627514118303571687 : Rat) / 100000000000000000000), D0 := ((273627514118303571687 : Rat) / 100000000000000000000), D1 := ((91880004118303571687 : Rat) / 100000000000000000000), D2 := ((17834014118303571687 : Rat) / 100000000000000000000), D3 := ((7005676439732143077 : Rat) / 100000000000000000000), D4 := ((7478466975446408169 : Rat) / 200000000000000000000), LB := ((399948523338689 : Rat) / 250000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((273627514118303571687 : Rat) / 100000000000000000000), R := ((21900579909375000021 : Rat) / 8000000000000000000), D0 := ((21900579909375000021 : Rat) / 8000000000000000000), D1 := ((7360779109375000021 : Rat) / 8000000000000000000), D2 := ((1437099909375000021 : Rat) / 8000000000000000000), D3 := ((2854164475446428661 : Rat) / 40000000000000000000), D4 := ((3609498738839275509 : Rat) / 100000000000000000000), LB := ((41356351512363 : Rat) / 25000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21900579909375000021 : Rat) / 8000000000000000000), R := ((136943491808035714419 : Rat) / 50000000000000000000), D0 := ((136943491808035714419 : Rat) / 50000000000000000000), D1 := ((46069736808035714419 : Rat) / 50000000000000000000), D2 := ((9046741808035714419 : Rat) / 50000000000000000000), D3 := ((1816286484375000057 : Rat) / 25000000000000000000), D4 := ((6959527979910693867 : Rat) / 200000000000000000000), LB := ((9705192363135551 : Rat) / 5000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((136943491808035714419 : Rat) / 50000000000000000000), R := ((548033436729910714827 : Rat) / 200000000000000000000), D0 := ((548033436729910714827 : Rat) / 200000000000000000000), D1 := ((184538416729910714827 : Rat) / 200000000000000000000), D2 := ((36446436729910714827 : Rat) / 200000000000000000000), D3 := ((14789761372767857607 : Rat) / 200000000000000000000), D4 := ((1675014620535709179 : Rat) / 50000000000000000000), LB := ((2471949457934497 : Rat) / 1000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((548033436729910714827 : Rat) / 200000000000000000000), R := ((274146453113839285989 : Rat) / 100000000000000000000), D0 := ((274146453113839285989 : Rat) / 100000000000000000000), D1 := ((92398943113839285989 : Rat) / 100000000000000000000), D2 := ((18352953113839285989 : Rat) / 100000000000000000000), D3 := ((7524615435267857379 : Rat) / 100000000000000000000), D4 := ((1288117796874995913 : Rat) / 40000000000000000000), LB := ((3260490537865701 : Rat) / 1000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((274146453113839285989 : Rat) / 100000000000000000000), R := ((548552375725446429129 : Rat) / 200000000000000000000), D0 := ((548552375725446429129 : Rat) / 200000000000000000000), D1 := ((185057355725446429129 : Rat) / 200000000000000000000), D2 := ((36965375725446429129 : Rat) / 200000000000000000000), D3 := ((15308700368303571909 : Rat) / 200000000000000000000), D4 := ((3090559743303561207 : Rat) / 100000000000000000000), LB := ((1728850131932691 : Rat) / 400000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((548552375725446429129 : Rat) / 200000000000000000000), R := ((13720296130580357157 : Rat) / 5000000000000000000), D0 := ((13720296130580357157 : Rat) / 5000000000000000000), D1 := ((4632920630580357157 : Rat) / 5000000000000000000), D2 := ((930621130580357157 : Rat) / 5000000000000000000), D3 := ((778408493303571453 : Rat) / 10000000000000000000), D4 := ((5921649988839265263 : Rat) / 200000000000000000000), LB := ((28372968068196003 : Rat) / 5000000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((13720296130580357157 : Rat) / 5000000000000000000), R := ((274665392109375000291 : Rat) / 100000000000000000000), D0 := ((274665392109375000291 : Rat) / 100000000000000000000), D1 := ((92917882109375000291 : Rat) / 100000000000000000000), D2 := ((18871892109375000291 : Rat) / 100000000000000000000), D3 := ((8043554430803571681 : Rat) / 100000000000000000000), D4 := ((353886280691963007 : Rat) / 12500000000000000000), LB := ((7131772441004991 : Rat) / 2500000000000000000) },
  { w1 := ((1816500300933297 : Rat) / 2000000000000000), w2 := ((5949247682841493 : Rat) / 125000000000000000), w3 := ((7428468025484497 : Rat) / 50000000000000000), w4 := ((3455732069190453 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26662183767857142861 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((274665392109375000291 : Rat) / 100000000000000000000), R := ((137462430803571428721 : Rat) / 50000000000000000000), D0 := ((137462430803571428721 : Rat) / 50000000000000000000), D1 := ((46588675803571428721 : Rat) / 50000000000000000000), D2 := ((9565680803571428721 : Rat) / 50000000000000000000), D3 := ((259469497767857151 : Rat) / 3125000000000000000), D4 := ((514324149553569381 : Rat) / 20000000000000000000), LB := ((45602062883527 : Rat) / 6250000000000000) }
]

def block349RightChunk000L : Rat := ((1749053125000000003 : Rat) / 1000000000000000000)
def block349RightChunk000R : Rat := ((137462430803571428721 : Rat) / 50000000000000000000)

def block349RightChunk000Certificate : Bool :=
  allBoxesValid block349RightChunk000 &&
  coversFromBool block349RightChunk000 block349RightChunk000L block349RightChunk000R

theorem block349RightChunk000Certificate_eq_true :
    block349RightChunk000Certificate = true := by
  native_decide

def block349RightChainCertificate : Bool :=
  decide (
    block349RightL = ((1749053125000000003 : Rat) / 1000000000000000000) /\
    ((137462430803571428721 : Rat) / 50000000000000000000) = block349RightR)

theorem block349RightChainCertificate_eq_true :
    block349RightChainCertificate = true := by
  native_decide

def block349LeftBoxCount : Nat := boxCount block349LeftBoxes
def block349RightBoxCount : Nat := 59

def block349_rational_certificate : Prop :=
    block349LeftCertificate = true /\
    block349RightChainCertificate = true /\
    block349RightChunk000Certificate = true

theorem block349_rational_certificate_proof :
    block349_rational_certificate := by
  exact ⟨block349LeftCertificate_eq_true, block349RightChainCertificate_eq_true, block349RightChunk000Certificate_eq_true⟩

end Block349
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block349

open Set

def block349W1 : Rat := ((1816500300933297 : Rat) / 2000000000000000)
def block349W2 : Rat := ((5949247682841493 : Rat) / 125000000000000000)
def block349W3 : Rat := ((7428468025484497 : Rat) / 50000000000000000)
def block349W4 : Rat := ((3455732069190453 : Rat) / 25000000000000000)
def block349S1 : Rat := ((18174751 : Rat) / 10000000)
def block349S2 : Rat := ((511587 : Rat) / 200000)
def block349S3 : Rat := ((26662183767857142861 : Rat) / 10000000000000000000)
def block349S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block349V (y : ℝ) : ℝ :=
  ratPotential block349W1 block349W2 block349W3 block349W4 block349S1 block349S2 block349S3 block349S4 y

def block349LeftParamsCertificate : Bool :=
  allBoxesSameParams block349LeftBoxes block349W1 block349W2 block349W3 block349W4 block349S1 block349S2 block349S3 block349S4

theorem block349LeftParamsCertificate_eq_true :
    block349LeftParamsCertificate = true := by
  native_decide

theorem block349_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block349LeftL : ℝ) (block349LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block349S1 : ℝ))
    (hy2ne : y ≠ (block349S2 : ℝ))
    (hy3ne : y ≠ (block349S3 : ℝ))
    (hy4ne : y ≠ (block349S4 : ℝ)) :
    0 < block349V y := by
  have hcert := block349LeftCertificate_eq_true
  unfold block349LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block349LeftBoxes) (lo := block349LeftL) (hi := block349LeftR)
    (w1 := block349W1) (w2 := block349W2) (w3 := block349W3) (w4 := block349W4)
    (s1 := block349S1) (s2 := block349S2) (s3 := block349S3) (s4 := block349S4)
    hboxes hcover block349LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block349RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block349RightChunk000 block349W1 block349W2 block349W3 block349W4 block349S1 block349S2 block349S3 block349S4

theorem block349RightChunk000ParamsCertificate_eq_true :
    block349RightChunk000ParamsCertificate = true := by
  native_decide

theorem block349_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block349RightChunk000L : ℝ) (block349RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block349S1 : ℝ))
    (hy2ne : y ≠ (block349S2 : ℝ))
    (hy3ne : y ≠ (block349S3 : ℝ))
    (hy4ne : y ≠ (block349S4 : ℝ)) :
    0 < block349V y := by
  have hcert := block349RightChunk000Certificate_eq_true
  unfold block349RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block349RightChunk000) (lo := block349RightChunk000L) (hi := block349RightChunk000R)
    (w1 := block349W1) (w2 := block349W2) (w3 := block349W3) (w4 := block349W4)
    (s1 := block349S1) (s2 := block349S2) (s3 := block349S3) (s4 := block349S4)
    hboxes hcover block349RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block349_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block349RightL : ℝ) (block349RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block349S1 : ℝ))
    (hy2ne : y ≠ (block349S2 : ℝ))
    (hy3ne : y ≠ (block349S3 : ℝ))
    (hy4ne : y ≠ (block349S4 : ℝ)) :
    0 < block349V y := by
  have hL : (block349RightChunk000L : ℝ) = (block349RightL : ℝ) := by
    norm_num [block349RightChunk000L, block349RightL]
  have hR : (block349RightChunk000R : ℝ) = (block349RightR : ℝ) := by
    norm_num [block349RightChunk000R, block349RightR]
  have hyc : y ∈ Icc (block349RightChunk000L : ℝ) (block349RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block349_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block349_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block349LeftL : ℝ) (block349LeftR : ℝ) →
    y ≠ 0 → y ≠ (block349S1 : ℝ) → y ≠ (block349S2 : ℝ) →
    y ≠ (block349S3 : ℝ) → y ≠ (block349S4 : ℝ) → 0 < block349V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block349RightL : ℝ) (block349RightR : ℝ) →
    y ≠ 0 → y ≠ (block349S1 : ℝ) → y ≠ (block349S2 : ℝ) →
    y ≠ (block349S3 : ℝ) → y ≠ (block349S4 : ℝ) → 0 < block349V y)

theorem block349_reallog_certificate_proof :
    block349_reallog_certificate := by
  exact ⟨block349_left_V_pos, block349_right_V_pos⟩

end Block349
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block349.block349V
#check Erdos1038Lean.M1817475.Block349.block349_left_V_pos
#check Erdos1038Lean.M1817475.Block349.block349_right_V_pos
#check Erdos1038Lean.M1817475.Block349.block349_reallog_certificate_proof
