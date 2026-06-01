/-
Self-contained Lean4Web paste file.
Block 96 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block096

def block096LeftL : Rat := ((39925618303571428613 : Rat) / 50000000000000000000)
def block096LeftR : Rat := ((1247981026785714287 : Rat) / 1562500000000000000)
def block096RightL : Rat := ((89925618303571428613 : Rat) / 50000000000000000000)
def block096RightR : Rat := ((4372981026785714287 : Rat) / 1562500000000000000)

def block096LeftBoxes : List RatBox := [
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((39925618303571428613 : Rat) / 50000000000000000000), R := ((1247981026785714287 : Rat) / 1562500000000000000), D0 := ((1247981026785714287 : Rat) / 1562500000000000000), D1 := ((50948136696428571387 : Rat) / 50000000000000000000), D2 := ((87971131696428571387 : Rat) / 50000000000000000000), D3 := ((372575427594866071 : Rat) / 195312500000000000), D4 := ((99298910446428566387 : Rat) / 50000000000000000000), LB := ((2999125510488407 : Rat) / 500000000000000000) }
]

def block096LeftCertificate : Bool :=
  allBoxesValid block096LeftBoxes &&
  coversFromBool block096LeftBoxes block096LeftL block096LeftR

theorem block096LeftCertificate_eq_true :
    block096LeftCertificate = true := by
  native_decide

def block096RightChunk000 : List RatBox := [
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((89925618303571428613 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((948136696428571387 : Rat) / 50000000000000000000), D2 := ((37971131696428571387 : Rat) / 50000000000000000000), D3 := ((177262927594866071 : Rat) / 195312500000000000), D4 := ((49298910446428566387 : Rat) / 50000000000000000000), LB := ((15637921294699817 : Rat) / 2000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((44431172767857142789 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((6692899273259123 : Rat) / 5000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((25919675267857142789 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((5295343141627161 : Rat) / 10000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((16663926517857142789 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((535532638112531 : Rat) / 2000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((12036052142857142789 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((126480040200427 : Rat) / 6250000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((518995177767857142789 : Rat) / 200000000000000000000), D0 := ((518995177767857142789 : Rat) / 200000000000000000000), D1 := ((155500157767857142789 : Rat) / 200000000000000000000), D2 := ((7408177767857142789 : Rat) / 200000000000000000000), D3 := ((7408177767857142789 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((1255727037357679 : Rat) / 400000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((518995177767857142789 : Rat) / 200000000000000000000), R := ((1045398533303571428367 : Rat) / 400000000000000000000), D0 := ((1045398533303571428367 : Rat) / 400000000000000000000), D1 := ((318408493303571428367 : Rat) / 400000000000000000000), D2 := ((22224533303571428367 : Rat) / 400000000000000000000), D3 := ((22224533303571428367 : Rat) / 200000000000000000000), D4 := ((37902937232142837211 : Rat) / 200000000000000000000), LB := ((1073117145541591 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1045398533303571428367 : Rat) / 400000000000000000000), R := ((2098205244374999999523 : Rat) / 800000000000000000000), D0 := ((2098205244374999999523 : Rat) / 800000000000000000000), D1 := ((644225164374999999523 : Rat) / 800000000000000000000), D2 := ((51857244374999999523 : Rat) / 800000000000000000000), D3 := ((7408177767857142789 : Rat) / 80000000000000000000), D4 := ((68397696696428531633 : Rat) / 400000000000000000000), LB := ((14592492028389359 : Rat) / 2500000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2098205244374999999523 : Rat) / 800000000000000000000), R := ((840763733303571428367 : Rat) / 320000000000000000000), D0 := ((840763733303571428367 : Rat) / 320000000000000000000), D1 := ((259171701303571428367 : Rat) / 320000000000000000000), D2 := ((22224533303571428367 : Rat) / 320000000000000000000), D3 := ((66673599910714285101 : Rat) / 800000000000000000000), D4 := ((129387215624999920477 : Rat) / 800000000000000000000), LB := ((10155064269925851 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((840763733303571428367 : Rat) / 320000000000000000000), R := ((263201677767857142789 : Rat) / 100000000000000000000), D0 := ((263201677767857142789 : Rat) / 100000000000000000000), D1 := ((81454167767857142789 : Rat) / 100000000000000000000), D2 := ((7408177767857142789 : Rat) / 100000000000000000000), D3 := ((125939022053571427413 : Rat) / 1600000000000000000000), D4 := ((50273250696428539633 : Rat) / 320000000000000000000), LB := ((2988235713355769 : Rat) / 500000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((263201677767857142789 : Rat) / 100000000000000000000), R := ((4218635022053571427413 : Rat) / 1600000000000000000000), D0 := ((4218635022053571427413 : Rat) / 1600000000000000000000), D1 := ((1310674862053571427413 : Rat) / 1600000000000000000000), D2 := ((125939022053571427413 : Rat) / 1600000000000000000000), D3 := ((7408177767857142789 : Rat) / 100000000000000000000), D4 := ((15247379732142847211 : Rat) / 100000000000000000000), LB := ((22819795807779153 : Rat) / 10000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4218635022053571427413 : Rat) / 1600000000000000000000), R := ((1688935644374999999523 : Rat) / 640000000000000000000), D0 := ((1688935644374999999523 : Rat) / 640000000000000000000), D1 := ((525751580374999999523 : Rat) / 640000000000000000000), D2 := ((51857244374999999523 : Rat) / 640000000000000000000), D3 := ((22224533303571428367 : Rat) / 320000000000000000000), D4 := ((236549897946428412587 : Rat) / 1600000000000000000000), LB := ((1488974986557673 : Rat) / 250000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1688935644374999999523 : Rat) / 640000000000000000000), R := ((2113021599910714285101 : Rat) / 800000000000000000000), D0 := ((2113021599910714285101 : Rat) / 800000000000000000000), D1 := ((659041519910714285101 : Rat) / 800000000000000000000), D2 := ((66673599910714285101 : Rat) / 800000000000000000000), D3 := ((214837155267857140881 : Rat) / 3200000000000000000000), D4 := ((93138323624999936477 : Rat) / 640000000000000000000), LB := ((4565515394412911 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2113021599910714285101 : Rat) / 800000000000000000000), R := ((8459494577410714283193 : Rat) / 3200000000000000000000), D0 := ((8459494577410714283193 : Rat) / 3200000000000000000000), D1 := ((2643574257410714283193 : Rat) / 3200000000000000000000), D2 := ((274102577410714283193 : Rat) / 3200000000000000000000), D3 := ((51857244374999999523 : Rat) / 800000000000000000000), D4 := ((114570860089285634899 : Rat) / 800000000000000000000), LB := ((3325435973801083 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8459494577410714283193 : Rat) / 3200000000000000000000), R := ((4233451377589285712991 : Rat) / 1600000000000000000000), D0 := ((4233451377589285712991 : Rat) / 1600000000000000000000), D1 := ((1325491217589285712991 : Rat) / 1600000000000000000000), D2 := ((140755377589285712991 : Rat) / 1600000000000000000000), D3 := ((200020799732142855303 : Rat) / 3200000000000000000000), D4 := ((450875262589285396807 : Rat) / 3200000000000000000000), LB := ((2243248455234159 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4233451377589285712991 : Rat) / 1600000000000000000000), R := ((8474310932946428568771 : Rat) / 3200000000000000000000), D0 := ((8474310932946428568771 : Rat) / 3200000000000000000000), D1 := ((2658390612946428568771 : Rat) / 3200000000000000000000), D2 := ((288918932946428568771 : Rat) / 3200000000000000000000), D3 := ((96306310982142856257 : Rat) / 1600000000000000000000), D4 := ((221733542410714127009 : Rat) / 1600000000000000000000), LB := ((2654616668588683 : Rat) / 2000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8474310932946428568771 : Rat) / 3200000000000000000000), R := ((212042977767857142789 : Rat) / 80000000000000000000), D0 := ((212042977767857142789 : Rat) / 80000000000000000000), D1 := ((66644969767857142789 : Rat) / 80000000000000000000), D2 := ((7408177767857142789 : Rat) / 80000000000000000000), D3 := ((7408177767857142789 : Rat) / 128000000000000000000), D4 := ((436058907053571111229 : Rat) / 3200000000000000000000), LB := ((5868532034484231 : Rat) / 10000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((212042977767857142789 : Rat) / 80000000000000000000), R := ((8489127288482142854349 : Rat) / 3200000000000000000000), D0 := ((8489127288482142854349 : Rat) / 3200000000000000000000), D1 := ((2673206968482142854349 : Rat) / 3200000000000000000000), D2 := ((303735288482142854349 : Rat) / 3200000000000000000000), D3 := ((22224533303571428367 : Rat) / 400000000000000000000), D4 := ((10716268232142849211 : Rat) / 80000000000000000000), LB := ((642772858007179 : Rat) / 20000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8489127288482142854349 : Rat) / 3200000000000000000000), R := ((16985662754732142851487 : Rat) / 6400000000000000000000), D0 := ((16985662754732142851487 : Rat) / 6400000000000000000000), D1 := ((5353822114732142851487 : Rat) / 6400000000000000000000), D2 := ((614878754732142851487 : Rat) / 6400000000000000000000), D3 := ((170388088660714284147 : Rat) / 3200000000000000000000), D4 := ((421242551517856825651 : Rat) / 3200000000000000000000), LB := ((304226500641841 : Rat) / 100000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16985662754732142851487 : Rat) / 6400000000000000000000), R := ((4248267733124999998569 : Rat) / 1600000000000000000000), D0 := ((4248267733124999998569 : Rat) / 1600000000000000000000), D1 := ((1340307573124999998569 : Rat) / 1600000000000000000000), D2 := ((155571733124999998569 : Rat) / 1600000000000000000000), D3 := ((66673599910714285101 : Rat) / 1280000000000000000000), D4 := ((835076925267856508513 : Rat) / 6400000000000000000000), LB := ((3671432837173 : Rat) / 1250000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4248267733124999998569 : Rat) / 1600000000000000000000), R := ((3400095822053571427413 : Rat) / 1280000000000000000000), D0 := ((3400095822053571427413 : Rat) / 1280000000000000000000), D1 := ((1073727694053571427413 : Rat) / 1280000000000000000000), D2 := ((125939022053571427413 : Rat) / 1280000000000000000000), D3 := ((81489955446428570679 : Rat) / 1600000000000000000000), D4 := ((206917186874999841431 : Rat) / 1600000000000000000000), LB := ((28862613711279073 : Rat) / 10000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3400095822053571427413 : Rat) / 1280000000000000000000), R := ((8503943644017857139927 : Rat) / 3200000000000000000000), D0 := ((8503943644017857139927 : Rat) / 3200000000000000000000), D1 := ((2688023324017857139927 : Rat) / 3200000000000000000000), D2 := ((318551644017857139927 : Rat) / 3200000000000000000000), D3 := ((318551644017857139927 : Rat) / 6400000000000000000000), D4 := ((164052113946428444587 : Rat) / 1280000000000000000000), LB := ((1445734403319271 : Rat) / 500000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8503943644017857139927 : Rat) / 3200000000000000000000), R := ((17015295465803571422643 : Rat) / 6400000000000000000000), D0 := ((17015295465803571422643 : Rat) / 6400000000000000000000), D1 := ((5383454825803571422643 : Rat) / 6400000000000000000000), D2 := ((644511465803571422643 : Rat) / 6400000000000000000000), D3 := ((155571733124999998569 : Rat) / 3200000000000000000000), D4 := ((406426195982142540073 : Rat) / 3200000000000000000000), LB := ((147737358720193 : Rat) / 50000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17015295465803571422643 : Rat) / 6400000000000000000000), R := ((2127837955446428570679 : Rat) / 800000000000000000000), D0 := ((2127837955446428570679 : Rat) / 800000000000000000000), D1 := ((673857875446428570679 : Rat) / 800000000000000000000), D2 := ((81489955446428570679 : Rat) / 800000000000000000000), D3 := ((303735288482142854349 : Rat) / 6400000000000000000000), D4 := ((805444214196427937357 : Rat) / 6400000000000000000000), LB := ((3078206300263897 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2127837955446428570679 : Rat) / 800000000000000000000), R := ((17030111821339285708221 : Rat) / 6400000000000000000000), D0 := ((17030111821339285708221 : Rat) / 6400000000000000000000), D1 := ((5398271181339285708221 : Rat) / 6400000000000000000000), D2 := ((659327821339285708221 : Rat) / 6400000000000000000000), D3 := ((7408177767857142789 : Rat) / 160000000000000000000), D4 := ((99754504553571349321 : Rat) / 800000000000000000000), LB := ((3264099716120461 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17030111821339285708221 : Rat) / 6400000000000000000000), R := ((1703751999910714285101 : Rat) / 640000000000000000000), D0 := ((1703751999910714285101 : Rat) / 640000000000000000000), D1 := ((540567935910714285101 : Rat) / 640000000000000000000), D2 := ((66673599910714285101 : Rat) / 640000000000000000000), D3 := ((288918932946428568771 : Rat) / 6400000000000000000000), D4 := ((790627858660713651779 : Rat) / 6400000000000000000000), LB := ((4393548369191827 : Rat) / 1250000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1703751999910714285101 : Rat) / 640000000000000000000), R := ((4263084088660714284147 : Rat) / 1600000000000000000000), D0 := ((4263084088660714284147 : Rat) / 1600000000000000000000), D1 := ((1355123928660714284147 : Rat) / 1600000000000000000000), D2 := ((170388088660714284147 : Rat) / 1600000000000000000000), D3 := ((140755377589285712991 : Rat) / 3200000000000000000000), D4 := ((78321968089285650899 : Rat) / 640000000000000000000), LB := ((4989361826411853 : Rat) / 10000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4263084088660714284147 : Rat) / 1600000000000000000000), R := ((8533576355089285711083 : Rat) / 3200000000000000000000), D0 := ((8533576355089285711083 : Rat) / 3200000000000000000000), D1 := ((2717656035089285711083 : Rat) / 3200000000000000000000), D2 := ((348184355089285711083 : Rat) / 3200000000000000000000), D3 := ((66673599910714285101 : Rat) / 1600000000000000000000), D4 := ((192100831339285555853 : Rat) / 1600000000000000000000), LB := ((6785850480145461 : Rat) / 5000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8533576355089285711083 : Rat) / 3200000000000000000000), R := ((533811533303571428367 : Rat) / 200000000000000000000), D0 := ((533811533303571428367 : Rat) / 200000000000000000000), D1 := ((170316513303571428367 : Rat) / 200000000000000000000), D2 := ((22224533303571428367 : Rat) / 200000000000000000000), D3 := ((125939022053571427413 : Rat) / 3200000000000000000000), D4 := ((376793484910713968917 : Rat) / 3200000000000000000000), LB := ((504258879135977 : Rat) / 200000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((533811533303571428367 : Rat) / 200000000000000000000), R := ((8548392710624999996661 : Rat) / 3200000000000000000000), D0 := ((8548392710624999996661 : Rat) / 3200000000000000000000), D1 := ((2732472390624999996661 : Rat) / 3200000000000000000000), D2 := ((363000710624999996661 : Rat) / 3200000000000000000000), D3 := ((7408177767857142789 : Rat) / 200000000000000000000), D4 := ((23086581696428551633 : Rat) / 200000000000000000000), LB := ((4020420517993839 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8548392710624999996661 : Rat) / 3200000000000000000000), R := ((171116017767857142789 : Rat) / 64000000000000000000), D0 := ((171116017767857142789 : Rat) / 64000000000000000000), D1 := ((54797611367857142789 : Rat) / 64000000000000000000), D2 := ((7408177767857142789 : Rat) / 64000000000000000000), D3 := ((22224533303571428367 : Rat) / 640000000000000000000), D4 := ((361977129374999683339 : Rat) / 3200000000000000000000), LB := ((2944468267226663 : Rat) / 500000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((171116017767857142789 : Rat) / 64000000000000000000), R := ((2142654310982142856257 : Rat) / 800000000000000000000), D0 := ((2142654310982142856257 : Rat) / 800000000000000000000), D1 := ((688674230982142856257 : Rat) / 800000000000000000000), D2 := ((96306310982142856257 : Rat) / 800000000000000000000), D3 := ((51857244374999999523 : Rat) / 1600000000000000000000), D4 := ((7091379032142850811 : Rat) / 64000000000000000000), LB := ((15939004129061907 : Rat) / 10000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2142654310982142856257 : Rat) / 800000000000000000000), R := ((4292716799732142855303 : Rat) / 1600000000000000000000), D0 := ((4292716799732142855303 : Rat) / 1600000000000000000000), D1 := ((1384756639732142855303 : Rat) / 1600000000000000000000), D2 := ((200020799732142855303 : Rat) / 1600000000000000000000), D3 := ((22224533303571428367 : Rat) / 800000000000000000000), D4 := ((84938149017857063743 : Rat) / 800000000000000000000), LB := ((762573356611651 : Rat) / 100000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4292716799732142855303 : Rat) / 1600000000000000000000), R := ((1075031244374999999523 : Rat) / 400000000000000000000), D0 := ((1075031244374999999523 : Rat) / 400000000000000000000), D1 := ((348041204374999999523 : Rat) / 400000000000000000000), D2 := ((51857244374999999523 : Rat) / 400000000000000000000), D3 := ((7408177767857142789 : Rat) / 320000000000000000000), D4 := ((162468120267856984697 : Rat) / 1600000000000000000000), LB := ((8034605599718053 : Rat) / 500000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1075031244374999999523 : Rat) / 400000000000000000000), R := ((431494133303571428367 : Rat) / 160000000000000000000), D0 := ((431494133303571428367 : Rat) / 160000000000000000000), D1 := ((140698117303571428367 : Rat) / 160000000000000000000), D2 := ((22224533303571428367 : Rat) / 160000000000000000000), D3 := ((7408177767857142789 : Rat) / 400000000000000000000), D4 := ((38764985624999960477 : Rat) / 400000000000000000000), LB := ((14935314362484131 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((431494133303571428367 : Rat) / 160000000000000000000), R := ((135304927767857142789 : Rat) / 50000000000000000000), D0 := ((135304927767857142789 : Rat) / 50000000000000000000), D1 := ((44431172767857142789 : Rat) / 50000000000000000000), D2 := ((7408177767857142789 : Rat) / 50000000000000000000), D3 := ((7408177767857142789 : Rat) / 800000000000000000000), D4 := ((14024358696428555633 : Rat) / 160000000000000000000), LB := ((1149291320012551 : Rat) / 20000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((135304927767857142789 : Rat) / 50000000000000000000), R := ((1086359023124999994523 : Rat) / 400000000000000000000), D0 := ((1086359023124999994523 : Rat) / 400000000000000000000), D1 := ((359368983124999994523 : Rat) / 400000000000000000000), D2 := ((63185023124999994523 : Rat) / 400000000000000000000), D3 := ((3919600982142852211 : Rat) / 400000000000000000000), D4 := ((3919600982142852211 : Rat) / 50000000000000000000), LB := ((4838490462033013 : Rat) / 100000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1086359023124999994523 : Rat) / 400000000000000000000), R := ((2176637647232142841257 : Rat) / 800000000000000000000), D0 := ((2176637647232142841257 : Rat) / 800000000000000000000), D1 := ((722657567232142841257 : Rat) / 800000000000000000000), D2 := ((130289647232142841257 : Rat) / 800000000000000000000), D3 := ((11758802946428556633 : Rat) / 800000000000000000000), D4 := ((27437206874999965477 : Rat) / 400000000000000000000), LB := ((203889487175209 : Rat) / 6250000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2176637647232142841257 : Rat) / 800000000000000000000), R := ((545139312053571423367 : Rat) / 200000000000000000000), D0 := ((545139312053571423367 : Rat) / 200000000000000000000), D1 := ((181644292053571423367 : Rat) / 200000000000000000000), D2 := ((33552312053571423367 : Rat) / 200000000000000000000), D3 := ((3919600982142852211 : Rat) / 200000000000000000000), D4 := ((50954812767857078743 : Rat) / 800000000000000000000), LB := ((3398585720388897 : Rat) / 250000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((545139312053571423367 : Rat) / 200000000000000000000), R := ((2184476849196428545679 : Rat) / 800000000000000000000), D0 := ((2184476849196428545679 : Rat) / 800000000000000000000), D1 := ((730496769196428545679 : Rat) / 800000000000000000000), D2 := ((138128849196428545679 : Rat) / 800000000000000000000), D3 := ((3919600982142852211 : Rat) / 160000000000000000000), D4 := ((11758802946428556633 : Rat) / 200000000000000000000), LB := ((15796278765006777 : Rat) / 50000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2184476849196428545679 : Rat) / 800000000000000000000), R := ((4372873299374999943569 : Rat) / 1600000000000000000000), D0 := ((4372873299374999943569 : Rat) / 1600000000000000000000), D1 := ((1464913139374999943569 : Rat) / 1600000000000000000000), D2 := ((280177299374999943569 : Rat) / 1600000000000000000000), D3 := ((43115610803571374321 : Rat) / 1600000000000000000000), D4 := ((43115610803571374321 : Rat) / 800000000000000000000), LB := ((798480770922283 : Rat) / 200000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4372873299374999943569 : Rat) / 1600000000000000000000), R := ((218839645017857139789 : Rat) / 80000000000000000000), D0 := ((218839645017857139789 : Rat) / 80000000000000000000), D1 := ((73441637017857139789 : Rat) / 80000000000000000000), D2 := ((14204845017857139789 : Rat) / 80000000000000000000), D3 := ((11758802946428556633 : Rat) / 400000000000000000000), D4 := ((82311620624999896431 : Rat) / 1600000000000000000000), LB := ((38264742756910497 : Rat) / 100000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((218839645017857139789 : Rat) / 80000000000000000000), R := ((8757505401696428443771 : Rat) / 3200000000000000000000), D0 := ((8757505401696428443771 : Rat) / 3200000000000000000000), D1 := ((2941585081696428443771 : Rat) / 3200000000000000000000), D2 := ((572113401696428443771 : Rat) / 3200000000000000000000), D3 := ((3919600982142852211 : Rat) / 128000000000000000000), D4 := ((3919600982142852211 : Rat) / 80000000000000000000), LB := ((4679353267947467 : Rat) / 1250000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8757505401696428443771 : Rat) / 3200000000000000000000), R := ((4380712501339285647991 : Rat) / 1600000000000000000000), D0 := ((4380712501339285647991 : Rat) / 1600000000000000000000), D1 := ((1472752341339285647991 : Rat) / 1600000000000000000000), D2 := ((288016501339285647991 : Rat) / 1600000000000000000000), D3 := ((50954812767857078743 : Rat) / 1600000000000000000000), D4 := ((152864438303571236229 : Rat) / 3200000000000000000000), LB := ((414063350284051 : Rat) / 156250000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4380712501339285647991 : Rat) / 1600000000000000000000), R := ((8765344603660714148193 : Rat) / 3200000000000000000000), D0 := ((8765344603660714148193 : Rat) / 3200000000000000000000), D1 := ((2949424283660714148193 : Rat) / 3200000000000000000000), D2 := ((579952603660714148193 : Rat) / 3200000000000000000000), D3 := ((105829226517857009697 : Rat) / 3200000000000000000000), D4 := ((74472418660714192009 : Rat) / 1600000000000000000000), LB := ((1120286161890513 : Rat) / 625000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8765344603660714148193 : Rat) / 3200000000000000000000), R := ((2192316051160714250101 : Rat) / 800000000000000000000), D0 := ((2192316051160714250101 : Rat) / 800000000000000000000), D1 := ((738335971160714250101 : Rat) / 800000000000000000000), D2 := ((145968051160714250101 : Rat) / 800000000000000000000), D3 := ((27437206874999965477 : Rat) / 800000000000000000000), D4 := ((145025236339285531807 : Rat) / 3200000000000000000000), LB := ((5850507874635147 : Rat) / 5000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2192316051160714250101 : Rat) / 800000000000000000000), R := ((1754636761124999970523 : Rat) / 640000000000000000000), D0 := ((1754636761124999970523 : Rat) / 640000000000000000000), D1 := ((591452697124999970523 : Rat) / 640000000000000000000), D2 := ((117558361124999970523 : Rat) / 640000000000000000000), D3 := ((113668428482142714119 : Rat) / 3200000000000000000000), D4 := ((35276408839285669899 : Rat) / 800000000000000000000), LB := ((195889011402689 : Rat) / 250000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1754636761124999970523 : Rat) / 640000000000000000000), R := ((4388551703303571352413 : Rat) / 1600000000000000000000), D0 := ((4388551703303571352413 : Rat) / 1600000000000000000000), D1 := ((1480591543303571352413 : Rat) / 1600000000000000000000), D2 := ((295855703303571352413 : Rat) / 1600000000000000000000), D3 := ((11758802946428556633 : Rat) / 320000000000000000000), D4 := ((27437206874999965477 : Rat) / 640000000000000000000), LB := ((793442221348889 : Rat) / 1250000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4388551703303571352413 : Rat) / 1600000000000000000000), R := ((8781023007589285557037 : Rat) / 3200000000000000000000), D0 := ((8781023007589285557037 : Rat) / 3200000000000000000000), D1 := ((2965102687589285557037 : Rat) / 3200000000000000000000), D2 := ((595631007589285557037 : Rat) / 3200000000000000000000), D3 := ((121507630446428418541 : Rat) / 3200000000000000000000), D4 := ((66633216696428487587 : Rat) / 1600000000000000000000), LB := ((1453845040146673 : Rat) / 2000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8781023007589285557037 : Rat) / 3200000000000000000000), R := ((274529456517857137789 : Rat) / 100000000000000000000), D0 := ((274529456517857137789 : Rat) / 100000000000000000000), D1 := ((92781946517857137789 : Rat) / 100000000000000000000), D2 := ((18735956517857137789 : Rat) / 100000000000000000000), D3 := ((3919600982142852211 : Rat) / 100000000000000000000), D4 := ((129346832410714122963 : Rat) / 3200000000000000000000), LB := ((1330740781802231 : Rat) / 1250000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((274529456517857137789 : Rat) / 100000000000000000000), R := ((8788862209553571261459 : Rat) / 3200000000000000000000), D0 := ((8788862209553571261459 : Rat) / 3200000000000000000000), D1 := ((2972941889553571261459 : Rat) / 3200000000000000000000), D2 := ((603470209553571261459 : Rat) / 3200000000000000000000), D3 := ((129346832410714122963 : Rat) / 3200000000000000000000), D4 := ((3919600982142852211 : Rat) / 100000000000000000000), LB := ((3307257820957421 : Rat) / 2000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8788862209553571261459 : Rat) / 3200000000000000000000), R := ((879278181053571411367 : Rat) / 320000000000000000000), D0 := ((879278181053571411367 : Rat) / 320000000000000000000), D1 := ((297686149053571411367 : Rat) / 320000000000000000000), D2 := ((60738981053571411367 : Rat) / 320000000000000000000), D3 := ((66633216696428487587 : Rat) / 1600000000000000000000), D4 := ((121507630446428418541 : Rat) / 3200000000000000000000), LB := ((25012873848441197 : Rat) / 10000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((879278181053571411367 : Rat) / 320000000000000000000), R := ((8796701411517856965881 : Rat) / 3200000000000000000000), D0 := ((8796701411517856965881 : Rat) / 3200000000000000000000), D1 := ((2980781091517856965881 : Rat) / 3200000000000000000000), D2 := ((611309411517856965881 : Rat) / 3200000000000000000000), D3 := ((27437206874999965477 : Rat) / 640000000000000000000), D4 := ((11758802946428556633 : Rat) / 320000000000000000000), LB := ((452037271384903 : Rat) / 125000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8796701411517856965881 : Rat) / 3200000000000000000000), R := ((2200155253124999954523 : Rat) / 800000000000000000000), D0 := ((2200155253124999954523 : Rat) / 800000000000000000000), D1 := ((746175173124999954523 : Rat) / 800000000000000000000), D2 := ((153807253124999954523 : Rat) / 800000000000000000000), D3 := ((35276408839285669899 : Rat) / 800000000000000000000), D4 := ((113668428482142714119 : Rat) / 3200000000000000000000), LB := ((2504488498762003 : Rat) / 500000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2200155253124999954523 : Rat) / 800000000000000000000), R := ((4404230107232142761257 : Rat) / 1600000000000000000000), D0 := ((4404230107232142761257 : Rat) / 1600000000000000000000), D1 := ((1496269947232142761257 : Rat) / 1600000000000000000000), D2 := ((311534107232142761257 : Rat) / 1600000000000000000000), D3 := ((74472418660714192009 : Rat) / 1600000000000000000000), D4 := ((27437206874999965477 : Rat) / 800000000000000000000), LB := ((797856778517847 : Rat) / 500000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4404230107232142761257 : Rat) / 1600000000000000000000), R := ((1102037427053571403367 : Rat) / 400000000000000000000), D0 := ((1102037427053571403367 : Rat) / 400000000000000000000), D1 := ((375047387053571403367 : Rat) / 400000000000000000000), D2 := ((78863427053571403367 : Rat) / 400000000000000000000), D3 := ((3919600982142852211 : Rat) / 80000000000000000000), D4 := ((50954812767857078743 : Rat) / 1600000000000000000000), LB := ((2995018893564849 : Rat) / 500000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1102037427053571403367 : Rat) / 400000000000000000000), R := ((441598891017857131789 : Rat) / 160000000000000000000), D0 := ((441598891017857131789 : Rat) / 160000000000000000000), D1 := ((150802875017857131789 : Rat) / 160000000000000000000), D2 := ((32329291017857131789 : Rat) / 160000000000000000000), D3 := ((43115610803571374321 : Rat) / 800000000000000000000), D4 := ((11758802946428556633 : Rat) / 400000000000000000000), LB := ((2060050108679601 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((441598891017857131789 : Rat) / 160000000000000000000), R := ((552978514017857127789 : Rat) / 200000000000000000000), D0 := ((552978514017857127789 : Rat) / 200000000000000000000), D1 := ((189483494017857127789 : Rat) / 200000000000000000000), D2 := ((41391514017857127789 : Rat) / 200000000000000000000), D3 := ((11758802946428556633 : Rat) / 200000000000000000000), D4 := ((3919600982142852211 : Rat) / 160000000000000000000), LB := ((18689314186926653 : Rat) / 1000000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((552978514017857127789 : Rat) / 200000000000000000000), R := ((1109876629017857107789 : Rat) / 400000000000000000000), D0 := ((1109876629017857107789 : Rat) / 400000000000000000000), D1 := ((382886589017857107789 : Rat) / 400000000000000000000), D2 := ((86702629017857107789 : Rat) / 400000000000000000000), D3 := ((27437206874999965477 : Rat) / 400000000000000000000), D4 := ((3919600982142852211 : Rat) / 200000000000000000000), LB := ((2596788705630837 : Rat) / 100000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1109876629017857107789 : Rat) / 400000000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((3919600982142852211 : Rat) / 50000000000000000000), D4 := ((3919600982142852211 : Rat) / 400000000000000000000), LB := ((3159247493743289 : Rat) / 25000000000000000) },
  { w1 := ((424023315958443 : Rat) / 200000000000000), w2 := (0 : Rat), w3 := ((350950255184761 : Rat) / 5000000000000000), w4 := ((4868142456372647 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135304927767857142789 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((4372981026785714287 : Rat) / 1562500000000000000), D0 := ((4372981026785714287 : Rat) / 1562500000000000000), D1 := ((1533176183035714287 : Rat) / 1562500000000000000), D2 := ((376207589285714287 : Rat) / 1562500000000000000), D3 := ((926093017857142879 : Rat) / 10000000000000000000), D4 := ((88858013392857773 : Rat) / 6250000000000000000), LB := ((779871551362693 : Rat) / 125000000000000000) }
]

def block096RightChunk000L : Rat := ((89925618303571428613 : Rat) / 50000000000000000000)
def block096RightChunk000R : Rat := ((4372981026785714287 : Rat) / 1562500000000000000)

def block096RightChunk000Certificate : Bool :=
  allBoxesValid block096RightChunk000 &&
  coversFromBool block096RightChunk000 block096RightChunk000L block096RightChunk000R

theorem block096RightChunk000Certificate_eq_true :
    block096RightChunk000Certificate = true := by
  native_decide

def block096RightChainCertificate : Bool :=
  decide (
    block096RightL = ((89925618303571428613 : Rat) / 50000000000000000000) /\
    ((4372981026785714287 : Rat) / 1562500000000000000) = block096RightR)

theorem block096RightChainCertificate_eq_true :
    block096RightChainCertificate = true := by
  native_decide

def block096LeftBoxCount : Nat := boxCount block096LeftBoxes
def block096RightBoxCount : Nat := 61

def block096_rational_certificate : Prop :=
    block096LeftCertificate = true /\
    block096RightChainCertificate = true /\
    block096RightChunk000Certificate = true

theorem block096_rational_certificate_proof :
    block096_rational_certificate := by
  exact ⟨block096LeftCertificate_eq_true, block096RightChainCertificate_eq_true, block096RightChunk000Certificate_eq_true⟩

end Block096
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block096

open Set

def block096W1 : Rat := ((424023315958443 : Rat) / 200000000000000)
def block096W2 : Rat := (0 : Rat)
def block096W3 : Rat := ((350950255184761 : Rat) / 5000000000000000)
def block096W4 : Rat := ((4868142456372647 : Rat) / 25000000000000000)
def block096S1 : Rat := ((18174751 : Rat) / 10000000)
def block096S2 : Rat := ((511587 : Rat) / 200000)
def block096S3 : Rat := ((135304927767857142789 : Rat) / 50000000000000000000)
def block096S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block096V (y : ℝ) : ℝ :=
  ratPotential block096W1 block096W2 block096W3 block096W4 block096S1 block096S2 block096S3 block096S4 y

def block096LeftParamsCertificate : Bool :=
  allBoxesSameParams block096LeftBoxes block096W1 block096W2 block096W3 block096W4 block096S1 block096S2 block096S3 block096S4

theorem block096LeftParamsCertificate_eq_true :
    block096LeftParamsCertificate = true := by
  native_decide

theorem block096_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block096LeftL : ℝ) (block096LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block096S1 : ℝ))
    (hy2ne : y ≠ (block096S2 : ℝ))
    (hy3ne : y ≠ (block096S3 : ℝ))
    (hy4ne : y ≠ (block096S4 : ℝ)) :
    0 < block096V y := by
  have hcert := block096LeftCertificate_eq_true
  unfold block096LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block096LeftBoxes) (lo := block096LeftL) (hi := block096LeftR)
    (w1 := block096W1) (w2 := block096W2) (w3 := block096W3) (w4 := block096W4)
    (s1 := block096S1) (s2 := block096S2) (s3 := block096S3) (s4 := block096S4)
    hboxes hcover block096LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block096RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block096RightChunk000 block096W1 block096W2 block096W3 block096W4 block096S1 block096S2 block096S3 block096S4

theorem block096RightChunk000ParamsCertificate_eq_true :
    block096RightChunk000ParamsCertificate = true := by
  native_decide

theorem block096_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block096RightChunk000L : ℝ) (block096RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block096S1 : ℝ))
    (hy2ne : y ≠ (block096S2 : ℝ))
    (hy3ne : y ≠ (block096S3 : ℝ))
    (hy4ne : y ≠ (block096S4 : ℝ)) :
    0 < block096V y := by
  have hcert := block096RightChunk000Certificate_eq_true
  unfold block096RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block096RightChunk000) (lo := block096RightChunk000L) (hi := block096RightChunk000R)
    (w1 := block096W1) (w2 := block096W2) (w3 := block096W3) (w4 := block096W4)
    (s1 := block096S1) (s2 := block096S2) (s3 := block096S3) (s4 := block096S4)
    hboxes hcover block096RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block096_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block096RightL : ℝ) (block096RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block096S1 : ℝ))
    (hy2ne : y ≠ (block096S2 : ℝ))
    (hy3ne : y ≠ (block096S3 : ℝ))
    (hy4ne : y ≠ (block096S4 : ℝ)) :
    0 < block096V y := by
  have hL : (block096RightChunk000L : ℝ) = (block096RightL : ℝ) := by
    norm_num [block096RightChunk000L, block096RightL]
  have hR : (block096RightChunk000R : ℝ) = (block096RightR : ℝ) := by
    norm_num [block096RightChunk000R, block096RightR]
  have hyc : y ∈ Icc (block096RightChunk000L : ℝ) (block096RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block096_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block096_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block096LeftL : ℝ) (block096LeftR : ℝ) →
    y ≠ 0 → y ≠ (block096S1 : ℝ) → y ≠ (block096S2 : ℝ) →
    y ≠ (block096S3 : ℝ) → y ≠ (block096S4 : ℝ) → 0 < block096V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block096RightL : ℝ) (block096RightR : ℝ) →
    y ≠ 0 → y ≠ (block096S1 : ℝ) → y ≠ (block096S2 : ℝ) →
    y ≠ (block096S3 : ℝ) → y ≠ (block096S4 : ℝ) → 0 < block096V y)

theorem block096_reallog_certificate_proof :
    block096_reallog_certificate := by
  exact ⟨block096_left_V_pos, block096_right_V_pos⟩

end Block096
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block096.block096V
#check Erdos1038Lean.M1817475.Block096.block096_left_V_pos
#check Erdos1038Lean.M1817475.Block096.block096_right_V_pos
#check Erdos1038Lean.M1817475.Block096.block096_reallog_certificate_proof
