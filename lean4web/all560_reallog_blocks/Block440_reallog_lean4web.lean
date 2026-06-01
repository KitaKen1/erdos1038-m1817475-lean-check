/-
Self-contained Lean4Web paste file.
Block 440 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block440

def block440LeftL : Rat := ((36563171875000000189 : Rat) / 50000000000000000000)
def block440LeftR : Rat := ((914323660714285719 : Rat) / 1250000000000000000)
def block440RightL : Rat := ((86563171875000000189 : Rat) / 50000000000000000000)
def block440RightR : Rat := ((3414323660714285719 : Rat) / 1250000000000000000)

def block440LeftBoxes : List RatBox := [
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((36563171875000000189 : Rat) / 50000000000000000000), R := ((914323660714285719 : Rat) / 1250000000000000000), D0 := ((914323660714285719 : Rat) / 1250000000000000000), D1 := ((54310583124999999811 : Rat) / 50000000000000000000), D2 := ((91333578124999999811 : Rat) / 50000000000000000000), D3 := ((47484389107142857097 : Rat) / 25000000000000000000), D4 := ((102661356874999994811 : Rat) / 50000000000000000000), LB := ((24826792361825403 : Rat) / 10000000000000000000) }
]

def block440LeftCertificate : Bool :=
  allBoxesValid block440LeftBoxes &&
  coversFromBool block440LeftBoxes block440LeftL block440LeftR

theorem block440LeftCertificate_eq_true :
    block440LeftCertificate = true := by
  native_decide

def block440RightChunk000 : List RatBox := [
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86563171875000000189 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((4310583124999999811 : Rat) / 50000000000000000000), D2 := ((41333578124999999811 : Rat) / 50000000000000000000), D3 := ((22484389107142857097 : Rat) / 25000000000000000000), D4 := ((52661356874999994811 : Rat) / 50000000000000000000), LB := ((4838831392564153 : Rat) / 5000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((40658195089285714383 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((5383915917740667 : Rat) / 12500000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((31402446339285714383 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((6536251055436919 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((22146697589285714383 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((5443880321946047 : Rat) / 125000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((722279413 : Rat) / 320000000), D0 := ((722279413 : Rat) / 320000000), D1 := ((140687381 : Rat) / 320000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((19832760401785714383 : Rat) / 50000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((8132954777567 : Rat) / 200000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((722279413 : Rat) / 320000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((96259787 : Rat) / 320000000), D3 := ((18675791808035714383 : Rat) / 50000000000000000000), D4 := ((5273674093749999 : Rat) / 10000000000000000), LB := ((20748924607674343 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((17518823214285714383 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((19384819740079287 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((1481581821 : Rat) / 640000000), D0 := ((1481581821 : Rat) / 640000000), D1 := ((318397757 : Rat) / 640000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((16361854620535714383 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((9466786145830589 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1481581821 : Rat) / 640000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((155496579 : Rat) / 640000000), D3 := ((15783370323660714383 : Rat) / 50000000000000000000), D4 := ((4695189796874999 : Rat) / 10000000000000000), LB := ((680344768389643 : Rat) / 200000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((2985377439 : Rat) / 1280000000), D0 := ((2985377439 : Rat) / 1280000000), D1 := ((659009311 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((15204886026785714383 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((954430911873849 : Rat) / 125000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2985377439 : Rat) / 1280000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((288779361 : Rat) / 1280000000), D3 := ((14915643878348214383 : Rat) / 50000000000000000000), D4 := ((4521644507812499 : Rat) / 10000000000000000), LB := ((13116098129204931 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((3000186637 : Rat) / 1280000000), D0 := ((3000186637 : Rat) / 1280000000), D1 := ((673818509 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((14626401729910714383 : Rat) / 50000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((30733644072757013 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3000186637 : Rat) / 1280000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((273970163 : Rat) / 1280000000), D3 := ((14337159581473214383 : Rat) / 50000000000000000000), D4 := ((4405947648437499 : Rat) / 10000000000000000), LB := ((11196276055609397 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((6022587071 : Rat) / 2560000000), D0 := ((6022587071 : Rat) / 2560000000), D1 := ((273970163 : Rat) / 512000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14047917433035714383 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((1997062272291801 : Rat) / 500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6022587071 : Rat) / 2560000000), R := ((602999167 : Rat) / 256000000), D0 := ((602999167 : Rat) / 256000000), D1 := ((688627707 : Rat) / 1280000000), D2 := ((525726529 : Rat) / 2560000000), D3 := ((13903296358816964383 : Rat) / 50000000000000000000), D4 := ((4319175003906249 : Rat) / 10000000000000000), LB := ((15970710289123363 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((602999167 : Rat) / 256000000), R := ((6037396269 : Rat) / 2560000000), D0 := ((6037396269 : Rat) / 2560000000), D1 := ((1384660013 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 256000000), D3 := ((13758675284598214383 : Rat) / 50000000000000000000), D4 := ((4290250789062499 : Rat) / 10000000000000000), LB := ((3064650676760667 : Rat) / 1250000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6037396269 : Rat) / 2560000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((510917331 : Rat) / 2560000000), D3 := ((13614054210379464383 : Rat) / 50000000000000000000), D4 := ((4261326574218749 : Rat) / 10000000000000000), LB := ((8837200264829037 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((6052205467 : Rat) / 2560000000), D0 := ((6052205467 : Rat) / 2560000000), D1 := ((1399469211 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((13469433136160714383 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((5709540543222813 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6052205467 : Rat) / 2560000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((496108133 : Rat) / 2560000000), D3 := ((13324812061941964383 : Rat) / 50000000000000000000), D4 := ((4203478144531249 : Rat) / 10000000000000000), LB := ((5757606561694467 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((1213402933 : Rat) / 512000000), D0 := ((1213402933 : Rat) / 512000000), D1 := ((1414278409 : Rat) / 2560000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((13180190987723214383 : Rat) / 50000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((6966310574656187 : Rat) / 100000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1213402933 : Rat) / 512000000), R := ((12141433929 : Rat) / 5120000000), D0 := ((12141433929 : Rat) / 5120000000), D1 := ((2835961417 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 512000000), D3 := ((13035569913504464383 : Rat) / 50000000000000000000), D4 := ((4145629714843749 : Rat) / 10000000000000000), LB := ((18671646446645207 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12141433929 : Rat) / 5120000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((955193271 : Rat) / 5120000000), D3 := ((12963259376395089383 : Rat) / 50000000000000000000), D4 := ((2065583803710937 : Rat) / 5000000000000000), LB := ((16628756125807581 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((12156243127 : Rat) / 5120000000), D0 := ((12156243127 : Rat) / 5120000000), D1 := ((570154123 : Rat) / 1024000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((12890948839285714383 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((294814191817791 : Rat) / 200000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12156243127 : Rat) / 5120000000), R := ((6081823863 : Rat) / 2560000000), D0 := ((6081823863 : Rat) / 2560000000), D1 := ((1429087607 : Rat) / 2560000000), D2 := ((940384073 : Rat) / 5120000000), D3 := ((12818638302176339383 : Rat) / 50000000000000000000), D4 := ((1025560848144531 : Rat) / 2500000000000000), LB := ((2601693257004517 : Rat) / 2000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6081823863 : Rat) / 2560000000), R := ((486842093 : Rat) / 204800000), D0 := ((486842093 : Rat) / 204800000), D1 := ((2865579813 : Rat) / 5120000000), D2 := ((466489737 : Rat) / 2560000000), D3 := ((12746327765066964383 : Rat) / 50000000000000000000), D4 := ((4087781285156249 : Rat) / 10000000000000000), LB := ((11433007064004241 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((486842093 : Rat) / 204800000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 40960000), D3 := ((12674017227957589383 : Rat) / 50000000000000000000), D4 := ((2036659588867187 : Rat) / 5000000000000000), LB := ((5007667310493111 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((12185861523 : Rat) / 5120000000), D0 := ((12185861523 : Rat) / 5120000000), D1 := ((2880389011 : Rat) / 5120000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((12601706690848214383 : Rat) / 50000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((8756473923964003 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12185861523 : Rat) / 5120000000), R := ((6096633061 : Rat) / 2560000000), D0 := ((6096633061 : Rat) / 2560000000), D1 := ((288779361 : Rat) / 512000000), D2 := ((910765677 : Rat) / 5120000000), D3 := ((12529396153738839383 : Rat) / 50000000000000000000), D4 := ((31596835647583 : Rat) / 78125000000000), LB := ((7657472666513371 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6096633061 : Rat) / 2560000000), R := ((12200670721 : Rat) / 5120000000), D0 := ((12200670721 : Rat) / 5120000000), D1 := ((2895198209 : Rat) / 5120000000), D2 := ((451680539 : Rat) / 2560000000), D3 := ((12457085616629464383 : Rat) / 50000000000000000000), D4 := ((4029932855468749 : Rat) / 10000000000000000), LB := ((1679850433025723 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12200670721 : Rat) / 5120000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((895956479 : Rat) / 5120000000), D3 := ((12384775079520089383 : Rat) / 50000000000000000000), D4 := ((2007735374023437 : Rat) / 5000000000000000), LB := ((594335567259921 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((12215479919 : Rat) / 5120000000), D0 := ((12215479919 : Rat) / 5120000000), D1 := ((2910007407 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((12312464542410714383 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((42643625610711 : Rat) / 80000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12215479919 : Rat) / 5120000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((881147281 : Rat) / 5120000000), D3 := ((12240154005301339383 : Rat) / 50000000000000000000), D4 := ((996636633300781 : Rat) / 2500000000000000), LB := ((195273508051641 : Rat) / 400000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((12230289117 : Rat) / 5120000000), D0 := ((12230289117 : Rat) / 5120000000), D1 := ((584963321 : Rat) / 1024000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((12167843468191964383 : Rat) / 50000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((1149669437213903 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12230289117 : Rat) / 5120000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((866338083 : Rat) / 5120000000), D3 := ((12095532931082589383 : Rat) / 50000000000000000000), D4 := ((1978811159179687 : Rat) / 5000000000000000), LB := ((5602709567316573 : Rat) / 12500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((2449019663 : Rat) / 1024000000), D0 := ((2449019663 : Rat) / 1024000000), D1 := ((2939625803 : Rat) / 5120000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((12023222393973214383 : Rat) / 50000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((4533528016215371 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2449019663 : Rat) / 1024000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((170305777 : Rat) / 1024000000), D3 := ((11950911856863839383 : Rat) / 50000000000000000000), D4 := ((491087262939453 : Rat) / 1250000000000000), LB := ((23770031500243427 : Rat) / 50000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((12259907513 : Rat) / 5120000000), D0 := ((12259907513 : Rat) / 5120000000), D1 := ((2954435001 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((11878601319754464383 : Rat) / 50000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((2572438712809197 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12259907513 : Rat) / 5120000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((836719687 : Rat) / 5120000000), D3 := ((11806290782645089383 : Rat) / 50000000000000000000), D4 := ((1949886944335937 : Rat) / 5000000000000000), LB := ((570744437992779 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((12274716711 : Rat) / 5120000000), D0 := ((12274716711 : Rat) / 5120000000), D1 := ((2969244199 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((11733980245535714383 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((6443038846599969 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12274716711 : Rat) / 5120000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((821910489 : Rat) / 5120000000), D3 := ((11661669708426339383 : Rat) / 50000000000000000000), D4 := ((967712418457031 : Rat) / 2500000000000000), LB := ((7353021855686509 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((12289525909 : Rat) / 5120000000), D0 := ((12289525909 : Rat) / 5120000000), D1 := ((2984053397 : Rat) / 5120000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((11589359171316964383 : Rat) / 50000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((4219392227100757 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12289525909 : Rat) / 5120000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((807101291 : Rat) / 5120000000), D3 := ((11517048634207589383 : Rat) / 50000000000000000000), D4 := ((1920962729492187 : Rat) / 5000000000000000), LB := ((242543709952657 : Rat) / 250000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((12304335107 : Rat) / 5120000000), D0 := ((12304335107 : Rat) / 5120000000), D1 := ((599772519 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((11444738097098214383 : Rat) / 50000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((5571683433285013 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12304335107 : Rat) / 5120000000), R := ((6155869853 : Rat) / 2560000000), D0 := ((6155869853 : Rat) / 2560000000), D1 := ((1503133597 : Rat) / 2560000000), D2 := ((792292093 : Rat) / 5120000000), D3 := ((11372427559988839383 : Rat) / 50000000000000000000), D4 := ((238312577758789 : Rat) / 625000000000000), LB := ((3191281299834703 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6155869853 : Rat) / 2560000000), R := ((2463828861 : Rat) / 1024000000), D0 := ((2463828861 : Rat) / 1024000000), D1 := ((3013671793 : Rat) / 5120000000), D2 := ((392443747 : Rat) / 2560000000), D3 := ((11300117022879464383 : Rat) / 50000000000000000000), D4 := ((3798539136718749 : Rat) / 10000000000000000), LB := ((7284270829016129 : Rat) / 5000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2463828861 : Rat) / 1024000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((155496579 : Rat) / 1024000000), D3 := ((11227806485770089383 : Rat) / 50000000000000000000), D4 := ((1892038514648437 : Rat) / 5000000000000000), LB := ((4138792053087273 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((12333953503 : Rat) / 5120000000), D0 := ((12333953503 : Rat) / 5120000000), D1 := ((3028480991 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((11155495948660714383 : Rat) / 50000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((18726591352105637 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12333953503 : Rat) / 5120000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((762673697 : Rat) / 5120000000), D3 := ((11083185411551339383 : Rat) / 50000000000000000000), D4 := ((938788203613281 : Rat) / 2500000000000000), LB := ((263555411576237 : Rat) / 125000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11010874874441964383 : Rat) / 50000000000000000000), D4 := ((3740690707031249 : Rat) / 10000000000000000), LB := ((4830850534676967 : Rat) / 20000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((10866253800223214383 : Rat) / 50000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((2039776442078721 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((10721632726004464383 : Rat) / 50000000000000000000), D4 := ((3682842277343749 : Rat) / 10000000000000000), LB := ((1834401144191599 : Rat) / 1250000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((10577011651785714383 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((4395681949432989 : Rat) / 2000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((10432390577566964383 : Rat) / 50000000000000000000), D4 := ((3624993847656249 : Rat) / 10000000000000000), LB := ((7521013796150909 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((10287769503348214383 : Rat) / 50000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((9752050525174069 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((10143148429129464383 : Rat) / 50000000000000000000), D4 := ((3567145417968749 : Rat) / 10000000000000000), LB := ((12191913591050839 : Rat) / 2500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((9998527354910714383 : Rat) / 50000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((18165480627531927 : Rat) / 10000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((9709285206473214383 : Rat) / 50000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((529048289912357 : Rat) / 125000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((9420043058035714383 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((280486118801207 : Rat) / 40000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((9130800909598214383 : Rat) / 50000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((10173267024463889 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((8841558761160714383 : Rat) / 50000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((2884224081202133 : Rat) / 500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((8263074464285714383 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((7145215726693521 : Rat) / 500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((7684590167410714383 : Rat) / 50000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((24696979712769823 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((7106105870535714383 : Rat) / 50000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((220914441659959 : Rat) / 10000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((5949137276785714383 : Rat) / 50000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((6576856501506849 : Rat) / 250000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((131531950089285714383 : Rat) / 50000000000000000000), D0 := ((131531950089285714383 : Rat) / 50000000000000000000), D1 := ((40658195089285714383 : Rat) / 50000000000000000000), D2 := ((3635200089285714383 : Rat) / 50000000000000000000), D3 := ((3635200089285714383 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((2220480861581017 : Rat) / 20000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((131531950089285714383 : Rat) / 50000000000000000000), R := ((268104896517857143143 : Rat) / 100000000000000000000), D0 := ((268104896517857143143 : Rat) / 100000000000000000000), D1 := ((86357386517857143143 : Rat) / 100000000000000000000), D2 := ((12311396517857143143 : Rat) / 100000000000000000000), D3 := ((5040996339285714377 : Rat) / 100000000000000000000), D4 := ((7692578660714280617 : Rat) / 50000000000000000000), LB := ((10007595686848747 : Rat) / 50000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((268104896517857143143 : Rat) / 100000000000000000000), R := ((541250789375000000663 : Rat) / 200000000000000000000), D0 := ((541250789375000000663 : Rat) / 200000000000000000000), D1 := ((177755769375000000663 : Rat) / 200000000000000000000), D2 := ((29663789375000000663 : Rat) / 200000000000000000000), D3 := ((15122989017857143131 : Rat) / 200000000000000000000), D4 := ((10344160982142846857 : Rat) / 100000000000000000000), LB := ((7224635082392303 : Rat) / 100000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((541250789375000000663 : Rat) / 200000000000000000000), R := ((1087542575089285715703 : Rat) / 400000000000000000000), D0 := ((1087542575089285715703 : Rat) / 400000000000000000000), D1 := ((360552535089285715703 : Rat) / 400000000000000000000), D2 := ((64368575089285715703 : Rat) / 400000000000000000000), D3 := ((35286974375000000639 : Rat) / 400000000000000000000), D4 := ((15647325624999979337 : Rat) / 200000000000000000000), LB := ((30027572508302153 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1087542575089285715703 : Rat) / 400000000000000000000), R := ((2180126146517857145783 : Rat) / 800000000000000000000), D0 := ((2180126146517857145783 : Rat) / 800000000000000000000), D1 := ((726146066517857145783 : Rat) / 800000000000000000000), D2 := ((133778146517857145783 : Rat) / 800000000000000000000), D3 := ((15122989017857143131 : Rat) / 160000000000000000000), D4 := ((26253654910714244297 : Rat) / 400000000000000000000), LB := ((3553869823236487 : Rat) / 250000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2180126146517857145783 : Rat) / 800000000000000000000), R := ((4365293289375000005943 : Rat) / 1600000000000000000000), D0 := ((4365293289375000005943 : Rat) / 1600000000000000000000), D1 := ((1457333129375000005943 : Rat) / 1600000000000000000000), D2 := ((272597289375000005943 : Rat) / 1600000000000000000000), D3 := ((156270886517857145687 : Rat) / 1600000000000000000000), D4 := ((47466313482142774217 : Rat) / 800000000000000000000), LB := ((7836095111197539 : Rat) / 1000000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4365293289375000005943 : Rat) / 1600000000000000000000), R := ((8735627575089285726263 : Rat) / 3200000000000000000000), D0 := ((8735627575089285726263 : Rat) / 3200000000000000000000), D1 := ((2919707255089285726263 : Rat) / 3200000000000000000000), D2 := ((550235575089285726263 : Rat) / 3200000000000000000000), D3 := ((317582769375000005751 : Rat) / 3200000000000000000000), D4 := ((89891630624999834057 : Rat) / 1600000000000000000000), LB := ((2539078582578791 : Rat) / 500000000000000000) },
  { w1 := ((6263230733922749 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((16007180896167447 : Rat) / 50000000000000000), w4 := ((3687511510628841 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131531950089285714383 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8735627575089285726263 : Rat) / 3200000000000000000000), R := ((3414323660714285719 : Rat) / 1250000000000000000), D0 := ((3414323660714285719 : Rat) / 1250000000000000000), D1 := ((1142479785714285719 : Rat) / 1250000000000000000), D2 := ((216904910714285719 : Rat) / 1250000000000000000), D3 := ((5040996339285714377 : Rat) / 50000000000000000000), D4 := ((174742264910713953737 : Rat) / 3200000000000000000000), LB := ((1489171760514843 : Rat) / 3125000000000000000) }
]

def block440RightChunk000L : Rat := ((86563171875000000189 : Rat) / 50000000000000000000)
def block440RightChunk000R : Rat := ((3414323660714285719 : Rat) / 1250000000000000000)

def block440RightChunk000Certificate : Bool :=
  allBoxesValid block440RightChunk000 &&
  coversFromBool block440RightChunk000 block440RightChunk000L block440RightChunk000R

theorem block440RightChunk000Certificate_eq_true :
    block440RightChunk000Certificate = true := by
  native_decide

def block440RightChainCertificate : Bool :=
  decide (
    block440RightL = ((86563171875000000189 : Rat) / 50000000000000000000) /\
    ((3414323660714285719 : Rat) / 1250000000000000000) = block440RightR)

theorem block440RightChainCertificate_eq_true :
    block440RightChainCertificate = true := by
  native_decide

def block440LeftBoxCount : Nat := boxCount block440LeftBoxes
def block440RightBoxCount : Nat := 72

def block440_rational_certificate : Prop :=
    block440LeftCertificate = true /\
    block440RightChainCertificate = true /\
    block440RightChunk000Certificate = true

theorem block440_rational_certificate_proof :
    block440_rational_certificate := by
  exact ⟨block440LeftCertificate_eq_true, block440RightChainCertificate_eq_true, block440RightChunk000Certificate_eq_true⟩

end Block440
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block440

open Set

def block440W1 : Rat := ((6263230733922749 : Rat) / 10000000000000000)
def block440W2 : Rat := (0 : Rat)
def block440W3 : Rat := ((16007180896167447 : Rat) / 50000000000000000)
def block440W4 : Rat := ((3687511510628841 : Rat) / 50000000000000000)
def block440S1 : Rat := ((18174751 : Rat) / 10000000)
def block440S2 : Rat := ((511587 : Rat) / 200000)
def block440S3 : Rat := ((131531950089285714383 : Rat) / 50000000000000000000)
def block440S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block440V (y : ℝ) : ℝ :=
  ratPotential block440W1 block440W2 block440W3 block440W4 block440S1 block440S2 block440S3 block440S4 y

def block440LeftParamsCertificate : Bool :=
  allBoxesSameParams block440LeftBoxes block440W1 block440W2 block440W3 block440W4 block440S1 block440S2 block440S3 block440S4

theorem block440LeftParamsCertificate_eq_true :
    block440LeftParamsCertificate = true := by
  native_decide

theorem block440_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block440LeftL : ℝ) (block440LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block440S1 : ℝ))
    (hy2ne : y ≠ (block440S2 : ℝ))
    (hy3ne : y ≠ (block440S3 : ℝ))
    (hy4ne : y ≠ (block440S4 : ℝ)) :
    0 < block440V y := by
  have hcert := block440LeftCertificate_eq_true
  unfold block440LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block440LeftBoxes) (lo := block440LeftL) (hi := block440LeftR)
    (w1 := block440W1) (w2 := block440W2) (w3 := block440W3) (w4 := block440W4)
    (s1 := block440S1) (s2 := block440S2) (s3 := block440S3) (s4 := block440S4)
    hboxes hcover block440LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block440RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block440RightChunk000 block440W1 block440W2 block440W3 block440W4 block440S1 block440S2 block440S3 block440S4

theorem block440RightChunk000ParamsCertificate_eq_true :
    block440RightChunk000ParamsCertificate = true := by
  native_decide

theorem block440_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block440RightChunk000L : ℝ) (block440RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block440S1 : ℝ))
    (hy2ne : y ≠ (block440S2 : ℝ))
    (hy3ne : y ≠ (block440S3 : ℝ))
    (hy4ne : y ≠ (block440S4 : ℝ)) :
    0 < block440V y := by
  have hcert := block440RightChunk000Certificate_eq_true
  unfold block440RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block440RightChunk000) (lo := block440RightChunk000L) (hi := block440RightChunk000R)
    (w1 := block440W1) (w2 := block440W2) (w3 := block440W3) (w4 := block440W4)
    (s1 := block440S1) (s2 := block440S2) (s3 := block440S3) (s4 := block440S4)
    hboxes hcover block440RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block440_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block440RightL : ℝ) (block440RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block440S1 : ℝ))
    (hy2ne : y ≠ (block440S2 : ℝ))
    (hy3ne : y ≠ (block440S3 : ℝ))
    (hy4ne : y ≠ (block440S4 : ℝ)) :
    0 < block440V y := by
  have hL : (block440RightChunk000L : ℝ) = (block440RightL : ℝ) := by
    norm_num [block440RightChunk000L, block440RightL]
  have hR : (block440RightChunk000R : ℝ) = (block440RightR : ℝ) := by
    norm_num [block440RightChunk000R, block440RightR]
  have hyc : y ∈ Icc (block440RightChunk000L : ℝ) (block440RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block440_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block440_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block440LeftL : ℝ) (block440LeftR : ℝ) →
    y ≠ 0 → y ≠ (block440S1 : ℝ) → y ≠ (block440S2 : ℝ) →
    y ≠ (block440S3 : ℝ) → y ≠ (block440S4 : ℝ) → 0 < block440V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block440RightL : ℝ) (block440RightR : ℝ) →
    y ≠ 0 → y ≠ (block440S1 : ℝ) → y ≠ (block440S2 : ℝ) →
    y ≠ (block440S3 : ℝ) → y ≠ (block440S4 : ℝ) → 0 < block440V y)

theorem block440_reallog_certificate_proof :
    block440_reallog_certificate := by
  exact ⟨block440_left_V_pos, block440_right_V_pos⟩

end Block440
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block440.block440V
#check Erdos1038Lean.M1817475.Block440.block440_left_V_pos
#check Erdos1038Lean.M1817475.Block440.block440_right_V_pos
#check Erdos1038Lean.M1817475.Block440.block440_reallog_certificate_proof
