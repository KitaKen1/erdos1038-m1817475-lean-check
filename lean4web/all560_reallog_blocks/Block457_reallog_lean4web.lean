/-
Self-contained Lean4Web paste file.
Block 457 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block457

def block457LeftL : Rat := ((18198502232142857241 : Rat) / 25000000000000000000)
def block457LeftR : Rat := ((36406779017857143053 : Rat) / 50000000000000000000)
def block457RightL : Rat := ((43198502232142857241 : Rat) / 25000000000000000000)
def block457RightR : Rat := ((136406779017857143053 : Rat) / 50000000000000000000)

def block457LeftBoxes : List RatBox := [
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18198502232142857241 : Rat) / 25000000000000000000), R := ((36406779017857143053 : Rat) / 50000000000000000000), D0 := ((36406779017857143053 : Rat) / 50000000000000000000), D1 := ((27238375267857142759 : Rat) / 25000000000000000000), D2 := ((45749872767857142759 : Rat) / 25000000000000000000), D3 := ((94802610803571428487 : Rat) / 50000000000000000000), D4 := ((51413762142857140259 : Rat) / 25000000000000000000), LB := ((947093122838593 : Rat) / 250000000000000000) }
]

def block457LeftCertificate : Bool :=
  allBoxesValid block457LeftBoxes &&
  coversFromBool block457LeftBoxes block457LeftL block457LeftR

theorem block457LeftCertificate_eq_true :
    block457LeftCertificate = true := by
  native_decide

def block457RightChunk000 : List RatBox := [
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43198502232142857241 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((2238375267857142759 : Rat) / 25000000000000000000), D2 := ((20749872767857142759 : Rat) / 25000000000000000000), D3 := ((44802610803571428487 : Rat) / 50000000000000000000), D4 := ((26413762142857140259 : Rat) / 25000000000000000000), LB := ((2076491294328211 : Rat) / 2500000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((40325860267857142969 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((35562119985025137 : Rat) / 100000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((33522361 : Rat) / 16000000), D0 := ((33522361 : Rat) / 16000000), D1 := ((22213797 : Rat) / 80000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((31070111517857142969 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((1787629905121439 : Rat) / 10000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33522361 : Rat) / 16000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 16000000), D3 := ((26442237142857142969 : Rat) / 50000000000000000000), D4 := ((6893430124999999 : Rat) / 10000000000000000), LB := ((8111105611318361 : Rat) / 250000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((21814362767857142969 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((9172872265242181 : Rat) / 500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((722279413 : Rat) / 320000000), D0 := ((722279413 : Rat) / 320000000), D1 := ((140687381 : Rat) / 320000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((19500425580357142969 : Rat) / 50000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((5060107429267201 : Rat) / 250000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((722279413 : Rat) / 320000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((96259787 : Rat) / 320000000), D3 := ((18343456986607142969 : Rat) / 50000000000000000000), D4 := ((5273674093749999 : Rat) / 10000000000000000), LB := ((2017304230731619 : Rat) / 500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((1466772623 : Rat) / 640000000), D0 := ((1466772623 : Rat) / 640000000), D1 := ((303588559 : Rat) / 640000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((17186488392857142969 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((9817528391971489 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1466772623 : Rat) / 640000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((170305777 : Rat) / 640000000), D3 := ((16608004095982142969 : Rat) / 50000000000000000000), D4 := ((4926583515624999 : Rat) / 10000000000000000), LB := ((4034760624472181 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((2955759043 : Rat) / 1280000000), D0 := ((2955759043 : Rat) / 1280000000), D1 := ((125878183 : Rat) / 256000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((16029519799107142969 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((415636611615609 : Rat) / 50000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2955759043 : Rat) / 1280000000), R := ((1481581821 : Rat) / 640000000), D0 := ((1481581821 : Rat) / 640000000), D1 := ((318397757 : Rat) / 640000000), D2 := ((318397757 : Rat) / 1280000000), D3 := ((15740277650669642969 : Rat) / 50000000000000000000), D4 := ((4753038226562499 : Rat) / 10000000000000000), LB := ((6044701103851309 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1481581821 : Rat) / 640000000), R := ((2970568241 : Rat) / 1280000000), D0 := ((2970568241 : Rat) / 1280000000), D1 := ((644200113 : Rat) / 1280000000), D2 := ((155496579 : Rat) / 640000000), D3 := ((15451035502232142969 : Rat) / 50000000000000000000), D4 := ((4695189796874999 : Rat) / 10000000000000000), LB := ((9964823063717699 : Rat) / 2500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2970568241 : Rat) / 1280000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((303588559 : Rat) / 1280000000), D3 := ((15161793353794642969 : Rat) / 50000000000000000000), D4 := ((4637341367187499 : Rat) / 10000000000000000), LB := ((21392019964528927 : Rat) / 10000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((2985377439 : Rat) / 1280000000), D0 := ((2985377439 : Rat) / 1280000000), D1 := ((659009311 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((14872551205357142969 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((2538134565172809 : Rat) / 5000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2985377439 : Rat) / 1280000000), R := ((5978159477 : Rat) / 2560000000), D0 := ((5978159477 : Rat) / 2560000000), D1 := ((1325423221 : Rat) / 2560000000), D2 := ((288779361 : Rat) / 1280000000), D3 := ((14583309056919642969 : Rat) / 50000000000000000000), D4 := ((4521644507812499 : Rat) / 10000000000000000), LB := ((17751986342038027 : Rat) / 5000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((5978159477 : Rat) / 2560000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((570154123 : Rat) / 2560000000), D3 := ((14438687982700892969 : Rat) / 50000000000000000000), D4 := ((4492720292968749 : Rat) / 10000000000000000), LB := ((2907700904873467 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((239718747 : Rat) / 102400000), D0 := ((239718747 : Rat) / 102400000), D1 := ((1340232419 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((14294066908482142969 : Rat) / 50000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((5803278362641051 : Rat) / 2500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((239718747 : Rat) / 102400000), R := ((3000186637 : Rat) / 1280000000), D0 := ((3000186637 : Rat) / 1280000000), D1 := ((673818509 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 102400000), D3 := ((14149445834263392969 : Rat) / 50000000000000000000), D4 := ((4434871863281249 : Rat) / 10000000000000000), LB := ((17917609706078683 : Rat) / 10000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3000186637 : Rat) / 1280000000), R := ((6007777873 : Rat) / 2560000000), D0 := ((6007777873 : Rat) / 2560000000), D1 := ((1355041617 : Rat) / 2560000000), D2 := ((273970163 : Rat) / 1280000000), D3 := ((14004824760044642969 : Rat) / 50000000000000000000), D4 := ((4405947648437499 : Rat) / 10000000000000000), LB := ((6598038062638513 : Rat) / 5000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6007777873 : Rat) / 2560000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((540535727 : Rat) / 2560000000), D3 := ((13860203685825892969 : Rat) / 50000000000000000000), D4 := ((4377023433593749 : Rat) / 10000000000000000), LB := ((2263588481948263 : Rat) / 2500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((6022587071 : Rat) / 2560000000), D0 := ((6022587071 : Rat) / 2560000000), D1 := ((273970163 : Rat) / 512000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((13715582611607142969 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((2749278076599297 : Rat) / 5000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6022587071 : Rat) / 2560000000), R := ((602999167 : Rat) / 256000000), D0 := ((602999167 : Rat) / 256000000), D1 := ((688627707 : Rat) / 1280000000), D2 := ((525726529 : Rat) / 2560000000), D3 := ((13570961537388392969 : Rat) / 50000000000000000000), D4 := ((4319175003906249 : Rat) / 10000000000000000), LB := ((79221159214203 : Rat) / 312500000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((602999167 : Rat) / 256000000), R := ((6037396269 : Rat) / 2560000000), D0 := ((6037396269 : Rat) / 2560000000), D1 := ((1384660013 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 256000000), D3 := ((13426340463169642969 : Rat) / 50000000000000000000), D4 := ((4290250789062499 : Rat) / 10000000000000000), LB := ((1066264306910647 : Rat) / 62500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6037396269 : Rat) / 2560000000), R := ((12082197137 : Rat) / 5120000000), D0 := ((12082197137 : Rat) / 5120000000), D1 := ((22213797 : Rat) / 40960000), D2 := ((510917331 : Rat) / 2560000000), D3 := ((13281719388950892969 : Rat) / 50000000000000000000), D4 := ((4261326574218749 : Rat) / 10000000000000000), LB := ((498031391226169 : Rat) / 250000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12082197137 : Rat) / 5120000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((1014430063 : Rat) / 5120000000), D3 := ((13209408851841517969 : Rat) / 50000000000000000000), D4 := ((2123432233398437 : Rat) / 5000000000000000), LB := ((1922692184630967 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((2419401267 : Rat) / 1024000000), D0 := ((2419401267 : Rat) / 1024000000), D1 := ((2791533823 : Rat) / 5120000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((13137098314732142969 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((9343534867777281 : Rat) / 5000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2419401267 : Rat) / 1024000000), R := ((6052205467 : Rat) / 2560000000), D0 := ((6052205467 : Rat) / 2560000000), D1 := ((1399469211 : Rat) / 2560000000), D2 := ((199924173 : Rat) / 1024000000), D3 := ((13064787777622767969 : Rat) / 50000000000000000000), D4 := ((1054485062988281 : Rat) / 2500000000000000), LB := ((18302660998693251 : Rat) / 10000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6052205467 : Rat) / 2560000000), R := ((12111815533 : Rat) / 5120000000), D0 := ((12111815533 : Rat) / 5120000000), D1 := ((2806343021 : Rat) / 5120000000), D2 := ((496108133 : Rat) / 2560000000), D3 := ((12992477240513392969 : Rat) / 50000000000000000000), D4 := ((4203478144531249 : Rat) / 10000000000000000), LB := ((4518669605563467 : Rat) / 2500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12111815533 : Rat) / 5120000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((984811667 : Rat) / 5120000000), D3 := ((12920166703404017969 : Rat) / 50000000000000000000), D4 := ((2094508018554687 : Rat) / 5000000000000000), LB := ((1800412630759661 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((12126624731 : Rat) / 5120000000), D0 := ((12126624731 : Rat) / 5120000000), D1 := ((2821152219 : Rat) / 5120000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((12847856166294642969 : Rat) / 50000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((18092030893311559 : Rat) / 10000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12126624731 : Rat) / 5120000000), R := ((1213402933 : Rat) / 512000000), D0 := ((1213402933 : Rat) / 512000000), D1 := ((1414278409 : Rat) / 2560000000), D2 := ((970002469 : Rat) / 5120000000), D3 := ((12775545629185267969 : Rat) / 50000000000000000000), D4 := ((520011477783203 : Rat) / 1250000000000000), LB := ((9169720395110631 : Rat) / 5000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1213402933 : Rat) / 512000000), R := ((12141433929 : Rat) / 5120000000), D0 := ((12141433929 : Rat) / 5120000000), D1 := ((2835961417 : Rat) / 5120000000), D2 := ((96259787 : Rat) / 512000000), D3 := ((12703235092075892969 : Rat) / 50000000000000000000), D4 := ((4145629714843749 : Rat) / 10000000000000000), LB := ((234342842867101 : Rat) / 125000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12141433929 : Rat) / 5120000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((955193271 : Rat) / 5120000000), D3 := ((12630924554966517969 : Rat) / 50000000000000000000), D4 := ((2065583803710937 : Rat) / 5000000000000000), LB := ((19317085523408647 : Rat) / 10000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((12156243127 : Rat) / 5120000000), D0 := ((12156243127 : Rat) / 5120000000), D1 := ((570154123 : Rat) / 1024000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((12558614017857142969 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((2004953354196419 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12156243127 : Rat) / 5120000000), R := ((6081823863 : Rat) / 2560000000), D0 := ((6081823863 : Rat) / 2560000000), D1 := ((1429087607 : Rat) / 2560000000), D2 := ((940384073 : Rat) / 5120000000), D3 := ((12486303480747767969 : Rat) / 50000000000000000000), D4 := ((1025560848144531 : Rat) / 2500000000000000), LB := ((2094591420116587 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6081823863 : Rat) / 2560000000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((466489737 : Rat) / 2560000000), D3 := ((12413992943638392969 : Rat) / 50000000000000000000), D4 := ((4087781285156249 : Rat) / 10000000000000000), LB := ((5096671044526463 : Rat) / 50000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((6096633061 : Rat) / 2560000000), D0 := ((6096633061 : Rat) / 2560000000), D1 := ((288779361 : Rat) / 512000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((12269371869419642969 : Rat) / 50000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((37263217236443297 : Rat) / 100000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6096633061 : Rat) / 2560000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((451680539 : Rat) / 2560000000), D3 := ((12124750795200892969 : Rat) / 50000000000000000000), D4 := ((4029932855468749 : Rat) / 10000000000000000), LB := ((1776890347666947 : Rat) / 2500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((11980129720982142969 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((11173351096113449 : Rat) / 10000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((11835508646763392969 : Rat) / 50000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((497951204512727 : Rat) / 312500000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((11690887572544642969 : Rat) / 50000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((42804083096281 : Rat) / 20000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((11546266498325892969 : Rat) / 50000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((86212092546459 : Rat) / 31250000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((11401645424107142969 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((34504146927243073 : Rat) / 10000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((11257024349888392969 : Rat) / 50000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((2635227301362379 : Rat) / 625000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((11112403275669642969 : Rat) / 50000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((2034885045180207 : Rat) / 2000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((10823161127232142969 : Rat) / 50000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((29637497165445753 : Rat) / 10000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((10533918978794642969 : Rat) / 50000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((1307415480321773 : Rat) / 250000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((10244676830357142969 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((782820180060547 : Rat) / 100000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((9955434681919642969 : Rat) / 50000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((10773615397560957 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((9666192533482142969 : Rat) / 50000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((3168430021911889 : Rat) / 500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((9087708236607142969 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((710982816403833 : Rat) / 50000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((8509223939732142969 : Rat) / 50000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((23777815629558427 : Rat) / 1000000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((7930739642857142969 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((160153979972651 : Rat) / 7812500000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((6773771049107142969 : Rat) / 50000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((10072597106508907 : Rat) / 200000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((5616802455357142969 : Rat) / 50000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((640525129469893 : Rat) / 10000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((131199615267857142969 : Rat) / 50000000000000000000), D0 := ((131199615267857142969 : Rat) / 50000000000000000000), D1 := ((40325860267857142969 : Rat) / 50000000000000000000), D2 := ((3302865267857142969 : Rat) / 50000000000000000000), D3 := ((3302865267857142969 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((18266138948122557 : Rat) / 100000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((131199615267857142969 : Rat) / 50000000000000000000), R := ((133803197142857143011 : Rat) / 50000000000000000000), D0 := ((133803197142857143011 : Rat) / 50000000000000000000), D1 := ((42929442142857143011 : Rat) / 50000000000000000000), D2 := ((5906447142857143011 : Rat) / 50000000000000000000), D3 := ((1301790937500000021 : Rat) / 25000000000000000000), D4 := ((8024913482142852031 : Rat) / 50000000000000000000), LB := ((11488770607165269 : Rat) / 50000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((133803197142857143011 : Rat) / 50000000000000000000), R := ((16888123510044642879 : Rat) / 6250000000000000000), D0 := ((16888123510044642879 : Rat) / 6250000000000000000), D1 := ((5528904135044642879 : Rat) / 6250000000000000000), D2 := ((901029760044642879 : Rat) / 6250000000000000000), D3 := ((3905372812500000063 : Rat) / 50000000000000000000), D4 := ((5421331607142851989 : Rat) / 50000000000000000000), LB := ((8824503200292971 : Rat) / 100000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16888123510044642879 : Rat) / 6250000000000000000), R := ((54302353419642857217 : Rat) / 20000000000000000000), D0 := ((54302353419642857217 : Rat) / 20000000000000000000), D1 := ((17952851419642857217 : Rat) / 20000000000000000000), D2 := ((3143653419642857217 : Rat) / 20000000000000000000), D3 := ((9112536562500000147 : Rat) / 100000000000000000000), D4 := ((32183911481584781 : Rat) / 390625000000000000), LB := ((3922067645822627 : Rat) / 100000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54302353419642857217 : Rat) / 20000000000000000000), R := ((544325325133928572191 : Rat) / 200000000000000000000), D0 := ((544325325133928572191 : Rat) / 200000000000000000000), D1 := ((180830305133928572191 : Rat) / 200000000000000000000), D2 := ((32738325133928572191 : Rat) / 200000000000000000000), D3 := ((3905372812500000063 : Rat) / 40000000000000000000), D4 := ((1387458080357140783 : Rat) / 20000000000000000000), LB := ((492097580055887 : Rat) / 25000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((544325325133928572191 : Rat) / 200000000000000000000), R := ((1089952441205357144403 : Rat) / 400000000000000000000), D0 := ((1089952441205357144403 : Rat) / 400000000000000000000), D1 := ((362962401205357144403 : Rat) / 400000000000000000000), D2 := ((66778441205357144403 : Rat) / 400000000000000000000), D3 := ((40355519062500000651 : Rat) / 400000000000000000000), D4 := ((12572789866071407809 : Rat) / 200000000000000000000), LB := ((5645700063495837 : Rat) / 500000000000000000) },
  { w1 := ((5776122880916411 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((3426391236583687 : Rat) / 10000000000000000), w4 := ((1551156508761161 : Rat) / 25000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131199615267857142969 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1089952441205357144403 : Rat) / 400000000000000000000), R := ((136406779017857143053 : Rat) / 50000000000000000000), D0 := ((136406779017857143053 : Rat) / 50000000000000000000), D1 := ((45533024017857143053 : Rat) / 50000000000000000000), D2 := ((8510029017857143053 : Rat) / 50000000000000000000), D3 := ((1301790937500000021 : Rat) / 12500000000000000000), D4 := ((23843788794642815597 : Rat) / 400000000000000000000), LB := ((2248734177479339 : Rat) / 5000000000000000000) }
]

def block457RightChunk000L : Rat := ((43198502232142857241 : Rat) / 25000000000000000000)
def block457RightChunk000R : Rat := ((136406779017857143053 : Rat) / 50000000000000000000)

def block457RightChunk000Certificate : Bool :=
  allBoxesValid block457RightChunk000 &&
  coversFromBool block457RightChunk000 block457RightChunk000L block457RightChunk000R

theorem block457RightChunk000Certificate_eq_true :
    block457RightChunk000Certificate = true := by
  native_decide

def block457RightChainCertificate : Bool :=
  decide (
    block457RightL = ((43198502232142857241 : Rat) / 25000000000000000000) /\
    ((136406779017857143053 : Rat) / 50000000000000000000) = block457RightR)

theorem block457RightChainCertificate_eq_true :
    block457RightChainCertificate = true := by
  native_decide

def block457LeftBoxCount : Nat := boxCount block457LeftBoxes
def block457RightBoxCount : Nat := 62

def block457_rational_certificate : Prop :=
    block457LeftCertificate = true /\
    block457RightChainCertificate = true /\
    block457RightChunk000Certificate = true

theorem block457_rational_certificate_proof :
    block457_rational_certificate := by
  exact ⟨block457LeftCertificate_eq_true, block457RightChainCertificate_eq_true, block457RightChunk000Certificate_eq_true⟩

end Block457
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block457

open Set

def block457W1 : Rat := ((5776122880916411 : Rat) / 10000000000000000)
def block457W2 : Rat := (0 : Rat)
def block457W3 : Rat := ((3426391236583687 : Rat) / 10000000000000000)
def block457W4 : Rat := ((1551156508761161 : Rat) / 25000000000000000)
def block457S1 : Rat := ((18174751 : Rat) / 10000000)
def block457S2 : Rat := ((511587 : Rat) / 200000)
def block457S3 : Rat := ((131199615267857142969 : Rat) / 50000000000000000000)
def block457S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block457V (y : ℝ) : ℝ :=
  ratPotential block457W1 block457W2 block457W3 block457W4 block457S1 block457S2 block457S3 block457S4 y

def block457LeftParamsCertificate : Bool :=
  allBoxesSameParams block457LeftBoxes block457W1 block457W2 block457W3 block457W4 block457S1 block457S2 block457S3 block457S4

theorem block457LeftParamsCertificate_eq_true :
    block457LeftParamsCertificate = true := by
  native_decide

theorem block457_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block457LeftL : ℝ) (block457LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block457S1 : ℝ))
    (hy2ne : y ≠ (block457S2 : ℝ))
    (hy3ne : y ≠ (block457S3 : ℝ))
    (hy4ne : y ≠ (block457S4 : ℝ)) :
    0 < block457V y := by
  have hcert := block457LeftCertificate_eq_true
  unfold block457LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block457LeftBoxes) (lo := block457LeftL) (hi := block457LeftR)
    (w1 := block457W1) (w2 := block457W2) (w3 := block457W3) (w4 := block457W4)
    (s1 := block457S1) (s2 := block457S2) (s3 := block457S3) (s4 := block457S4)
    hboxes hcover block457LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block457RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block457RightChunk000 block457W1 block457W2 block457W3 block457W4 block457S1 block457S2 block457S3 block457S4

theorem block457RightChunk000ParamsCertificate_eq_true :
    block457RightChunk000ParamsCertificate = true := by
  native_decide

theorem block457_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block457RightChunk000L : ℝ) (block457RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block457S1 : ℝ))
    (hy2ne : y ≠ (block457S2 : ℝ))
    (hy3ne : y ≠ (block457S3 : ℝ))
    (hy4ne : y ≠ (block457S4 : ℝ)) :
    0 < block457V y := by
  have hcert := block457RightChunk000Certificate_eq_true
  unfold block457RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block457RightChunk000) (lo := block457RightChunk000L) (hi := block457RightChunk000R)
    (w1 := block457W1) (w2 := block457W2) (w3 := block457W3) (w4 := block457W4)
    (s1 := block457S1) (s2 := block457S2) (s3 := block457S3) (s4 := block457S4)
    hboxes hcover block457RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block457_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block457RightL : ℝ) (block457RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block457S1 : ℝ))
    (hy2ne : y ≠ (block457S2 : ℝ))
    (hy3ne : y ≠ (block457S3 : ℝ))
    (hy4ne : y ≠ (block457S4 : ℝ)) :
    0 < block457V y := by
  have hL : (block457RightChunk000L : ℝ) = (block457RightL : ℝ) := by
    norm_num [block457RightChunk000L, block457RightL]
  have hR : (block457RightChunk000R : ℝ) = (block457RightR : ℝ) := by
    norm_num [block457RightChunk000R, block457RightR]
  have hyc : y ∈ Icc (block457RightChunk000L : ℝ) (block457RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block457_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block457_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block457LeftL : ℝ) (block457LeftR : ℝ) →
    y ≠ 0 → y ≠ (block457S1 : ℝ) → y ≠ (block457S2 : ℝ) →
    y ≠ (block457S3 : ℝ) → y ≠ (block457S4 : ℝ) → 0 < block457V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block457RightL : ℝ) (block457RightR : ℝ) →
    y ≠ 0 → y ≠ (block457S1 : ℝ) → y ≠ (block457S2 : ℝ) →
    y ≠ (block457S3 : ℝ) → y ≠ (block457S4 : ℝ) → 0 < block457V y)

theorem block457_reallog_certificate_proof :
    block457_reallog_certificate := by
  exact ⟨block457_left_V_pos, block457_right_V_pos⟩

end Block457
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block457.block457V
#check Erdos1038Lean.M1817475.Block457.block457_left_V_pos
#check Erdos1038Lean.M1817475.Block457.block457_right_V_pos
#check Erdos1038Lean.M1817475.Block457.block457_reallog_certificate_proof
