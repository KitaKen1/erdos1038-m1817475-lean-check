/-
Self-contained Lean4Web paste file.
Block 416 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block416

def block416LeftL : Rat := ((36797761160714285893 : Rat) / 50000000000000000000)
def block416LeftR : Rat := ((1150235491071428577 : Rat) / 1562500000000000000)
def block416RightL : Rat := ((86797761160714285893 : Rat) / 50000000000000000000)
def block416RightR : Rat := ((4275235491071428577 : Rat) / 1562500000000000000)

def block416LeftBoxes : List RatBox := [
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((36797761160714285893 : Rat) / 50000000000000000000), R := ((1150235491071428577 : Rat) / 1562500000000000000), D0 := ((1150235491071428577 : Rat) / 1562500000000000000), D1 := ((54075993839285714107 : Rat) / 50000000000000000000), D2 := ((91098988839285714107 : Rat) / 50000000000000000000), D3 := ((47601683749999999949 : Rat) / 25000000000000000000), D4 := ((102426767589285709107 : Rat) / 50000000000000000000), LB := ((8519537640631833 : Rat) / 10000000000000000000) }
]

def block416LeftCertificate : Bool :=
  allBoxesValid block416LeftBoxes &&
  coversFromBool block416LeftBoxes block416LeftL block416LeftR

theorem block416LeftCertificate_eq_true :
    block416LeftCertificate = true := by
  native_decide

def block416RightChunk000 : List RatBox := [
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86797761160714285893 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((4075993839285714107 : Rat) / 50000000000000000000), D2 := ((41098988839285714107 : Rat) / 50000000000000000000), D3 := ((22601683749999999949 : Rat) / 25000000000000000000), D4 := ((52426767589285709107 : Rat) / 50000000000000000000), LB := ((11812259947861539 : Rat) / 10000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41127373660714285791 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((1090621184919843 : Rat) / 2000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((31871624910714285791 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((814307183972179 : Rat) / 12500000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((22615876160714285791 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((856386096833051 : Rat) / 10000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((20301938973214285791 : Rat) / 50000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((30025422555035007 : Rat) / 1000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((17988001785714285791 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((28824569901355963 : Rat) / 1000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((16831033191964285791 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((981697731461073 : Rat) / 100000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((15674064598214285791 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((7124533314987941 : Rat) / 500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((15095580301339285791 : Rat) / 50000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((716194126034897 : Rat) / 100000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14517096004464285791 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((9178108487727099 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((13938611707589285791 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((26525426734554103 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((13649369559151785791 : Rat) / 50000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((358593781558789 : Rat) / 125000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13360127410714285791 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((66228277882531 : Rat) / 100000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((6096633061 : Rat) / 2560000000), D0 := ((6096633061 : Rat) / 2560000000), D1 := ((288779361 : Rat) / 512000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((13070885262276785791 : Rat) / 50000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((34815714361758343 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6096633061 : Rat) / 2560000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((451680539 : Rat) / 2560000000), D3 := ((12926264188058035791 : Rat) / 50000000000000000000), D4 := ((4029932855468749 : Rat) / 10000000000000000), LB := ((12827117129900617 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((12781643113839285791 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((213754449307383 : Rat) / 125000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((12637022039620535791 : Rat) / 50000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((4580590337310911 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((12492400965401785791 : Rat) / 50000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((57629363183361 : Rat) / 312500000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((12259907513 : Rat) / 5120000000), D0 := ((12259907513 : Rat) / 5120000000), D1 := ((2954435001 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((12347779891183035791 : Rat) / 50000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((73052776330777 : Rat) / 39062500000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12259907513 : Rat) / 5120000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((836719687 : Rat) / 5120000000), D3 := ((12275469354073660791 : Rat) / 50000000000000000000), D4 := ((1949886944335937 : Rat) / 5000000000000000), LB := ((3887332896502331 : Rat) / 2500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((12274716711 : Rat) / 5120000000), D0 := ((12274716711 : Rat) / 5120000000), D1 := ((2969244199 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12203158816964285791 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((12557929774612009 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12274716711 : Rat) / 5120000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((821910489 : Rat) / 5120000000), D3 := ((12130848279854910791 : Rat) / 50000000000000000000), D4 := ((967712418457031 : Rat) / 2500000000000000), LB := ((2432094599769223 : Rat) / 2500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((12289525909 : Rat) / 5120000000), D0 := ((12289525909 : Rat) / 5120000000), D1 := ((2984053397 : Rat) / 5120000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((12058537742745535791 : Rat) / 50000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((1765443704082499 : Rat) / 2500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12289525909 : Rat) / 5120000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((807101291 : Rat) / 5120000000), D3 := ((11986227205636160791 : Rat) / 50000000000000000000), D4 := ((1920962729492187 : Rat) / 5000000000000000), LB := ((911848233411533 : Rat) / 2000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((12304335107 : Rat) / 5120000000), D0 := ((12304335107 : Rat) / 5120000000), D1 := ((599772519 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((11913916668526785791 : Rat) / 50000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((11109624556455283 : Rat) / 50000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12304335107 : Rat) / 5120000000), R := ((6155869853 : Rat) / 2560000000), D0 := ((6155869853 : Rat) / 2560000000), D1 := ((1503133597 : Rat) / 2560000000), D2 := ((792292093 : Rat) / 5120000000), D3 := ((11841606131417410791 : Rat) / 50000000000000000000), D4 := ((238312577758789 : Rat) / 625000000000000), LB := ((5099938086908229 : Rat) / 1000000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6155869853 : Rat) / 2560000000), R := ((24630884011 : Rat) / 10240000000), D0 := ((24630884011 : Rat) / 10240000000), D1 := ((6019938987 : Rat) / 10240000000), D2 := ((392443747 : Rat) / 2560000000), D3 := ((11769295594308035791 : Rat) / 50000000000000000000), D4 := ((3798539136718749 : Rat) / 10000000000000000), LB := ((9650733976013237 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24630884011 : Rat) / 10240000000), R := ((2463828861 : Rat) / 1024000000), D0 := ((2463828861 : Rat) / 1024000000), D1 := ((3013671793 : Rat) / 5120000000), D2 := ((1562370389 : Rat) / 10240000000), D3 := ((11733140325753348291 : Rat) / 50000000000000000000), D4 := ((7582616166015623 : Rat) / 20000000000000000), LB := ((1087604587137643 : Rat) / 1250000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2463828861 : Rat) / 1024000000), R := ((24645693209 : Rat) / 10240000000), D0 := ((24645693209 : Rat) / 10240000000), D1 := ((1206949637 : Rat) / 2048000000), D2 := ((155496579 : Rat) / 1024000000), D3 := ((11696985057198660791 : Rat) / 50000000000000000000), D4 := ((1892038514648437 : Rat) / 5000000000000000), LB := ((7793325667927453 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24645693209 : Rat) / 10240000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((1547561191 : Rat) / 10240000000), D3 := ((11660829788643973291 : Rat) / 50000000000000000000), D4 := ((7553691951171873 : Rat) / 20000000000000000), LB := ((6928358466148227 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((24660502407 : Rat) / 10240000000), D0 := ((24660502407 : Rat) / 10240000000), D1 := ((6049557383 : Rat) / 10240000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((11624674520089285791 : Rat) / 50000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((3053047218038729 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24660502407 : Rat) / 10240000000), R := ((12333953503 : Rat) / 5120000000), D0 := ((12333953503 : Rat) / 5120000000), D1 := ((3028480991 : Rat) / 5120000000), D2 := ((1532751993 : Rat) / 10240000000), D3 := ((11588519251534598291 : Rat) / 50000000000000000000), D4 := ((7524767736328123 : Rat) / 20000000000000000), LB := ((5326694708746443 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12333953503 : Rat) / 5120000000), R := ((4935062321 : Rat) / 2048000000), D0 := ((4935062321 : Rat) / 2048000000), D1 := ((6064366581 : Rat) / 10240000000), D2 := ((762673697 : Rat) / 5120000000), D3 := ((11552363982979910791 : Rat) / 50000000000000000000), D4 := ((938788203613281 : Rat) / 2500000000000000), LB := ((9180644444490571 : Rat) / 20000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4935062321 : Rat) / 2048000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((303588559 : Rat) / 2048000000), D3 := ((11516208714425223291 : Rat) / 50000000000000000000), D4 := ((7495843521484373 : Rat) / 20000000000000000), LB := ((9742854355951 : Rat) / 25000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((24690120803 : Rat) / 10240000000), D0 := ((24690120803 : Rat) / 10240000000), D1 := ((6079175779 : Rat) / 10240000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11480053445870535791 : Rat) / 50000000000000000000), D4 := ((3740690707031249 : Rat) / 10000000000000000), LB := ((32473198836899253 : Rat) / 100000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24690120803 : Rat) / 10240000000), R := ((12348762701 : Rat) / 5120000000), D0 := ((12348762701 : Rat) / 5120000000), D1 := ((3043290189 : Rat) / 5120000000), D2 := ((1503133597 : Rat) / 10240000000), D3 := ((11443898177315848291 : Rat) / 50000000000000000000), D4 := ((7466919306640623 : Rat) / 20000000000000000), LB := ((26410251307534827 : Rat) / 100000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12348762701 : Rat) / 5120000000), R := ((24704930001 : Rat) / 10240000000), D0 := ((24704930001 : Rat) / 10240000000), D1 := ((6093984977 : Rat) / 10240000000), D2 := ((747864499 : Rat) / 5120000000), D3 := ((11407742908761160791 : Rat) / 50000000000000000000), D4 := ((1863114299804687 : Rat) / 5000000000000000), LB := ((10392139299612163 : Rat) / 50000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24704930001 : Rat) / 10240000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((1488324399 : Rat) / 10240000000), D3 := ((11371587640206473291 : Rat) / 50000000000000000000), D4 := ((7437995091796873 : Rat) / 20000000000000000), LB := ((3119400722601251 : Rat) / 20000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((24719739199 : Rat) / 10240000000), D0 := ((24719739199 : Rat) / 10240000000), D1 := ((244351767 : Rat) / 409600000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11335432371651785791 : Rat) / 50000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((5425084305877431 : Rat) / 50000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24719739199 : Rat) / 10240000000), R := ((12363571899 : Rat) / 5120000000), D0 := ((12363571899 : Rat) / 5120000000), D1 := ((3058099387 : Rat) / 5120000000), D2 := ((1473515201 : Rat) / 10240000000), D3 := ((11299277103097098291 : Rat) / 50000000000000000000), D4 := ((7409070876953123 : Rat) / 20000000000000000), LB := ((818191930943013 : Rat) / 12500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12363571899 : Rat) / 5120000000), R := ((24734548397 : Rat) / 10240000000), D0 := ((24734548397 : Rat) / 10240000000), D1 := ((6123603373 : Rat) / 10240000000), D2 := ((733055301 : Rat) / 5120000000), D3 := ((11263121834542410791 : Rat) / 50000000000000000000), D4 := ((462163048095703 : Rat) / 1250000000000000), LB := ((6712214482309381 : Rat) / 250000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24734548397 : Rat) / 10240000000), R := ((49476501393 : Rat) / 20480000000), D0 := ((49476501393 : Rat) / 20480000000), D1 := ((2450922269 : Rat) / 4096000000), D2 := ((1458706003 : Rat) / 10240000000), D3 := ((11226966565987723291 : Rat) / 50000000000000000000), D4 := ((7380146662109373 : Rat) / 20000000000000000), LB := ((282406204434843 : Rat) / 500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49476501393 : Rat) / 20480000000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((2910007407 : Rat) / 20480000000), D3 := ((11208888931710379541 : Rat) / 50000000000000000000), D4 := ((14745831216796871 : Rat) / 40000000000000000), LB := ((549138041749081 : Rat) / 1000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((49491310591 : Rat) / 20480000000), D0 := ((49491310591 : Rat) / 20480000000), D1 := ((12269420543 : Rat) / 20480000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11190811297433035791 : Rat) / 50000000000000000000), D4 := ((3682842277343749 : Rat) / 10000000000000000), LB := ((5345853007284601 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49491310591 : Rat) / 20480000000), R := ((4949871519 : Rat) / 2048000000), D0 := ((4949871519 : Rat) / 2048000000), D1 := ((6138412571 : Rat) / 10240000000), D2 := ((2895198209 : Rat) / 20480000000), D3 := ((11172733663155692041 : Rat) / 50000000000000000000), D4 := ((14716907001953121 : Rat) / 40000000000000000), LB := ((1302891237205811 : Rat) / 2500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4949871519 : Rat) / 2048000000), R := ((49506119789 : Rat) / 20480000000), D0 := ((49506119789 : Rat) / 20480000000), D1 := ((12284229741 : Rat) / 20480000000), D2 := ((288779361 : Rat) / 2048000000), D3 := ((11154656028878348291 : Rat) / 50000000000000000000), D4 := ((7351222447265623 : Rat) / 20000000000000000), LB := ((1017707892560421 : Rat) / 2000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49506119789 : Rat) / 20480000000), R := ((12378381097 : Rat) / 5120000000), D0 := ((12378381097 : Rat) / 5120000000), D1 := ((614581717 : Rat) / 1024000000), D2 := ((2880389011 : Rat) / 20480000000), D3 := ((11136578394601004541 : Rat) / 50000000000000000000), D4 := ((14687982787109371 : Rat) / 40000000000000000), LB := ((4976799900590773 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12378381097 : Rat) / 5120000000), R := ((49520928987 : Rat) / 20480000000), D0 := ((49520928987 : Rat) / 20480000000), D1 := ((12299038939 : Rat) / 20480000000), D2 := ((718246103 : Rat) / 5120000000), D3 := ((11118500760323660791 : Rat) / 50000000000000000000), D4 := ((1834190084960937 : Rat) / 5000000000000000), LB := ((609546218129451 : Rat) / 1250000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49520928987 : Rat) / 20480000000), R := ((24764166793 : Rat) / 10240000000), D0 := ((24764166793 : Rat) / 10240000000), D1 := ((6153221769 : Rat) / 10240000000), D2 := ((2865579813 : Rat) / 20480000000), D3 := ((11100423126046317041 : Rat) / 50000000000000000000), D4 := ((14659058572265621 : Rat) / 40000000000000000), LB := ((5984090764067293 : Rat) / 12500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24764166793 : Rat) / 10240000000), R := ((9907147637 : Rat) / 4096000000), D0 := ((9907147637 : Rat) / 4096000000), D1 := ((12313848137 : Rat) / 20480000000), D2 := ((1429087607 : Rat) / 10240000000), D3 := ((11082345491768973291 : Rat) / 50000000000000000000), D4 := ((7322298232421873 : Rat) / 20000000000000000), LB := ((9419064494877727 : Rat) / 20000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9907147637 : Rat) / 4096000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((570154123 : Rat) / 4096000000), D3 := ((11064267857491629541 : Rat) / 50000000000000000000), D4 := ((14630134357421871 : Rat) / 40000000000000000), LB := ((46431725356582687 : Rat) / 100000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((49550547383 : Rat) / 20480000000), D0 := ((49550547383 : Rat) / 20480000000), D1 := ((2465731467 : Rat) / 4096000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((11046190223214285791 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((9176434985355697 : Rat) / 20000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49550547383 : Rat) / 20480000000), R := ((24778975991 : Rat) / 10240000000), D0 := ((24778975991 : Rat) / 10240000000), D1 := ((6168030967 : Rat) / 10240000000), D2 := ((2835961417 : Rat) / 20480000000), D3 := ((11028112588936942041 : Rat) / 50000000000000000000), D4 := ((14601210142578121 : Rat) / 40000000000000000), LB := ((45446912707711173 : Rat) / 100000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24778975991 : Rat) / 10240000000), R := ((49565356581 : Rat) / 20480000000), D0 := ((49565356581 : Rat) / 20480000000), D1 := ((12343466533 : Rat) / 20480000000), D2 := ((1414278409 : Rat) / 10240000000), D3 := ((11010034954659598291 : Rat) / 50000000000000000000), D4 := ((7293374017578123 : Rat) / 20000000000000000), LB := ((70509658727483 : Rat) / 156250000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49565356581 : Rat) / 20480000000), R := ((2478638059 : Rat) / 1024000000), D0 := ((2478638059 : Rat) / 1024000000), D1 := ((3087717783 : Rat) / 5120000000), D2 := ((2821152219 : Rat) / 20480000000), D3 := ((10991957320382254541 : Rat) / 50000000000000000000), D4 := ((14572285927734371 : Rat) / 40000000000000000), LB := ((8984045163639709 : Rat) / 20000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2478638059 : Rat) / 1024000000), R := ((49580165779 : Rat) / 20480000000), D0 := ((49580165779 : Rat) / 20480000000), D1 := ((12358275731 : Rat) / 20480000000), D2 := ((140687381 : Rat) / 1024000000), D3 := ((10973879686104910791 : Rat) / 50000000000000000000), D4 := ((909863988769531 : Rat) / 2500000000000000), LB := ((896585820874013 : Rat) / 2000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49580165779 : Rat) / 20480000000), R := ((24793785189 : Rat) / 10240000000), D0 := ((24793785189 : Rat) / 10240000000), D1 := ((1236568033 : Rat) / 2048000000), D2 := ((2806343021 : Rat) / 20480000000), D3 := ((10955802051827567041 : Rat) / 50000000000000000000), D4 := ((14543361712890621 : Rat) / 40000000000000000), LB := ((4485362428865297 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24793785189 : Rat) / 10240000000), R := ((49594974977 : Rat) / 20480000000), D0 := ((49594974977 : Rat) / 20480000000), D1 := ((12373084929 : Rat) / 20480000000), D2 := ((1399469211 : Rat) / 10240000000), D3 := ((10937724417550223291 : Rat) / 50000000000000000000), D4 := ((7264449802734373 : Rat) / 20000000000000000), LB := ((5624184247118337 : Rat) / 12500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49594974977 : Rat) / 20480000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((2791533823 : Rat) / 20480000000), D3 := ((10919646783272879541 : Rat) / 50000000000000000000), D4 := ((14514437498046871 : Rat) / 40000000000000000), LB := ((4524908993819021 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((1984391367 : Rat) / 819200000), D0 := ((1984391367 : Rat) / 819200000), D1 := ((12387894127 : Rat) / 20480000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((10901569148995535791 : Rat) / 50000000000000000000), D4 := ((3624993847656249 : Rat) / 10000000000000000), LB := ((22810361708273247 : Rat) / 50000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1984391367 : Rat) / 819200000), R := ((24808594387 : Rat) / 10240000000), D0 := ((24808594387 : Rat) / 10240000000), D1 := ((6197649363 : Rat) / 10240000000), D2 := ((22213797 : Rat) / 163840000), D3 := ((10883491514718192041 : Rat) / 50000000000000000000), D4 := ((14485513283203121 : Rat) / 40000000000000000), LB := ((922172541587607 : Rat) / 2000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24808594387 : Rat) / 10240000000), R := ((49624593373 : Rat) / 20480000000), D0 := ((49624593373 : Rat) / 20480000000), D1 := ((496108133 : Rat) / 819200000), D2 := ((1384660013 : Rat) / 10240000000), D3 := ((10865413880440848291 : Rat) / 50000000000000000000), D4 := ((7235525587890623 : Rat) / 20000000000000000), LB := ((2335652751302153 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49624593373 : Rat) / 20480000000), R := ((12407999493 : Rat) / 5120000000), D0 := ((12407999493 : Rat) / 5120000000), D1 := ((3102526981 : Rat) / 5120000000), D2 := ((2761915427 : Rat) / 20480000000), D3 := ((10847336246163504541 : Rat) / 50000000000000000000), D4 := ((14456589068359371 : Rat) / 40000000000000000), LB := ((948685255943521 : Rat) / 2000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12407999493 : Rat) / 5120000000), R := ((49639402571 : Rat) / 20480000000), D0 := ((49639402571 : Rat) / 20480000000), D1 := ((12417512523 : Rat) / 20480000000), D2 := ((688627707 : Rat) / 5120000000), D3 := ((10829258611886160791 : Rat) / 50000000000000000000), D4 := ((1805265870117187 : Rat) / 5000000000000000), LB := ((4827250738316663 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49639402571 : Rat) / 20480000000), R := ((4964680717 : Rat) / 2048000000), D0 := ((4964680717 : Rat) / 2048000000), D1 := ((6212458561 : Rat) / 10240000000), D2 := ((2747106229 : Rat) / 20480000000), D3 := ((10811180977608817041 : Rat) / 50000000000000000000), D4 := ((14427664853515621 : Rat) / 40000000000000000), LB := ((4922804723364593 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4964680717 : Rat) / 2048000000), R := ((49654211769 : Rat) / 20480000000), D0 := ((49654211769 : Rat) / 20480000000), D1 := ((12432321721 : Rat) / 20480000000), D2 := ((273970163 : Rat) / 2048000000), D3 := ((10793103343331473291 : Rat) / 50000000000000000000), D4 := ((7206601373046873 : Rat) / 20000000000000000), LB := ((251505711331243 : Rat) / 500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49654211769 : Rat) / 20480000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((2732297031 : Rat) / 20480000000), D3 := ((10775025709054129541 : Rat) / 50000000000000000000), D4 := ((14398740638671871 : Rat) / 40000000000000000), LB := ((257460269381303 : Rat) / 500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((49669020967 : Rat) / 20480000000), D0 := ((49669020967 : Rat) / 20480000000), D1 := ((12447130919 : Rat) / 20480000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((10756948074776785791 : Rat) / 50000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((660013061818971 : Rat) / 1250000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((49669020967 : Rat) / 20480000000), R := ((24838212783 : Rat) / 10240000000), D0 := ((24838212783 : Rat) / 10240000000), D1 := ((6227267759 : Rat) / 10240000000), D2 := ((2717487833 : Rat) / 20480000000), D3 := ((10738870440499442041 : Rat) / 50000000000000000000), D4 := ((14369816423828121 : Rat) / 40000000000000000), LB := ((2711418992606199 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24838212783 : Rat) / 10240000000), R := ((9936766033 : Rat) / 4096000000), D0 := ((9936766033 : Rat) / 4096000000), D1 := ((12461940117 : Rat) / 20480000000), D2 := ((1355041617 : Rat) / 10240000000), D3 := ((10720792806222098291 : Rat) / 50000000000000000000), D4 := ((7177677158203123 : Rat) / 20000000000000000), LB := ((5577432447950031 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((9936766033 : Rat) / 4096000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((540535727 : Rat) / 4096000000), D3 := ((10702715171944754541 : Rat) / 50000000000000000000), D4 := ((14340892208984371 : Rat) / 40000000000000000), LB := ((2871957311319853 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((24853021981 : Rat) / 10240000000), D0 := ((24853021981 : Rat) / 10240000000), D1 := ((6242076957 : Rat) / 10240000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((10684637537667410791 : Rat) / 50000000000000000000), D4 := ((111925235168457 : Rat) / 312500000000000), LB := ((3538395947251527 : Rat) / 125000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24853021981 : Rat) / 10240000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((1340232419 : Rat) / 10240000000), D3 := ((10648482269112723291 : Rat) / 50000000000000000000), D4 := ((7148752943359373 : Rat) / 20000000000000000), LB := ((3405395070581879 : Rat) / 50000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((24867831179 : Rat) / 10240000000), D0 := ((24867831179 : Rat) / 10240000000), D1 := ((1251377231 : Rat) / 2048000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((10612327000558035791 : Rat) / 50000000000000000000), D4 := ((3567145417968749 : Rat) / 10000000000000000), LB := ((2254118849306097 : Rat) / 20000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24867831179 : Rat) / 10240000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((1325423221 : Rat) / 10240000000), D3 := ((10576171732003348291 : Rat) / 50000000000000000000), D4 := ((7119828728515623 : Rat) / 20000000000000000), LB := ((162123367660999 : Rat) / 1000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((24882640377 : Rat) / 10240000000), D0 := ((24882640377 : Rat) / 10240000000), D1 := ((6271695353 : Rat) / 10240000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((10540016463448660791 : Rat) / 50000000000000000000), D4 := ((1776341655273437 : Rat) / 5000000000000000), LB := ((21638250737442133 : Rat) / 100000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24882640377 : Rat) / 10240000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((1310614023 : Rat) / 10240000000), D3 := ((10503861194893973291 : Rat) / 50000000000000000000), D4 := ((7090904513671873 : Rat) / 20000000000000000), LB := ((2755059487187239 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((995897983 : Rat) / 409600000), D0 := ((995897983 : Rat) / 409600000), D1 := ((6286504551 : Rat) / 10240000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10467705926339285791 : Rat) / 50000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((1697582694413849 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((995897983 : Rat) / 409600000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((51832193 : Rat) / 409600000), D3 := ((10431550657784598291 : Rat) / 50000000000000000000), D4 := ((7061980298828123 : Rat) / 20000000000000000), LB := ((4084373885274023 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((24912258773 : Rat) / 10240000000), D0 := ((24912258773 : Rat) / 10240000000), D1 := ((6301313749 : Rat) / 10240000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10395395389229910791 : Rat) / 50000000000000000000), D4 := ((880939773925781 : Rat) / 2500000000000000), LB := ((12057296881037849 : Rat) / 25000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24912258773 : Rat) / 10240000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((1280995627 : Rat) / 10240000000), D3 := ((10359240120675223291 : Rat) / 50000000000000000000), D4 := ((7033056083984373 : Rat) / 20000000000000000), LB := ((5611036470603709 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((24927067971 : Rat) / 10240000000), D0 := ((24927067971 : Rat) / 10240000000), D1 := ((6316122947 : Rat) / 10240000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10323084852120535791 : Rat) / 50000000000000000000), D4 := ((3509296988281249 : Rat) / 10000000000000000), LB := ((161224156510327 : Rat) / 250000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24927067971 : Rat) / 10240000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((1266186429 : Rat) / 10240000000), D3 := ((10286929583565848291 : Rat) / 50000000000000000000), D4 := ((7004131869140623 : Rat) / 20000000000000000), LB := ((1834237529772971 : Rat) / 2500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((24941877169 : Rat) / 10240000000), D0 := ((24941877169 : Rat) / 10240000000), D1 := ((1266186429 : Rat) / 2048000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10250774315011160791 : Rat) / 50000000000000000000), D4 := ((1747417440429687 : Rat) / 5000000000000000), LB := ((8275232857597181 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24941877169 : Rat) / 10240000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((1251377231 : Rat) / 10240000000), D3 := ((10214619046456473291 : Rat) / 50000000000000000000), D4 := ((6975207654296873 : Rat) / 20000000000000000), LB := ((9264062138307633 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((24956686367 : Rat) / 10240000000), D0 := ((24956686367 : Rat) / 10240000000), D1 := ((6345741343 : Rat) / 10240000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10178463777901785791 : Rat) / 50000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((1287961064179513 : Rat) / 1250000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24956686367 : Rat) / 10240000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((1236568033 : Rat) / 10240000000), D3 := ((10142308509347098291 : Rat) / 50000000000000000000), D4 := ((6946283439453123 : Rat) / 20000000000000000), LB := ((2848591366029253 : Rat) / 2500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10106153240792410791 : Rat) / 50000000000000000000), D4 := ((433238833251953 : Rat) / 1250000000000000), LB := ((7171977587998313 : Rat) / 50000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((10033842703683035791 : Rat) / 50000000000000000000), D4 := ((3451448558593749 : Rat) / 10000000000000000), LB := ((3893973088793523 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((9961532166573660791 : Rat) / 50000000000000000000), D4 := ((1718493225585937 : Rat) / 5000000000000000), LB := ((410115161743347 : Rat) / 625000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((9889221629464285791 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((9440167322146281 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((9816911092354910791 : Rat) / 50000000000000000000), D4 := ((852015559082031 : Rat) / 2500000000000000), LB := ((12531162166316973 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((9744600555245535791 : Rat) / 50000000000000000000), D4 := ((3393600128906249 : Rat) / 10000000000000000), LB := ((3167419004058869 : Rat) / 2000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((9672290018136160791 : Rat) / 50000000000000000000), D4 := ((1689569010742187 : Rat) / 5000000000000000), LB := ((9680144160463741 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((9599979481026785791 : Rat) / 50000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((3036550048017561 : Rat) / 25000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((9455358406808035791 : Rat) / 50000000000000000000), D4 := ((3335751699218749 : Rat) / 10000000000000000), LB := ((1889742457089949 : Rat) / 2000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9310737332589285791 : Rat) / 50000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((18590703452489449 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((9166116258370535791 : Rat) / 50000000000000000000), D4 := ((3277903269531249 : Rat) / 10000000000000000), LB := ((14330912493733597 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((9021495184151785791 : Rat) / 50000000000000000000), D4 := ((3248979054687499 : Rat) / 10000000000000000), LB := ((1984218932336357 : Rat) / 500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((8876874109933035791 : Rat) / 50000000000000000000), D4 := ((3220054839843749 : Rat) / 10000000000000000), LB := ((1292045083135747 : Rat) / 250000000000000000) }
]

def block416RightChunk000L : Rat := ((86797761160714285893 : Rat) / 50000000000000000000)
def block416RightChunk000R : Rat := ((197230201 : Rat) / 80000000)

def block416RightChunk000Certificate : Bool :=
  allBoxesValid block416RightChunk000 &&
  coversFromBool block416RightChunk000 block416RightChunk000L block416RightChunk000R

theorem block416RightChunk000Certificate_eq_true :
    block416RightChunk000Certificate = true := by
  native_decide

def block416RightChunk001 : List RatBox := [
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((8732253035714285791 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((10976032986482337 : Rat) / 5000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((632617563 : Rat) / 256000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8443010887276785791 : Rat) / 50000000000000000000), D4 := ((3133282195312499 : Rat) / 10000000000000000), LB := ((1026993184854727 : Rat) / 200000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8153768738839285791 : Rat) / 50000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((15540819248391 : Rat) / 125000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((7575284441964285791 : Rat) / 50000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((4190953695607069 : Rat) / 500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((6996800145089285791 : Rat) / 50000000000000000000), D4 := ((2844040046874999 : Rat) / 10000000000000000), LB := ((4676238457612173 : Rat) / 250000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6418315848214285791 : Rat) / 50000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((308918361304501 : Rat) / 20000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5261347254464285791 : Rat) / 50000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((99959683425831 : Rat) / 2000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((132001128660714285791 : Rat) / 50000000000000000000), D0 := ((132001128660714285791 : Rat) / 50000000000000000000), D1 := ((41127373660714285791 : Rat) / 50000000000000000000), D2 := ((4104378660714285791 : Rat) / 50000000000000000000), D3 := ((4104378660714285791 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((259308755936061 : Rat) / 10000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((132001128660714285791 : Rat) / 50000000000000000000), R := ((53761732875000000051 : Rat) / 20000000000000000000), D0 := ((53761732875000000051 : Rat) / 20000000000000000000), D1 := ((17412230875000000051 : Rat) / 20000000000000000000), D2 := ((2603032875000000051 : Rat) / 20000000000000000000), D3 := ((4806407053571428673 : Rat) / 100000000000000000000), D4 := ((7223400089285709209 : Rat) / 50000000000000000000), LB := ((4095016890724413 : Rat) / 25000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((53761732875000000051 : Rat) / 20000000000000000000), R := ((542423735803571429183 : Rat) / 200000000000000000000), D0 := ((542423735803571429183 : Rat) / 200000000000000000000), D1 := ((178928715803571429183 : Rat) / 200000000000000000000), D2 := ((30836735803571429183 : Rat) / 200000000000000000000), D3 := ((14419221160714286019 : Rat) / 200000000000000000000), D4 := ((1928078624999997949 : Rat) / 20000000000000000000), LB := ((655905318462047 : Rat) / 12500000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((542423735803571429183 : Rat) / 200000000000000000000), R := ((1089653878660714287039 : Rat) / 400000000000000000000), D0 := ((1089653878660714287039 : Rat) / 400000000000000000000), D1 := ((362663838660714287039 : Rat) / 400000000000000000000), D2 := ((66479878660714287039 : Rat) / 400000000000000000000), D3 := ((33644849375000000711 : Rat) / 400000000000000000000), D4 := ((14474379196428550817 : Rat) / 200000000000000000000), LB := ((743174883877209 : Rat) / 40000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1089653878660714287039 : Rat) / 400000000000000000000), R := ((2184114164375000002751 : Rat) / 800000000000000000000), D0 := ((2184114164375000002751 : Rat) / 800000000000000000000), D1 := ((730134084375000002751 : Rat) / 800000000000000000000), D2 := ((137766164375000002751 : Rat) / 800000000000000000000), D3 := ((14419221160714286019 : Rat) / 160000000000000000000), D4 := ((24142351339285672961 : Rat) / 400000000000000000000), LB := ((3685471572900667 : Rat) / 500000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2184114164375000002751 : Rat) / 800000000000000000000), R := ((174921389432142857367 : Rat) / 64000000000000000000), D0 := ((174921389432142857367 : Rat) / 64000000000000000000), D1 := ((58602983032142857367 : Rat) / 64000000000000000000), D2 := ((11213549432142857367 : Rat) / 64000000000000000000), D3 := ((148998618660714288863 : Rat) / 1600000000000000000000), D4 := ((43478295624999917249 : Rat) / 800000000000000000000), LB := ((7005307931209237 : Rat) / 2000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((174921389432142857367 : Rat) / 64000000000000000000), R := ((8750875878660714297023 : Rat) / 3200000000000000000000), D0 := ((8750875878660714297023 : Rat) / 3200000000000000000000), D1 := ((2934955558660714297023 : Rat) / 3200000000000000000000), D2 := ((565483878660714297023 : Rat) / 3200000000000000000000), D3 := ((302803644375000006399 : Rat) / 3200000000000000000000), D4 := ((3286007367857136233 : Rat) / 64000000000000000000), LB := ((20726682872648783 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8750875878660714297023 : Rat) / 3200000000000000000000), R := ((17506558164375000022719 : Rat) / 6400000000000000000000), D0 := ((17506558164375000022719 : Rat) / 6400000000000000000000), D1 := ((5874717524375000022719 : Rat) / 6400000000000000000000), D2 := ((1135774164375000022719 : Rat) / 6400000000000000000000), D3 := ((610413695803571441471 : Rat) / 6400000000000000000000), D4 := ((159493961339285382977 : Rat) / 3200000000000000000000), LB := ((14958490385479917 : Rat) / 10000000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17506558164375000022719 : Rat) / 6400000000000000000000), R := ((35017922735803571474111 : Rat) / 12800000000000000000000), D0 := ((35017922735803571474111 : Rat) / 12800000000000000000000), D1 := ((11754241455803571474111 : Rat) / 12800000000000000000000), D2 := ((2276354735803571474111 : Rat) / 12800000000000000000000), D3 := ((245126759732142862323 : Rat) / 2560000000000000000000), D4 := ((314181515624999337281 : Rat) / 6400000000000000000000), LB := ((155473034082039 : Rat) / 125000000000000000) },
  { w1 := ((6993899391570341 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((2923986340962117 : Rat) / 10000000000000000), w4 := ((347814631447751 : Rat) / 4000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((132001128660714285791 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35017922735803571474111 : Rat) / 12800000000000000000000), R := ((4275235491071428577 : Rat) / 1562500000000000000), D0 := ((4275235491071428577 : Rat) / 1562500000000000000), D1 := ((1435430647321428577 : Rat) / 1562500000000000000), D2 := ((278462053571428577 : Rat) / 1562500000000000000), D3 := ((4806407053571428673 : Rat) / 50000000000000000000), D4 := ((623556624196427245889 : Rat) / 12800000000000000000000), LB := ((3438647424633401 : Rat) / 10000000000000000000) }
]

def block416RightChunk001L : Rat := ((197230201 : Rat) / 80000000)
def block416RightChunk001R : Rat := ((4275235491071428577 : Rat) / 1562500000000000000)

def block416RightChunk001Certificate : Bool :=
  allBoxesValid block416RightChunk001 &&
  coversFromBool block416RightChunk001 block416RightChunk001L block416RightChunk001R

theorem block416RightChunk001Certificate_eq_true :
    block416RightChunk001Certificate = true := by
  native_decide

def block416RightChainCertificate : Bool :=
  decide (
    block416RightL = ((86797761160714285893 : Rat) / 50000000000000000000) /\
    ((197230201 : Rat) / 80000000) = ((197230201 : Rat) / 80000000) /\
    ((4275235491071428577 : Rat) / 1562500000000000000) = block416RightR)

theorem block416RightChainCertificate_eq_true :
    block416RightChainCertificate = true := by
  native_decide

def block416LeftBoxCount : Nat := boxCount block416LeftBoxes
def block416RightBoxCount : Nat := 117

def block416_rational_certificate : Prop :=
    block416LeftCertificate = true /\
    block416RightChainCertificate = true /\
    block416RightChunk000Certificate = true /\
    block416RightChunk001Certificate = true

theorem block416_rational_certificate_proof :
    block416_rational_certificate := by
  exact ⟨block416LeftCertificate_eq_true, block416RightChainCertificate_eq_true, block416RightChunk000Certificate_eq_true, block416RightChunk001Certificate_eq_true⟩

end Block416
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block416

open Set

def block416W1 : Rat := ((6993899391570341 : Rat) / 10000000000000000)
def block416W2 : Rat := (0 : Rat)
def block416W3 : Rat := ((2923986340962117 : Rat) / 10000000000000000)
def block416W4 : Rat := ((347814631447751 : Rat) / 4000000000000000)
def block416S1 : Rat := ((18174751 : Rat) / 10000000)
def block416S2 : Rat := ((511587 : Rat) / 200000)
def block416S3 : Rat := ((132001128660714285791 : Rat) / 50000000000000000000)
def block416S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block416V (y : ℝ) : ℝ :=
  ratPotential block416W1 block416W2 block416W3 block416W4 block416S1 block416S2 block416S3 block416S4 y

def block416LeftParamsCertificate : Bool :=
  allBoxesSameParams block416LeftBoxes block416W1 block416W2 block416W3 block416W4 block416S1 block416S2 block416S3 block416S4

theorem block416LeftParamsCertificate_eq_true :
    block416LeftParamsCertificate = true := by
  native_decide

theorem block416_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block416LeftL : ℝ) (block416LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block416S1 : ℝ))
    (hy2ne : y ≠ (block416S2 : ℝ))
    (hy3ne : y ≠ (block416S3 : ℝ))
    (hy4ne : y ≠ (block416S4 : ℝ)) :
    0 < block416V y := by
  have hcert := block416LeftCertificate_eq_true
  unfold block416LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block416LeftBoxes) (lo := block416LeftL) (hi := block416LeftR)
    (w1 := block416W1) (w2 := block416W2) (w3 := block416W3) (w4 := block416W4)
    (s1 := block416S1) (s2 := block416S2) (s3 := block416S3) (s4 := block416S4)
    hboxes hcover block416LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block416RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block416RightChunk000 block416W1 block416W2 block416W3 block416W4 block416S1 block416S2 block416S3 block416S4

theorem block416RightChunk000ParamsCertificate_eq_true :
    block416RightChunk000ParamsCertificate = true := by
  native_decide

theorem block416_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block416RightChunk000L : ℝ) (block416RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block416S1 : ℝ))
    (hy2ne : y ≠ (block416S2 : ℝ))
    (hy3ne : y ≠ (block416S3 : ℝ))
    (hy4ne : y ≠ (block416S4 : ℝ)) :
    0 < block416V y := by
  have hcert := block416RightChunk000Certificate_eq_true
  unfold block416RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block416RightChunk000) (lo := block416RightChunk000L) (hi := block416RightChunk000R)
    (w1 := block416W1) (w2 := block416W2) (w3 := block416W3) (w4 := block416W4)
    (s1 := block416S1) (s2 := block416S2) (s3 := block416S3) (s4 := block416S4)
    hboxes hcover block416RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block416RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block416RightChunk001 block416W1 block416W2 block416W3 block416W4 block416S1 block416S2 block416S3 block416S4

theorem block416RightChunk001ParamsCertificate_eq_true :
    block416RightChunk001ParamsCertificate = true := by
  native_decide

theorem block416_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block416RightChunk001L : ℝ) (block416RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block416S1 : ℝ))
    (hy2ne : y ≠ (block416S2 : ℝ))
    (hy3ne : y ≠ (block416S3 : ℝ))
    (hy4ne : y ≠ (block416S4 : ℝ)) :
    0 < block416V y := by
  have hcert := block416RightChunk001Certificate_eq_true
  unfold block416RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block416RightChunk001) (lo := block416RightChunk001L) (hi := block416RightChunk001R)
    (w1 := block416W1) (w2 := block416W2) (w3 := block416W3) (w4 := block416W4)
    (s1 := block416S1) (s2 := block416S2) (s3 := block416S3) (s4 := block416S4)
    hboxes hcover block416RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block416_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block416RightL : ℝ) (block416RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block416S1 : ℝ))
    (hy2ne : y ≠ (block416S2 : ℝ))
    (hy3ne : y ≠ (block416S3 : ℝ))
    (hy4ne : y ≠ (block416S4 : ℝ)) :
    0 < block416V y := by
  by_cases h0 : y ≤ (block416RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block416RightChunk000L : ℝ) (block416RightChunk000R : ℝ) := by
      have hL : (block416RightChunk000L : ℝ) = (block416RightL : ℝ) := by
        norm_num [block416RightChunk000L, block416RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block416_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block416RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block416RightChunk001L : ℝ) = (block416RightChunk000R : ℝ) := by
      norm_num [block416RightChunk001L, block416RightChunk000R]
    have hR : (block416RightChunk001R : ℝ) = (block416RightR : ℝ) := by
      norm_num [block416RightChunk001R, block416RightR]
    have hyc : y ∈ Icc (block416RightChunk001L : ℝ) (block416RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block416_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block416_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block416LeftL : ℝ) (block416LeftR : ℝ) →
    y ≠ 0 → y ≠ (block416S1 : ℝ) → y ≠ (block416S2 : ℝ) →
    y ≠ (block416S3 : ℝ) → y ≠ (block416S4 : ℝ) → 0 < block416V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block416RightL : ℝ) (block416RightR : ℝ) →
    y ≠ 0 → y ≠ (block416S1 : ℝ) → y ≠ (block416S2 : ℝ) →
    y ≠ (block416S3 : ℝ) → y ≠ (block416S4 : ℝ) → 0 < block416V y)

theorem block416_reallog_certificate_proof :
    block416_reallog_certificate := by
  exact ⟨block416_left_V_pos, block416_right_V_pos⟩

end Block416
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block416.block416V
#check Erdos1038Lean.M1817475.Block416.block416_left_V_pos
#check Erdos1038Lean.M1817475.Block416.block416_right_V_pos
#check Erdos1038Lean.M1817475.Block416.block416_reallog_certificate_proof
