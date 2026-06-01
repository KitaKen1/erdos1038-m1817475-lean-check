/-
Self-contained Lean4Web paste file.
Block 421 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block421

def block421LeftL : Rat := ((18374444196428571519 : Rat) / 25000000000000000000)
def block421LeftR : Rat := ((36758662946428571609 : Rat) / 50000000000000000000)
def block421RightL : Rat := ((43374444196428571519 : Rat) / 25000000000000000000)
def block421RightR : Rat := ((136758662946428571609 : Rat) / 50000000000000000000)

def block421LeftBoxes : List RatBox := [
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18374444196428571519 : Rat) / 25000000000000000000), R := ((36758662946428571609 : Rat) / 50000000000000000000), D0 := ((36758662946428571609 : Rat) / 50000000000000000000), D1 := ((27062433303571428481 : Rat) / 25000000000000000000), D2 := ((45573930803571428481 : Rat) / 25000000000000000000), D3 := ((95154494732142857043 : Rat) / 50000000000000000000), D4 := ((51237820178571425981 : Rat) / 25000000000000000000), LB := ((2342607620460957 : Rat) / 2000000000000000000) }
]

def block421LeftCertificate : Bool :=
  allBoxesValid block421LeftBoxes &&
  coversFromBool block421LeftBoxes block421LeftL block421LeftR

theorem block421LeftCertificate_eq_true :
    block421LeftCertificate = true := by
  native_decide

def block421RightChunk000 : List RatBox := [
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43374444196428571519 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((2062433303571428481 : Rat) / 25000000000000000000), D2 := ((20573930803571428481 : Rat) / 25000000000000000000), D3 := ((45154494732142857043 : Rat) / 50000000000000000000), D4 := ((26237820178571425981 : Rat) / 25000000000000000000), LB := ((1134681976191351 : Rat) / 1000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((80103603 : Rat) / 40000000), D0 := ((80103603 : Rat) / 40000000), D1 := ((7404599 : Rat) / 40000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((41029628125000000081 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((2602763549080253 : Rat) / 5000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((80103603 : Rat) / 40000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((22213797 : Rat) / 40000000), D3 := ((31773879375000000081 : Rat) / 50000000000000000000), D4 := ((7819004999999999 : Rat) / 10000000000000000), LB := ((10464275450627497 : Rat) / 200000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((357437407 : Rat) / 160000000), D0 := ((357437407 : Rat) / 160000000), D1 := ((66641391 : Rat) / 160000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((22518130625000000081 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((3811767103995499 : Rat) / 50000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((357437407 : Rat) / 160000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((51832193 : Rat) / 160000000), D3 := ((20204193437500000081 : Rat) / 50000000000000000000), D4 := ((5505067812499999 : Rat) / 10000000000000000), LB := ((22808843033920723 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((182421003 : Rat) / 80000000), R := ((737088611 : Rat) / 320000000), D0 := ((737088611 : Rat) / 320000000), D1 := ((155496579 : Rat) / 320000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((17890256250000000081 : Rat) / 50000000000000000000), D4 := ((5042280374999999 : Rat) / 10000000000000000), LB := ((2299936209547919 : Rat) / 100000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((737088611 : Rat) / 320000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((81450589 : Rat) / 320000000), D3 := ((16733287656250000081 : Rat) / 50000000000000000000), D4 := ((4810886656249999 : Rat) / 10000000000000000), LB := ((5078378608544057 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((74449321 : Rat) / 32000000), R := ((1496391019 : Rat) / 640000000), D0 := ((1496391019 : Rat) / 640000000), D1 := ((66641391 : Rat) / 128000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((15576319062500000081 : Rat) / 50000000000000000000), D4 := ((4579492937499999 : Rat) / 10000000000000000), LB := ((5128331071843441 : Rat) / 500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1496391019 : Rat) / 640000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((140687381 : Rat) / 640000000), D3 := ((14997834765625000081 : Rat) / 50000000000000000000), D4 := ((4463796078124999 : Rat) / 10000000000000000), LB := ((1863490947114313 : Rat) / 500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((751897809 : Rat) / 320000000), R := ((602999167 : Rat) / 256000000), D0 := ((602999167 : Rat) / 256000000), D1 := ((688627707 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((14419350468750000081 : Rat) / 50000000000000000000), D4 := ((4348099218749999 : Rat) / 10000000000000000), LB := ((3905176812988083 : Rat) / 500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((602999167 : Rat) / 256000000), R := ((1511200217 : Rat) / 640000000), D0 := ((1511200217 : Rat) / 640000000), D1 := ((348016153 : Rat) / 640000000), D2 := ((51832193 : Rat) / 256000000), D3 := ((14130108320312500081 : Rat) / 50000000000000000000), D4 := ((4290250789062499 : Rat) / 10000000000000000), LB := ((5211576698655129 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1511200217 : Rat) / 640000000), R := ((3029805033 : Rat) / 1280000000), D0 := ((3029805033 : Rat) / 1280000000), D1 := ((140687381 : Rat) / 256000000), D2 := ((125878183 : Rat) / 640000000), D3 := ((13840866171875000081 : Rat) / 50000000000000000000), D4 := ((4232402359374999 : Rat) / 10000000000000000), LB := ((28363687753684003 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3029805033 : Rat) / 1280000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((244351767 : Rat) / 1280000000), D3 := ((13551624023437500081 : Rat) / 50000000000000000000), D4 := ((4174553929687499 : Rat) / 10000000000000000), LB := ((172193857025469 : Rat) / 250000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((6081823863 : Rat) / 2560000000), D0 := ((6081823863 : Rat) / 2560000000), D1 := ((1429087607 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((13262381875000000081 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((17617063655632967 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6081823863 : Rat) / 2560000000), R := ((3044614231 : Rat) / 1280000000), D0 := ((3044614231 : Rat) / 1280000000), D1 := ((718246103 : Rat) / 1280000000), D2 := ((466489737 : Rat) / 2560000000), D3 := ((13117760800781250081 : Rat) / 50000000000000000000), D4 := ((4087781285156249 : Rat) / 10000000000000000), LB := ((26345430302773393 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3044614231 : Rat) / 1280000000), R := ((6096633061 : Rat) / 2560000000), D0 := ((6096633061 : Rat) / 2560000000), D1 := ((288779361 : Rat) / 512000000), D2 := ((229542569 : Rat) / 1280000000), D3 := ((12973139726562500081 : Rat) / 50000000000000000000), D4 := ((4058857070312499 : Rat) / 10000000000000000), LB := ((18057513922630497 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6096633061 : Rat) / 2560000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((451680539 : Rat) / 2560000000), D3 := ((12828518652343750081 : Rat) / 50000000000000000000), D4 := ((4029932855468749 : Rat) / 10000000000000000), LB := ((207544116550909 : Rat) / 200000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((305201883 : Rat) / 128000000), R := ((6111442259 : Rat) / 2560000000), D0 := ((6111442259 : Rat) / 2560000000), D1 := ((1458706003 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 128000000), D3 := ((12683897578125000081 : Rat) / 50000000000000000000), D4 := ((4001008640624999 : Rat) / 10000000000000000), LB := ((6623302679774623 : Rat) / 20000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6111442259 : Rat) / 2560000000), R := ((12230289117 : Rat) / 5120000000), D0 := ((12230289117 : Rat) / 5120000000), D1 := ((584963321 : Rat) / 1024000000), D2 := ((436871341 : Rat) / 2560000000), D3 := ((12539276503906250081 : Rat) / 50000000000000000000), D4 := ((3972084425781249 : Rat) / 10000000000000000), LB := ((20208106048743707 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12230289117 : Rat) / 5120000000), R := ((3059423429 : Rat) / 1280000000), D0 := ((3059423429 : Rat) / 1280000000), D1 := ((733055301 : Rat) / 1280000000), D2 := ((866338083 : Rat) / 5120000000), D3 := ((12466965966796875081 : Rat) / 50000000000000000000), D4 := ((1978811159179687 : Rat) / 5000000000000000), LB := ((17174947997417311 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3059423429 : Rat) / 1280000000), R := ((2449019663 : Rat) / 1024000000), D0 := ((2449019663 : Rat) / 1024000000), D1 := ((2939625803 : Rat) / 5120000000), D2 := ((214733371 : Rat) / 1280000000), D3 := ((12394655429687500081 : Rat) / 50000000000000000000), D4 := ((3943160210937499 : Rat) / 10000000000000000), LB := ((14300530649309917 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2449019663 : Rat) / 1024000000), R := ((6126251457 : Rat) / 2560000000), D0 := ((6126251457 : Rat) / 2560000000), D1 := ((1473515201 : Rat) / 2560000000), D2 := ((170305777 : Rat) / 1024000000), D3 := ((12322344892578125081 : Rat) / 50000000000000000000), D4 := ((491087262939453 : Rat) / 1250000000000000), LB := ((2896471413258439 : Rat) / 2500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6126251457 : Rat) / 2560000000), R := ((12259907513 : Rat) / 5120000000), D0 := ((12259907513 : Rat) / 5120000000), D1 := ((2954435001 : Rat) / 5120000000), D2 := ((422062143 : Rat) / 2560000000), D3 := ((12250034355468750081 : Rat) / 50000000000000000000), D4 := ((3914235996093749 : Rat) / 10000000000000000), LB := ((1806413587417649 : Rat) / 2000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12259907513 : Rat) / 5120000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((836719687 : Rat) / 5120000000), D3 := ((12177723818359375081 : Rat) / 50000000000000000000), D4 := ((1949886944335937 : Rat) / 5000000000000000), LB := ((1660039049301877 : Rat) / 2500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((766707007 : Rat) / 320000000), R := ((12274716711 : Rat) / 5120000000), D0 := ((12274716711 : Rat) / 5120000000), D1 := ((2969244199 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((12105413281250000081 : Rat) / 50000000000000000000), D4 := ((3885311781249999 : Rat) / 10000000000000000), LB := ((44112533987147873 : Rat) / 100000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12274716711 : Rat) / 5120000000), R := ((1228212131 : Rat) / 512000000), D0 := ((1228212131 : Rat) / 512000000), D1 := ((1488324399 : Rat) / 2560000000), D2 := ((821910489 : Rat) / 5120000000), D3 := ((12033102744140625081 : Rat) / 50000000000000000000), D4 := ((967712418457031 : Rat) / 2500000000000000), LB := ((2346487294489219 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1228212131 : Rat) / 512000000), R := ((12289525909 : Rat) / 5120000000), D0 := ((12289525909 : Rat) / 5120000000), D1 := ((2984053397 : Rat) / 5120000000), D2 := ((81450589 : Rat) / 512000000), D3 := ((11960792207031250081 : Rat) / 50000000000000000000), D4 := ((3856387566406249 : Rat) / 10000000000000000), LB := ((2235054795235447 : Rat) / 50000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12289525909 : Rat) / 5120000000), R := ((24586456417 : Rat) / 10240000000), D0 := ((24586456417 : Rat) / 10240000000), D1 := ((5975511393 : Rat) / 10240000000), D2 := ((807101291 : Rat) / 5120000000), D3 := ((11888481669921875081 : Rat) / 50000000000000000000), D4 := ((1920962729492187 : Rat) / 5000000000000000), LB := ((5096117300508393 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24586456417 : Rat) / 10240000000), R := ((3074232627 : Rat) / 1280000000), D0 := ((3074232627 : Rat) / 1280000000), D1 := ((747864499 : Rat) / 1280000000), D2 := ((1606797983 : Rat) / 10240000000), D3 := ((11852326401367187581 : Rat) / 50000000000000000000), D4 := ((7669388810546873 : Rat) / 20000000000000000), LB := ((9377153216316297 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3074232627 : Rat) / 1280000000), R := ((4920253123 : Rat) / 2048000000), D0 := ((4920253123 : Rat) / 2048000000), D1 := ((5990320591 : Rat) / 10240000000), D2 := ((199924173 : Rat) / 1280000000), D3 := ((11816171132812500081 : Rat) / 50000000000000000000), D4 := ((3827463351562499 : Rat) / 10000000000000000), LB := ((344166781918559 : Rat) / 400000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4920253123 : Rat) / 2048000000), R := ((12304335107 : Rat) / 5120000000), D0 := ((12304335107 : Rat) / 5120000000), D1 := ((599772519 : Rat) / 1024000000), D2 := ((318397757 : Rat) / 2048000000), D3 := ((11780015864257812581 : Rat) / 50000000000000000000), D4 := ((7640464595703123 : Rat) / 20000000000000000), LB := ((1968359600157607 : Rat) / 2500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12304335107 : Rat) / 5120000000), R := ((24616074813 : Rat) / 10240000000), D0 := ((24616074813 : Rat) / 10240000000), D1 := ((6005129789 : Rat) / 10240000000), D2 := ((792292093 : Rat) / 5120000000), D3 := ((11743860595703125081 : Rat) / 50000000000000000000), D4 := ((238312577758789 : Rat) / 625000000000000), LB := ((718511630624169 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24616074813 : Rat) / 10240000000), R := ((6155869853 : Rat) / 2560000000), D0 := ((6155869853 : Rat) / 2560000000), D1 := ((1503133597 : Rat) / 2560000000), D2 := ((1577179587 : Rat) / 10240000000), D3 := ((11707705327148437581 : Rat) / 50000000000000000000), D4 := ((7611540380859373 : Rat) / 20000000000000000), LB := ((3269680771675401 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6155869853 : Rat) / 2560000000), R := ((24630884011 : Rat) / 10240000000), D0 := ((24630884011 : Rat) / 10240000000), D1 := ((6019938987 : Rat) / 10240000000), D2 := ((392443747 : Rat) / 2560000000), D3 := ((11671550058593750081 : Rat) / 50000000000000000000), D4 := ((3798539136718749 : Rat) / 10000000000000000), LB := ((5936334156753237 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24630884011 : Rat) / 10240000000), R := ((2463828861 : Rat) / 1024000000), D0 := ((2463828861 : Rat) / 1024000000), D1 := ((3013671793 : Rat) / 5120000000), D2 := ((1562370389 : Rat) / 10240000000), D3 := ((11635394790039062581 : Rat) / 50000000000000000000), D4 := ((7582616166015623 : Rat) / 20000000000000000), LB := ((5376195977455783 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2463828861 : Rat) / 1024000000), R := ((24645693209 : Rat) / 10240000000), D0 := ((24645693209 : Rat) / 10240000000), D1 := ((1206949637 : Rat) / 2048000000), D2 := ((155496579 : Rat) / 1024000000), D3 := ((11599239521484375081 : Rat) / 50000000000000000000), D4 := ((1892038514648437 : Rat) / 5000000000000000), LB := ((60738883036867 : Rat) / 125000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24645693209 : Rat) / 10240000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((1547561191 : Rat) / 10240000000), D3 := ((11563084252929687581 : Rat) / 50000000000000000000), D4 := ((7553691951171873 : Rat) / 20000000000000000), LB := ((21926218089077243 : Rat) / 50000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((24660502407 : Rat) / 10240000000), D0 := ((24660502407 : Rat) / 10240000000), D1 := ((6049557383 : Rat) / 10240000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((11526928984375000081 : Rat) / 50000000000000000000), D4 := ((3769614921874999 : Rat) / 10000000000000000), LB := ((988690553657863 : Rat) / 2500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24660502407 : Rat) / 10240000000), R := ((12333953503 : Rat) / 5120000000), D0 := ((12333953503 : Rat) / 5120000000), D1 := ((3028480991 : Rat) / 5120000000), D2 := ((1532751993 : Rat) / 10240000000), D3 := ((11490773715820312581 : Rat) / 50000000000000000000), D4 := ((7524767736328123 : Rat) / 20000000000000000), LB := ((3567835615249093 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12333953503 : Rat) / 5120000000), R := ((4935062321 : Rat) / 2048000000), D0 := ((4935062321 : Rat) / 2048000000), D1 := ((6064366581 : Rat) / 10240000000), D2 := ((762673697 : Rat) / 5120000000), D3 := ((11454618447265625081 : Rat) / 50000000000000000000), D4 := ((938788203613281 : Rat) / 2500000000000000), LB := ((3224634892390471 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4935062321 : Rat) / 2048000000), R := ((6170679051 : Rat) / 2560000000), D0 := ((6170679051 : Rat) / 2560000000), D1 := ((303588559 : Rat) / 512000000), D2 := ((303588559 : Rat) / 2048000000), D3 := ((11418463178710937581 : Rat) / 50000000000000000000), D4 := ((7495843521484373 : Rat) / 20000000000000000), LB := ((14626665158026797 : Rat) / 50000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6170679051 : Rat) / 2560000000), R := ((24690120803 : Rat) / 10240000000), D0 := ((24690120803 : Rat) / 10240000000), D1 := ((6079175779 : Rat) / 10240000000), D2 := ((377634549 : Rat) / 2560000000), D3 := ((11382307910156250081 : Rat) / 50000000000000000000), D4 := ((3740690707031249 : Rat) / 10000000000000000), LB := ((13350524767835603 : Rat) / 50000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24690120803 : Rat) / 10240000000), R := ((12348762701 : Rat) / 5120000000), D0 := ((12348762701 : Rat) / 5120000000), D1 := ((3043290189 : Rat) / 5120000000), D2 := ((1503133597 : Rat) / 10240000000), D3 := ((11346152641601562581 : Rat) / 50000000000000000000), D4 := ((7466919306640623 : Rat) / 20000000000000000), LB := ((24591275367555343 : Rat) / 100000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12348762701 : Rat) / 5120000000), R := ((24704930001 : Rat) / 10240000000), D0 := ((24704930001 : Rat) / 10240000000), D1 := ((6093984977 : Rat) / 10240000000), D2 := ((747864499 : Rat) / 5120000000), D3 := ((11309997373046875081 : Rat) / 50000000000000000000), D4 := ((1863114299804687 : Rat) / 5000000000000000), LB := ((2292579640486847 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24704930001 : Rat) / 10240000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((1488324399 : Rat) / 10240000000), D3 := ((11273842104492187581 : Rat) / 50000000000000000000), D4 := ((7437995091796873 : Rat) / 20000000000000000), LB := ((4341284256636213 : Rat) / 20000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((123561673 : Rat) / 51200000), R := ((24719739199 : Rat) / 10240000000), D0 := ((24719739199 : Rat) / 10240000000), D1 := ((244351767 : Rat) / 409600000), D2 := ((7404599 : Rat) / 51200000), D3 := ((11237686835937500081 : Rat) / 50000000000000000000), D4 := ((3711766492187499 : Rat) / 10000000000000000), LB := ((4186995783695413 : Rat) / 20000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24719739199 : Rat) / 10240000000), R := ((12363571899 : Rat) / 5120000000), D0 := ((12363571899 : Rat) / 5120000000), D1 := ((3058099387 : Rat) / 5120000000), D2 := ((1473515201 : Rat) / 10240000000), D3 := ((11201531567382812581 : Rat) / 50000000000000000000), D4 := ((7409070876953123 : Rat) / 20000000000000000), LB := ((20613318748859133 : Rat) / 100000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12363571899 : Rat) / 5120000000), R := ((24734548397 : Rat) / 10240000000), D0 := ((24734548397 : Rat) / 10240000000), D1 := ((6123603373 : Rat) / 10240000000), D2 := ((733055301 : Rat) / 5120000000), D3 := ((11165376298828125081 : Rat) / 50000000000000000000), D4 := ((462163048095703 : Rat) / 1250000000000000), LB := ((2074331098068649 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24734548397 : Rat) / 10240000000), R := ((6185488249 : Rat) / 2560000000), D0 := ((6185488249 : Rat) / 2560000000), D1 := ((1532751993 : Rat) / 2560000000), D2 := ((1458706003 : Rat) / 10240000000), D3 := ((11129221030273437581 : Rat) / 50000000000000000000), D4 := ((7380146662109373 : Rat) / 20000000000000000), LB := ((10663423419012691 : Rat) / 50000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6185488249 : Rat) / 2560000000), R := ((4949871519 : Rat) / 2048000000), D0 := ((4949871519 : Rat) / 2048000000), D1 := ((6138412571 : Rat) / 10240000000), D2 := ((362825351 : Rat) / 2560000000), D3 := ((11093065761718750081 : Rat) / 50000000000000000000), D4 := ((3682842277343749 : Rat) / 10000000000000000), LB := ((1397864926051557 : Rat) / 6250000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4949871519 : Rat) / 2048000000), R := ((12378381097 : Rat) / 5120000000), D0 := ((12378381097 : Rat) / 5120000000), D1 := ((614581717 : Rat) / 1024000000), D2 := ((288779361 : Rat) / 2048000000), D3 := ((11056910493164062581 : Rat) / 50000000000000000000), D4 := ((7351222447265623 : Rat) / 20000000000000000), LB := ((23862220942977297 : Rat) / 100000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12378381097 : Rat) / 5120000000), R := ((24764166793 : Rat) / 10240000000), D0 := ((24764166793 : Rat) / 10240000000), D1 := ((6153221769 : Rat) / 10240000000), D2 := ((718246103 : Rat) / 5120000000), D3 := ((11020755224609375081 : Rat) / 50000000000000000000), D4 := ((1834190084960937 : Rat) / 5000000000000000), LB := ((25817949034950827 : Rat) / 100000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24764166793 : Rat) / 10240000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((1429087607 : Rat) / 10240000000), D3 := ((10984599956054687581 : Rat) / 50000000000000000000), D4 := ((7322298232421873 : Rat) / 20000000000000000), LB := ((2823500097050291 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((387055803 : Rat) / 160000000), R := ((24778975991 : Rat) / 10240000000), D0 := ((24778975991 : Rat) / 10240000000), D1 := ((6168030967 : Rat) / 10240000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((10948444687500000081 : Rat) / 50000000000000000000), D4 := ((3653918062499999 : Rat) / 10000000000000000), LB := ((3111537695777017 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24778975991 : Rat) / 10240000000), R := ((2478638059 : Rat) / 1024000000), D0 := ((2478638059 : Rat) / 1024000000), D1 := ((3087717783 : Rat) / 5120000000), D2 := ((1414278409 : Rat) / 10240000000), D3 := ((10912289418945312581 : Rat) / 50000000000000000000), D4 := ((7293374017578123 : Rat) / 20000000000000000), LB := ((1723054990574041 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2478638059 : Rat) / 1024000000), R := ((24793785189 : Rat) / 10240000000), D0 := ((24793785189 : Rat) / 10240000000), D1 := ((1236568033 : Rat) / 2048000000), D2 := ((140687381 : Rat) / 1024000000), D3 := ((10876134150390625081 : Rat) / 50000000000000000000), D4 := ((909863988769531 : Rat) / 2500000000000000), LB := ((3827421523311947 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24793785189 : Rat) / 10240000000), R := ((6200297447 : Rat) / 2560000000), D0 := ((6200297447 : Rat) / 2560000000), D1 := ((1547561191 : Rat) / 2560000000), D2 := ((1399469211 : Rat) / 10240000000), D3 := ((10839978881835937581 : Rat) / 50000000000000000000), D4 := ((7264449802734373 : Rat) / 20000000000000000), LB := ((2127839604806961 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6200297447 : Rat) / 2560000000), R := ((24808594387 : Rat) / 10240000000), D0 := ((24808594387 : Rat) / 10240000000), D1 := ((6197649363 : Rat) / 10240000000), D2 := ((348016153 : Rat) / 2560000000), D3 := ((10803823613281250081 : Rat) / 50000000000000000000), D4 := ((3624993847656249 : Rat) / 10000000000000000), LB := ((236554613680523 : Rat) / 500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24808594387 : Rat) / 10240000000), R := ((12407999493 : Rat) / 5120000000), D0 := ((12407999493 : Rat) / 5120000000), D1 := ((3102526981 : Rat) / 5120000000), D2 := ((1384660013 : Rat) / 10240000000), D3 := ((10767668344726562581 : Rat) / 50000000000000000000), D4 := ((7235525587890623 : Rat) / 20000000000000000), LB := ((656734040565439 : Rat) / 1250000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12407999493 : Rat) / 5120000000), R := ((4964680717 : Rat) / 2048000000), D0 := ((4964680717 : Rat) / 2048000000), D1 := ((6212458561 : Rat) / 10240000000), D2 := ((688627707 : Rat) / 5120000000), D3 := ((10731513076171875081 : Rat) / 50000000000000000000), D4 := ((1805265870117187 : Rat) / 5000000000000000), LB := ((5824233377271781 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4964680717 : Rat) / 2048000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((273970163 : Rat) / 2048000000), D3 := ((10695357807617187581 : Rat) / 50000000000000000000), D4 := ((7206601373046873 : Rat) / 20000000000000000), LB := ((6442391882942877 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((24838212783 : Rat) / 10240000000), D0 := ((24838212783 : Rat) / 10240000000), D1 := ((6227267759 : Rat) / 10240000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((10659202539062500081 : Rat) / 50000000000000000000), D4 := ((3596069632812499 : Rat) / 10000000000000000), LB := ((1421713351968057 : Rat) / 2000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24838212783 : Rat) / 10240000000), R := ((12422808691 : Rat) / 5120000000), D0 := ((12422808691 : Rat) / 5120000000), D1 := ((3117336179 : Rat) / 5120000000), D2 := ((1355041617 : Rat) / 10240000000), D3 := ((10623047270507812581 : Rat) / 50000000000000000000), D4 := ((7177677158203123 : Rat) / 20000000000000000), LB := ((977872428125099 : Rat) / 1250000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12422808691 : Rat) / 5120000000), R := ((24853021981 : Rat) / 10240000000), D0 := ((24853021981 : Rat) / 10240000000), D1 := ((6242076957 : Rat) / 10240000000), D2 := ((673818509 : Rat) / 5120000000), D3 := ((10586892001953125081 : Rat) / 50000000000000000000), D4 := ((111925235168457 : Rat) / 312500000000000), LB := ((8585853826324347 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24853021981 : Rat) / 10240000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((1340232419 : Rat) / 10240000000), D3 := ((10550736733398437581 : Rat) / 50000000000000000000), D4 := ((7148752943359373 : Rat) / 20000000000000000), LB := ((939741647522363 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((24867831179 : Rat) / 10240000000), D0 := ((24867831179 : Rat) / 10240000000), D1 := ((1251377231 : Rat) / 2048000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((10514581464843750081 : Rat) / 50000000000000000000), D4 := ((3567145417968749 : Rat) / 10000000000000000), LB := ((102578964798003 : Rat) / 100000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((24867831179 : Rat) / 10240000000), R := ((12437617889 : Rat) / 5120000000), D0 := ((12437617889 : Rat) / 5120000000), D1 := ((3132145377 : Rat) / 5120000000), D2 := ((1325423221 : Rat) / 10240000000), D3 := ((10478426196289062581 : Rat) / 50000000000000000000), D4 := ((7119828728515623 : Rat) / 20000000000000000), LB := ((558376278933799 : Rat) / 500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12437617889 : Rat) / 5120000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((659009311 : Rat) / 5120000000), D3 := ((10442270927734375081 : Rat) / 50000000000000000000), D4 := ((1776341655273437 : Rat) / 5000000000000000), LB := ((10837684476849851 : Rat) / 100000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((12452427087 : Rat) / 5120000000), D0 := ((12452427087 : Rat) / 5120000000), D1 := ((125878183 : Rat) / 204800000), D2 := ((81450589 : Rat) / 640000000), D3 := ((10369960390625000081 : Rat) / 50000000000000000000), D4 := ((3538221203124999 : Rat) / 10000000000000000), LB := ((3964572617114713 : Rat) / 12500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12452427087 : Rat) / 5120000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((644200113 : Rat) / 5120000000), D3 := ((10297649853515625081 : Rat) / 50000000000000000000), D4 := ((880939773925781 : Rat) / 2500000000000000), LB := ((2729935711899001 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((2493447257 : Rat) / 1024000000), D0 := ((2493447257 : Rat) / 1024000000), D1 := ((3161763773 : Rat) / 5120000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((10225339316406250081 : Rat) / 50000000000000000000), D4 := ((3509296988281249 : Rat) / 10000000000000000), LB := ((397519194043211 : Rat) / 500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2493447257 : Rat) / 1024000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((125878183 : Rat) / 1024000000), D3 := ((10153028779296875081 : Rat) / 50000000000000000000), D4 := ((1747417440429687 : Rat) / 5000000000000000), LB := ((10645217054531947 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((10080718242187500081 : Rat) / 50000000000000000000), D4 := ((3480372773437499 : Rat) / 10000000000000000), LB := ((6773219967923863 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((10008407705078125081 : Rat) / 50000000000000000000), D4 := ((433238833251953 : Rat) / 1250000000000000), LB := ((8328085108631547 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((9936097167968750081 : Rat) / 50000000000000000000), D4 := ((3451448558593749 : Rat) / 10000000000000000), LB := ((19976575639905347 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((9863786630859375081 : Rat) / 50000000000000000000), D4 := ((1718493225585937 : Rat) / 5000000000000000), LB := ((587746884755963 : Rat) / 250000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((9791476093750000081 : Rat) / 50000000000000000000), D4 := ((3422524343749999 : Rat) / 10000000000000000), LB := ((557001715013633 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((9646855019531250081 : Rat) / 50000000000000000000), D4 := ((3393600128906249 : Rat) / 10000000000000000), LB := ((6900617209534693 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((9502233945312500081 : Rat) / 50000000000000000000), D4 := ((3364675914062499 : Rat) / 10000000000000000), LB := ((22921093446060387 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((9357612871093750081 : Rat) / 50000000000000000000), D4 := ((3335751699218749 : Rat) / 10000000000000000), LB := ((411873060456789 : Rat) / 125000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((9212991796875000081 : Rat) / 50000000000000000000), D4 := ((3306827484374999 : Rat) / 10000000000000000), LB := ((6373197128558411 : Rat) / 50000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((8923749648437500081 : Rat) / 50000000000000000000), D4 := ((3248979054687499 : Rat) / 10000000000000000), LB := ((13188575552161713 : Rat) / 5000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((8634507500000000081 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((11095651901852327 : Rat) / 2000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((632617563 : Rat) / 256000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((8345265351562500081 : Rat) / 50000000000000000000), D4 := ((3133282195312499 : Rat) / 10000000000000000), LB := ((4439563750691003 : Rat) / 500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((8056023203125000081 : Rat) / 50000000000000000000), D4 := ((3075433765624999 : Rat) / 10000000000000000), LB := ((1763337744062371 : Rat) / 400000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((796325403 : Rat) / 320000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((7477538906250000081 : Rat) / 50000000000000000000), D4 := ((2959736906249999 : Rat) / 10000000000000000), LB := ((13515232121770249 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((320011081 : Rat) / 128000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((6899054609375000081 : Rat) / 50000000000000000000), D4 := ((2844040046874999 : Rat) / 10000000000000000), LB := ((495140957204169 : Rat) / 20000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((6320570312500000081 : Rat) / 50000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((11379509921094731 : Rat) / 500000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((5163601718750000081 : Rat) / 50000000000000000000), D4 := ((2496949468749999 : Rat) / 10000000000000000), LB := ((7458302320488967 : Rat) / 125000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((131903383125000000081 : Rat) / 50000000000000000000), D0 := ((131903383125000000081 : Rat) / 50000000000000000000), D1 := ((41029628125000000081 : Rat) / 50000000000000000000), D2 := ((4006633125000000081 : Rat) / 50000000000000000000), D3 := ((4006633125000000081 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((1058397371259609 : Rat) / 25000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((131903383125000000081 : Rat) / 50000000000000000000), R := ((26866204607142857169 : Rat) / 10000000000000000000), D0 := ((26866204607142857169 : Rat) / 10000000000000000000), D1 := ((8691453607142857169 : Rat) / 10000000000000000000), D2 := ((1286854607142857169 : Rat) / 10000000000000000000), D3 := ((606909977678571441 : Rat) / 12500000000000000000), D4 := ((7321145624999994919 : Rat) / 50000000000000000000), LB := ((8544927292986959 : Rat) / 50000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((26866204607142857169 : Rat) / 10000000000000000000), R := ((135544842991071428727 : Rat) / 50000000000000000000), D0 := ((135544842991071428727 : Rat) / 50000000000000000000), D1 := ((44671087991071428727 : Rat) / 50000000000000000000), D2 := ((7648092991071428727 : Rat) / 50000000000000000000), D3 := ((1820729933035714323 : Rat) / 25000000000000000000), D4 := ((978701142857141831 : Rat) / 10000000000000000000), LB := ((5634864101444853 : Rat) / 100000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((135544842991071428727 : Rat) / 50000000000000000000), R := ((17018969121093750021 : Rat) / 6250000000000000000), D0 := ((17018969121093750021 : Rat) / 6250000000000000000), D1 := ((5659749746093750021 : Rat) / 6250000000000000000), D2 := ((1031875371093750021 : Rat) / 6250000000000000000), D3 := ((4248369843750000087 : Rat) / 50000000000000000000), D4 := ((3679685758928566273 : Rat) / 50000000000000000000), LB := ((20832164936525593 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17018969121093750021 : Rat) / 6250000000000000000), R := ((272910415915178571777 : Rat) / 100000000000000000000), D0 := ((272910415915178571777 : Rat) / 100000000000000000000), D1 := ((91162905915178571777 : Rat) / 100000000000000000000), D2 := ((17116915915178571777 : Rat) / 100000000000000000000), D3 := ((1820729933035714323 : Rat) / 20000000000000000000), D4 := ((192048486328124677 : Rat) / 3125000000000000000), LB := ((8720743955627719 : Rat) / 1000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((272910415915178571777 : Rat) / 100000000000000000000), R := ((109285548361607142999 : Rat) / 40000000000000000000), D0 := ((109285548361607142999 : Rat) / 40000000000000000000), D1 := ((36586544361607142999 : Rat) / 40000000000000000000), D2 := ((6968148361607142999 : Rat) / 40000000000000000000), D3 := ((18814209308035714671 : Rat) / 200000000000000000000), D4 := ((5538641584821418223 : Rat) / 100000000000000000000), LB := ((871466550672223 : Rat) / 200000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((109285548361607142999 : Rat) / 40000000000000000000), R := ((1093462393593750001431 : Rat) / 400000000000000000000), D0 := ((1093462393593750001431 : Rat) / 400000000000000000000), D1 := ((366472353593750001431 : Rat) / 400000000000000000000), D2 := ((70288393593750001431 : Rat) / 400000000000000000000), D3 := ((38235328593750000783 : Rat) / 400000000000000000000), D4 := ((2094074638392853001 : Rat) / 40000000000000000000), LB := ((26645871879406313 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1093462393593750001431 : Rat) / 400000000000000000000), R := ((2187531697165178574303 : Rat) / 800000000000000000000), D0 := ((2187531697165178574303 : Rat) / 800000000000000000000), D1 := ((733551617165178574303 : Rat) / 800000000000000000000), D2 := ((141183697165178574303 : Rat) / 800000000000000000000), D3 := ((77077567165178573007 : Rat) / 800000000000000000000), D4 := ((20333836406249958569 : Rat) / 400000000000000000000), LB := ((19518565692810963 : Rat) / 10000000000000000000) },
  { w1 := ((1709280858511049 : Rat) / 2500000000000000), w2 := (0 : Rat), w3 := ((297827575885721 : Rat) / 1000000000000000), w4 := ((4224741710678209 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((131903383125000000081 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2187531697165178574303 : Rat) / 800000000000000000000), R := ((136758662946428571609 : Rat) / 50000000000000000000), D0 := ((136758662946428571609 : Rat) / 50000000000000000000), D1 := ((45884907946428571609 : Rat) / 50000000000000000000), D2 := ((8861912946428571609 : Rat) / 50000000000000000000), D3 := ((606909977678571441 : Rat) / 6250000000000000000), D4 := ((40060762834821345697 : Rat) / 800000000000000000000), LB := ((435736751613347 : Rat) / 10000000000000000000) }
]

def block421RightChunk000L : Rat := ((43374444196428571519 : Rat) / 25000000000000000000)
def block421RightChunk000R : Rat := ((136758662946428571609 : Rat) / 50000000000000000000)

def block421RightChunk000Certificate : Bool :=
  allBoxesValid block421RightChunk000 &&
  coversFromBool block421RightChunk000 block421RightChunk000L block421RightChunk000R

theorem block421RightChunk000Certificate_eq_true :
    block421RightChunk000Certificate = true := by
  native_decide

def block421RightChainCertificate : Bool :=
  decide (
    block421RightL = ((43374444196428571519 : Rat) / 25000000000000000000) /\
    ((136758662946428571609 : Rat) / 50000000000000000000) = block421RightR)

theorem block421RightChainCertificate_eq_true :
    block421RightChainCertificate = true := by
  native_decide

def block421LeftBoxCount : Nat := boxCount block421LeftBoxes
def block421RightBoxCount : Nat := 98

def block421_rational_certificate : Prop :=
    block421LeftCertificate = true /\
    block421RightChainCertificate = true /\
    block421RightChunk000Certificate = true

theorem block421_rational_certificate_proof :
    block421_rational_certificate := by
  exact ⟨block421LeftCertificate_eq_true, block421RightChainCertificate_eq_true, block421RightChunk000Certificate_eq_true⟩

end Block421
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block421

open Set

def block421W1 : Rat := ((1709280858511049 : Rat) / 2500000000000000)
def block421W2 : Rat := (0 : Rat)
def block421W3 : Rat := ((297827575885721 : Rat) / 1000000000000000)
def block421W4 : Rat := ((4224741710678209 : Rat) / 50000000000000000)
def block421S1 : Rat := ((18174751 : Rat) / 10000000)
def block421S2 : Rat := ((511587 : Rat) / 200000)
def block421S3 : Rat := ((131903383125000000081 : Rat) / 50000000000000000000)
def block421S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block421V (y : ℝ) : ℝ :=
  ratPotential block421W1 block421W2 block421W3 block421W4 block421S1 block421S2 block421S3 block421S4 y

def block421LeftParamsCertificate : Bool :=
  allBoxesSameParams block421LeftBoxes block421W1 block421W2 block421W3 block421W4 block421S1 block421S2 block421S3 block421S4

theorem block421LeftParamsCertificate_eq_true :
    block421LeftParamsCertificate = true := by
  native_decide

theorem block421_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block421LeftL : ℝ) (block421LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block421S1 : ℝ))
    (hy2ne : y ≠ (block421S2 : ℝ))
    (hy3ne : y ≠ (block421S3 : ℝ))
    (hy4ne : y ≠ (block421S4 : ℝ)) :
    0 < block421V y := by
  have hcert := block421LeftCertificate_eq_true
  unfold block421LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block421LeftBoxes) (lo := block421LeftL) (hi := block421LeftR)
    (w1 := block421W1) (w2 := block421W2) (w3 := block421W3) (w4 := block421W4)
    (s1 := block421S1) (s2 := block421S2) (s3 := block421S3) (s4 := block421S4)
    hboxes hcover block421LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block421RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block421RightChunk000 block421W1 block421W2 block421W3 block421W4 block421S1 block421S2 block421S3 block421S4

theorem block421RightChunk000ParamsCertificate_eq_true :
    block421RightChunk000ParamsCertificate = true := by
  native_decide

theorem block421_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block421RightChunk000L : ℝ) (block421RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block421S1 : ℝ))
    (hy2ne : y ≠ (block421S2 : ℝ))
    (hy3ne : y ≠ (block421S3 : ℝ))
    (hy4ne : y ≠ (block421S4 : ℝ)) :
    0 < block421V y := by
  have hcert := block421RightChunk000Certificate_eq_true
  unfold block421RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block421RightChunk000) (lo := block421RightChunk000L) (hi := block421RightChunk000R)
    (w1 := block421W1) (w2 := block421W2) (w3 := block421W3) (w4 := block421W4)
    (s1 := block421S1) (s2 := block421S2) (s3 := block421S3) (s4 := block421S4)
    hboxes hcover block421RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block421_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block421RightL : ℝ) (block421RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block421S1 : ℝ))
    (hy2ne : y ≠ (block421S2 : ℝ))
    (hy3ne : y ≠ (block421S3 : ℝ))
    (hy4ne : y ≠ (block421S4 : ℝ)) :
    0 < block421V y := by
  have hL : (block421RightChunk000L : ℝ) = (block421RightL : ℝ) := by
    norm_num [block421RightChunk000L, block421RightL]
  have hR : (block421RightChunk000R : ℝ) = (block421RightR : ℝ) := by
    norm_num [block421RightChunk000R, block421RightR]
  have hyc : y ∈ Icc (block421RightChunk000L : ℝ) (block421RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block421_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block421_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block421LeftL : ℝ) (block421LeftR : ℝ) →
    y ≠ 0 → y ≠ (block421S1 : ℝ) → y ≠ (block421S2 : ℝ) →
    y ≠ (block421S3 : ℝ) → y ≠ (block421S4 : ℝ) → 0 < block421V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block421RightL : ℝ) (block421RightR : ℝ) →
    y ≠ 0 → y ≠ (block421S1 : ℝ) → y ≠ (block421S2 : ℝ) →
    y ≠ (block421S3 : ℝ) → y ≠ (block421S4 : ℝ) → 0 < block421V y)

theorem block421_reallog_certificate_proof :
    block421_reallog_certificate := by
  exact ⟨block421_left_V_pos, block421_right_V_pos⟩

end Block421
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block421.block421V
#check Erdos1038Lean.M1817475.Block421.block421_left_V_pos
#check Erdos1038Lean.M1817475.Block421.block421_right_V_pos
#check Erdos1038Lean.M1817475.Block421.block421_reallog_certificate_proof
