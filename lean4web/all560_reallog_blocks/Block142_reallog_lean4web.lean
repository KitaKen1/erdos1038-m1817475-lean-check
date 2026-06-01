/-
Self-contained Lean4Web paste file.
Block 142 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block142

def block142LeftL : Rat := ((39475988839285714347 : Rat) / 50000000000000000000)
def block142LeftR : Rat := ((19742881696428571459 : Rat) / 25000000000000000000)
def block142RightL : Rat := ((89475988839285714347 : Rat) / 50000000000000000000)
def block142RightR : Rat := ((69742881696428571459 : Rat) / 25000000000000000000)

def block142LeftBoxes : List RatBox := [
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((39475988839285714347 : Rat) / 50000000000000000000), R := ((19742881696428571459 : Rat) / 25000000000000000000), D0 := ((19742881696428571459 : Rat) / 25000000000000000000), D1 := ((51397766160714285653 : Rat) / 50000000000000000000), D2 := ((88420761160714285653 : Rat) / 50000000000000000000), D3 := ((1945511457142857139 : Rat) / 1000000000000000000), D4 := ((99748539910714280653 : Rat) / 50000000000000000000), LB := ((1260694747888317 : Rat) / 250000000000000000) }
]

def block142LeftCertificate : Bool :=
  allBoxesValid block142LeftBoxes &&
  coversFromBool block142LeftBoxes block142LeftL block142LeftR

theorem block142LeftCertificate_eq_true :
    block142LeftCertificate = true := by
  native_decide

def block142RightChunk000 : List RatBox := [
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((89475988839285714347 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1397766160714285653 : Rat) / 50000000000000000000), D2 := ((38420761160714285653 : Rat) / 50000000000000000000), D3 := ((945511457142857139 : Rat) / 1000000000000000000), D4 := ((49748539910714280653 : Rat) / 50000000000000000000), LB := ((103302086359599 : Rat) / 12500000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((45877806696428571297 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((2114129769853233 : Rat) / 1250000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((27366309196428571297 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((7268984343090531 : Rat) / 10000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((18110560446428571297 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((1716160492476631 : Rat) / 50000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((520441811696428571297 : Rat) / 200000000000000000000), D0 := ((520441811696428571297 : Rat) / 200000000000000000000), D1 := ((156946791696428571297 : Rat) / 200000000000000000000), D2 := ((8854811696428571297 : Rat) / 200000000000000000000), D3 := ((8854811696428571297 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((6437174545850427 : Rat) / 200000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((520441811696428571297 : Rat) / 200000000000000000000), R := ((1049738435089285713891 : Rat) / 400000000000000000000), D0 := ((1049738435089285713891 : Rat) / 400000000000000000000), D1 := ((322748395089285713891 : Rat) / 400000000000000000000), D2 := ((26564435089285713891 : Rat) / 400000000000000000000), D3 := ((26564435089285713891 : Rat) / 200000000000000000000), D4 := ((36456303303571408703 : Rat) / 200000000000000000000), LB := ((16150148823383143 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1049738435089285713891 : Rat) / 400000000000000000000), R := ((2108331681874999999079 : Rat) / 800000000000000000000), D0 := ((2108331681874999999079 : Rat) / 800000000000000000000), D1 := ((654351601874999999079 : Rat) / 800000000000000000000), D2 := ((61983681874999999079 : Rat) / 800000000000000000000), D3 := ((8854811696428571297 : Rat) / 80000000000000000000), D4 := ((64057794910714246109 : Rat) / 400000000000000000000), LB := ((8065036143956067 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2108331681874999999079 : Rat) / 800000000000000000000), R := ((264648311696428571297 : Rat) / 100000000000000000000), D0 := ((264648311696428571297 : Rat) / 100000000000000000000), D1 := ((82900801696428571297 : Rat) / 100000000000000000000), D2 := ((8854811696428571297 : Rat) / 100000000000000000000), D3 := ((79693305267857141673 : Rat) / 800000000000000000000), D4 := ((119260778124999920921 : Rat) / 800000000000000000000), LB := ((21951484395157927 : Rat) / 100000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((264648311696428571297 : Rat) / 100000000000000000000), R := ((4243227798839285712049 : Rat) / 1600000000000000000000), D0 := ((4243227798839285712049 : Rat) / 1600000000000000000000), D1 := ((1335267638839285712049 : Rat) / 1600000000000000000000), D2 := ((150531798839285712049 : Rat) / 1600000000000000000000), D3 := ((8854811696428571297 : Rat) / 100000000000000000000), D4 := ((13800745803571418703 : Rat) / 100000000000000000000), LB := ((2713059564116521 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4243227798839285712049 : Rat) / 1600000000000000000000), R := ((1699062081874999999079 : Rat) / 640000000000000000000), D0 := ((1699062081874999999079 : Rat) / 640000000000000000000), D1 := ((535878017874999999079 : Rat) / 640000000000000000000), D2 := ((61983681874999999079 : Rat) / 640000000000000000000), D3 := ((26564435089285713891 : Rat) / 320000000000000000000), D4 := ((211957121160714127951 : Rat) / 1600000000000000000000), LB := ((283144840899841 : Rat) / 31250000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1699062081874999999079 : Rat) / 640000000000000000000), R := ((2126041305267857141673 : Rat) / 800000000000000000000), D0 := ((2126041305267857141673 : Rat) / 800000000000000000000), D1 := ((672061225267857141673 : Rat) / 800000000000000000000), D2 := ((79693305267857141673 : Rat) / 800000000000000000000), D3 := ((256789539196428567613 : Rat) / 3200000000000000000000), D4 := ((83011886124999936921 : Rat) / 640000000000000000000), LB := ((821233574227101 : Rat) / 125000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2126041305267857141673 : Rat) / 800000000000000000000), R := ((8513020032767857137989 : Rat) / 3200000000000000000000), D0 := ((8513020032767857137989 : Rat) / 3200000000000000000000), D1 := ((2697099712767857137989 : Rat) / 3200000000000000000000), D2 := ((327628032767857137989 : Rat) / 3200000000000000000000), D3 := ((61983681874999999079 : Rat) / 800000000000000000000), D4 := ((101551154732142778327 : Rat) / 800000000000000000000), LB := ((4310802838877137 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8513020032767857137989 : Rat) / 3200000000000000000000), R := ((4260937422232142854643 : Rat) / 1600000000000000000000), D0 := ((4260937422232142854643 : Rat) / 1600000000000000000000), D1 := ((1352977262232142854643 : Rat) / 1600000000000000000000), D2 := ((168241422232142854643 : Rat) / 1600000000000000000000), D3 := ((239079915803571425019 : Rat) / 3200000000000000000000), D4 := ((397349807232142542011 : Rat) / 3200000000000000000000), LB := ((2296621848176611 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4260937422232142854643 : Rat) / 1600000000000000000000), R := ((8530729656160714280583 : Rat) / 3200000000000000000000), D0 := ((8530729656160714280583 : Rat) / 3200000000000000000000), D1 := ((2714809336160714280583 : Rat) / 3200000000000000000000), D2 := ((345337656160714280583 : Rat) / 3200000000000000000000), D3 := ((115112552053571426861 : Rat) / 1600000000000000000000), D4 := ((194247497767856985357 : Rat) / 1600000000000000000000), LB := ((1083844834661729 : Rat) / 2000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8530729656160714280583 : Rat) / 3200000000000000000000), R := ((17070314124017857132463 : Rat) / 6400000000000000000000), D0 := ((17070314124017857132463 : Rat) / 6400000000000000000000), D1 := ((5438473484017857132463 : Rat) / 6400000000000000000000), D2 := ((699530124017857132463 : Rat) / 6400000000000000000000), D3 := ((8854811696428571297 : Rat) / 128000000000000000000), D4 := ((379640183839285399417 : Rat) / 3200000000000000000000), LB := ((1804086536366531 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17070314124017857132463 : Rat) / 6400000000000000000000), R := ((213489611696428571297 : Rat) / 80000000000000000000), D0 := ((213489611696428571297 : Rat) / 80000000000000000000), D1 := ((68091603696428571297 : Rat) / 80000000000000000000), D2 := ((8854811696428571297 : Rat) / 80000000000000000000), D3 := ((433885773124999993553 : Rat) / 6400000000000000000000), D4 := ((750425555982142227537 : Rat) / 6400000000000000000000), LB := ((2970828679659143 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((213489611696428571297 : Rat) / 80000000000000000000), R := ((17088023747410714275057 : Rat) / 6400000000000000000000), D0 := ((17088023747410714275057 : Rat) / 6400000000000000000000), D1 := ((5456183107410714275057 : Rat) / 6400000000000000000000), D2 := ((717239747410714275057 : Rat) / 6400000000000000000000), D3 := ((26564435089285713891 : Rat) / 400000000000000000000), D4 := ((9269634303571420703 : Rat) / 80000000000000000000), LB := ((24093810563703133 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17088023747410714275057 : Rat) / 6400000000000000000000), R := ((8548439279553571423177 : Rat) / 3200000000000000000000), D0 := ((8548439279553571423177 : Rat) / 3200000000000000000000), D1 := ((2732518959553571423177 : Rat) / 3200000000000000000000), D2 := ((363047279553571423177 : Rat) / 3200000000000000000000), D3 := ((416176149732142850959 : Rat) / 6400000000000000000000), D4 := ((732715932589285084943 : Rat) / 6400000000000000000000), LB := ((19264360313393791 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8548439279553571423177 : Rat) / 3200000000000000000000), R := ((17105733370803571417651 : Rat) / 6400000000000000000000), D0 := ((17105733370803571417651 : Rat) / 6400000000000000000000), D1 := ((5473892730803571417651 : Rat) / 6400000000000000000000), D2 := ((734949370803571417651 : Rat) / 6400000000000000000000), D3 := ((203660669017857139831 : Rat) / 3200000000000000000000), D4 := ((361930560446428256823 : Rat) / 3200000000000000000000), LB := ((15247585593537727 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17105733370803571417651 : Rat) / 6400000000000000000000), R := ((4278647045624999997237 : Rat) / 1600000000000000000000), D0 := ((4278647045624999997237 : Rat) / 1600000000000000000000), D1 := ((1370686885624999997237 : Rat) / 1600000000000000000000), D2 := ((185951045624999997237 : Rat) / 1600000000000000000000), D3 := ((79693305267857141673 : Rat) / 1280000000000000000000), D4 := ((715006309196427942349 : Rat) / 6400000000000000000000), LB := ((2414572349735411 : Rat) / 2000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4278647045624999997237 : Rat) / 1600000000000000000000), R := ((3424688598839285712049 : Rat) / 1280000000000000000000), D0 := ((3424688598839285712049 : Rat) / 1280000000000000000000), D1 := ((1098320470839285712049 : Rat) / 1280000000000000000000), D2 := ((150531798839285712049 : Rat) / 1280000000000000000000), D3 := ((97402928660714284267 : Rat) / 1600000000000000000000), D4 := ((176537874374999842763 : Rat) / 1600000000000000000000), LB := ((9771439237232227 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3424688598839285712049 : Rat) / 1280000000000000000000), R := ((8566148902946428565771 : Rat) / 3200000000000000000000), D0 := ((8566148902946428565771 : Rat) / 3200000000000000000000), D1 := ((2750228582946428565771 : Rat) / 3200000000000000000000), D2 := ((380756902946428565771 : Rat) / 3200000000000000000000), D3 := ((380756902946428565771 : Rat) / 6400000000000000000000), D4 := ((139459337160714159951 : Rat) / 1280000000000000000000), LB := ((8376609745968933 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8566148902946428565771 : Rat) / 3200000000000000000000), R := ((17141152617589285702839 : Rat) / 6400000000000000000000), D0 := ((17141152617589285702839 : Rat) / 6400000000000000000000), D1 := ((5509311977589285702839 : Rat) / 6400000000000000000000), D2 := ((770368617589285702839 : Rat) / 6400000000000000000000), D3 := ((185951045624999997237 : Rat) / 3200000000000000000000), D4 := ((344220937053571114229 : Rat) / 3200000000000000000000), LB := ((3961945722394389 : Rat) / 5000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17141152617589285702839 : Rat) / 6400000000000000000000), R := ((2143750928660714284267 : Rat) / 800000000000000000000), D0 := ((2143750928660714284267 : Rat) / 800000000000000000000), D1 := ((689770848660714284267 : Rat) / 800000000000000000000), D2 := ((97402928660714284267 : Rat) / 800000000000000000000), D3 := ((363047279553571423177 : Rat) / 6400000000000000000000), D4 := ((679587062410713657161 : Rat) / 6400000000000000000000), LB := ((8451236117404393 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2143750928660714284267 : Rat) / 800000000000000000000), R := ((17158862240982142845433 : Rat) / 6400000000000000000000), D0 := ((17158862240982142845433 : Rat) / 6400000000000000000000), D1 := ((5527021600982142845433 : Rat) / 6400000000000000000000), D2 := ((788078240982142845433 : Rat) / 6400000000000000000000), D3 := ((8854811696428571297 : Rat) / 160000000000000000000), D4 := ((83841531339285635733 : Rat) / 800000000000000000000), LB := ((1999852274694791 : Rat) / 2000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17158862240982142845433 : Rat) / 6400000000000000000000), R := ((1716771705267857141673 : Rat) / 640000000000000000000), D0 := ((1716771705267857141673 : Rat) / 640000000000000000000), D1 := ((553587641267857141673 : Rat) / 640000000000000000000), D2 := ((79693305267857141673 : Rat) / 640000000000000000000), D3 := ((345337656160714280583 : Rat) / 6400000000000000000000), D4 := ((661877439017856514567 : Rat) / 6400000000000000000000), LB := ((2522302342539251 : Rat) / 2000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1716771705267857141673 : Rat) / 640000000000000000000), R := ((17176571864374999988027 : Rat) / 6400000000000000000000), D0 := ((17176571864374999988027 : Rat) / 6400000000000000000000), D1 := ((5544731224374999988027 : Rat) / 6400000000000000000000), D2 := ((805787864374999988027 : Rat) / 6400000000000000000000), D3 := ((168241422232142854643 : Rat) / 3200000000000000000000), D4 := ((65302262732142794327 : Rat) / 640000000000000000000), LB := ((2041844111632593 : Rat) / 1250000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17176571864374999988027 : Rat) / 6400000000000000000000), R := ((4296356669017857139831 : Rat) / 1600000000000000000000), D0 := ((4296356669017857139831 : Rat) / 1600000000000000000000), D1 := ((1388396509017857139831 : Rat) / 1600000000000000000000), D2 := ((203660669017857139831 : Rat) / 1600000000000000000000), D3 := ((327628032767857137989 : Rat) / 6400000000000000000000), D4 := ((644167815624999371973 : Rat) / 6400000000000000000000), LB := ((2121930488245327 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4296356669017857139831 : Rat) / 1600000000000000000000), R := ((17194281487767857130621 : Rat) / 6400000000000000000000), D0 := ((17194281487767857130621 : Rat) / 6400000000000000000000), D1 := ((5562440847767857130621 : Rat) / 6400000000000000000000), D2 := ((823497487767857130621 : Rat) / 6400000000000000000000), D3 := ((79693305267857141673 : Rat) / 1600000000000000000000), D4 := ((158828250982142700169 : Rat) / 1600000000000000000000), LB := ((27319419680835177 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17194281487767857130621 : Rat) / 6400000000000000000000), R := ((8601568149732142850959 : Rat) / 3200000000000000000000), D0 := ((8601568149732142850959 : Rat) / 3200000000000000000000), D1 := ((2785647829732142850959 : Rat) / 3200000000000000000000), D2 := ((416176149732142850959 : Rat) / 3200000000000000000000), D3 := ((61983681874999999079 : Rat) / 1280000000000000000000), D4 := ((626458192232142229379 : Rat) / 6400000000000000000000), LB := ((3469371153429157 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8601568149732142850959 : Rat) / 3200000000000000000000), R := ((3442398222232142854643 : Rat) / 1280000000000000000000), D0 := ((3442398222232142854643 : Rat) / 1280000000000000000000), D1 := ((1116030094232142854643 : Rat) / 1280000000000000000000), D2 := ((168241422232142854643 : Rat) / 1280000000000000000000), D3 := ((150531798839285712049 : Rat) / 3200000000000000000000), D4 := ((308801690267856829041 : Rat) / 3200000000000000000000), LB := ((2170282429133613 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3442398222232142854643 : Rat) / 1280000000000000000000), R := ((538151435089285713891 : Rat) / 200000000000000000000), D0 := ((538151435089285713891 : Rat) / 200000000000000000000), D1 := ((174656415089285713891 : Rat) / 200000000000000000000), D2 := ((26564435089285713891 : Rat) / 200000000000000000000), D3 := ((292208785982142852801 : Rat) / 6400000000000000000000), D4 := ((121749713767857017357 : Rat) / 1280000000000000000000), LB := ((2676205843250873 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((538151435089285713891 : Rat) / 200000000000000000000), R := ((8619277773124999993553 : Rat) / 3200000000000000000000), D0 := ((8619277773124999993553 : Rat) / 3200000000000000000000), D1 := ((2803357453124999993553 : Rat) / 3200000000000000000000), D2 := ((433885773124999993553 : Rat) / 3200000000000000000000), D3 := ((8854811696428571297 : Rat) / 200000000000000000000), D4 := ((18746679910714266109 : Rat) / 200000000000000000000), LB := ((104325752899459 : Rat) / 50000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8619277773124999993553 : Rat) / 3200000000000000000000), R := ((172562651696428571297 : Rat) / 64000000000000000000), D0 := ((172562651696428571297 : Rat) / 64000000000000000000), D1 := ((56244245296428571297 : Rat) / 64000000000000000000), D2 := ((8854811696428571297 : Rat) / 64000000000000000000), D3 := ((26564435089285713891 : Rat) / 640000000000000000000), D4 := ((291092066874999686447 : Rat) / 3200000000000000000000), LB := ((306080282821513 : Rat) / 62500000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((172562651696428571297 : Rat) / 64000000000000000000), R := ((8636987396517857136147 : Rat) / 3200000000000000000000), D0 := ((8636987396517857136147 : Rat) / 3200000000000000000000), D1 := ((2821067076517857136147 : Rat) / 3200000000000000000000), D2 := ((451595396517857136147 : Rat) / 3200000000000000000000), D3 := ((61983681874999999079 : Rat) / 1600000000000000000000), D4 := ((5644745103571422303 : Rat) / 64000000000000000000), LB := ((210233146294099 : Rat) / 25000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8636987396517857136147 : Rat) / 3200000000000000000000), R := ((2161460552053571426861 : Rat) / 800000000000000000000), D0 := ((2161460552053571426861 : Rat) / 800000000000000000000), D1 := ((707480472053571426861 : Rat) / 800000000000000000000), D2 := ((115112552053571426861 : Rat) / 800000000000000000000), D3 := ((115112552053571426861 : Rat) / 3200000000000000000000), D4 := ((273382443482142543853 : Rat) / 3200000000000000000000), LB := ((3178486278778897 : Rat) / 250000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2161460552053571426861 : Rat) / 800000000000000000000), R := ((4331775915803571425019 : Rat) / 1600000000000000000000), D0 := ((4331775915803571425019 : Rat) / 1600000000000000000000), D1 := ((1423815755803571425019 : Rat) / 1600000000000000000000), D2 := ((239079915803571425019 : Rat) / 1600000000000000000000), D3 := ((26564435089285713891 : Rat) / 800000000000000000000), D4 := ((66131907946428493139 : Rat) / 800000000000000000000), LB := ((4596227477458359 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4331775915803571425019 : Rat) / 1600000000000000000000), R := ((1085157681874999999079 : Rat) / 400000000000000000000), D0 := ((1085157681874999999079 : Rat) / 400000000000000000000), D1 := ((358167641874999999079 : Rat) / 400000000000000000000), D2 := ((61983681874999999079 : Rat) / 400000000000000000000), D3 := ((8854811696428571297 : Rat) / 320000000000000000000), D4 := ((123409004196428414981 : Rat) / 1600000000000000000000), LB := ((22977604048734723 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1085157681874999999079 : Rat) / 400000000000000000000), R := ((435834035089285713891 : Rat) / 160000000000000000000), D0 := ((435834035089285713891 : Rat) / 160000000000000000000), D1 := ((145038019089285713891 : Rat) / 160000000000000000000), D2 := ((26564435089285713891 : Rat) / 160000000000000000000), D3 := ((8854811696428571297 : Rat) / 400000000000000000000), D4 := ((28638548124999960921 : Rat) / 400000000000000000000), LB := ((796582131502601 : Rat) / 31250000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((435834035089285713891 : Rat) / 160000000000000000000), R := ((136751561696428571297 : Rat) / 50000000000000000000), D0 := ((136751561696428571297 : Rat) / 50000000000000000000), D1 := ((45877806696428571297 : Rat) / 50000000000000000000), D2 := ((8854811696428571297 : Rat) / 50000000000000000000), D3 := ((8854811696428571297 : Rat) / 800000000000000000000), D4 := ((9684456910714270109 : Rat) / 160000000000000000000), LB := ((61994827165603 : Rat) / 625000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((136751561696428571297 : Rat) / 50000000000000000000), R := ((549479213839285708891 : Rat) / 200000000000000000000), D0 := ((549479213839285708891 : Rat) / 200000000000000000000), D1 := ((185984193839285708891 : Rat) / 200000000000000000000), D2 := ((37892213839285708891 : Rat) / 200000000000000000000), D3 := ((2472967053571423703 : Rat) / 200000000000000000000), D4 := ((2472967053571423703 : Rat) / 50000000000000000000), LB := ((3497649883332593 : Rat) / 50000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((549479213839285708891 : Rat) / 200000000000000000000), R := ((220286278946428568297 : Rat) / 80000000000000000000), D0 := ((220286278946428568297 : Rat) / 80000000000000000000), D1 := ((74888270946428568297 : Rat) / 80000000000000000000), D2 := ((15651478946428568297 : Rat) / 80000000000000000000), D3 := ((7418901160714271109 : Rat) / 400000000000000000000), D4 := ((7418901160714271109 : Rat) / 200000000000000000000), LB := ((19660441700751 : Rat) / 625000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((220286278946428568297 : Rat) / 80000000000000000000), R := ((2205335756517857106673 : Rat) / 800000000000000000000), D0 := ((2205335756517857106673 : Rat) / 800000000000000000000), D1 := ((751355676517857106673 : Rat) / 800000000000000000000), D2 := ((158987756517857106673 : Rat) / 800000000000000000000), D3 := ((17310769374999965921 : Rat) / 800000000000000000000), D4 := ((2472967053571423703 : Rat) / 80000000000000000000), LB := ((11397082039752371 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2205335756517857106673 : Rat) / 800000000000000000000), R := ((275976090446428566297 : Rat) / 100000000000000000000), D0 := ((275976090446428566297 : Rat) / 100000000000000000000), D1 := ((94228580446428566297 : Rat) / 100000000000000000000), D2 := ((20182590446428566297 : Rat) / 100000000000000000000), D3 := ((2472967053571423703 : Rat) / 100000000000000000000), D4 := ((22256703482142813327 : Rat) / 800000000000000000000), LB := ((163799346034883 : Rat) / 20000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((275976090446428566297 : Rat) / 100000000000000000000), R := ((883618082839285696891 : Rat) / 320000000000000000000), D0 := ((883618082839285696891 : Rat) / 320000000000000000000), D1 := ((302026050839285696891 : Rat) / 320000000000000000000), D2 := ((65078882839285696891 : Rat) / 320000000000000000000), D3 := ((42040439910714202951 : Rat) / 1600000000000000000000), D4 := ((2472967053571423703 : Rat) / 100000000000000000000), LB := ((4488330048769501 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((883618082839285696891 : Rat) / 320000000000000000000), R := ((2210281690624999954079 : Rat) / 800000000000000000000), D0 := ((2210281690624999954079 : Rat) / 800000000000000000000), D1 := ((756301610624999954079 : Rat) / 800000000000000000000), D2 := ((163933690624999954079 : Rat) / 800000000000000000000), D3 := ((22256703482142813327 : Rat) / 800000000000000000000), D4 := ((7418901160714271109 : Rat) / 320000000000000000000), LB := ((850703442515821 : Rat) / 200000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2210281690624999954079 : Rat) / 800000000000000000000), R := ((4423036348303571331861 : Rat) / 1600000000000000000000), D0 := ((4423036348303571331861 : Rat) / 1600000000000000000000), D1 := ((1515076188303571331861 : Rat) / 1600000000000000000000), D2 := ((330340348303571331861 : Rat) / 1600000000000000000000), D3 := ((46986374017857050357 : Rat) / 1600000000000000000000), D4 := ((17310769374999965921 : Rat) / 800000000000000000000), LB := ((4330244849919951 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4423036348303571331861 : Rat) / 1600000000000000000000), R := ((353941826546428563497 : Rat) / 128000000000000000000), D0 := ((353941826546428563497 : Rat) / 128000000000000000000), D1 := ((121305013746428563497 : Rat) / 128000000000000000000), D2 := ((26526146546428563497 : Rat) / 128000000000000000000), D3 := ((96445715089285524417 : Rat) / 3200000000000000000000), D4 := ((32148571696428508139 : Rat) / 1600000000000000000000), LB := ((3096618694665043 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((353941826546428563497 : Rat) / 128000000000000000000), R := ((1106377328839285688891 : Rat) / 400000000000000000000), D0 := ((1106377328839285688891 : Rat) / 400000000000000000000), D1 := ((379387288839285688891 : Rat) / 400000000000000000000), D2 := ((83203328839285688891 : Rat) / 400000000000000000000), D3 := ((2472967053571423703 : Rat) / 80000000000000000000), D4 := ((2472967053571423703 : Rat) / 128000000000000000000), LB := ((9699946433842921 : Rat) / 5000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1106377328839285688891 : Rat) / 400000000000000000000), R := ((8853491597767856934831 : Rat) / 3200000000000000000000), D0 := ((8853491597767856934831 : Rat) / 3200000000000000000000), D1 := ((3037571277767856934831 : Rat) / 3200000000000000000000), D2 := ((668099597767856934831 : Rat) / 3200000000000000000000), D3 := ((101391649196428371823 : Rat) / 3200000000000000000000), D4 := ((7418901160714271109 : Rat) / 400000000000000000000), LB := ((2089290809300981 : Rat) / 2000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8853491597767856934831 : Rat) / 3200000000000000000000), R := ((4427982282410714179267 : Rat) / 1600000000000000000000), D0 := ((4427982282410714179267 : Rat) / 1600000000000000000000), D1 := ((1520022122410714179267 : Rat) / 1600000000000000000000), D2 := ((335286282410714179267 : Rat) / 1600000000000000000000), D3 := ((51932308124999897763 : Rat) / 1600000000000000000000), D4 := ((56878242232142745169 : Rat) / 3200000000000000000000), LB := ((131864554704271 : Rat) / 312500000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4427982282410714179267 : Rat) / 1600000000000000000000), R := ((8858437531874999782237 : Rat) / 3200000000000000000000), D0 := ((8858437531874999782237 : Rat) / 3200000000000000000000), D1 := ((3042517211874999782237 : Rat) / 3200000000000000000000), D2 := ((673045531874999782237 : Rat) / 3200000000000000000000), D3 := ((106337583303571219229 : Rat) / 3200000000000000000000), D4 := ((27202637589285660733 : Rat) / 1600000000000000000000), LB := ((8563284159990303 : Rat) / 100000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8858437531874999782237 : Rat) / 3200000000000000000000), R := ((443045524946428560297 : Rat) / 160000000000000000000), D0 := ((443045524946428560297 : Rat) / 160000000000000000000), D1 := ((152249508946428560297 : Rat) / 160000000000000000000), D2 := ((33775924946428560297 : Rat) / 160000000000000000000), D3 := ((27202637589285660733 : Rat) / 800000000000000000000), D4 := ((51932308124999897763 : Rat) / 3200000000000000000000), LB := ((259862234004149 : Rat) / 5000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((443045524946428560297 : Rat) / 160000000000000000000), R := ((8863383465982142629643 : Rat) / 3200000000000000000000), D0 := ((8863383465982142629643 : Rat) / 3200000000000000000000), D1 := ((3047463145982142629643 : Rat) / 3200000000000000000000), D2 := ((677991465982142629643 : Rat) / 3200000000000000000000), D3 := ((22256703482142813327 : Rat) / 640000000000000000000), D4 := ((2472967053571423703 : Rat) / 160000000000000000000), LB := ((17020023578925847 : Rat) / 50000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8863383465982142629643 : Rat) / 3200000000000000000000), R := ((4432928216517857026673 : Rat) / 1600000000000000000000), D0 := ((4432928216517857026673 : Rat) / 1600000000000000000000), D1 := ((1524968056517857026673 : Rat) / 1600000000000000000000), D2 := ((340232216517857026673 : Rat) / 1600000000000000000000), D3 := ((56878242232142745169 : Rat) / 1600000000000000000000), D4 := ((46986374017857050357 : Rat) / 3200000000000000000000), LB := ((4869867097342939 : Rat) / 5000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4432928216517857026673 : Rat) / 1600000000000000000000), R := ((8868329400089285477049 : Rat) / 3200000000000000000000), D0 := ((8868329400089285477049 : Rat) / 3200000000000000000000), D1 := ((3052409080089285477049 : Rat) / 3200000000000000000000), D2 := ((682937400089285477049 : Rat) / 3200000000000000000000), D3 := ((116229451517856914041 : Rat) / 3200000000000000000000), D4 := ((22256703482142813327 : Rat) / 1600000000000000000000), LB := ((9900466419240639 : Rat) / 5000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8868329400089285477049 : Rat) / 3200000000000000000000), R := ((554425147946428556297 : Rat) / 200000000000000000000), D0 := ((554425147946428556297 : Rat) / 200000000000000000000), D1 := ((190930127946428556297 : Rat) / 200000000000000000000), D2 := ((42838147946428556297 : Rat) / 200000000000000000000), D3 := ((7418901160714271109 : Rat) / 200000000000000000000), D4 := ((42040439910714202951 : Rat) / 3200000000000000000000), LB := ((33914063728915367 : Rat) / 10000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((554425147946428556297 : Rat) / 200000000000000000000), R := ((4437874150624999874079 : Rat) / 1600000000000000000000), D0 := ((4437874150624999874079 : Rat) / 1600000000000000000000), D1 := ((1529913990624999874079 : Rat) / 1600000000000000000000), D2 := ((345178150624999874079 : Rat) / 1600000000000000000000), D3 := ((2472967053571423703 : Rat) / 64000000000000000000), D4 := ((2472967053571423703 : Rat) / 200000000000000000000), LB := ((18634677836992797 : Rat) / 50000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4437874150624999874079 : Rat) / 1600000000000000000000), R := ((2220173558839285648891 : Rat) / 800000000000000000000), D0 := ((2220173558839285648891 : Rat) / 800000000000000000000), D1 := ((766193478839285648891 : Rat) / 800000000000000000000), D2 := ((173825558839285648891 : Rat) / 800000000000000000000), D3 := ((32148571696428508139 : Rat) / 800000000000000000000), D4 := ((17310769374999965921 : Rat) / 1600000000000000000000), LB := ((2859134642660799 : Rat) / 500000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2220173558839285648891 : Rat) / 800000000000000000000), R := ((1111323262946428536297 : Rat) / 400000000000000000000), D0 := ((1111323262946428536297 : Rat) / 400000000000000000000), D1 := ((384333222946428536297 : Rat) / 400000000000000000000), D2 := ((88149262946428536297 : Rat) / 400000000000000000000), D3 := ((17310769374999965921 : Rat) / 400000000000000000000), D4 := ((7418901160714271109 : Rat) / 800000000000000000000), LB := ((1082342038278561 : Rat) / 250000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1111323262946428536297 : Rat) / 400000000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((2472967053571423703 : Rat) / 50000000000000000000), D4 := ((2472967053571423703 : Rat) / 400000000000000000000), LB := ((13948298086383537 : Rat) / 1000000000000000000) },
  { w1 := ((24751160135098567 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((401307041781181 : Rat) / 3125000000000000), w4 := ((5598612039011487 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((136751561696428571297 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((69742881696428571459 : Rat) / 25000000000000000000), D0 := ((69742881696428571459 : Rat) / 25000000000000000000), D1 := ((24306004196428571459 : Rat) / 25000000000000000000), D2 := ((5794506696428571459 : Rat) / 25000000000000000000), D3 := ((2734201696428571621 : Rat) / 50000000000000000000), D4 := ((130617321428573959 : Rat) / 25000000000000000000), LB := ((2029374901257097 : Rat) / 500000000000000000) }
]

def block142RightChunk000L : Rat := ((89475988839285714347 : Rat) / 50000000000000000000)
def block142RightChunk000R : Rat := ((69742881696428571459 : Rat) / 25000000000000000000)

def block142RightChunk000Certificate : Bool :=
  allBoxesValid block142RightChunk000 &&
  coversFromBool block142RightChunk000 block142RightChunk000L block142RightChunk000R

theorem block142RightChunk000Certificate_eq_true :
    block142RightChunk000Certificate = true := by
  native_decide

def block142RightChainCertificate : Bool :=
  decide (
    block142RightL = ((89475988839285714347 : Rat) / 50000000000000000000) /\
    ((69742881696428571459 : Rat) / 25000000000000000000) = block142RightR)

theorem block142RightChainCertificate_eq_true :
    block142RightChainCertificate = true := by
  native_decide

def block142LeftBoxCount : Nat := boxCount block142LeftBoxes
def block142RightBoxCount : Nat := 62

def block142_rational_certificate : Prop :=
    block142LeftCertificate = true /\
    block142RightChainCertificate = true /\
    block142RightChunk000Certificate = true

theorem block142_rational_certificate_proof :
    block142_rational_certificate := by
  exact ⟨block142LeftCertificate_eq_true, block142RightChainCertificate_eq_true, block142RightChunk000Certificate_eq_true⟩

end Block142
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block142

open Set

def block142W1 : Rat := ((24751160135098567 : Rat) / 10000000000000000)
def block142W2 : Rat := (0 : Rat)
def block142W3 : Rat := ((401307041781181 : Rat) / 3125000000000000)
def block142W4 : Rat := ((5598612039011487 : Rat) / 50000000000000000)
def block142S1 : Rat := ((18174751 : Rat) / 10000000)
def block142S2 : Rat := ((511587 : Rat) / 200000)
def block142S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block142S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block142V (y : ℝ) : ℝ :=
  ratPotential block142W1 block142W2 block142W3 block142W4 block142S1 block142S2 block142S3 block142S4 y

def block142LeftParamsCertificate : Bool :=
  allBoxesSameParams block142LeftBoxes block142W1 block142W2 block142W3 block142W4 block142S1 block142S2 block142S3 block142S4

theorem block142LeftParamsCertificate_eq_true :
    block142LeftParamsCertificate = true := by
  native_decide

theorem block142_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block142LeftL : ℝ) (block142LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block142S1 : ℝ))
    (hy2ne : y ≠ (block142S2 : ℝ))
    (hy3ne : y ≠ (block142S3 : ℝ))
    (hy4ne : y ≠ (block142S4 : ℝ)) :
    0 < block142V y := by
  have hcert := block142LeftCertificate_eq_true
  unfold block142LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block142LeftBoxes) (lo := block142LeftL) (hi := block142LeftR)
    (w1 := block142W1) (w2 := block142W2) (w3 := block142W3) (w4 := block142W4)
    (s1 := block142S1) (s2 := block142S2) (s3 := block142S3) (s4 := block142S4)
    hboxes hcover block142LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block142RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block142RightChunk000 block142W1 block142W2 block142W3 block142W4 block142S1 block142S2 block142S3 block142S4

theorem block142RightChunk000ParamsCertificate_eq_true :
    block142RightChunk000ParamsCertificate = true := by
  native_decide

theorem block142_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block142RightChunk000L : ℝ) (block142RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block142S1 : ℝ))
    (hy2ne : y ≠ (block142S2 : ℝ))
    (hy3ne : y ≠ (block142S3 : ℝ))
    (hy4ne : y ≠ (block142S4 : ℝ)) :
    0 < block142V y := by
  have hcert := block142RightChunk000Certificate_eq_true
  unfold block142RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block142RightChunk000) (lo := block142RightChunk000L) (hi := block142RightChunk000R)
    (w1 := block142W1) (w2 := block142W2) (w3 := block142W3) (w4 := block142W4)
    (s1 := block142S1) (s2 := block142S2) (s3 := block142S3) (s4 := block142S4)
    hboxes hcover block142RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block142_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block142RightL : ℝ) (block142RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block142S1 : ℝ))
    (hy2ne : y ≠ (block142S2 : ℝ))
    (hy3ne : y ≠ (block142S3 : ℝ))
    (hy4ne : y ≠ (block142S4 : ℝ)) :
    0 < block142V y := by
  have hL : (block142RightChunk000L : ℝ) = (block142RightL : ℝ) := by
    norm_num [block142RightChunk000L, block142RightL]
  have hR : (block142RightChunk000R : ℝ) = (block142RightR : ℝ) := by
    norm_num [block142RightChunk000R, block142RightR]
  have hyc : y ∈ Icc (block142RightChunk000L : ℝ) (block142RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block142_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block142_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block142LeftL : ℝ) (block142LeftR : ℝ) →
    y ≠ 0 → y ≠ (block142S1 : ℝ) → y ≠ (block142S2 : ℝ) →
    y ≠ (block142S3 : ℝ) → y ≠ (block142S4 : ℝ) → 0 < block142V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block142RightL : ℝ) (block142RightR : ℝ) →
    y ≠ 0 → y ≠ (block142S1 : ℝ) → y ≠ (block142S2 : ℝ) →
    y ≠ (block142S3 : ℝ) → y ≠ (block142S4 : ℝ) → 0 < block142V y)

theorem block142_reallog_certificate_proof :
    block142_reallog_certificate := by
  exact ⟨block142_left_V_pos, block142_right_V_pos⟩

end Block142
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block142.block142V
#check Erdos1038Lean.M1817475.Block142.block142_left_V_pos
#check Erdos1038Lean.M1817475.Block142.block142_right_V_pos
#check Erdos1038Lean.M1817475.Block142.block142_reallog_certificate_proof
