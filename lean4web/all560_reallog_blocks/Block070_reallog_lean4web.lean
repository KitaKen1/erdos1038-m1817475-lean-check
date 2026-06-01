/-
Self-contained Lean4Web paste file.
Block 70 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block070

def block070LeftL : Rat := ((40179756696428571459 : Rat) / 50000000000000000000)
def block070LeftR : Rat := ((4018953125000000003 : Rat) / 5000000000000000000)
def block070RightL : Rat := ((90179756696428571459 : Rat) / 50000000000000000000)
def block070RightR : Rat := ((14018953125000000003 : Rat) / 5000000000000000000)

def block070LeftBoxes : List RatBox := [
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((40179756696428571459 : Rat) / 50000000000000000000), R := ((4018953125000000003 : Rat) / 5000000000000000000), D0 := ((4018953125000000003 : Rat) / 5000000000000000000), D1 := ((50693998303571428541 : Rat) / 50000000000000000000), D2 := ((87716993303571428541 : Rat) / 50000000000000000000), D3 := ((93571017053571428541 : Rat) / 50000000000000000000), D4 := ((99044772053571423541 : Rat) / 50000000000000000000), LB := ((10186691003320411 : Rat) / 2500000000000000000) }
]

def block070LeftCertificate : Bool :=
  allBoxesValid block070LeftBoxes &&
  coversFromBool block070LeftBoxes block070LeftL block070LeftR

theorem block070LeftCertificate_eq_true :
    block070LeftCertificate = true := by
  native_decide

def block070RightChunk000 : List RatBox := [
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((90179756696428571459 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((693998303571428541 : Rat) / 50000000000000000000), D2 := ((37716993303571428541 : Rat) / 50000000000000000000), D3 := ((43571017053571428541 : Rat) / 50000000000000000000), D4 := ((49044772053571423541 : Rat) / 50000000000000000000), LB := ((3142528899417357 : Rat) / 250000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((2283337042982643 : Rat) / 1000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((19492417 : Rat) / 40000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((5766271560805769 : Rat) / 50000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((209318019 : Rat) / 80000000), D0 := ((209318019 : Rat) / 80000000), D1 := ((63920011 : Rat) / 80000000), D2 := ((4683219 : Rat) / 80000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((5107544764605751 : Rat) / 50000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209318019 : Rat) / 80000000), R := ((423319257 : Rat) / 160000000), D0 := ((423319257 : Rat) / 160000000), D1 := ((132523241 : Rat) / 160000000), D2 := ((14049657 : Rat) / 160000000), D3 := ((4683219 : Rat) / 80000000), D4 := ((1680153374999999 : Rat) / 10000000000000000), LB := ((346838735364419 : Rat) / 6250000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423319257 : Rat) / 160000000), R := ((851321733 : Rat) / 320000000), D0 := ((851321733 : Rat) / 320000000), D1 := ((269729701 : Rat) / 320000000), D2 := ((32782533 : Rat) / 320000000), D3 := ((4683219 : Rat) / 160000000), D4 := ((1387452187499999 : Rat) / 10000000000000000), LB := ((4422136488819067 : Rat) / 100000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((851321733 : Rat) / 320000000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 320000000), D4 := ((1241101593749999 : Rat) / 10000000000000000), LB := ((6899531723571273 : Rat) / 500000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107000619 : Rat) / 40000000), R := ((429097226999999999 : Rat) / 160000000000000000), D0 := ((429097226999999999 : Rat) / 160000000000000000), D1 := ((138301210999999999 : Rat) / 160000000000000000), D2 := ((19827626999999999 : Rat) / 160000000000000000), D3 := ((1094750999999999 : Rat) / 160000000000000000), D4 := ((1094750999999999 : Rat) / 10000000000000000), LB := ((3669242699270181 : Rat) / 200000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((429097226999999999 : Rat) / 160000000000000000), R := ((215095988999999999 : Rat) / 80000000000000000), D0 := ((215095988999999999 : Rat) / 80000000000000000), D1 := ((69697980999999999 : Rat) / 80000000000000000), D2 := ((10461188999999999 : Rat) / 80000000000000000), D3 := ((1094750999999999 : Rat) / 80000000000000000), D4 := ((3284252999999997 : Rat) / 32000000000000000), LB := ((7766988452644341 : Rat) / 1000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((215095988999999999 : Rat) / 80000000000000000), R := ((172295741399999999 : Rat) / 64000000000000000), D0 := ((172295741399999999 : Rat) / 64000000000000000), D1 := ((55977334999999999 : Rat) / 64000000000000000), D2 := ((8587901399999999 : Rat) / 64000000000000000), D3 := ((1094750999999999 : Rat) / 64000000000000000), D4 := ((7663256999999993 : Rat) / 80000000000000000), LB := ((2357532513067917 : Rat) / 200000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((172295741399999999 : Rat) / 64000000000000000), R := ((431286728999999997 : Rat) / 160000000000000000), D0 := ((431286728999999997 : Rat) / 160000000000000000), D1 := ((140490712999999997 : Rat) / 160000000000000000), D2 := ((22017128999999997 : Rat) / 160000000000000000), D3 := ((3284252999999997 : Rat) / 160000000000000000), D4 := ((29558276999999973 : Rat) / 320000000000000000), LB := ((1530268226152387 : Rat) / 200000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((431286728999999997 : Rat) / 160000000000000000), R := ((863668208999999993 : Rat) / 320000000000000000), D0 := ((863668208999999993 : Rat) / 320000000000000000), D1 := ((282076176999999993 : Rat) / 320000000000000000), D2 := ((45129008999999993 : Rat) / 320000000000000000), D3 := ((7663256999999993 : Rat) / 320000000000000000), D4 := ((14231762999999987 : Rat) / 160000000000000000), LB := ((244287140815147 : Rat) / 62500000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((863668208999999993 : Rat) / 320000000000000000), R := ((108095369999999999 : Rat) / 40000000000000000), D0 := ((108095369999999999 : Rat) / 40000000000000000), D1 := ((35396365999999999 : Rat) / 40000000000000000), D2 := ((5777969999999999 : Rat) / 40000000000000000), D3 := ((1094750999999999 : Rat) / 40000000000000000), D4 := ((1094750999999999 : Rat) / 12800000000000000), LB := ((1465360782446079 : Rat) / 2500000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((108095369999999999 : Rat) / 40000000000000000), R := ((1730620670999999983 : Rat) / 640000000000000000), D0 := ((1730620670999999983 : Rat) / 640000000000000000), D1 := ((567436606999999983 : Rat) / 640000000000000000), D2 := ((93542270999999983 : Rat) / 640000000000000000), D3 := ((18610766999999983 : Rat) / 640000000000000000), D4 := ((3284252999999997 : Rat) / 40000000000000000), LB := ((1069452137461957 : Rat) / 250000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1730620670999999983 : Rat) / 640000000000000000), R := ((865857710999999991 : Rat) / 320000000000000000), D0 := ((865857710999999991 : Rat) / 320000000000000000), D1 := ((284265678999999991 : Rat) / 320000000000000000), D2 := ((47318510999999991 : Rat) / 320000000000000000), D3 := ((9852758999999991 : Rat) / 320000000000000000), D4 := ((51453296999999953 : Rat) / 640000000000000000), LB := ((1504628693515253 : Rat) / 500000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((865857710999999991 : Rat) / 320000000000000000), R := ((1732810172999999981 : Rat) / 640000000000000000), D0 := ((1732810172999999981 : Rat) / 640000000000000000), D1 := ((569626108999999981 : Rat) / 640000000000000000), D2 := ((95731772999999981 : Rat) / 640000000000000000), D3 := ((20800268999999981 : Rat) / 640000000000000000), D4 := ((25179272999999977 : Rat) / 320000000000000000), LB := ((4666001636023931 : Rat) / 2500000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1732810172999999981 : Rat) / 640000000000000000), R := ((86695246199999999 : Rat) / 32000000000000000), D0 := ((86695246199999999 : Rat) / 32000000000000000), D1 := ((28536042999999999 : Rat) / 32000000000000000), D2 := ((4841326199999999 : Rat) / 32000000000000000), D3 := ((1094750999999999 : Rat) / 32000000000000000), D4 := ((9852758999999991 : Rat) / 128000000000000000), LB := ((1067750662629291 : Rat) / 1250000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((86695246199999999 : Rat) / 32000000000000000), R := ((3468904598999999959 : Rat) / 1280000000000000000), D0 := ((3468904598999999959 : Rat) / 1280000000000000000), D1 := ((1142536470999999959 : Rat) / 1280000000000000000), D2 := ((194747798999999959 : Rat) / 1280000000000000000), D3 := ((44884790999999959 : Rat) / 1280000000000000000), D4 := ((12042260999999989 : Rat) / 160000000000000000), LB := ((32407318561346043 : Rat) / 10000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3468904598999999959 : Rat) / 1280000000000000000), R := ((1734999674999999979 : Rat) / 640000000000000000), D0 := ((1734999674999999979 : Rat) / 640000000000000000), D1 := ((571815610999999979 : Rat) / 640000000000000000), D2 := ((97921274999999979 : Rat) / 640000000000000000), D3 := ((22989770999999979 : Rat) / 640000000000000000), D4 := ((95243336999999913 : Rat) / 1280000000000000000), LB := ((1426215284895671 : Rat) / 500000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1734999674999999979 : Rat) / 640000000000000000), R := ((3471094100999999957 : Rat) / 1280000000000000000), D0 := ((3471094100999999957 : Rat) / 1280000000000000000), D1 := ((1144725972999999957 : Rat) / 1280000000000000000), D2 := ((196937300999999957 : Rat) / 1280000000000000000), D3 := ((47074292999999957 : Rat) / 1280000000000000000), D4 := ((47074292999999957 : Rat) / 640000000000000000), LB := ((1000112151497623 : Rat) / 400000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3471094100999999957 : Rat) / 1280000000000000000), R := ((868047212999999989 : Rat) / 320000000000000000), D0 := ((868047212999999989 : Rat) / 320000000000000000), D1 := ((286455180999999989 : Rat) / 320000000000000000), D2 := ((49508012999999989 : Rat) / 320000000000000000), D3 := ((12042260999999989 : Rat) / 320000000000000000), D4 := ((18610766999999983 : Rat) / 256000000000000000), LB := ((546263300964217 : Rat) / 250000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((868047212999999989 : Rat) / 320000000000000000), R := ((694656720599999991 : Rat) / 256000000000000000), D0 := ((694656720599999991 : Rat) / 256000000000000000), D1 := ((229383094999999991 : Rat) / 256000000000000000), D2 := ((39825360599999991 : Rat) / 256000000000000000), D3 := ((9852758999999991 : Rat) / 256000000000000000), D4 := ((22989770999999979 : Rat) / 320000000000000000), LB := ((119221786366773 : Rat) / 62500000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((694656720599999991 : Rat) / 256000000000000000), R := ((1737189176999999977 : Rat) / 640000000000000000), D0 := ((1737189176999999977 : Rat) / 640000000000000000), D1 := ((574005112999999977 : Rat) / 640000000000000000), D2 := ((100110776999999977 : Rat) / 640000000000000000), D3 := ((25179272999999977 : Rat) / 640000000000000000), D4 := ((90864332999999917 : Rat) / 1280000000000000000), LB := ((8342974937892711 : Rat) / 5000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1737189176999999977 : Rat) / 640000000000000000), R := ((3475473104999999953 : Rat) / 1280000000000000000), D0 := ((3475473104999999953 : Rat) / 1280000000000000000), D1 := ((1149104976999999953 : Rat) / 1280000000000000000), D2 := ((201316304999999953 : Rat) / 1280000000000000000), D3 := ((51453296999999953 : Rat) / 1280000000000000000), D4 := ((44884790999999959 : Rat) / 640000000000000000), LB := ((14690512361844599 : Rat) / 10000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3475473104999999953 : Rat) / 1280000000000000000), R := ((217285490999999997 : Rat) / 80000000000000000), D0 := ((217285490999999997 : Rat) / 80000000000000000), D1 := ((71887482999999997 : Rat) / 80000000000000000), D2 := ((12650690999999997 : Rat) / 80000000000000000), D3 := ((3284252999999997 : Rat) / 80000000000000000), D4 := ((88674830999999919 : Rat) / 1280000000000000000), LB := ((818629982285643 : Rat) / 625000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((217285490999999997 : Rat) / 80000000000000000), R := ((3477662606999999951 : Rat) / 1280000000000000000), D0 := ((3477662606999999951 : Rat) / 1280000000000000000), D1 := ((1151294478999999951 : Rat) / 1280000000000000000), D2 := ((203505806999999951 : Rat) / 1280000000000000000), D3 := ((53642798999999951 : Rat) / 1280000000000000000), D4 := ((1094750999999999 : Rat) / 16000000000000000), LB := ((2383578495147587 : Rat) / 2000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3477662606999999951 : Rat) / 1280000000000000000), R := ((69575147159999999 : Rat) / 25600000000000000), D0 := ((69575147159999999 : Rat) / 25600000000000000), D1 := ((23047784599999999 : Rat) / 25600000000000000), D2 := ((4092011159999999 : Rat) / 25600000000000000), D3 := ((1094750999999999 : Rat) / 25600000000000000), D4 := ((86485328999999921 : Rat) / 1280000000000000000), LB := ((174367844904353 : Rat) / 156250000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((69575147159999999 : Rat) / 25600000000000000), R := ((3479852108999999949 : Rat) / 1280000000000000000), D0 := ((3479852108999999949 : Rat) / 1280000000000000000), D1 := ((1153483980999999949 : Rat) / 1280000000000000000), D2 := ((205695308999999949 : Rat) / 1280000000000000000), D3 := ((55832300999999949 : Rat) / 1280000000000000000), D4 := ((42695288999999961 : Rat) / 640000000000000000), LB := ((10832988717318637 : Rat) / 10000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3479852108999999949 : Rat) / 1280000000000000000), R := ((870236714999999987 : Rat) / 320000000000000000), D0 := ((870236714999999987 : Rat) / 320000000000000000), D1 := ((288644682999999987 : Rat) / 320000000000000000), D2 := ((51697514999999987 : Rat) / 320000000000000000), D3 := ((14231762999999987 : Rat) / 320000000000000000), D4 := ((84295826999999923 : Rat) / 1280000000000000000), LB := ((273714510261841 : Rat) / 250000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((870236714999999987 : Rat) / 320000000000000000), R := ((3482041610999999947 : Rat) / 1280000000000000000), D0 := ((3482041610999999947 : Rat) / 1280000000000000000), D1 := ((1155673482999999947 : Rat) / 1280000000000000000), D2 := ((207884810999999947 : Rat) / 1280000000000000000), D3 := ((58021802999999947 : Rat) / 1280000000000000000), D4 := ((20800268999999981 : Rat) / 320000000000000000), LB := ((11517073225773 : Rat) / 10000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3482041610999999947 : Rat) / 1280000000000000000), R := ((1741568180999999973 : Rat) / 640000000000000000), D0 := ((1741568180999999973 : Rat) / 640000000000000000), D1 := ((578384116999999973 : Rat) / 640000000000000000), D2 := ((104489780999999973 : Rat) / 640000000000000000), D3 := ((29558276999999973 : Rat) / 640000000000000000), D4 := ((3284252999999997 : Rat) / 51200000000000000), LB := ((6274826458090299 : Rat) / 5000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1741568180999999973 : Rat) / 640000000000000000), R := ((696846222599999989 : Rat) / 256000000000000000), D0 := ((696846222599999989 : Rat) / 256000000000000000), D1 := ((231572596999999989 : Rat) / 256000000000000000), D2 := ((42014862599999989 : Rat) / 256000000000000000), D3 := ((12042260999999989 : Rat) / 256000000000000000), D4 := ((40505786999999963 : Rat) / 640000000000000000), LB := ((14057957978400593 : Rat) / 10000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((696846222599999989 : Rat) / 256000000000000000), R := ((435665732999999993 : Rat) / 160000000000000000), D0 := ((435665732999999993 : Rat) / 160000000000000000), D1 := ((144869716999999993 : Rat) / 160000000000000000), D2 := ((26396132999999993 : Rat) / 160000000000000000), D3 := ((7663256999999993 : Rat) / 160000000000000000), D4 := ((79916822999999927 : Rat) / 1280000000000000000), LB := ((2006763035638931 : Rat) / 1250000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((435665732999999993 : Rat) / 160000000000000000), R := ((3486420614999999943 : Rat) / 1280000000000000000), D0 := ((3486420614999999943 : Rat) / 1280000000000000000), D1 := ((1160052486999999943 : Rat) / 1280000000000000000), D2 := ((212263814999999943 : Rat) / 1280000000000000000), D3 := ((62400806999999943 : Rat) / 1280000000000000000), D4 := ((9852758999999991 : Rat) / 160000000000000000), LB := ((185507114162331 : Rat) / 100000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3486420614999999943 : Rat) / 1280000000000000000), R := ((1743757682999999971 : Rat) / 640000000000000000), D0 := ((1743757682999999971 : Rat) / 640000000000000000), D1 := ((580573618999999971 : Rat) / 640000000000000000), D2 := ((106679282999999971 : Rat) / 640000000000000000), D3 := ((31747778999999971 : Rat) / 640000000000000000), D4 := ((77727320999999929 : Rat) / 1280000000000000000), LB := ((10780465415872187 : Rat) / 5000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1743757682999999971 : Rat) / 640000000000000000), R := ((3488610116999999941 : Rat) / 1280000000000000000), D0 := ((3488610116999999941 : Rat) / 1280000000000000000), D1 := ((1162241988999999941 : Rat) / 1280000000000000000), D2 := ((214453316999999941 : Rat) / 1280000000000000000), D3 := ((64590308999999941 : Rat) / 1280000000000000000), D4 := ((7663256999999993 : Rat) / 128000000000000000), LB := ((2509847604279969 : Rat) / 1000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3488610116999999941 : Rat) / 1280000000000000000), R := ((174485243399999997 : Rat) / 64000000000000000), D0 := ((174485243399999997 : Rat) / 64000000000000000), D1 := ((58166836999999997 : Rat) / 64000000000000000), D2 := ((10777403399999997 : Rat) / 64000000000000000), D3 := ((3284252999999997 : Rat) / 64000000000000000), D4 := ((75537818999999931 : Rat) / 1280000000000000000), LB := ((3647206869213937 : Rat) / 1250000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((174485243399999997 : Rat) / 64000000000000000), R := ((1745947184999999969 : Rat) / 640000000000000000), D0 := ((1745947184999999969 : Rat) / 640000000000000000), D1 := ((582763120999999969 : Rat) / 640000000000000000), D2 := ((108868784999999969 : Rat) / 640000000000000000), D3 := ((33937280999999969 : Rat) / 640000000000000000), D4 := ((18610766999999983 : Rat) / 320000000000000000), LB := ((1759358088458951 : Rat) / 10000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1745947184999999969 : Rat) / 640000000000000000), R := ((54595060499999999 : Rat) / 20000000000000000), D0 := ((54595060499999999 : Rat) / 20000000000000000), D1 := ((18245558499999999 : Rat) / 20000000000000000), D2 := ((3436360499999999 : Rat) / 20000000000000000), D3 := ((1094750999999999 : Rat) / 20000000000000000), D4 := ((36126782999999967 : Rat) / 640000000000000000), LB := ((3204975722171377 : Rat) / 2500000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((54595060499999999 : Rat) / 20000000000000000), R := ((1748136686999999967 : Rat) / 640000000000000000), D0 := ((1748136686999999967 : Rat) / 640000000000000000), D1 := ((584952622999999967 : Rat) / 640000000000000000), D2 := ((111058286999999967 : Rat) / 640000000000000000), D3 := ((36126782999999967 : Rat) / 640000000000000000), D4 := ((1094750999999999 : Rat) / 20000000000000000), LB := ((526064225930889 : Rat) / 200000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1748136686999999967 : Rat) / 640000000000000000), R := ((874615718999999983 : Rat) / 320000000000000000), D0 := ((874615718999999983 : Rat) / 320000000000000000), D1 := ((293023686999999983 : Rat) / 320000000000000000), D2 := ((56076518999999983 : Rat) / 320000000000000000), D3 := ((18610766999999983 : Rat) / 320000000000000000), D4 := ((33937280999999969 : Rat) / 640000000000000000), LB := ((4235561728807569 : Rat) / 1000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((874615718999999983 : Rat) / 320000000000000000), R := ((350065237799999993 : Rat) / 128000000000000000), D0 := ((350065237799999993 : Rat) / 128000000000000000), D1 := ((117428424999999993 : Rat) / 128000000000000000), D2 := ((22649557799999993 : Rat) / 128000000000000000), D3 := ((7663256999999993 : Rat) / 128000000000000000), D4 := ((3284252999999997 : Rat) / 64000000000000000), LB := ((76422369794589 : Rat) / 12500000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((350065237799999993 : Rat) / 128000000000000000), R := ((437855234999999991 : Rat) / 160000000000000000), D0 := ((437855234999999991 : Rat) / 160000000000000000), D1 := ((147059218999999991 : Rat) / 160000000000000000), D2 := ((28585634999999991 : Rat) / 160000000000000000), D3 := ((9852758999999991 : Rat) / 160000000000000000), D4 := ((31747778999999971 : Rat) / 640000000000000000), LB := ((2070680539095121 : Rat) / 250000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((437855234999999991 : Rat) / 160000000000000000), R := ((876805220999999981 : Rat) / 320000000000000000), D0 := ((876805220999999981 : Rat) / 320000000000000000), D1 := ((295213188999999981 : Rat) / 320000000000000000), D2 := ((58266020999999981 : Rat) / 320000000000000000), D3 := ((20800268999999981 : Rat) / 320000000000000000), D4 := ((7663256999999993 : Rat) / 160000000000000000), LB := ((8852467650652951 : Rat) / 2000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((876805220999999981 : Rat) / 320000000000000000), R := ((43894998599999999 : Rat) / 16000000000000000), D0 := ((43894998599999999 : Rat) / 16000000000000000), D1 := ((14815396999999999 : Rat) / 16000000000000000), D2 := ((2968038599999999 : Rat) / 16000000000000000), D3 := ((1094750999999999 : Rat) / 16000000000000000), D4 := ((14231762999999987 : Rat) / 320000000000000000), LB := ((10426846353099983 : Rat) / 1000000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43894998599999999 : Rat) / 16000000000000000), R := ((440044736999999989 : Rat) / 160000000000000000), D0 := ((440044736999999989 : Rat) / 160000000000000000), D1 := ((149248720999999989 : Rat) / 160000000000000000), D2 := ((30775136999999989 : Rat) / 160000000000000000), D3 := ((12042260999999989 : Rat) / 160000000000000000), D4 := ((3284252999999997 : Rat) / 80000000000000000), LB := ((169123216227883 : Rat) / 31250000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((440044736999999989 : Rat) / 160000000000000000), R := ((110284871999999997 : Rat) / 40000000000000000), D0 := ((110284871999999997 : Rat) / 40000000000000000), D1 := ((37585867999999997 : Rat) / 40000000000000000), D2 := ((7967471999999997 : Rat) / 40000000000000000), D3 := ((3284252999999997 : Rat) / 40000000000000000), D4 := ((1094750999999999 : Rat) / 32000000000000000), LB := ((13146668390572047 : Rat) / 500000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((110284871999999997 : Rat) / 40000000000000000), R := ((221664494999999993 : Rat) / 80000000000000000), D0 := ((221664494999999993 : Rat) / 80000000000000000), D1 := ((76266486999999993 : Rat) / 80000000000000000), D2 := ((17029694999999993 : Rat) / 80000000000000000), D3 := ((7663256999999993 : Rat) / 80000000000000000), D4 := ((1094750999999999 : Rat) / 40000000000000000), LB := ((3297266131860521 : Rat) / 100000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((221664494999999993 : Rat) / 80000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((1094750999999999 : Rat) / 10000000000000000), D4 := ((1094750999999999 : Rat) / 80000000000000000), LB := ((7925769061545723 : Rat) / 50000000000000000) },
  { w1 := ((30773538779252463 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1257568491294751 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((14018953125000000003 : Rat) / 5000000000000000000), D0 := ((14018953125000000003 : Rat) / 5000000000000000000), D1 := ((4931577625000000003 : Rat) / 5000000000000000000), D2 := ((1229278125000000003 : Rat) / 5000000000000000000), D3 := ((643875750000000003 : Rat) / 5000000000000000000), D4 := ((96500250000000503 : Rat) / 5000000000000000000), LB := ((269858110376657 : Rat) / 62500000000000000) }
]

def block070RightChunk000L : Rat := ((90179756696428571459 : Rat) / 50000000000000000000)
def block070RightChunk000R : Rat := ((14018953125000000003 : Rat) / 5000000000000000000)

def block070RightChunk000Certificate : Bool :=
  allBoxesValid block070RightChunk000 &&
  coversFromBool block070RightChunk000 block070RightChunk000L block070RightChunk000R

theorem block070RightChunk000Certificate_eq_true :
    block070RightChunk000Certificate = true := by
  native_decide

def block070RightChainCertificate : Bool :=
  decide (
    block070RightL = ((90179756696428571459 : Rat) / 50000000000000000000) /\
    ((14018953125000000003 : Rat) / 5000000000000000000) = block070RightR)

theorem block070RightChainCertificate_eq_true :
    block070RightChainCertificate = true := by
  native_decide

def block070LeftBoxCount : Nat := boxCount block070LeftBoxes
def block070RightBoxCount : Nat := 50

def block070_rational_certificate : Prop :=
    block070LeftCertificate = true /\
    block070RightChainCertificate = true /\
    block070RightChunk000Certificate = true

theorem block070_rational_certificate_proof :
    block070_rational_certificate := by
  exact ⟨block070LeftCertificate_eq_true, block070RightChainCertificate_eq_true, block070RightChunk000Certificate_eq_true⟩

end Block070
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block070

open Set

def block070W1 : Rat := ((30773538779252463 : Rat) / 10000000000000000)
def block070W2 : Rat := (0 : Rat)
def block070W3 : Rat := (0 : Rat)
def block070W4 : Rat := ((1257568491294751 : Rat) / 5000000000000000)
def block070S1 : Rat := ((18174751 : Rat) / 10000000)
def block070S2 : Rat := ((511587 : Rat) / 200000)
def block070S3 : Rat := ((107000619 : Rat) / 40000000)
def block070S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block070V (y : ℝ) : ℝ :=
  ratPotential block070W1 block070W2 block070W3 block070W4 block070S1 block070S2 block070S3 block070S4 y

def block070LeftParamsCertificate : Bool :=
  allBoxesSameParams block070LeftBoxes block070W1 block070W2 block070W3 block070W4 block070S1 block070S2 block070S3 block070S4

theorem block070LeftParamsCertificate_eq_true :
    block070LeftParamsCertificate = true := by
  native_decide

theorem block070_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block070LeftL : ℝ) (block070LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block070S1 : ℝ))
    (hy2ne : y ≠ (block070S2 : ℝ))
    (hy3ne : y ≠ (block070S3 : ℝ))
    (hy4ne : y ≠ (block070S4 : ℝ)) :
    0 < block070V y := by
  have hcert := block070LeftCertificate_eq_true
  unfold block070LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block070LeftBoxes) (lo := block070LeftL) (hi := block070LeftR)
    (w1 := block070W1) (w2 := block070W2) (w3 := block070W3) (w4 := block070W4)
    (s1 := block070S1) (s2 := block070S2) (s3 := block070S3) (s4 := block070S4)
    hboxes hcover block070LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block070RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block070RightChunk000 block070W1 block070W2 block070W3 block070W4 block070S1 block070S2 block070S3 block070S4

theorem block070RightChunk000ParamsCertificate_eq_true :
    block070RightChunk000ParamsCertificate = true := by
  native_decide

theorem block070_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block070RightChunk000L : ℝ) (block070RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block070S1 : ℝ))
    (hy2ne : y ≠ (block070S2 : ℝ))
    (hy3ne : y ≠ (block070S3 : ℝ))
    (hy4ne : y ≠ (block070S4 : ℝ)) :
    0 < block070V y := by
  have hcert := block070RightChunk000Certificate_eq_true
  unfold block070RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block070RightChunk000) (lo := block070RightChunk000L) (hi := block070RightChunk000R)
    (w1 := block070W1) (w2 := block070W2) (w3 := block070W3) (w4 := block070W4)
    (s1 := block070S1) (s2 := block070S2) (s3 := block070S3) (s4 := block070S4)
    hboxes hcover block070RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block070_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block070RightL : ℝ) (block070RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block070S1 : ℝ))
    (hy2ne : y ≠ (block070S2 : ℝ))
    (hy3ne : y ≠ (block070S3 : ℝ))
    (hy4ne : y ≠ (block070S4 : ℝ)) :
    0 < block070V y := by
  have hL : (block070RightChunk000L : ℝ) = (block070RightL : ℝ) := by
    norm_num [block070RightChunk000L, block070RightL]
  have hR : (block070RightChunk000R : ℝ) = (block070RightR : ℝ) := by
    norm_num [block070RightChunk000R, block070RightR]
  have hyc : y ∈ Icc (block070RightChunk000L : ℝ) (block070RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block070_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block070_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block070LeftL : ℝ) (block070LeftR : ℝ) →
    y ≠ 0 → y ≠ (block070S1 : ℝ) → y ≠ (block070S2 : ℝ) →
    y ≠ (block070S3 : ℝ) → y ≠ (block070S4 : ℝ) → 0 < block070V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block070RightL : ℝ) (block070RightR : ℝ) →
    y ≠ 0 → y ≠ (block070S1 : ℝ) → y ≠ (block070S2 : ℝ) →
    y ≠ (block070S3 : ℝ) → y ≠ (block070S4 : ℝ) → 0 < block070V y)

theorem block070_reallog_certificate_proof :
    block070_reallog_certificate := by
  exact ⟨block070_left_V_pos, block070_right_V_pos⟩

end Block070
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block070.block070V
#check Erdos1038Lean.M1817475.Block070.block070_left_V_pos
#check Erdos1038Lean.M1817475.Block070.block070_right_V_pos
#check Erdos1038Lean.M1817475.Block070.block070_reallog_certificate_proof
