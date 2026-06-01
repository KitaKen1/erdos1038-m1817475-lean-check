/-
Self-contained Lean4Web paste file.
Block 343 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block343

def block343LeftL : Rat := ((4688912946428571447 : Rat) / 6250000000000000000)
def block343LeftR : Rat := ((37521078125000000147 : Rat) / 50000000000000000000)
def block343RightL : Rat := ((10938912946428571447 : Rat) / 6250000000000000000)
def block343RightR : Rat := ((137521078125000000147 : Rat) / 50000000000000000000)

def block343LeftBoxes : List RatBox := [
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4688912946428571447 : Rat) / 6250000000000000000), R := ((37521078125000000147 : Rat) / 50000000000000000000), D0 := ((37521078125000000147 : Rat) / 50000000000000000000), D1 := ((6670306428571428553 : Rat) / 6250000000000000000), D2 := ((11298180803571428553 : Rat) / 6250000000000000000), D3 := ((95916909910714285581 : Rat) / 50000000000000000000), D4 := ((50553601428571426011 : Rat) / 25000000000000000000), LB := ((1580862330747463 : Rat) / 250000000000000000) }
]

def block343LeftCertificate : Bool :=
  allBoxesValid block343LeftBoxes &&
  coversFromBool block343LeftBoxes block343LeftL block343LeftR

theorem block343LeftCertificate_eq_true :
    block343LeftCertificate = true := by
  native_decide

def block343RightChunk000 : List RatBox := [
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((10938912946428571447 : Rat) / 6250000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((420306428571428553 : Rat) / 6250000000000000000), D2 := ((5048180803571428553 : Rat) / 6250000000000000000), D3 := ((45916909910714285581 : Rat) / 50000000000000000000), D4 := ((25553601428571426011 : Rat) / 25000000000000000000), LB := ((4769971650782729 : Rat) / 2500000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42554458482142857157 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((17649478965759233 : Rat) / 100000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24042960982142857157 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((5698929928243489 : Rat) / 50000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19415086607142857157 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((7494287557624277 : Rat) / 100000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17101149419642857157 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((8017578103484961 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14787212232142857157 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((1975167970109791 : Rat) / 125000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13630243638392857157 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((9641375205894559 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((13051759341517857157 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((10801209364125819 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12473275044642857157 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((3392651348558179 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11894790747767857157 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((4033903883877893 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11605548599330357157 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((5309582089662673 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11316306450892857157 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((718980329261619 : Rat) / 250000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11027064302455357157 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((1956490026880503 : Rat) / 2500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10737822154017857157 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((876365270301227 : Rat) / 200000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10593201079799107157 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((3635072448567117 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10448580005580357157 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((7465339122283629 : Rat) / 2500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10303958931361607157 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((1219070074278003 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10159337857142857157 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((19944646673612787 : Rat) / 10000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10014716782924107157 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((3317543322061689 : Rat) / 2000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9870095708705357157 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((22422517742099 : Rat) / 15625000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9725474634486607157 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((165951247882129 : Rat) / 125000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9580853560267857157 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((6706089918921687 : Rat) / 5000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9436232486049107157 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14810619048654383 : Rat) / 10000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9291611411830357157 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((1752859507024307 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9146990337611607157 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((675914300402973 : Rat) / 312500000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9002369263392857157 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((339783029356909 : Rat) / 125000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8857748189174107157 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((3426677483140239 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8713127114955357157 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((4296901475675019 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8568506040736607157 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((213550828679413 : Rat) / 40000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8423884966517857157 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((15310916889410553 : Rat) / 10000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8134642818080357157 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((4616461308116049 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7845400669642857157 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((8611914577559027 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7556158521205357157 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((13691204878819557 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7266916372767857157 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((10361961614228171 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6688432075892857157 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((1003663550776629 : Rat) / 100000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028705463482142857157 : Rat) / 400000000000000000000), D0 := ((1028705463482142857157 : Rat) / 400000000000000000000), D1 := ((301715423482142857157 : Rat) / 400000000000000000000), D2 := ((5531463482142857157 : Rat) / 400000000000000000000), D3 := ((5531463482142857157 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((5408531359606261 : Rat) / 100000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028705463482142857157 : Rat) / 400000000000000000000), R := ((517118463482142857157 : Rat) / 200000000000000000000), D0 := ((517118463482142857157 : Rat) / 200000000000000000000), D1 := ((153623443482142857157 : Rat) / 200000000000000000000), D2 := ((5531463482142857157 : Rat) / 200000000000000000000), D3 := ((38720244375000000099 : Rat) / 400000000000000000000), D4 := ((80242587946428531627 : Rat) / 400000000000000000000), LB := ((27888197314780233 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517118463482142857157 : Rat) / 200000000000000000000), R := ((1039768390446428571471 : Rat) / 400000000000000000000), D0 := ((1039768390446428571471 : Rat) / 400000000000000000000), D1 := ((312778350446428571471 : Rat) / 400000000000000000000), D2 := ((16594390446428571471 : Rat) / 400000000000000000000), D3 := ((16594390446428571471 : Rat) / 200000000000000000000), D4 := ((7471112446428567447 : Rat) / 40000000000000000000), LB := ((96830175761453 : Rat) / 5000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1039768390446428571471 : Rat) / 400000000000000000000), R := ((261324963482142857157 : Rat) / 100000000000000000000), D0 := ((261324963482142857157 : Rat) / 100000000000000000000), D1 := ((79577453482142857157 : Rat) / 100000000000000000000), D2 := ((5531463482142857157 : Rat) / 100000000000000000000), D3 := ((5531463482142857157 : Rat) / 80000000000000000000), D4 := ((69179660982142817313 : Rat) / 400000000000000000000), LB := ((10826086905855403 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261324963482142857157 : Rat) / 100000000000000000000), R := ((528181390446428571471 : Rat) / 200000000000000000000), D0 := ((528181390446428571471 : Rat) / 200000000000000000000), D1 := ((164686370446428571471 : Rat) / 200000000000000000000), D2 := ((16594390446428571471 : Rat) / 200000000000000000000), D3 := ((5531463482142857157 : Rat) / 100000000000000000000), D4 := ((15912049374999990039 : Rat) / 100000000000000000000), LB := ((2344540992015587 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528181390446428571471 : Rat) / 200000000000000000000), R := ((133428213482142857157 : Rat) / 50000000000000000000), D0 := ((133428213482142857157 : Rat) / 50000000000000000000), D1 := ((42554458482142857157 : Rat) / 50000000000000000000), D2 := ((5531463482142857157 : Rat) / 50000000000000000000), D3 := ((5531463482142857157 : Rat) / 200000000000000000000), D4 := ((26292635267857122921 : Rat) / 200000000000000000000), LB := ((3919202377397657 : Rat) / 50000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133428213482142857157 : Rat) / 50000000000000000000), R := ((268902859285714285809 : Rat) / 100000000000000000000), D0 := ((268902859285714285809 : Rat) / 100000000000000000000), D1 := ((87155349285714285809 : Rat) / 100000000000000000000), D2 := ((13109359285714285809 : Rat) / 100000000000000000000), D3 := ((409286464285714299 : Rat) / 20000000000000000000), D4 := ((5190292946428566441 : Rat) / 50000000000000000000), LB := ((5880703488837749 : Rat) / 50000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((268902859285714285809 : Rat) / 100000000000000000000), R := ((33868661450892857163 : Rat) / 12500000000000000000), D0 := ((33868661450892857163 : Rat) / 12500000000000000000), D1 := ((11150222700892857163 : Rat) / 12500000000000000000), D2 := ((1894473950892857163 : Rat) / 12500000000000000000), D3 := ((409286464285714299 : Rat) / 10000000000000000000), D4 := ((8334153571428561387 : Rat) / 100000000000000000000), LB := ((5052940427747177 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((33868661450892857163 : Rat) / 12500000000000000000), R := ((1085843598750000000711 : Rat) / 400000000000000000000), D0 := ((1085843598750000000711 : Rat) / 400000000000000000000), D1 := ((358853558750000000711 : Rat) / 400000000000000000000), D2 := ((62669598750000000711 : Rat) / 400000000000000000000), D3 := ((3683578178571428691 : Rat) / 80000000000000000000), D4 := ((1571930312499997473 : Rat) / 25000000000000000000), LB := ((11431147509528339 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1085843598750000000711 : Rat) / 400000000000000000000), R := ((543945015535714286103 : Rat) / 200000000000000000000), D0 := ((543945015535714286103 : Rat) / 200000000000000000000), D1 := ((180449995535714286103 : Rat) / 200000000000000000000), D2 := ((32358015535714286103 : Rat) / 200000000000000000000), D3 := ((409286464285714299 : Rat) / 8000000000000000000), D4 := ((23104452678571388073 : Rat) / 400000000000000000000), LB := ((1301808622166889 : Rat) / 125000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((543945015535714286103 : Rat) / 200000000000000000000), R := ((1089936463392857143701 : Rat) / 400000000000000000000), D0 := ((1089936463392857143701 : Rat) / 400000000000000000000), D1 := ((362946423392857143701 : Rat) / 400000000000000000000), D2 := ((66762463392857143701 : Rat) / 400000000000000000000), D3 := ((4502151107142857289 : Rat) / 80000000000000000000), D4 := ((10529010178571408289 : Rat) / 200000000000000000000), LB := ((3047438473145203 : Rat) / 5000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1089936463392857143701 : Rat) / 400000000000000000000), R := ((2181919359107142858897 : Rat) / 800000000000000000000), D0 := ((2181919359107142858897 : Rat) / 800000000000000000000), D1 := ((727939279107142858897 : Rat) / 800000000000000000000), D2 := ((135571359107142858897 : Rat) / 800000000000000000000), D3 := ((9413588678571428877 : Rat) / 160000000000000000000), D4 := ((19011588035714245083 : Rat) / 400000000000000000000), LB := ((974958860777031 : Rat) / 250000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2181919359107142858897 : Rat) / 800000000000000000000), R := ((272995723928571428799 : Rat) / 100000000000000000000), D0 := ((272995723928571428799 : Rat) / 100000000000000000000), D1 := ((91248213928571428799 : Rat) / 100000000000000000000), D2 := ((17202223928571428799 : Rat) / 100000000000000000000), D3 := ((1227859392857142897 : Rat) / 20000000000000000000), D4 := ((35976743749999918671 : Rat) / 800000000000000000000), LB := ((10273534449464217 : Rat) / 10000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272995723928571428799 : Rat) / 100000000000000000000), R := ((4369978015178571432279 : Rat) / 1600000000000000000000), D0 := ((4369978015178571432279 : Rat) / 1600000000000000000000), D1 := ((1462017855178571432279 : Rat) / 1600000000000000000000), D2 := ((277282015178571432279 : Rat) / 1600000000000000000000), D3 := ((20055036750000000651 : Rat) / 320000000000000000000), D4 := ((4241288928571418397 : Rat) / 100000000000000000000), LB := ((987706823382381 : Rat) / 250000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4369978015178571432279 : Rat) / 1600000000000000000000), R := ((2186012223750000001887 : Rat) / 800000000000000000000), D0 := ((2186012223750000001887 : Rat) / 800000000000000000000), D1 := ((732032143750000001887 : Rat) / 800000000000000000000), D2 := ((139664223750000001887 : Rat) / 800000000000000000000), D3 := ((409286464285714299 : Rat) / 6400000000000000000), D4 := ((65814190535714122857 : Rat) / 1600000000000000000000), LB := ((30920226276957563 : Rat) / 10000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2186012223750000001887 : Rat) / 800000000000000000000), R := ((4374070879821428575269 : Rat) / 1600000000000000000000), D0 := ((4374070879821428575269 : Rat) / 1600000000000000000000), D1 := ((1466110719821428575269 : Rat) / 1600000000000000000000), D2 := ((281374879821428575269 : Rat) / 1600000000000000000000), D3 := ((20873609678571429249 : Rat) / 320000000000000000000), D4 := ((31883879107142775681 : Rat) / 800000000000000000000), LB := ((12149063414951533 : Rat) / 5000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4374070879821428575269 : Rat) / 1600000000000000000000), R := ((1094029328035714286691 : Rat) / 400000000000000000000), D0 := ((1094029328035714286691 : Rat) / 400000000000000000000), D1 := ((367039288035714286691 : Rat) / 400000000000000000000), D2 := ((70855328035714286691 : Rat) / 400000000000000000000), D3 := ((5320724035714285887 : Rat) / 80000000000000000000), D4 := ((61721325892856979867 : Rat) / 1600000000000000000000), LB := ((9852812234078523 : Rat) / 5000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094029328035714286691 : Rat) / 400000000000000000000), R := ((4378163744464285718259 : Rat) / 1600000000000000000000), D0 := ((4378163744464285718259 : Rat) / 1600000000000000000000), D1 := ((1470203584464285718259 : Rat) / 1600000000000000000000), D2 := ((285467744464285718259 : Rat) / 1600000000000000000000), D3 := ((21692182607142857847 : Rat) / 320000000000000000000), D4 := ((14918723392857102093 : Rat) / 400000000000000000000), LB := ((4304119259662259 : Rat) / 2500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4378163744464285718259 : Rat) / 1600000000000000000000), R := ((2190105088392857144877 : Rat) / 800000000000000000000), D0 := ((2190105088392857144877 : Rat) / 800000000000000000000), D1 := ((736125008392857144877 : Rat) / 800000000000000000000), D2 := ((143757088392857144877 : Rat) / 800000000000000000000), D3 := ((11050734535714286073 : Rat) / 160000000000000000000), D4 := ((57628461249999836877 : Rat) / 1600000000000000000000), LB := ((8457840229455227 : Rat) / 5000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190105088392857144877 : Rat) / 800000000000000000000), R := ((4382256609107142861249 : Rat) / 1600000000000000000000), D0 := ((4382256609107142861249 : Rat) / 1600000000000000000000), D1 := ((1474296449107142861249 : Rat) / 1600000000000000000000), D2 := ((289560609107142861249 : Rat) / 1600000000000000000000), D3 := ((4502151107142857289 : Rat) / 64000000000000000000), D4 := ((27791014464285632691 : Rat) / 800000000000000000000), LB := ((945041494096327 : Rat) / 500000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4382256609107142861249 : Rat) / 1600000000000000000000), R := ((548037880178571429093 : Rat) / 200000000000000000000), D0 := ((548037880178571429093 : Rat) / 200000000000000000000), D1 := ((184542860178571429093 : Rat) / 200000000000000000000), D2 := ((36450880178571429093 : Rat) / 200000000000000000000), D3 := ((2865005250000000093 : Rat) / 40000000000000000000), D4 := ((53535596607142693887 : Rat) / 1600000000000000000000), LB := ((2328376097892937 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((548037880178571429093 : Rat) / 200000000000000000000), R := ((4386349473750000004239 : Rat) / 1600000000000000000000), D0 := ((4386349473750000004239 : Rat) / 1600000000000000000000), D1 := ((1478389313750000004239 : Rat) / 1600000000000000000000), D2 := ((293653473750000004239 : Rat) / 1600000000000000000000), D3 := ((23329328464285715043 : Rat) / 320000000000000000000), D4 := ((6436145535714265299 : Rat) / 200000000000000000000), LB := ((15096267083218873 : Rat) / 5000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4386349473750000004239 : Rat) / 1600000000000000000000), R := ((2194197953035714287867 : Rat) / 800000000000000000000), D0 := ((2194197953035714287867 : Rat) / 800000000000000000000), D1 := ((740217873035714287867 : Rat) / 800000000000000000000), D2 := ((147849953035714287867 : Rat) / 800000000000000000000), D3 := ((11869307464285714671 : Rat) / 160000000000000000000), D4 := ((49442731964285550897 : Rat) / 1600000000000000000000), LB := ((7954768558950387 : Rat) / 2000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2194197953035714287867 : Rat) / 800000000000000000000), R := ((1098122192678571429681 : Rat) / 400000000000000000000), D0 := ((1098122192678571429681 : Rat) / 400000000000000000000), D1 := ((371132152678571429681 : Rat) / 400000000000000000000), D2 := ((74948192678571429681 : Rat) / 400000000000000000000), D3 := ((1227859392857142897 : Rat) / 16000000000000000000), D4 := ((23698149821428489701 : Rat) / 800000000000000000000), LB := ((6870847108412237 : Rat) / 10000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1098122192678571429681 : Rat) / 400000000000000000000), R := ((2198290817678571430857 : Rat) / 800000000000000000000), D0 := ((2198290817678571430857 : Rat) / 800000000000000000000), D1 := ((744310737678571430857 : Rat) / 800000000000000000000), D2 := ((151942817678571430857 : Rat) / 800000000000000000000), D3 := ((12687880392857143269 : Rat) / 160000000000000000000), D4 := ((10825858749999959103 : Rat) / 400000000000000000000), LB := ((4192767889487359 : Rat) / 1000000000000000000) },
  { w1 := ((575551735415353 : Rat) / 625000000000000), w2 := ((474892195352379 : Rat) / 10000000000000000), w3 := ((1470156391212689 : Rat) / 10000000000000000), w4 := ((1721389586602471 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133428213482142857157 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2198290817678571430857 : Rat) / 800000000000000000000), R := ((137521078125000000147 : Rat) / 50000000000000000000), D0 := ((137521078125000000147 : Rat) / 50000000000000000000), D1 := ((46647323125000000147 : Rat) / 50000000000000000000), D2 := ((9624328125000000147 : Rat) / 50000000000000000000), D3 := ((409286464285714299 : Rat) / 5000000000000000000), D4 := ((19605285178571346711 : Rat) / 800000000000000000000), LB := ((9103691297658867 : Rat) / 1000000000000000000) }
]

def block343RightChunk000L : Rat := ((10938912946428571447 : Rat) / 6250000000000000000)
def block343RightChunk000R : Rat := ((137521078125000000147 : Rat) / 50000000000000000000)

def block343RightChunk000Certificate : Bool :=
  allBoxesValid block343RightChunk000 &&
  coversFromBool block343RightChunk000 block343RightChunk000L block343RightChunk000R

theorem block343RightChunk000Certificate_eq_true :
    block343RightChunk000Certificate = true := by
  native_decide

def block343RightChainCertificate : Bool :=
  decide (
    block343RightL = ((10938912946428571447 : Rat) / 6250000000000000000) /\
    ((137521078125000000147 : Rat) / 50000000000000000000) = block343RightR)

theorem block343RightChainCertificate_eq_true :
    block343RightChainCertificate = true := by
  native_decide

def block343LeftBoxCount : Nat := boxCount block343LeftBoxes
def block343RightBoxCount : Nat := 61

def block343_rational_certificate : Prop :=
    block343LeftCertificate = true /\
    block343RightChainCertificate = true /\
    block343RightChunk000Certificate = true

theorem block343_rational_certificate_proof :
    block343_rational_certificate := by
  exact ⟨block343LeftCertificate_eq_true, block343RightChainCertificate_eq_true, block343RightChunk000Certificate_eq_true⟩

end Block343
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block343

open Set

def block343W1 : Rat := ((575551735415353 : Rat) / 625000000000000)
def block343W2 : Rat := ((474892195352379 : Rat) / 10000000000000000)
def block343W3 : Rat := ((1470156391212689 : Rat) / 10000000000000000)
def block343W4 : Rat := ((1721389586602471 : Rat) / 12500000000000000)
def block343S1 : Rat := ((18174751 : Rat) / 10000000)
def block343S2 : Rat := ((511587 : Rat) / 200000)
def block343S3 : Rat := ((133428213482142857157 : Rat) / 50000000000000000000)
def block343S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block343V (y : ℝ) : ℝ :=
  ratPotential block343W1 block343W2 block343W3 block343W4 block343S1 block343S2 block343S3 block343S4 y

def block343LeftParamsCertificate : Bool :=
  allBoxesSameParams block343LeftBoxes block343W1 block343W2 block343W3 block343W4 block343S1 block343S2 block343S3 block343S4

theorem block343LeftParamsCertificate_eq_true :
    block343LeftParamsCertificate = true := by
  native_decide

theorem block343_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block343LeftL : ℝ) (block343LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block343S1 : ℝ))
    (hy2ne : y ≠ (block343S2 : ℝ))
    (hy3ne : y ≠ (block343S3 : ℝ))
    (hy4ne : y ≠ (block343S4 : ℝ)) :
    0 < block343V y := by
  have hcert := block343LeftCertificate_eq_true
  unfold block343LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block343LeftBoxes) (lo := block343LeftL) (hi := block343LeftR)
    (w1 := block343W1) (w2 := block343W2) (w3 := block343W3) (w4 := block343W4)
    (s1 := block343S1) (s2 := block343S2) (s3 := block343S3) (s4 := block343S4)
    hboxes hcover block343LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block343RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block343RightChunk000 block343W1 block343W2 block343W3 block343W4 block343S1 block343S2 block343S3 block343S4

theorem block343RightChunk000ParamsCertificate_eq_true :
    block343RightChunk000ParamsCertificate = true := by
  native_decide

theorem block343_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block343RightChunk000L : ℝ) (block343RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block343S1 : ℝ))
    (hy2ne : y ≠ (block343S2 : ℝ))
    (hy3ne : y ≠ (block343S3 : ℝ))
    (hy4ne : y ≠ (block343S4 : ℝ)) :
    0 < block343V y := by
  have hcert := block343RightChunk000Certificate_eq_true
  unfold block343RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block343RightChunk000) (lo := block343RightChunk000L) (hi := block343RightChunk000R)
    (w1 := block343W1) (w2 := block343W2) (w3 := block343W3) (w4 := block343W4)
    (s1 := block343S1) (s2 := block343S2) (s3 := block343S3) (s4 := block343S4)
    hboxes hcover block343RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block343_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block343RightL : ℝ) (block343RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block343S1 : ℝ))
    (hy2ne : y ≠ (block343S2 : ℝ))
    (hy3ne : y ≠ (block343S3 : ℝ))
    (hy4ne : y ≠ (block343S4 : ℝ)) :
    0 < block343V y := by
  have hL : (block343RightChunk000L : ℝ) = (block343RightL : ℝ) := by
    norm_num [block343RightChunk000L, block343RightL]
  have hR : (block343RightChunk000R : ℝ) = (block343RightR : ℝ) := by
    norm_num [block343RightChunk000R, block343RightR]
  have hyc : y ∈ Icc (block343RightChunk000L : ℝ) (block343RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block343_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block343_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block343LeftL : ℝ) (block343LeftR : ℝ) →
    y ≠ 0 → y ≠ (block343S1 : ℝ) → y ≠ (block343S2 : ℝ) →
    y ≠ (block343S3 : ℝ) → y ≠ (block343S4 : ℝ) → 0 < block343V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block343RightL : ℝ) (block343RightR : ℝ) →
    y ≠ 0 → y ≠ (block343S1 : ℝ) → y ≠ (block343S2 : ℝ) →
    y ≠ (block343S3 : ℝ) → y ≠ (block343S4 : ℝ) → 0 < block343V y)

theorem block343_reallog_certificate_proof :
    block343_reallog_certificate := by
  exact ⟨block343_left_V_pos, block343_right_V_pos⟩

end Block343
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block343.block343V
#check Erdos1038Lean.M1817475.Block343.block343_left_V_pos
#check Erdos1038Lean.M1817475.Block343.block343_right_V_pos
#check Erdos1038Lean.M1817475.Block343.block343_reallog_certificate_proof
