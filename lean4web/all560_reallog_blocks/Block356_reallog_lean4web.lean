/-
Self-contained Lean4Web paste file.
Block 356 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block356

def block356LeftL : Rat := ((37384234375000000153 : Rat) / 50000000000000000000)
def block356LeftR : Rat := ((9348502232142857181 : Rat) / 12500000000000000000)
def block356RightL : Rat := ((87384234375000000153 : Rat) / 50000000000000000000)
def block356RightR : Rat := ((34348502232142857181 : Rat) / 12500000000000000000)

def block356LeftBoxes : List RatBox := [
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37384234375000000153 : Rat) / 50000000000000000000), R := ((9348502232142857181 : Rat) / 12500000000000000000), D0 := ((9348502232142857181 : Rat) / 12500000000000000000), D1 := ((53489520624999999847 : Rat) / 50000000000000000000), D2 := ((90512515624999999847 : Rat) / 50000000000000000000), D3 := ((47894920357142857079 : Rat) / 25000000000000000000), D4 := ((20246854410714284689 : Rat) / 10000000000000000000), LB := ((3100043952281431 : Rat) / 500000000000000000) }
]

def block356LeftCertificate : Bool :=
  allBoxesValid block356LeftBoxes &&
  coversFromBool block356LeftBoxes block356LeftL block356LeftR

theorem block356LeftCertificate_eq_true :
    block356LeftCertificate = true := by
  native_decide

def block356RightChunk000 : List RatBox := [
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87384234375000000153 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3489520624999999847 : Rat) / 50000000000000000000), D2 := ((40512515624999999847 : Rat) / 50000000000000000000), D3 := ((22894920357142857079 : Rat) / 25000000000000000000), D4 := ((10246854410714284689 : Rat) / 10000000000000000000), LB := ((4508485129218433 : Rat) / 2500000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42300320089285714311 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((7583142939413841 : Rat) / 50000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23788822589285714311 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((9833408069330377 : Rat) / 100000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19160948214285714311 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((1579025654147903 : Rat) / 25000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16847011026785714311 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((462032639302239 : Rat) / 62500000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14533073839285714311 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((9235060854723337 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13376105245535714311 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((6910323046508973 : Rat) / 500000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12797620948660714311 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((12339139716973313 : Rat) / 2000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12219136651785714311 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((653851587168219 : Rat) / 62500000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11929894503348214311 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((1880360646183847 : Rat) / 250000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11640652354910714311 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((2441681557639269 : Rat) / 500000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11351410206473214311 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((256000692441119 : Rat) / 100000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11062168058035714311 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((5656724086955389 : Rat) / 10000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10772925909598214311 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((521318402016243 : Rat) / 125000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10628304835379464311 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((34613507723864623 : Rat) / 10000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10483683761160714311 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((28458287732681387 : Rat) / 10000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10339062686941964311 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((2326744709820333 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10194441612723214311 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((4767681640767199 : Rat) / 2500000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10049820538504464311 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((3180039211310881 : Rat) / 2000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9905199464285714311 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((344762768669897 : Rat) / 250000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9760578390066964311 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((12779205868146959 : Rat) / 10000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9615957315848214311 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((1290703778090957 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9471336241629464311 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((2843676094653469 : Rat) / 2000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9326715167410714311 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((16761688957283027 : Rat) / 10000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9182094093191964311 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((2059004390382063 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9037473018973214311 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((12880897812198727 : Rat) / 5000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8892851944754464311 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((323413304495207 : Rat) / 100000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8748230870535714311 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((4039998910530501 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8603609796316964311 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((2500858773504963 : Rat) / 500000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8458988722098214311 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((2932297866487521 : Rat) / 2500000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8169746573660714311 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((3995949238155411 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7880504425223214311 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((7615903826866499 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7591262276785714311 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((25049442988802073 : Rat) / 10000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7012777979910714311 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((3819524110348381 : Rat) / 250000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6434293683035714311 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((8301381793641413 : Rat) / 500000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516864325089285714311 : Rat) / 200000000000000000000), D0 := ((516864325089285714311 : Rat) / 200000000000000000000), D1 := ((153369305089285714311 : Rat) / 200000000000000000000), D2 := ((5277325089285714311 : Rat) / 200000000000000000000), D3 := ((5277325089285714311 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((12889481376992973 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516864325089285714311 : Rat) / 200000000000000000000), R := ((261070825089285714311 : Rat) / 100000000000000000000), D0 := ((261070825089285714311 : Rat) / 100000000000000000000), D1 := ((79323315089285714311 : Rat) / 100000000000000000000), D2 := ((5277325089285714311 : Rat) / 100000000000000000000), D3 := ((15831975267857142933 : Rat) / 200000000000000000000), D4 := ((37609700624999980081 : Rat) / 200000000000000000000), LB := ((367375722167421 : Rat) / 312500000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261070825089285714311 : Rat) / 100000000000000000000), R := ((527418975267857142933 : Rat) / 200000000000000000000), D0 := ((527418975267857142933 : Rat) / 200000000000000000000), D1 := ((163923955267857142933 : Rat) / 200000000000000000000), D2 := ((15831975267857142933 : Rat) / 200000000000000000000), D3 := ((5277325089285714311 : Rat) / 100000000000000000000), D4 := ((3233237553571426577 : Rat) / 20000000000000000000), LB := ((3089477836358101 : Rat) / 125000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527418975267857142933 : Rat) / 200000000000000000000), R := ((133174075089285714311 : Rat) / 50000000000000000000), D0 := ((133174075089285714311 : Rat) / 50000000000000000000), D1 := ((42300320089285714311 : Rat) / 50000000000000000000), D2 := ((5277325089285714311 : Rat) / 50000000000000000000), D3 := ((5277325089285714311 : Rat) / 200000000000000000000), D4 := ((27055050446428551459 : Rat) / 200000000000000000000), LB := ((2039783096984833 : Rat) / 20000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133174075089285714311 : Rat) / 50000000000000000000), R := ((536916234196428571657 : Rat) / 200000000000000000000), D0 := ((536916234196428571657 : Rat) / 200000000000000000000), D1 := ((173421214196428571657 : Rat) / 200000000000000000000), D2 := ((25329234196428571657 : Rat) / 200000000000000000000), D3 := ((4219933839285714413 : Rat) / 200000000000000000000), D4 := ((5444431339285709287 : Rat) / 50000000000000000000), LB := ((2544388298402137 : Rat) / 20000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((536916234196428571657 : Rat) / 200000000000000000000), R := ((54113616803571428607 : Rat) / 20000000000000000000), D0 := ((54113616803571428607 : Rat) / 20000000000000000000), D1 := ((17764114803571428607 : Rat) / 20000000000000000000), D2 := ((2954916803571428607 : Rat) / 20000000000000000000), D3 := ((4219933839285714413 : Rat) / 100000000000000000000), D4 := ((3511558303571424547 : Rat) / 40000000000000000000), LB := ((49794690226951 : Rat) / 3125000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((54113616803571428607 : Rat) / 20000000000000000000), R := ((1086492269910714286553 : Rat) / 400000000000000000000), D0 := ((1086492269910714286553 : Rat) / 400000000000000000000), D1 := ((359502229910714286553 : Rat) / 400000000000000000000), D2 := ((63318269910714286553 : Rat) / 400000000000000000000), D3 := ((4219933839285714413 : Rat) / 80000000000000000000), D4 := ((6668928839285704161 : Rat) / 100000000000000000000), LB := ((13398913014767977 : Rat) / 5000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1086492269910714286553 : Rat) / 400000000000000000000), R := ((2177204473660714287519 : Rat) / 800000000000000000000), D0 := ((2177204473660714287519 : Rat) / 800000000000000000000), D1 := ((723224393660714287519 : Rat) / 800000000000000000000), D2 := ((130856473660714287519 : Rat) / 800000000000000000000), D3 := ((46419272232142858543 : Rat) / 800000000000000000000), D4 := ((22455781517857102231 : Rat) / 400000000000000000000), LB := ((34566485020221527 : Rat) / 10000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2177204473660714287519 : Rat) / 800000000000000000000), R := ((4358628881160714289451 : Rat) / 1600000000000000000000), D0 := ((4358628881160714289451 : Rat) / 1600000000000000000000), D1 := ((1450668721160714289451 : Rat) / 1600000000000000000000), D2 := ((265932881160714289451 : Rat) / 1600000000000000000000), D3 := ((97058478303571431499 : Rat) / 1600000000000000000000), D4 := ((40691629196428490049 : Rat) / 800000000000000000000), LB := ((6102427229262519 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4358628881160714289451 : Rat) / 1600000000000000000000), R := ((545356101875000000483 : Rat) / 200000000000000000000), D0 := ((545356101875000000483 : Rat) / 200000000000000000000), D1 := ((181861081875000000483 : Rat) / 200000000000000000000), D2 := ((33769101875000000483 : Rat) / 200000000000000000000), D3 := ((12659801517857143239 : Rat) / 200000000000000000000), D4 := ((15432664910714253137 : Rat) / 320000000000000000000), LB := ((27555357718459517 : Rat) / 10000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545356101875000000483 : Rat) / 200000000000000000000), R := ((4367068748839285718277 : Rat) / 1600000000000000000000), D0 := ((4367068748839285718277 : Rat) / 1600000000000000000000), D1 := ((1459108588839285718277 : Rat) / 1600000000000000000000), D2 := ((274372748839285718277 : Rat) / 1600000000000000000000), D3 := ((4219933839285714413 : Rat) / 64000000000000000000), D4 := ((9117923839285693909 : Rat) / 200000000000000000000), LB := ((2648886007604323 : Rat) / 25000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4367068748839285718277 : Rat) / 1600000000000000000000), R := ((8738357431517857150967 : Rat) / 3200000000000000000000), D0 := ((8738357431517857150967 : Rat) / 3200000000000000000000), D1 := ((2922437111517857150967 : Rat) / 3200000000000000000000), D2 := ((552965431517857150967 : Rat) / 3200000000000000000000), D3 := ((215216625803571435063 : Rat) / 3200000000000000000000), D4 := ((68723456874999836859 : Rat) / 1600000000000000000000), LB := ((1621946483554737 : Rat) / 500000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8738357431517857150967 : Rat) / 3200000000000000000000), R := ((437128868267857143269 : Rat) / 160000000000000000000), D0 := ((437128868267857143269 : Rat) / 160000000000000000000), D1 := ((146332852267857143269 : Rat) / 160000000000000000000), D2 := ((27859268267857143269 : Rat) / 160000000000000000000), D3 := ((54859139910714287369 : Rat) / 800000000000000000000), D4 := ((26645395982142791861 : Rat) / 640000000000000000000), LB := ((626438941035673 : Rat) / 250000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((437128868267857143269 : Rat) / 160000000000000000000), R := ((8746797299196428579793 : Rat) / 3200000000000000000000), D0 := ((8746797299196428579793 : Rat) / 3200000000000000000000), D1 := ((2930876979196428579793 : Rat) / 3200000000000000000000), D2 := ((561405299196428579793 : Rat) / 3200000000000000000000), D3 := ((223656493482142863889 : Rat) / 3200000000000000000000), D4 := ((32251761517857061223 : Rat) / 800000000000000000000), LB := ((157389987627643 : Rat) / 80000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8746797299196428579793 : Rat) / 3200000000000000000000), R := ((4375508616517857147103 : Rat) / 1600000000000000000000), D0 := ((4375508616517857147103 : Rat) / 1600000000000000000000), D1 := ((1467548456517857147103 : Rat) / 1600000000000000000000), D2 := ((282812616517857147103 : Rat) / 1600000000000000000000), D3 := ((113938213660714289151 : Rat) / 1600000000000000000000), D4 := ((124787112232142530479 : Rat) / 3200000000000000000000), LB := ((8179388420689049 : Rat) / 5000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4375508616517857147103 : Rat) / 1600000000000000000000), R := ((8755237166875000008619 : Rat) / 3200000000000000000000), D0 := ((8755237166875000008619 : Rat) / 3200000000000000000000), D1 := ((2939316846875000008619 : Rat) / 3200000000000000000000), D2 := ((569845166875000008619 : Rat) / 3200000000000000000000), D3 := ((46419272232142858543 : Rat) / 640000000000000000000), D4 := ((60283589196428408033 : Rat) / 1600000000000000000000), LB := ((7597316529729947 : Rat) / 5000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8755237166875000008619 : Rat) / 3200000000000000000000), R := ((1094932137589285715379 : Rat) / 400000000000000000000), D0 := ((1094932137589285715379 : Rat) / 400000000000000000000), D1 := ((367942097589285715379 : Rat) / 400000000000000000000), D2 := ((71758137589285715379 : Rat) / 400000000000000000000), D3 := ((29539536875000000891 : Rat) / 400000000000000000000), D4 := ((116347244553571101653 : Rat) / 3200000000000000000000), LB := ((3255060515099717 : Rat) / 2000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094932137589285715379 : Rat) / 400000000000000000000), R := ((1752735406910714287489 : Rat) / 640000000000000000000), D0 := ((1752735406910714287489 : Rat) / 640000000000000000000), D1 := ((589551342910714287489 : Rat) / 640000000000000000000), D2 := ((115657006910714287489 : Rat) / 640000000000000000000), D3 := ((240536228839285721541 : Rat) / 3200000000000000000000), D4 := ((2803182767857134681 : Rat) / 80000000000000000000), LB := ((1970830494592013 : Rat) / 1000000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1752735406910714287489 : Rat) / 640000000000000000000), R := ((4383948484196428575929 : Rat) / 1600000000000000000000), D0 := ((4383948484196428575929 : Rat) / 1600000000000000000000), D1 := ((1475988324196428575929 : Rat) / 1600000000000000000000), D2 := ((291252484196428575929 : Rat) / 1600000000000000000000), D3 := ((122378081339285717977 : Rat) / 1600000000000000000000), D4 := ((107907376874999672827 : Rat) / 3200000000000000000000), LB := ((204932392891779 : Rat) / 80000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4383948484196428575929 : Rat) / 1600000000000000000000), R := ((8772116902232142866271 : Rat) / 3200000000000000000000), D0 := ((8772116902232142866271 : Rat) / 3200000000000000000000), D1 := ((2956196582232142866271 : Rat) / 3200000000000000000000), D2 := ((586724902232142866271 : Rat) / 3200000000000000000000), D3 := ((248976096517857150367 : Rat) / 3200000000000000000000), D4 := ((51843721517856979207 : Rat) / 1600000000000000000000), LB := ((1066893082906379 : Rat) / 312500000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8772116902232142866271 : Rat) / 3200000000000000000000), R := ((2194084209017857145171 : Rat) / 800000000000000000000), D0 := ((2194084209017857145171 : Rat) / 800000000000000000000), D1 := ((740104129017857145171 : Rat) / 800000000000000000000), D2 := ((147736209017857145171 : Rat) / 800000000000000000000), D3 := ((12659801517857143239 : Rat) / 160000000000000000000), D4 := ((99467509196428244001 : Rat) / 3200000000000000000000), LB := ((2272065111216637 : Rat) / 500000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2194084209017857145171 : Rat) / 800000000000000000000), R := ((878477670375000000951 : Rat) / 320000000000000000000), D0 := ((878477670375000000951 : Rat) / 320000000000000000000), D1 := ((296885638375000000951 : Rat) / 320000000000000000000), D2 := ((59938470375000000951 : Rat) / 320000000000000000000), D3 := ((130817949017857146803 : Rat) / 1600000000000000000000), D4 := ((23811893839285632397 : Rat) / 800000000000000000000), LB := ((894329217684571 : Rat) / 625000000000000000) },
  { w1 := ((4471729879892043 : Rat) / 5000000000000000), w2 := ((11858715346994909 : Rat) / 250000000000000000), w3 := ((1884664832942853 : Rat) / 12500000000000000), w4 := ((13864719119000987 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133174075089285714311 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((878477670375000000951 : Rat) / 320000000000000000000), R := ((34348502232142857181 : Rat) / 12500000000000000000), D0 := ((34348502232142857181 : Rat) / 12500000000000000000), D1 := ((11630063482142857181 : Rat) / 12500000000000000000), D2 := ((2374314732142857181 : Rat) / 12500000000000000000), D3 := ((4219933839285714413 : Rat) / 50000000000000000000), D4 := ((43403853839285550381 : Rat) / 1600000000000000000000), LB := ((1069190237892903 : Rat) / 200000000000000000) }
]

def block356RightChunk000L : Rat := ((87384234375000000153 : Rat) / 50000000000000000000)
def block356RightChunk000R : Rat := ((34348502232142857181 : Rat) / 12500000000000000000)

def block356RightChunk000Certificate : Bool :=
  allBoxesValid block356RightChunk000 &&
  coversFromBool block356RightChunk000 block356RightChunk000L block356RightChunk000R

theorem block356RightChunk000Certificate_eq_true :
    block356RightChunk000Certificate = true := by
  native_decide

def block356RightChainCertificate : Bool :=
  decide (
    block356RightL = ((87384234375000000153 : Rat) / 50000000000000000000) /\
    ((34348502232142857181 : Rat) / 12500000000000000000) = block356RightR)

theorem block356RightChainCertificate_eq_true :
    block356RightChainCertificate = true := by
  native_decide

def block356LeftBoxCount : Nat := boxCount block356LeftBoxes
def block356RightBoxCount : Nat := 58

def block356_rational_certificate : Prop :=
    block356LeftCertificate = true /\
    block356RightChainCertificate = true /\
    block356RightChunk000Certificate = true

theorem block356_rational_certificate_proof :
    block356_rational_certificate := by
  exact ⟨block356LeftCertificate_eq_true, block356RightChainCertificate_eq_true, block356RightChunk000Certificate_eq_true⟩

end Block356
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block356

open Set

def block356W1 : Rat := ((4471729879892043 : Rat) / 5000000000000000)
def block356W2 : Rat := ((11858715346994909 : Rat) / 250000000000000000)
def block356W3 : Rat := ((1884664832942853 : Rat) / 12500000000000000)
def block356W4 : Rat := ((13864719119000987 : Rat) / 100000000000000000)
def block356S1 : Rat := ((18174751 : Rat) / 10000000)
def block356S2 : Rat := ((511587 : Rat) / 200000)
def block356S3 : Rat := ((133174075089285714311 : Rat) / 50000000000000000000)
def block356S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block356V (y : ℝ) : ℝ :=
  ratPotential block356W1 block356W2 block356W3 block356W4 block356S1 block356S2 block356S3 block356S4 y

def block356LeftParamsCertificate : Bool :=
  allBoxesSameParams block356LeftBoxes block356W1 block356W2 block356W3 block356W4 block356S1 block356S2 block356S3 block356S4

theorem block356LeftParamsCertificate_eq_true :
    block356LeftParamsCertificate = true := by
  native_decide

theorem block356_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block356LeftL : ℝ) (block356LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block356S1 : ℝ))
    (hy2ne : y ≠ (block356S2 : ℝ))
    (hy3ne : y ≠ (block356S3 : ℝ))
    (hy4ne : y ≠ (block356S4 : ℝ)) :
    0 < block356V y := by
  have hcert := block356LeftCertificate_eq_true
  unfold block356LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block356LeftBoxes) (lo := block356LeftL) (hi := block356LeftR)
    (w1 := block356W1) (w2 := block356W2) (w3 := block356W3) (w4 := block356W4)
    (s1 := block356S1) (s2 := block356S2) (s3 := block356S3) (s4 := block356S4)
    hboxes hcover block356LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block356RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block356RightChunk000 block356W1 block356W2 block356W3 block356W4 block356S1 block356S2 block356S3 block356S4

theorem block356RightChunk000ParamsCertificate_eq_true :
    block356RightChunk000ParamsCertificate = true := by
  native_decide

theorem block356_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block356RightChunk000L : ℝ) (block356RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block356S1 : ℝ))
    (hy2ne : y ≠ (block356S2 : ℝ))
    (hy3ne : y ≠ (block356S3 : ℝ))
    (hy4ne : y ≠ (block356S4 : ℝ)) :
    0 < block356V y := by
  have hcert := block356RightChunk000Certificate_eq_true
  unfold block356RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block356RightChunk000) (lo := block356RightChunk000L) (hi := block356RightChunk000R)
    (w1 := block356W1) (w2 := block356W2) (w3 := block356W3) (w4 := block356W4)
    (s1 := block356S1) (s2 := block356S2) (s3 := block356S3) (s4 := block356S4)
    hboxes hcover block356RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block356_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block356RightL : ℝ) (block356RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block356S1 : ℝ))
    (hy2ne : y ≠ (block356S2 : ℝ))
    (hy3ne : y ≠ (block356S3 : ℝ))
    (hy4ne : y ≠ (block356S4 : ℝ)) :
    0 < block356V y := by
  have hL : (block356RightChunk000L : ℝ) = (block356RightL : ℝ) := by
    norm_num [block356RightChunk000L, block356RightL]
  have hR : (block356RightChunk000R : ℝ) = (block356RightR : ℝ) := by
    norm_num [block356RightChunk000R, block356RightR]
  have hyc : y ∈ Icc (block356RightChunk000L : ℝ) (block356RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block356_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block356_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block356LeftL : ℝ) (block356LeftR : ℝ) →
    y ≠ 0 → y ≠ (block356S1 : ℝ) → y ≠ (block356S2 : ℝ) →
    y ≠ (block356S3 : ℝ) → y ≠ (block356S4 : ℝ) → 0 < block356V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block356RightL : ℝ) (block356RightR : ℝ) →
    y ≠ 0 → y ≠ (block356S1 : ℝ) → y ≠ (block356S2 : ℝ) →
    y ≠ (block356S3 : ℝ) → y ≠ (block356S4 : ℝ) → 0 < block356V y)

theorem block356_reallog_certificate_proof :
    block356_reallog_certificate := by
  exact ⟨block356_left_V_pos, block356_right_V_pos⟩

end Block356
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block356.block356V
#check Erdos1038Lean.M1817475.Block356.block356_left_V_pos
#check Erdos1038Lean.M1817475.Block356.block356_right_V_pos
#check Erdos1038Lean.M1817475.Block356.block356_reallog_certificate_proof
