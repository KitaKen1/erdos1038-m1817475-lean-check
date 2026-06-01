/-
Self-contained Lean4Web paste file.
Block 92 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block092

def block092LeftL : Rat := ((39964716517857142897 : Rat) / 50000000000000000000)
def block092LeftR : Rat := ((9993622767857142867 : Rat) / 12500000000000000000)
def block092RightL : Rat := ((89964716517857142897 : Rat) / 50000000000000000000)
def block092RightR : Rat := ((34993622767857142867 : Rat) / 12500000000000000000)

def block092LeftBoxes : List RatBox := [
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((39964716517857142897 : Rat) / 50000000000000000000), R := ((15987841517857142873 : Rat) / 20000000000000000000), D0 := ((15987841517857142873 : Rat) / 20000000000000000000), D1 := ((50909038482142857103 : Rat) / 50000000000000000000), D2 := ((87932033482142857103 : Rat) / 50000000000000000000), D3 := ((93786057232142857103 : Rat) / 50000000000000000000), D4 := ((49634793392857140337 : Rat) / 25000000000000000000), LB := ((2687461992068041 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((15987841517857142873 : Rat) / 20000000000000000000), R := ((9993622767857142867 : Rat) / 12500000000000000000), D0 := ((9993622767857142867 : Rat) / 12500000000000000000), D1 := ((20361660482142857127 : Rat) / 20000000000000000000), D2 := ((35170858482142857127 : Rat) / 20000000000000000000), D3 := ((37512467982142857127 : Rat) / 20000000000000000000), D4 := ((198529399017857132777 : Rat) / 100000000000000000000), LB := ((3545150776178563 : Rat) / 10000000000000000000) }
]

def block092LeftCertificate : Bool :=
  allBoxesValid block092LeftBoxes &&
  coversFromBool block092LeftBoxes block092LeftL block092LeftR

theorem block092LeftCertificate_eq_true :
    block092LeftCertificate = true := by
  native_decide

def block092RightChunk000 : List RatBox := [
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((89964716517857142897 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((909038482142857103 : Rat) / 50000000000000000000), D2 := ((37932033482142857103 : Rat) / 50000000000000000000), D3 := ((43786057232142857103 : Rat) / 50000000000000000000), D4 := ((24634793392857140337 : Rat) / 25000000000000000000), LB := ((14351134344438373 : Rat) / 1000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((48360548303571423571 : Rat) / 50000000000000000000), LB := ((1181509298426703 : Rat) / 6250000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((511587 : Rat) / 200000), R := ((209318019 : Rat) / 80000000), D0 := ((209318019 : Rat) / 80000000), D1 := ((63920011 : Rat) / 80000000), D2 := ((4683219 : Rat) / 80000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((11337553303571423571 : Rat) / 50000000000000000000), LB := ((21387039197715813 : Rat) / 100000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((209318019 : Rat) / 80000000), R := ((423319257 : Rat) / 160000000), D0 := ((423319257 : Rat) / 160000000), D1 := ((132523241 : Rat) / 160000000), D2 := ((14049657 : Rat) / 160000000), D3 := ((4683219 : Rat) / 80000000), D4 := ((8410541428571423571 : Rat) / 50000000000000000000), LB := ((21368522488967 : Rat) / 156250000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((423319257 : Rat) / 160000000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 160000000), D4 := ((6947035491071423571 : Rat) / 50000000000000000000), LB := ((79781552054639 : Rat) / 2000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((107000619 : Rat) / 40000000), R := ((1075489719553571423571 : Rat) / 400000000000000000000), D0 := ((1075489719553571423571 : Rat) / 400000000000000000000), D1 := ((348499679553571423571 : Rat) / 400000000000000000000), D2 := ((52315719553571423571 : Rat) / 400000000000000000000), D3 := ((5483529553571423571 : Rat) / 400000000000000000000), D4 := ((5483529553571423571 : Rat) / 50000000000000000000), LB := ((2964966455596807 : Rat) / 100000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((1075489719553571423571 : Rat) / 400000000000000000000), R := ((2156462968660714270713 : Rat) / 800000000000000000000), D0 := ((2156462968660714270713 : Rat) / 800000000000000000000), D1 := ((702482888660714270713 : Rat) / 800000000000000000000), D2 := ((110114968660714270713 : Rat) / 800000000000000000000), D3 := ((16450588660714270713 : Rat) / 800000000000000000000), D4 := ((38384706874999964997 : Rat) / 400000000000000000000), LB := ((7092208647571957 : Rat) / 250000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((2156462968660714270713 : Rat) / 800000000000000000000), R := ((540486624553571423571 : Rat) / 200000000000000000000), D0 := ((540486624553571423571 : Rat) / 200000000000000000000), D1 := ((176991604553571423571 : Rat) / 200000000000000000000), D2 := ((28899624553571423571 : Rat) / 200000000000000000000), D3 := ((5483529553571423571 : Rat) / 200000000000000000000), D4 := ((71285884196428506423 : Rat) / 800000000000000000000), LB := ((6876388442307091 : Rat) / 500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((540486624553571423571 : Rat) / 200000000000000000000), R := ((433486005553571423571 : Rat) / 160000000000000000000), D0 := ((433486005553571423571 : Rat) / 160000000000000000000), D1 := ((142689989553571423571 : Rat) / 160000000000000000000), D2 := ((24216405553571423571 : Rat) / 160000000000000000000), D3 := ((5483529553571423571 : Rat) / 160000000000000000000), D4 := ((16450588660714270713 : Rat) / 200000000000000000000), LB := ((7220526078363099 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((433486005553571423571 : Rat) / 160000000000000000000), R := ((4340343585089285659281 : Rat) / 1600000000000000000000), D0 := ((4340343585089285659281 : Rat) / 1600000000000000000000), D1 := ((1432383425089285659281 : Rat) / 1600000000000000000000), D2 := ((247647585089285659281 : Rat) / 1600000000000000000000), D3 := ((60318825089285659281 : Rat) / 1600000000000000000000), D4 := ((60318825089285659281 : Rat) / 800000000000000000000), LB := ((2510891064572973 : Rat) / 500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((4340343585089285659281 : Rat) / 1600000000000000000000), R := ((1086456778660714270713 : Rat) / 400000000000000000000), D0 := ((1086456778660714270713 : Rat) / 400000000000000000000), D1 := ((359466738660714270713 : Rat) / 400000000000000000000), D2 := ((63282778660714270713 : Rat) / 400000000000000000000), D3 := ((16450588660714270713 : Rat) / 400000000000000000000), D4 := ((115154120624999894991 : Rat) / 1600000000000000000000), LB := ((13183144412209913 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((1086456778660714270713 : Rat) / 400000000000000000000), R := ((347885510353571423571 : Rat) / 128000000000000000000), D0 := ((347885510353571423571 : Rat) / 128000000000000000000), D1 := ((115248697553571423571 : Rat) / 128000000000000000000), D2 := ((20469830353571423571 : Rat) / 128000000000000000000), D3 := ((5483529553571423571 : Rat) / 128000000000000000000), D4 := ((5483529553571423571 : Rat) / 80000000000000000000), LB := ((17687305749721771 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((347885510353571423571 : Rat) / 128000000000000000000), R := ((4351310644196428506423 : Rat) / 1600000000000000000000), D0 := ((4351310644196428506423 : Rat) / 1600000000000000000000), D1 := ((1443350484196428506423 : Rat) / 1600000000000000000000), D2 := ((258614644196428506423 : Rat) / 1600000000000000000000), D3 := ((71285884196428506423 : Rat) / 1600000000000000000000), D4 := ((213857652589285519269 : Rat) / 3200000000000000000000), LB := ((15972403774222599 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((4351310644196428506423 : Rat) / 1600000000000000000000), R := ((17410726106339285449263 : Rat) / 6400000000000000000000), D0 := ((17410726106339285449263 : Rat) / 6400000000000000000000), D1 := ((5778885466339285449263 : Rat) / 6400000000000000000000), D2 := ((1039942106339285449263 : Rat) / 6400000000000000000000), D3 := ((290627066339285449263 : Rat) / 6400000000000000000000), D4 := ((104187061517857047849 : Rat) / 1600000000000000000000), LB := ((1469232686886901 : Rat) / 400000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17410726106339285449263 : Rat) / 6400000000000000000000), R := ((8708104817946428436417 : Rat) / 3200000000000000000000), D0 := ((8708104817946428436417 : Rat) / 3200000000000000000000), D1 := ((2892184497946428436417 : Rat) / 3200000000000000000000), D2 := ((522712817946428436417 : Rat) / 3200000000000000000000), D3 := ((148055297946428436417 : Rat) / 3200000000000000000000), D4 := ((16450588660714270713 : Rat) / 256000000000000000000), LB := ((2845509976701077 : Rat) / 1000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((8708104817946428436417 : Rat) / 3200000000000000000000), R := ((3484338633089285659281 : Rat) / 1280000000000000000000), D0 := ((3484338633089285659281 : Rat) / 1280000000000000000000), D1 := ((1157970505089285659281 : Rat) / 1280000000000000000000), D2 := ((210181833089285659281 : Rat) / 1280000000000000000000), D3 := ((60318825089285659281 : Rat) / 1280000000000000000000), D4 := ((202890593482142672127 : Rat) / 3200000000000000000000), LB := ((20619869301077287 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((3484338633089285659281 : Rat) / 1280000000000000000000), R := ((2178397086874999964997 : Rat) / 800000000000000000000), D0 := ((2178397086874999964997 : Rat) / 800000000000000000000), D1 := ((724417006874999964997 : Rat) / 800000000000000000000), D2 := ((132049086874999964997 : Rat) / 800000000000000000000), D3 := ((38384706874999964997 : Rat) / 800000000000000000000), D4 := ((400297657410713920683 : Rat) / 6400000000000000000000), LB := ((661805463500531 : Rat) / 500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((2178397086874999964997 : Rat) / 800000000000000000000), R := ((17432660224553571143547 : Rat) / 6400000000000000000000), D0 := ((17432660224553571143547 : Rat) / 6400000000000000000000), D1 := ((5800819584553571143547 : Rat) / 6400000000000000000000), D2 := ((1061876224553571143547 : Rat) / 6400000000000000000000), D3 := ((312561184553571143547 : Rat) / 6400000000000000000000), D4 := ((49351765982142812139 : Rat) / 800000000000000000000), LB := ((126305210391231 : Rat) / 200000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17432660224553571143547 : Rat) / 6400000000000000000000), R := ((6974160795732142742133 : Rat) / 2560000000000000000000), D0 := ((6974160795732142742133 : Rat) / 2560000000000000000000), D1 := ((2321424539732142742133 : Rat) / 2560000000000000000000), D2 := ((425847195732142742133 : Rat) / 2560000000000000000000), D3 := ((126121179732142742133 : Rat) / 2560000000000000000000), D4 := ((389330598303571073541 : Rat) / 6400000000000000000000), LB := ((238203692493541 : Rat) / 125000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((6974160795732142742133 : Rat) / 2560000000000000000000), R := ((8719071877053571283559 : Rat) / 3200000000000000000000), D0 := ((8719071877053571283559 : Rat) / 3200000000000000000000), D1 := ((2903151557053571283559 : Rat) / 3200000000000000000000), D2 := ((533679877053571283559 : Rat) / 3200000000000000000000), D3 := ((159022357053571283559 : Rat) / 3200000000000000000000), D4 := ((773177667053570723511 : Rat) / 12800000000000000000000), LB := ((16006653661925219 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((8719071877053571283559 : Rat) / 3200000000000000000000), R := ((34881771037767856557807 : Rat) / 12800000000000000000000), D0 := ((34881771037767856557807 : Rat) / 12800000000000000000000), D1 := ((11618089757767856557807 : Rat) / 12800000000000000000000), D2 := ((2140203037767856557807 : Rat) / 12800000000000000000000), D3 := ((641572957767856557807 : Rat) / 12800000000000000000000), D4 := ((38384706874999964997 : Rat) / 640000000000000000000), LB := ((2616086568775211 : Rat) / 2000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34881771037767856557807 : Rat) / 12800000000000000000000), R := ((17443627283660713990689 : Rat) / 6400000000000000000000), D0 := ((17443627283660713990689 : Rat) / 6400000000000000000000), D1 := ((5811786643660713990689 : Rat) / 6400000000000000000000), D2 := ((1072843283660713990689 : Rat) / 6400000000000000000000), D3 := ((323528243660713990689 : Rat) / 6400000000000000000000), D4 := ((762210607946427876369 : Rat) / 12800000000000000000000), LB := ((411170869988009 : Rat) / 400000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17443627283660713990689 : Rat) / 6400000000000000000000), R := ((34892738096874999404949 : Rat) / 12800000000000000000000), D0 := ((34892738096874999404949 : Rat) / 12800000000000000000000), D1 := ((11629056816874999404949 : Rat) / 12800000000000000000000), D2 := ((2151170096874999404949 : Rat) / 12800000000000000000000), D3 := ((652540016874999404949 : Rat) / 12800000000000000000000), D4 := ((378363539196428226399 : Rat) / 6400000000000000000000), LB := ((7604844864813609 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34892738096874999404949 : Rat) / 12800000000000000000000), R := ((872455540660714270713 : Rat) / 320000000000000000000), D0 := ((872455540660714270713 : Rat) / 320000000000000000000), D1 := ((290863508660714270713 : Rat) / 320000000000000000000), D2 := ((53916340660714270713 : Rat) / 320000000000000000000), D3 := ((16450588660714270713 : Rat) / 320000000000000000000), D4 := ((751243548839285029227 : Rat) / 12800000000000000000000), LB := ((2529431696627893 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((872455540660714270713 : Rat) / 320000000000000000000), R := ((34903705155982142252091 : Rat) / 12800000000000000000000), D0 := ((34903705155982142252091 : Rat) / 12800000000000000000000), D1 := ((11640023875982142252091 : Rat) / 12800000000000000000000), D2 := ((2162137155982142252091 : Rat) / 12800000000000000000000), D3 := ((663507075982142252091 : Rat) / 12800000000000000000000), D4 := ((93220002410714200707 : Rat) / 1600000000000000000000), LB := ((26430763334051033 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34903705155982142252091 : Rat) / 12800000000000000000000), R := ((17454594342767856837831 : Rat) / 6400000000000000000000), D0 := ((17454594342767856837831 : Rat) / 6400000000000000000000), D1 := ((5822753702767856837831 : Rat) / 6400000000000000000000), D2 := ((1083810342767856837831 : Rat) / 6400000000000000000000), D3 := ((334495302767856837831 : Rat) / 6400000000000000000000), D4 := ((148055297946428436417 : Rat) / 2560000000000000000000), LB := ((1122723729363867 : Rat) / 31250000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17454594342767856837831 : Rat) / 6400000000000000000000), R := ((13964772180124999754979 : Rat) / 5120000000000000000000), D0 := ((13964772180124999754979 : Rat) / 5120000000000000000000), D1 := ((4659299668124999754979 : Rat) / 5120000000000000000000), D2 := ((868144980124999754979 : Rat) / 5120000000000000000000), D3 := ((268692948124999754979 : Rat) / 5120000000000000000000), D4 := ((367396480089285379257 : Rat) / 6400000000000000000000), LB := ((388592506382901 : Rat) / 500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((13964772180124999754979 : Rat) / 5120000000000000000000), R := ((34914672215089285099233 : Rat) / 12800000000000000000000), D0 := ((34914672215089285099233 : Rat) / 12800000000000000000000), D1 := ((11650990935089285099233 : Rat) / 12800000000000000000000), D2 := ((2173104215089285099233 : Rat) / 12800000000000000000000), D3 := ((674474135089285099233 : Rat) / 12800000000000000000000), D4 := ((1464102390803570093457 : Rat) / 25600000000000000000000), LB := ((3372743664041833 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34914672215089285099233 : Rat) / 12800000000000000000000), R := ((69834827959732141622037 : Rat) / 25600000000000000000000), D0 := ((69834827959732141622037 : Rat) / 25600000000000000000000), D1 := ((23307465399732141622037 : Rat) / 25600000000000000000000), D2 := ((4351691959732141622037 : Rat) / 25600000000000000000000), D3 := ((1354431799732141622037 : Rat) / 25600000000000000000000), D4 := ((729309430624999334943 : Rat) / 12800000000000000000000), LB := ((5753282340505983 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69834827959732141622037 : Rat) / 25600000000000000000000), R := ((8730038936160714130701 : Rat) / 3200000000000000000000), D0 := ((8730038936160714130701 : Rat) / 3200000000000000000000), D1 := ((2914118616160714130701 : Rat) / 3200000000000000000000), D2 := ((544646936160714130701 : Rat) / 3200000000000000000000), D3 := ((169989416160714130701 : Rat) / 3200000000000000000000), D4 := ((290627066339285449263 : Rat) / 5120000000000000000000), LB := ((11988688679059889 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((8730038936160714130701 : Rat) / 3200000000000000000000), R := ((69845795018839284469179 : Rat) / 25600000000000000000000), D0 := ((69845795018839284469179 : Rat) / 25600000000000000000000), D1 := ((23318432458839284469179 : Rat) / 25600000000000000000000), D2 := ((4362659018839284469179 : Rat) / 25600000000000000000000), D3 := ((1365398858839284469179 : Rat) / 25600000000000000000000), D4 := ((180956475267856977843 : Rat) / 3200000000000000000000), LB := ((1936154882822283 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69845795018839284469179 : Rat) / 25600000000000000000000), R := ((279405114193571423571 : Rat) / 102400000000000000000), D0 := ((279405114193571423571 : Rat) / 102400000000000000000), D1 := ((93295663953571423571 : Rat) / 102400000000000000000), D2 := ((17472570193571423571 : Rat) / 102400000000000000000), D3 := ((5483529553571423571 : Rat) / 102400000000000000000), D4 := ((1442168272589284399173 : Rat) / 25600000000000000000000), LB := ((2984031045693003 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279405114193571423571 : Rat) / 102400000000000000000), R := ((69856762077946427316321 : Rat) / 25600000000000000000000), D0 := ((69856762077946427316321 : Rat) / 25600000000000000000000), D1 := ((23329399517946427316321 : Rat) / 25600000000000000000000), D2 := ((4373626077946427316321 : Rat) / 25600000000000000000000), D3 := ((1376365917946427316321 : Rat) / 25600000000000000000000), D4 := ((718342371517856487801 : Rat) / 12800000000000000000000), LB := ((10654439781121461 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69856762077946427316321 : Rat) / 25600000000000000000000), R := ((17465561401874999684973 : Rat) / 6400000000000000000000), D0 := ((17465561401874999684973 : Rat) / 6400000000000000000000), D1 := ((5833720761874999684973 : Rat) / 6400000000000000000000), D2 := ((1094777401874999684973 : Rat) / 6400000000000000000000), D3 := ((345462361874999684973 : Rat) / 6400000000000000000000), D4 := ((1431201213482141552031 : Rat) / 25600000000000000000000), LB := ((1641415007691549 : Rat) / 12500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17465561401874999684973 : Rat) / 6400000000000000000000), R := ((69867729137053570163463 : Rat) / 25600000000000000000000), D0 := ((69867729137053570163463 : Rat) / 25600000000000000000000), D1 := ((23340366577053570163463 : Rat) / 25600000000000000000000), D2 := ((4384593137053570163463 : Rat) / 25600000000000000000000), D3 := ((1387332977053570163463 : Rat) / 25600000000000000000000), D4 := ((71285884196428506423 : Rat) / 1280000000000000000000), LB := ((2655088064124067 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69867729137053570163463 : Rat) / 25600000000000000000000), R := ((139740941803660711750497 : Rat) / 51200000000000000000000), D0 := ((139740941803660711750497 : Rat) / 51200000000000000000000), D1 := ((46686216683660711750497 : Rat) / 51200000000000000000000), D2 := ((8774669803660711750497 : Rat) / 51200000000000000000000), D3 := ((2780149483660711750497 : Rat) / 51200000000000000000000), D4 := ((1420234154374998704889 : Rat) / 25600000000000000000000), LB := ((2278664845046241 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139740941803660711750497 : Rat) / 51200000000000000000000), R := ((34936606333303570793517 : Rat) / 12800000000000000000000), D0 := ((34936606333303570793517 : Rat) / 12800000000000000000000), D1 := ((11672925053303570793517 : Rat) / 12800000000000000000000), D2 := ((2195038333303570793517 : Rat) / 12800000000000000000000), D3 := ((696408253303570793517 : Rat) / 12800000000000000000000), D4 := ((2834984779196425986207 : Rat) / 51200000000000000000000), LB := ((1311636102316327 : Rat) / 3125000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34936606333303570793517 : Rat) / 12800000000000000000000), R := ((139751908862767854597639 : Rat) / 51200000000000000000000), D0 := ((139751908862767854597639 : Rat) / 51200000000000000000000), D1 := ((46697183742767854597639 : Rat) / 51200000000000000000000), D2 := ((8785636862767854597639 : Rat) / 51200000000000000000000), D3 := ((2791116542767854597639 : Rat) / 51200000000000000000000), D4 := ((707375312410713640659 : Rat) / 12800000000000000000000), LB := ((38462140939621303 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139751908862767854597639 : Rat) / 51200000000000000000000), R := ((13975739239232142602121 : Rat) / 5120000000000000000000), D0 := ((13975739239232142602121 : Rat) / 5120000000000000000000), D1 := ((4670266727232142602121 : Rat) / 5120000000000000000000), D2 := ((879112039232142602121 : Rat) / 5120000000000000000000), D3 := ((279660007232142602121 : Rat) / 5120000000000000000000), D4 := ((564803544017856627813 : Rat) / 10240000000000000000000), LB := ((1752149206047937 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((13975739239232142602121 : Rat) / 5120000000000000000000), R := ((139762875921874997444781 : Rat) / 51200000000000000000000), D0 := ((139762875921874997444781 : Rat) / 51200000000000000000000), D1 := ((46708150801874997444781 : Rat) / 51200000000000000000000), D2 := ((8796603921874997444781 : Rat) / 51200000000000000000000), D3 := ((2802083601874997444781 : Rat) / 51200000000000000000000), D4 := ((1409267095267855857747 : Rat) / 25600000000000000000000), LB := ((31715216975081173 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139762875921874997444781 : Rat) / 51200000000000000000000), R := ((272985077053571423571 : Rat) / 100000000000000000000), D0 := ((272985077053571423571 : Rat) / 100000000000000000000), D1 := ((91237567053571423571 : Rat) / 100000000000000000000), D2 := ((17191577053571423571 : Rat) / 100000000000000000000), D3 := ((5483529553571423571 : Rat) / 100000000000000000000), D4 := ((2813050660982140291923 : Rat) / 51200000000000000000000), LB := ((5695834721335391 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((272985077053571423571 : Rat) / 100000000000000000000), R := ((139773842980982140291923 : Rat) / 51200000000000000000000), D0 := ((139773842980982140291923 : Rat) / 51200000000000000000000), D1 := ((46719117860982140291923 : Rat) / 51200000000000000000000), D2 := ((8807570980982140291923 : Rat) / 51200000000000000000000), D3 := ((2813050660982140291923 : Rat) / 51200000000000000000000), D4 := ((5483529553571423571 : Rat) / 100000000000000000000), LB := ((1266759504195969 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139773842980982140291923 : Rat) / 51200000000000000000000), R := ((69889663255267855857747 : Rat) / 25600000000000000000000), D0 := ((69889663255267855857747 : Rat) / 25600000000000000000000), D1 := ((23362300695267855857747 : Rat) / 25600000000000000000000), D2 := ((4406527255267855857747 : Rat) / 25600000000000000000000), D3 := ((1409267095267855857747 : Rat) / 25600000000000000000000), D4 := ((2802083601874997444781 : Rat) / 51200000000000000000000), LB := ((4456720890750887 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69889663255267855857747 : Rat) / 25600000000000000000000), R := ((27956962008017856627813 : Rat) / 10240000000000000000000), D0 := ((27956962008017856627813 : Rat) / 10240000000000000000000), D1 := ((9346016984017856627813 : Rat) / 10240000000000000000000), D2 := ((1763707608017856627813 : Rat) / 10240000000000000000000), D3 := ((564803544017856627813 : Rat) / 10240000000000000000000), D4 := ((279660007232142602121 : Rat) / 5120000000000000000000), LB := ((386495135139997 : Rat) / 2000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((27956962008017856627813 : Rat) / 10240000000000000000000), R := ((34947573392410713640659 : Rat) / 12800000000000000000000), D0 := ((34947573392410713640659 : Rat) / 12800000000000000000000), D1 := ((11683892112410713640659 : Rat) / 12800000000000000000000), D2 := ((2206005392410713640659 : Rat) / 12800000000000000000000), D3 := ((707375312410713640659 : Rat) / 12800000000000000000000), D4 := ((2791116542767854597639 : Rat) / 51200000000000000000000), LB := ((8229494522282721 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34947573392410713640659 : Rat) / 12800000000000000000000), R := ((139795777099196425986207 : Rat) / 51200000000000000000000), D0 := ((139795777099196425986207 : Rat) / 51200000000000000000000), D1 := ((46741051979196425986207 : Rat) / 51200000000000000000000), D2 := ((8829505099196425986207 : Rat) / 51200000000000000000000), D3 := ((2834984779196425986207 : Rat) / 51200000000000000000000), D4 := ((696408253303570793517 : Rat) / 12800000000000000000000), LB := ((6843322696253873 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139795777099196425986207 : Rat) / 51200000000000000000000), R := ((69900630314374998704889 : Rat) / 25600000000000000000000), D0 := ((69900630314374998704889 : Rat) / 25600000000000000000000), D1 := ((23373267754374998704889 : Rat) / 25600000000000000000000), D2 := ((4417494314374998704889 : Rat) / 25600000000000000000000), D3 := ((1420234154374998704889 : Rat) / 25600000000000000000000), D4 := ((2780149483660711750497 : Rat) / 51200000000000000000000), LB := ((5504035959547071 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69900630314374998704889 : Rat) / 25600000000000000000000), R := ((139806744158303568833349 : Rat) / 51200000000000000000000), D0 := ((139806744158303568833349 : Rat) / 51200000000000000000000), D1 := ((46752019038303568833349 : Rat) / 51200000000000000000000), D2 := ((8840472158303568833349 : Rat) / 51200000000000000000000), D3 := ((2845951838303568833349 : Rat) / 51200000000000000000000), D4 := ((1387332977053570163463 : Rat) / 25600000000000000000000), LB := ((842361679980197 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139806744158303568833349 : Rat) / 51200000000000000000000), R := ((3495305692196428506423 : Rat) / 1280000000000000000000), D0 := ((3495305692196428506423 : Rat) / 1280000000000000000000), D1 := ((1168937564196428506423 : Rat) / 1280000000000000000000), D2 := ((221148892196428506423 : Rat) / 1280000000000000000000), D3 := ((71285884196428506423 : Rat) / 1280000000000000000000), D4 := ((553836484910713780671 : Rat) / 10240000000000000000000), LB := ((2966815142108059 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((3495305692196428506423 : Rat) / 1280000000000000000000), R := ((139817711217410711680491 : Rat) / 51200000000000000000000), D0 := ((139817711217410711680491 : Rat) / 51200000000000000000000), D1 := ((46762986097410711680491 : Rat) / 51200000000000000000000), D2 := ((8851439217410711680491 : Rat) / 51200000000000000000000), D3 := ((2856918897410711680491 : Rat) / 51200000000000000000000), D4 := ((345462361874999684973 : Rat) / 6400000000000000000000), LB := ((3538464712515843 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139817711217410711680491 : Rat) / 51200000000000000000000), R := ((69911597373482141552031 : Rat) / 25600000000000000000000), D0 := ((69911597373482141552031 : Rat) / 25600000000000000000000), D1 := ((23384234813482141552031 : Rat) / 25600000000000000000000), D2 := ((4428461373482141552031 : Rat) / 25600000000000000000000), D3 := ((1431201213482141552031 : Rat) / 25600000000000000000000), D4 := ((2758215365446426056213 : Rat) / 51200000000000000000000), LB := ((1548093164174813 : Rat) / 125000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69911597373482141552031 : Rat) / 25600000000000000000000), R := ((55930374604696427526339 : Rat) / 20480000000000000000000), D0 := ((55930374604696427526339 : Rat) / 20480000000000000000000), D1 := ((18708484556696427526339 : Rat) / 20480000000000000000000), D2 := ((3543865804696427526339 : Rat) / 20480000000000000000000), D3 := ((1146057676696427526339 : Rat) / 20480000000000000000000), D4 := ((1376365917946427316321 : Rat) / 25600000000000000000000), LB := ((11428162443732903 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((55930374604696427526339 : Rat) / 20480000000000000000000), R := ((139828678276517854527633 : Rat) / 51200000000000000000000), D0 := ((139828678276517854527633 : Rat) / 51200000000000000000000), D1 := ((46773953156517854527633 : Rat) / 51200000000000000000000), D2 := ((8862406276517854527633 : Rat) / 51200000000000000000000), D3 := ((2867885956517854527633 : Rat) / 51200000000000000000000), D4 := ((5499980142232137841713 : Rat) / 102400000000000000000000), LB := ((21788712404491317 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139828678276517854527633 : Rat) / 51200000000000000000000), R := ((279662840082589280478837 : Rat) / 102400000000000000000000), D0 := ((279662840082589280478837 : Rat) / 102400000000000000000000), D1 := ((93553389842589280478837 : Rat) / 102400000000000000000000), D2 := ((17730296082589280478837 : Rat) / 102400000000000000000000), D3 := ((5741255442589280478837 : Rat) / 102400000000000000000000), D4 := ((2747248306339283209071 : Rat) / 51200000000000000000000), LB := ((20745117748588449 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279662840082589280478837 : Rat) / 102400000000000000000000), R := ((34958540451517856487801 : Rat) / 12800000000000000000000), D0 := ((34958540451517856487801 : Rat) / 12800000000000000000000), D1 := ((11694859171517856487801 : Rat) / 12800000000000000000000), D2 := ((2216972451517856487801 : Rat) / 12800000000000000000000), D3 := ((718342371517856487801 : Rat) / 12800000000000000000000), D4 := ((5489013083124994994571 : Rat) / 102400000000000000000000), LB := ((19725586096019931 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34958540451517856487801 : Rat) / 12800000000000000000000), R := ((279673807141696423325979 : Rat) / 102400000000000000000000), D0 := ((279673807141696423325979 : Rat) / 102400000000000000000000), D1 := ((93564356901696423325979 : Rat) / 102400000000000000000000), D2 := ((17741263141696423325979 : Rat) / 102400000000000000000000), D3 := ((5752222501696423325979 : Rat) / 102400000000000000000000), D4 := ((5483529553571423571 : Rat) / 102400000000000000000), LB := ((14632939655361 : Rat) / 78125000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279673807141696423325979 : Rat) / 102400000000000000000000), R := ((5593585813424999894991 : Rat) / 2048000000000000000000), D0 := ((5593585813424999894991 : Rat) / 2048000000000000000000), D1 := ((1871396808624999894991 : Rat) / 2048000000000000000000), D2 := ((354934933424999894991 : Rat) / 2048000000000000000000), D3 := ((115154120624999894991 : Rat) / 2048000000000000000000), D4 := ((5478046024017852147429 : Rat) / 102400000000000000000000), LB := ((17758893185748637 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((5593585813424999894991 : Rat) / 2048000000000000000000), R := ((279684774200803566173121 : Rat) / 102400000000000000000000), D0 := ((279684774200803566173121 : Rat) / 102400000000000000000000), D1 := ((93575323960803566173121 : Rat) / 102400000000000000000000), D2 := ((17752230200803566173121 : Rat) / 102400000000000000000000), D3 := ((5763189560803566173121 : Rat) / 102400000000000000000000), D4 := ((2736281247232140361929 : Rat) / 51200000000000000000000), LB := ((16811822962503609 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279684774200803566173121 : Rat) / 102400000000000000000000), R := ((69922564432589284399173 : Rat) / 25600000000000000000000), D0 := ((69922564432589284399173 : Rat) / 25600000000000000000000), D1 := ((23395201872589284399173 : Rat) / 25600000000000000000000), D2 := ((4439428432589284399173 : Rat) / 25600000000000000000000), D3 := ((1442168272589284399173 : Rat) / 25600000000000000000000), D4 := ((5467078964910709300287 : Rat) / 102400000000000000000000), LB := ((3177799562463779 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69922564432589284399173 : Rat) / 25600000000000000000000), R := ((279695741259910709020263 : Rat) / 102400000000000000000000), D0 := ((279695741259910709020263 : Rat) / 102400000000000000000000), D1 := ((93586291019910709020263 : Rat) / 102400000000000000000000), D2 := ((17763197259910709020263 : Rat) / 102400000000000000000000), D3 := ((5774156619910709020263 : Rat) / 102400000000000000000000), D4 := ((1365398858839284469179 : Rat) / 25600000000000000000000), LB := ((14990463596620263 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279695741259910709020263 : Rat) / 102400000000000000000000), R := ((139850612394732140221917 : Rat) / 51200000000000000000000), D0 := ((139850612394732140221917 : Rat) / 51200000000000000000000), D1 := ((46795887274732140221917 : Rat) / 51200000000000000000000), D2 := ((8884340394732140221917 : Rat) / 51200000000000000000000), D3 := ((2889820074732140221917 : Rat) / 51200000000000000000000), D4 := ((1091222381160713290629 : Rat) / 20480000000000000000000), LB := ((882266644706281 : Rat) / 6250000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139850612394732140221917 : Rat) / 51200000000000000000000), R := ((55941341663803570373481 : Rat) / 20480000000000000000000), D0 := ((55941341663803570373481 : Rat) / 20480000000000000000000), D1 := ((18719451615803570373481 : Rat) / 20480000000000000000000), D2 := ((3554832863803570373481 : Rat) / 20480000000000000000000), D3 := ((1157024735803570373481 : Rat) / 20480000000000000000000), D4 := ((2725314188124997514787 : Rat) / 51200000000000000000000), LB := ((3316613026929649 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((55941341663803570373481 : Rat) / 20480000000000000000000), R := ((8741005995267856977843 : Rat) / 3200000000000000000000), D0 := ((8741005995267856977843 : Rat) / 3200000000000000000000), D1 := ((2925085675267856977843 : Rat) / 3200000000000000000000), D2 := ((555613995267856977843 : Rat) / 3200000000000000000000), D3 := ((180956475267856977843 : Rat) / 3200000000000000000000), D4 := ((5445144846696423606003 : Rat) / 102400000000000000000000), LB := ((1244106725325489 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((8741005995267856977843 : Rat) / 3200000000000000000000), R := ((279717675378124994714547 : Rat) / 102400000000000000000000), D0 := ((279717675378124994714547 : Rat) / 102400000000000000000000), D1 := ((93608225138124994714547 : Rat) / 102400000000000000000000), D2 := ((17785131378124994714547 : Rat) / 102400000000000000000000), D3 := ((5796090738124994714547 : Rat) / 102400000000000000000000), D4 := ((169989416160714130701 : Rat) / 3200000000000000000000), LB := ((11640158171166703 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279717675378124994714547 : Rat) / 102400000000000000000000), R := ((139861579453839283069059 : Rat) / 51200000000000000000000), D0 := ((139861579453839283069059 : Rat) / 51200000000000000000000), D1 := ((46806854333839283069059 : Rat) / 51200000000000000000000), D2 := ((8895307453839283069059 : Rat) / 51200000000000000000000), D3 := ((2900787133839283069059 : Rat) / 51200000000000000000000), D4 := ((5434177787589280758861 : Rat) / 102400000000000000000000), LB := ((434550856875493 : Rat) / 4000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139861579453839283069059 : Rat) / 51200000000000000000000), R := ((279728642437232137561689 : Rat) / 102400000000000000000000), D0 := ((279728642437232137561689 : Rat) / 102400000000000000000000), D1 := ((93619192197232137561689 : Rat) / 102400000000000000000000), D2 := ((17796098437232137561689 : Rat) / 102400000000000000000000), D3 := ((5807057797232137561689 : Rat) / 102400000000000000000000), D4 := ((542869425803570933529 : Rat) / 10240000000000000000000), LB := ((2022390741489577 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279728642437232137561689 : Rat) / 102400000000000000000000), R := ((13986706298339285449263 : Rat) / 5120000000000000000000), D0 := ((13986706298339285449263 : Rat) / 5120000000000000000000), D1 := ((4681233786339285449263 : Rat) / 5120000000000000000000), D2 := ((890079098339285449263 : Rat) / 5120000000000000000000), D3 := ((290627066339285449263 : Rat) / 5120000000000000000000), D4 := ((5423210728482137911719 : Rat) / 102400000000000000000000), LB := ((3665918699991 : Rat) / 39062500000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((13986706298339285449263 : Rat) / 5120000000000000000000), R := ((279739609496339280408831 : Rat) / 102400000000000000000000), D0 := ((279739609496339280408831 : Rat) / 102400000000000000000000), D1 := ((93630159256339280408831 : Rat) / 102400000000000000000000), D2 := ((17807065496339280408831 : Rat) / 102400000000000000000000), D3 := ((5818024856339280408831 : Rat) / 102400000000000000000000), D4 := ((1354431799732141622037 : Rat) / 25600000000000000000000), LB := ((8682212901944819 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279739609496339280408831 : Rat) / 102400000000000000000000), R := ((139872546512946425916201 : Rat) / 51200000000000000000000), D0 := ((139872546512946425916201 : Rat) / 51200000000000000000000), D1 := ((46817821392946425916201 : Rat) / 51200000000000000000000), D2 := ((8906274512946425916201 : Rat) / 51200000000000000000000), D3 := ((2911754192946425916201 : Rat) / 51200000000000000000000), D4 := ((5412243669374995064577 : Rat) / 102400000000000000000000), LB := ((4002191963625723 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139872546512946425916201 : Rat) / 51200000000000000000000), R := ((279750576555446423255973 : Rat) / 102400000000000000000000), D0 := ((279750576555446423255973 : Rat) / 102400000000000000000000), D1 := ((93641126315446423255973 : Rat) / 102400000000000000000000), D2 := ((17818032555446423255973 : Rat) / 102400000000000000000000), D3 := ((5828991915446423255973 : Rat) / 102400000000000000000000), D4 := ((2703380069910711820503 : Rat) / 51200000000000000000000), LB := ((3675656110918579 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279750576555446423255973 : Rat) / 102400000000000000000000), R := ((34969507510624999334943 : Rat) / 12800000000000000000000), D0 := ((34969507510624999334943 : Rat) / 12800000000000000000000), D1 := ((11705826230624999334943 : Rat) / 12800000000000000000000), D2 := ((2227939510624999334943 : Rat) / 12800000000000000000000), D3 := ((729309430624999334943 : Rat) / 12800000000000000000000), D4 := ((1080255322053570443487 : Rat) / 20480000000000000000000), LB := ((6723045203749223 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34969507510624999334943 : Rat) / 12800000000000000000000), R := ((55952308722910713220623 : Rat) / 20480000000000000000000), D0 := ((55952308722910713220623 : Rat) / 20480000000000000000000), D1 := ((18730418674910713220623 : Rat) / 20480000000000000000000), D2 := ((3565799922910713220623 : Rat) / 20480000000000000000000), D3 := ((1167991794910713220623 : Rat) / 20480000000000000000000), D4 := ((674474135089285099233 : Rat) / 12800000000000000000000), LB := ((6119630435885703 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((55952308722910713220623 : Rat) / 20480000000000000000000), R := ((139883513572053568763343 : Rat) / 51200000000000000000000), D0 := ((139883513572053568763343 : Rat) / 51200000000000000000000), D1 := ((46828788452053568763343 : Rat) / 51200000000000000000000), D2 := ((8917241572053568763343 : Rat) / 51200000000000000000000), D3 := ((2922721252053568763343 : Rat) / 51200000000000000000000), D4 := ((5390309551160709370293 : Rat) / 102400000000000000000000), LB := ((5541115627061277 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139883513572053568763343 : Rat) / 51200000000000000000000), R := ((279772510673660708950257 : Rat) / 102400000000000000000000), D0 := ((279772510673660708950257 : Rat) / 102400000000000000000000), D1 := ((93663060433660708950257 : Rat) / 102400000000000000000000), D2 := ((17839966673660708950257 : Rat) / 102400000000000000000000), D3 := ((5850926033660708950257 : Rat) / 102400000000000000000000), D4 := ((2692413010803568973361 : Rat) / 51200000000000000000000), LB := ((2493774316036923 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279772510673660708950257 : Rat) / 102400000000000000000000), R := ((69944498550803570093457 : Rat) / 25600000000000000000000), D0 := ((69944498550803570093457 : Rat) / 25600000000000000000000), D1 := ((23417135990803570093457 : Rat) / 25600000000000000000000), D2 := ((4461362550803570093457 : Rat) / 25600000000000000000000), D3 := ((1464102390803570093457 : Rat) / 25600000000000000000000), D4 := ((5379342492053566523151 : Rat) / 102400000000000000000000), LB := ((891795490507441 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69944498550803570093457 : Rat) / 25600000000000000000000), R := ((279783477732767851797399 : Rat) / 102400000000000000000000), D0 := ((279783477732767851797399 : Rat) / 102400000000000000000000), D1 := ((93674027492767851797399 : Rat) / 102400000000000000000000), D2 := ((17850933732767851797399 : Rat) / 102400000000000000000000), D3 := ((5861893092767851797399 : Rat) / 102400000000000000000000), D4 := ((268692948124999754979 : Rat) / 5120000000000000000000), LB := ((3955450237413949 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279783477732767851797399 : Rat) / 102400000000000000000000), R := ((27978896126232142322097 : Rat) / 10240000000000000000000), D0 := ((27978896126232142322097 : Rat) / 10240000000000000000000), D1 := ((9367951102232142322097 : Rat) / 10240000000000000000000), D2 := ((1785641726232142322097 : Rat) / 10240000000000000000000), D3 := ((586737662232142322097 : Rat) / 10240000000000000000000), D4 := ((5368375432946423676009 : Rat) / 102400000000000000000000), LB := ((3477015283537277 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((27978896126232142322097 : Rat) / 10240000000000000000000), R := ((279794444791874994644541 : Rat) / 102400000000000000000000), D0 := ((279794444791874994644541 : Rat) / 102400000000000000000000), D1 := ((93684994551874994644541 : Rat) / 102400000000000000000000), D2 := ((17861900791874994644541 : Rat) / 102400000000000000000000), D3 := ((5872860151874994644541 : Rat) / 102400000000000000000000), D4 := ((2681445951696426126219 : Rat) / 51200000000000000000000), LB := ((15118605182495859 : Rat) / 500000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279794444791874994644541 : Rat) / 102400000000000000000000), R := ((17487495520089285379257 : Rat) / 6400000000000000000000), D0 := ((17487495520089285379257 : Rat) / 6400000000000000000000), D1 := ((5855654880089285379257 : Rat) / 6400000000000000000000), D2 := ((1116711520089285379257 : Rat) / 6400000000000000000000), D3 := ((367396480089285379257 : Rat) / 6400000000000000000000), D4 := ((5357408373839280828867 : Rat) / 102400000000000000000000), LB := ((405565014169329 : Rat) / 15625000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17487495520089285379257 : Rat) / 6400000000000000000000), R := ((279805411850982137491683 : Rat) / 102400000000000000000000), D0 := ((279805411850982137491683 : Rat) / 102400000000000000000000), D1 := ((93695961610982137491683 : Rat) / 102400000000000000000000), D2 := ((17872867850982137491683 : Rat) / 102400000000000000000000), D3 := ((5883827210982137491683 : Rat) / 102400000000000000000000), D4 := ((334495302767856837831 : Rat) / 6400000000000000000000), LB := ((685234122142081 : Rat) / 31250000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279805411850982137491683 : Rat) / 102400000000000000000000), R := ((139905447690267854457627 : Rat) / 51200000000000000000000), D0 := ((139905447690267854457627 : Rat) / 51200000000000000000000), D1 := ((46850722570267854457627 : Rat) / 51200000000000000000000), D2 := ((8939175690267854457627 : Rat) / 51200000000000000000000), D3 := ((2944655370267854457627 : Rat) / 51200000000000000000000), D4 := ((213857652589285519269 : Rat) / 4096000000000000000000), LB := ((9075846157446943 : Rat) / 500000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139905447690267854457627 : Rat) / 51200000000000000000000), R := ((11192655156403571213553 : Rat) / 4096000000000000000000), D0 := ((11192655156403571213553 : Rat) / 4096000000000000000000), D1 := ((3748277146803571213553 : Rat) / 4096000000000000000000), D2 := ((715353396403571213553 : Rat) / 4096000000000000000000), D3 := ((235791770803571213553 : Rat) / 4096000000000000000000), D4 := ((2670478892589283279077 : Rat) / 51200000000000000000000), LB := ((7314626294774307 : Rat) / 500000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((11192655156403571213553 : Rat) / 4096000000000000000000), R := ((69955465609910712940599 : Rat) / 25600000000000000000000), D0 := ((69955465609910712940599 : Rat) / 25600000000000000000000), D1 := ((23428103049910712940599 : Rat) / 25600000000000000000000), D2 := ((4472329609910712940599 : Rat) / 25600000000000000000000), D3 := ((1475069449910712940599 : Rat) / 25600000000000000000000), D4 := ((5335474255624995134583 : Rat) / 102400000000000000000000), LB := ((90885317613143 : Rat) / 8000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69955465609910712940599 : Rat) / 25600000000000000000000), R := ((279827345969196423185967 : Rat) / 102400000000000000000000), D0 := ((279827345969196423185967 : Rat) / 102400000000000000000000), D1 := ((93717895729196423185967 : Rat) / 102400000000000000000000), D2 := ((17894801969196423185967 : Rat) / 102400000000000000000000), D3 := ((5905761329196423185967 : Rat) / 102400000000000000000000), D4 := ((1332497681517855927753 : Rat) / 25600000000000000000000), LB := ((130412846065589 : Rat) / 15625000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279827345969196423185967 : Rat) / 102400000000000000000000), R := ((139916414749374997304769 : Rat) / 51200000000000000000000), D0 := ((139916414749374997304769 : Rat) / 51200000000000000000000), D1 := ((46861689629374997304769 : Rat) / 51200000000000000000000), D2 := ((8950142749374997304769 : Rat) / 51200000000000000000000), D3 := ((2955622429374997304769 : Rat) / 51200000000000000000000), D4 := ((5324507196517852287441 : Rat) / 102400000000000000000000), LB := ((5587019959785167 : Rat) / 1000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139916414749374997304769 : Rat) / 51200000000000000000000), R := ((279838313028303566033109 : Rat) / 102400000000000000000000), D0 := ((279838313028303566033109 : Rat) / 102400000000000000000000), D1 := ((93728862788303566033109 : Rat) / 102400000000000000000000), D2 := ((17905769028303566033109 : Rat) / 102400000000000000000000), D3 := ((5916728388303566033109 : Rat) / 102400000000000000000000), D4 := ((531902366696428086387 : Rat) / 10240000000000000000000), LB := ((30829546957544807 : Rat) / 10000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279838313028303566033109 : Rat) / 102400000000000000000000), R := ((6996094913946428436417 : Rat) / 2560000000000000000000), D0 := ((6996094913946428436417 : Rat) / 2560000000000000000000), D1 := ((2343358657946428436417 : Rat) / 2560000000000000000000), D2 := ((447781313946428436417 : Rat) / 2560000000000000000000), D3 := ((148055297946428436417 : Rat) / 2560000000000000000000), D4 := ((5313540137410709440299 : Rat) / 102400000000000000000000), LB := ((4173622289993517 : Rat) / 5000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((6996094913946428436417 : Rat) / 2560000000000000000000), R := ((559693076645267846336931 : Rat) / 204800000000000000000000), D0 := ((559693076645267846336931 : Rat) / 204800000000000000000000), D1 := ((187474176165267846336931 : Rat) / 204800000000000000000000), D2 := ((35827988645267846336931 : Rat) / 204800000000000000000000), D3 := ((11849907365267846336931 : Rat) / 204800000000000000000000), D4 := ((663507075982142252091 : Rat) / 12800000000000000000000), LB := ((1177222013444279 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559693076645267846336931 : Rat) / 204800000000000000000000), R := ((279849280087410708880251 : Rat) / 102400000000000000000000), D0 := ((279849280087410708880251 : Rat) / 102400000000000000000000), D1 := ((93739829847410708880251 : Rat) / 102400000000000000000000), D2 := ((17916736087410708880251 : Rat) / 102400000000000000000000), D3 := ((5927695447410708880251 : Rat) / 102400000000000000000000), D4 := ((2122125937232140921977 : Rat) / 40960000000000000000000), LB := ((2336384983794293 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279849280087410708880251 : Rat) / 102400000000000000000000), R := ((559704043704374989184073 : Rat) / 204800000000000000000000), D0 := ((559704043704374989184073 : Rat) / 204800000000000000000000), D1 := ((187485143224374989184073 : Rat) / 204800000000000000000000), D2 := ((35838955704374989184073 : Rat) / 204800000000000000000000), D3 := ((11860874424374989184073 : Rat) / 204800000000000000000000), D4 := ((5302573078303566593157 : Rat) / 102400000000000000000000), LB := ((115980568966223 : Rat) / 1000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559704043704374989184073 : Rat) / 204800000000000000000000), R := ((139927381808482140151911 : Rat) / 51200000000000000000000), D0 := ((139927381808482140151911 : Rat) / 51200000000000000000000), D1 := ((46872656688482140151911 : Rat) / 51200000000000000000000), D2 := ((8961109808482140151911 : Rat) / 51200000000000000000000), D3 := ((2966589488482140151911 : Rat) / 51200000000000000000000), D4 := ((10599662627053561762743 : Rat) / 204800000000000000000000), LB := ((11520622356897547 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139927381808482140151911 : Rat) / 51200000000000000000000), R := ((111943002152696426406243 : Rat) / 40960000000000000000000), D0 := ((111943002152696426406243 : Rat) / 40960000000000000000000), D1 := ((37499222056696426406243 : Rat) / 40960000000000000000000), D2 := ((7169984552696426406243 : Rat) / 40960000000000000000000), D3 := ((2374368296696426406243 : Rat) / 40960000000000000000000), D4 := ((2648544774374997584793 : Rat) / 51200000000000000000000), LB := ((11449627599147139 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((111943002152696426406243 : Rat) / 40960000000000000000000), R := ((279860247146517851727393 : Rat) / 102400000000000000000000), D0 := ((279860247146517851727393 : Rat) / 102400000000000000000000), D1 := ((93750796906517851727393 : Rat) / 102400000000000000000000), D2 := ((17927703146517851727393 : Rat) / 102400000000000000000000), D3 := ((5938662506517851727393 : Rat) / 102400000000000000000000), D4 := ((10588695567946418915601 : Rat) / 204800000000000000000000), LB := ((1423134866522513 : Rat) / 12500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279860247146517851727393 : Rat) / 102400000000000000000000), R := ((559725977822589274878357 : Rat) / 204800000000000000000000), D0 := ((559725977822589274878357 : Rat) / 204800000000000000000000), D1 := ((187507077342589274878357 : Rat) / 204800000000000000000000), D2 := ((35860889822589274878357 : Rat) / 204800000000000000000000), D3 := ((11882808542589274878357 : Rat) / 204800000000000000000000), D4 := ((1058321203839284749203 : Rat) / 20480000000000000000000), LB := ((11326982674908503 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559725977822589274878357 : Rat) / 204800000000000000000000), R := ((69966432669017855787741 : Rat) / 25600000000000000000000), D0 := ((69966432669017855787741 : Rat) / 25600000000000000000000), D1 := ((23439070109017855787741 : Rat) / 25600000000000000000000), D2 := ((4483296669017855787741 : Rat) / 25600000000000000000000), D3 := ((1486036509017855787741 : Rat) / 25600000000000000000000), D4 := ((10577728508839276068459 : Rat) / 204800000000000000000000), LB := ((225506903129169 : Rat) / 2000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69966432669017855787741 : Rat) / 25600000000000000000000), R := ((559736944881696417725499 : Rat) / 204800000000000000000000), D0 := ((559736944881696417725499 : Rat) / 204800000000000000000000), D1 := ((187518044401696417725499 : Rat) / 204800000000000000000000), D2 := ((35871856881696417725499 : Rat) / 204800000000000000000000), D3 := ((11893775601696417725499 : Rat) / 204800000000000000000000), D4 := ((1321530622410713080611 : Rat) / 25600000000000000000000), LB := ((1123017271499327 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559736944881696417725499 : Rat) / 204800000000000000000000), R := ((55974242841124998914907 : Rat) / 20480000000000000000000), D0 := ((55974242841124998914907 : Rat) / 20480000000000000000000), D1 := ((18752352793124998914907 : Rat) / 20480000000000000000000), D2 := ((3587734041124998914907 : Rat) / 20480000000000000000000), D3 := ((1189925913124998914907 : Rat) / 20480000000000000000000), D4 := ((10566761449732133221317 : Rat) / 204800000000000000000000), LB := ((1119147169922341 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((55974242841124998914907 : Rat) / 20480000000000000000000), R := ((559747911940803560572641 : Rat) / 204800000000000000000000), D0 := ((559747911940803560572641 : Rat) / 204800000000000000000000), D1 := ((187529011460803560572641 : Rat) / 204800000000000000000000), D2 := ((35882823940803560572641 : Rat) / 204800000000000000000000), D3 := ((11904742660803560572641 : Rat) / 204800000000000000000000), D4 := ((5280638960089280898873 : Rat) / 102400000000000000000000), LB := ((11159248467629279 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559747911940803560572641 : Rat) / 204800000000000000000000), R := ((139938348867589282999053 : Rat) / 51200000000000000000000), D0 := ((139938348867589282999053 : Rat) / 51200000000000000000000), D1 := ((46883623747589282999053 : Rat) / 51200000000000000000000), D2 := ((8972076867589282999053 : Rat) / 51200000000000000000000), D3 := ((2977556547589282999053 : Rat) / 51200000000000000000000), D4 := ((422231775624999614967 : Rat) / 8192000000000000000000), LB := ((2226701877687809 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139938348867589282999053 : Rat) / 51200000000000000000000), R := ((559758878999910703419783 : Rat) / 204800000000000000000000), D0 := ((559758878999910703419783 : Rat) / 204800000000000000000000), D1 := ((187539978519910703419783 : Rat) / 204800000000000000000000), D2 := ((35893790999910703419783 : Rat) / 204800000000000000000000), D3 := ((11915709719910703419783 : Rat) / 204800000000000000000000), D4 := ((2637577715267854737651 : Rat) / 51200000000000000000000), LB := ((1389282605028519 : Rat) / 12500000000000000000) }
]

def block092RightChunk000L : Rat := ((89964716517857142897 : Rat) / 50000000000000000000)
def block092RightChunk000R : Rat := ((559758878999910703419783 : Rat) / 204800000000000000000000)

def block092RightChunk000Certificate : Bool :=
  allBoxesValid block092RightChunk000 &&
  coversFromBool block092RightChunk000 block092RightChunk000L block092RightChunk000R

theorem block092RightChunk000Certificate_eq_true :
    block092RightChunk000Certificate = true := by
  native_decide

def block092RightChunk001 : List RatBox := [
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559758878999910703419783 : Rat) / 204800000000000000000000), R := ((279882181264732137421677 : Rat) / 102400000000000000000000), D0 := ((279882181264732137421677 : Rat) / 102400000000000000000000), D1 := ((93772731024732137421677 : Rat) / 102400000000000000000000), D2 := ((17949637264732137421677 : Rat) / 102400000000000000000000), D3 := ((5960596624732137421677 : Rat) / 102400000000000000000000), D4 := ((10544827331517847527033 : Rat) / 204800000000000000000000), LB := ((5550754605543329 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279882181264732137421677 : Rat) / 102400000000000000000000), R := ((22390793842360713850677 : Rat) / 8192000000000000000000), D0 := ((22390793842360713850677 : Rat) / 8192000000000000000000), D1 := ((7502037823160713850677 : Rat) / 8192000000000000000000), D2 := ((1436190322360713850677 : Rat) / 8192000000000000000000), D3 := ((477067071160713850677 : Rat) / 8192000000000000000000), D4 := ((5269671900982138051731 : Rat) / 102400000000000000000000), LB := ((11095260899507409 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((22390793842360713850677 : Rat) / 8192000000000000000000), R := ((4373244762410714200707 : Rat) / 1600000000000000000000), D0 := ((4373244762410714200707 : Rat) / 1600000000000000000000), D1 := ((1465284602410714200707 : Rat) / 1600000000000000000000), D2 := ((280548762410714200707 : Rat) / 1600000000000000000000), D3 := ((93220002410714200707 : Rat) / 1600000000000000000000), D4 := ((10533860272410704679891 : Rat) / 204800000000000000000000), LB := ((2773880578429977 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((4373244762410714200707 : Rat) / 1600000000000000000000), R := ((559780813118124989114067 : Rat) / 204800000000000000000000), D0 := ((559780813118124989114067 : Rat) / 204800000000000000000000), D1 := ((187561912638124989114067 : Rat) / 204800000000000000000000), D2 := ((35915725118124989114067 : Rat) / 204800000000000000000000), D3 := ((11937643838124989114067 : Rat) / 204800000000000000000000), D4 := ((16450588660714270713 : Rat) / 320000000000000000000), LB := ((11102299872056687 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559780813118124989114067 : Rat) / 204800000000000000000000), R := ((279893148323839280268819 : Rat) / 102400000000000000000000), D0 := ((279893148323839280268819 : Rat) / 102400000000000000000000), D1 := ((93783698083839280268819 : Rat) / 102400000000000000000000), D2 := ((17960604323839280268819 : Rat) / 102400000000000000000000), D3 := ((5971563683839280268819 : Rat) / 102400000000000000000000), D4 := ((10522893213303561832749 : Rat) / 204800000000000000000000), LB := ((11115600003119841 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279893148323839280268819 : Rat) / 102400000000000000000000), R := ((559791780177232131961209 : Rat) / 204800000000000000000000), D0 := ((559791780177232131961209 : Rat) / 204800000000000000000000), D1 := ((187572879697232131961209 : Rat) / 204800000000000000000000), D2 := ((35926692177232131961209 : Rat) / 204800000000000000000000), D3 := ((11948610897232131961209 : Rat) / 204800000000000000000000), D4 := ((5258704841874995204589 : Rat) / 102400000000000000000000), LB := ((1113542914519261 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559791780177232131961209 : Rat) / 204800000000000000000000), R := ((27989863185339285169239 : Rat) / 10240000000000000000000), D0 := ((27989863185339285169239 : Rat) / 10240000000000000000000), D1 := ((9378918161339285169239 : Rat) / 10240000000000000000000), D2 := ((1796608785339285169239 : Rat) / 10240000000000000000000), D3 := ((597704721339285169239 : Rat) / 10240000000000000000000), D4 := ((10511926154196418985607 : Rat) / 204800000000000000000000), LB := ((11161793747194171 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((27989863185339285169239 : Rat) / 10240000000000000000000), R := ((559802747236339274808351 : Rat) / 204800000000000000000000), D0 := ((559802747236339274808351 : Rat) / 204800000000000000000000), D1 := ((187583846756339274808351 : Rat) / 204800000000000000000000), D2 := ((35937659236339274808351 : Rat) / 204800000000000000000000), D3 := ((11959577956339274808351 : Rat) / 204800000000000000000000), D4 := ((2626610656160711890509 : Rat) / 51200000000000000000000), LB := ((2238940053536087 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559802747236339274808351 : Rat) / 204800000000000000000000), R := ((279904115382946423115961 : Rat) / 102400000000000000000000), D0 := ((279904115382946423115961 : Rat) / 102400000000000000000000), D1 := ((93794665142946423115961 : Rat) / 102400000000000000000000), D2 := ((17971571382946423115961 : Rat) / 102400000000000000000000), D3 := ((5982530742946423115961 : Rat) / 102400000000000000000000), D4 := ((2100191819017855227693 : Rat) / 40960000000000000000000), LB := ((1123415517543247 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279904115382946423115961 : Rat) / 102400000000000000000000), R := ((559813714295446417655493 : Rat) / 204800000000000000000000), D0 := ((559813714295446417655493 : Rat) / 204800000000000000000000), D1 := ((187594813815446417655493 : Rat) / 204800000000000000000000), D2 := ((35948626295446417655493 : Rat) / 204800000000000000000000), D3 := ((11970545015446417655493 : Rat) / 204800000000000000000000), D4 := ((5247737782767852357447 : Rat) / 102400000000000000000000), LB := ((1410020618725083 : Rat) / 12500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559813714295446417655493 : Rat) / 204800000000000000000000), R := ((69977399728124998634883 : Rat) / 25600000000000000000000), D0 := ((69977399728124998634883 : Rat) / 25600000000000000000000), D1 := ((23450037168124998634883 : Rat) / 25600000000000000000000), D2 := ((4494263728124998634883 : Rat) / 25600000000000000000000), D3 := ((1497003568124998634883 : Rat) / 25600000000000000000000), D4 := ((10489992035982133291323 : Rat) / 204800000000000000000000), LB := ((11332736079849859 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69977399728124998634883 : Rat) / 25600000000000000000000), R := ((111964936270910712100527 : Rat) / 40960000000000000000000), D0 := ((111964936270910712100527 : Rat) / 40960000000000000000000), D1 := ((37521156174910712100527 : Rat) / 40960000000000000000000), D2 := ((7191918670910712100527 : Rat) / 40960000000000000000000), D3 := ((2396302414910712100527 : Rat) / 40960000000000000000000), D4 := ((1310563563303570233469 : Rat) / 25600000000000000000000), LB := ((2847968766300779 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((111964936270910712100527 : Rat) / 40960000000000000000000), R := ((279915082442053565963103 : Rat) / 102400000000000000000000), D0 := ((279915082442053565963103 : Rat) / 102400000000000000000000), D1 := ((93805632202053565963103 : Rat) / 102400000000000000000000), D2 := ((17982538442053565963103 : Rat) / 102400000000000000000000), D3 := ((5993497802053565963103 : Rat) / 102400000000000000000000), D4 := ((10479024976874990444181 : Rat) / 204800000000000000000000), LB := ((5728794207737753 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279915082442053565963103 : Rat) / 102400000000000000000000), R := ((559835648413660703349777 : Rat) / 204800000000000000000000), D0 := ((559835648413660703349777 : Rat) / 204800000000000000000000), D1 := ((187616747933660703349777 : Rat) / 204800000000000000000000), D2 := ((35970560413660703349777 : Rat) / 204800000000000000000000), D3 := ((11992479133660703349777 : Rat) / 204800000000000000000000), D4 := ((1047354144732141902061 : Rat) / 20480000000000000000000), LB := ((5764941325292483 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559835648413660703349777 : Rat) / 204800000000000000000000), R := ((139960282985803568693337 : Rat) / 51200000000000000000000), D0 := ((139960282985803568693337 : Rat) / 51200000000000000000000), D1 := ((46905557865803568693337 : Rat) / 51200000000000000000000), D2 := ((8994010985803568693337 : Rat) / 51200000000000000000000), D3 := ((2999490665803568693337 : Rat) / 51200000000000000000000), D4 := ((10468057917767847597039 : Rat) / 204800000000000000000000), LB := ((11608764300707897 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139960282985803568693337 : Rat) / 51200000000000000000000), R := ((559846615472767846196919 : Rat) / 204800000000000000000000), D0 := ((559846615472767846196919 : Rat) / 204800000000000000000000), D1 := ((187627714992767846196919 : Rat) / 204800000000000000000000), D2 := ((35981527472767846196919 : Rat) / 204800000000000000000000), D3 := ((12003446192767846196919 : Rat) / 204800000000000000000000), D4 := ((2615643597053569043367 : Rat) / 51200000000000000000000), LB := ((116942399064901 : Rat) / 1000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559846615472767846196919 : Rat) / 204800000000000000000000), R := ((55985209900232141762049 : Rat) / 20480000000000000000000), D0 := ((55985209900232141762049 : Rat) / 20480000000000000000000), D1 := ((18763319852232141762049 : Rat) / 20480000000000000000000), D2 := ((3598701100232141762049 : Rat) / 20480000000000000000000), D3 := ((1200892972232141762049 : Rat) / 20480000000000000000000), D4 := ((10457090858660704749897 : Rat) / 204800000000000000000000), LB := ((11786316018769227 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((55985209900232141762049 : Rat) / 20480000000000000000000), R := ((559857582531874989044061 : Rat) / 204800000000000000000000), D0 := ((559857582531874989044061 : Rat) / 204800000000000000000000), D1 := ((187638682051874989044061 : Rat) / 204800000000000000000000), D2 := ((35992494531874989044061 : Rat) / 204800000000000000000000), D3 := ((12014413251874989044061 : Rat) / 204800000000000000000000), D4 := ((5225803664553566663163 : Rat) / 102400000000000000000000), LB := ((475399967942991 : Rat) / 4000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((559857582531874989044061 : Rat) / 204800000000000000000000), R := ((34991441628839285029227 : Rat) / 12800000000000000000000), D0 := ((34991441628839285029227 : Rat) / 12800000000000000000000), D1 := ((11727760348839285029227 : Rat) / 12800000000000000000000), D2 := ((2249873628839285029227 : Rat) / 12800000000000000000000), D3 := ((751243548839285029227 : Rat) / 12800000000000000000000), D4 := ((2089224759910712380551 : Rat) / 40960000000000000000000), LB := ((1199029601753887 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((34991441628839285029227 : Rat) / 12800000000000000000000), R := ((279937016560267851657387 : Rat) / 102400000000000000000000), D0 := ((279937016560267851657387 : Rat) / 102400000000000000000000), D1 := ((93827566320267851657387 : Rat) / 102400000000000000000000), D2 := ((18004472560267851657387 : Rat) / 102400000000000000000000), D3 := ((6015431920267851657387 : Rat) / 102400000000000000000000), D4 := ((652540016874999404949 : Rat) / 12800000000000000000000), LB := ((5619577305993051 : Rat) / 2500000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279937016560267851657387 : Rat) / 102400000000000000000000), R := ((139971250044910711540479 : Rat) / 51200000000000000000000), D0 := ((139971250044910711540479 : Rat) / 51200000000000000000000), D1 := ((46916524924910711540479 : Rat) / 51200000000000000000000), D2 := ((9004978044910711540479 : Rat) / 51200000000000000000000), D3 := ((3010457724910711540479 : Rat) / 51200000000000000000000), D4 := ((5214836605446423816021 : Rat) / 102400000000000000000000), LB := ((1172900701507107 : Rat) / 250000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139971250044910711540479 : Rat) / 51200000000000000000000), R := ((279947983619374994504529 : Rat) / 102400000000000000000000), D0 := ((279947983619374994504529 : Rat) / 102400000000000000000000), D1 := ((93838533379374994504529 : Rat) / 102400000000000000000000), D2 := ((18015439619374994504529 : Rat) / 102400000000000000000000), D3 := ((6026398979374994504529 : Rat) / 102400000000000000000000), D4 := ((104187061517857047849 : Rat) / 2048000000000000000000), LB := ((14801950434240041 : Rat) / 2000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279947983619374994504529 : Rat) / 102400000000000000000000), R := ((2799534671489285659281 : Rat) / 1024000000000000000000), D0 := ((2799534671489285659281 : Rat) / 1024000000000000000000), D1 := ((938440169089285659281 : Rat) / 1024000000000000000000), D2 := ((180209231489285659281 : Rat) / 1024000000000000000000), D3 := ((60318825089285659281 : Rat) / 1024000000000000000000), D4 := ((5203869546339280968879 : Rat) / 102400000000000000000000), LB := ((1297059808863521 : Rat) / 125000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((2799534671489285659281 : Rat) / 1024000000000000000000), R := ((279958950678482137351671 : Rat) / 102400000000000000000000), D0 := ((279958950678482137351671 : Rat) / 102400000000000000000000), D1 := ((93849500438482137351671 : Rat) / 102400000000000000000000), D2 := ((18026406678482137351671 : Rat) / 102400000000000000000000), D3 := ((6037366038482137351671 : Rat) / 102400000000000000000000), D4 := ((1299596504196427386327 : Rat) / 25600000000000000000000), LB := ((6809322281919883 : Rat) / 500000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279958950678482137351671 : Rat) / 102400000000000000000000), R := ((139982217104017854387621 : Rat) / 51200000000000000000000), D0 := ((139982217104017854387621 : Rat) / 51200000000000000000000), D1 := ((46927491984017854387621 : Rat) / 51200000000000000000000), D2 := ((9015945104017854387621 : Rat) / 51200000000000000000000), D3 := ((3021424784017854387621 : Rat) / 51200000000000000000000), D4 := ((5192902487232138121737 : Rat) / 102400000000000000000000), LB := ((8564003590338931 : Rat) / 500000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139982217104017854387621 : Rat) / 51200000000000000000000), R := ((279969917737589280198813 : Rat) / 102400000000000000000000), D0 := ((279969917737589280198813 : Rat) / 102400000000000000000000), D1 := ((93860467497589280198813 : Rat) / 102400000000000000000000), D2 := ((18037373737589280198813 : Rat) / 102400000000000000000000), D3 := ((6048333097589280198813 : Rat) / 102400000000000000000000), D4 := ((2593709478839283349083 : Rat) / 51200000000000000000000), LB := ((4181020340587871 : Rat) / 200000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279969917737589280198813 : Rat) / 102400000000000000000000), R := ((17498462579196428226399 : Rat) / 6400000000000000000000), D0 := ((17498462579196428226399 : Rat) / 6400000000000000000000), D1 := ((5866621939196428226399 : Rat) / 6400000000000000000000), D2 := ((1127678579196428226399 : Rat) / 6400000000000000000000), D3 := ((378363539196428226399 : Rat) / 6400000000000000000000), D4 := ((1036387085624999054919 : Rat) / 20480000000000000000000), LB := ((24950465219664153 : Rat) / 1000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17498462579196428226399 : Rat) / 6400000000000000000000), R := ((55996176959339284609191 : Rat) / 20480000000000000000000), D0 := ((55996176959339284609191 : Rat) / 20480000000000000000000), D1 := ((18774286911339284609191 : Rat) / 20480000000000000000000), D2 := ((3609668159339284609191 : Rat) / 20480000000000000000000), D3 := ((1211860031339284609191 : Rat) / 20480000000000000000000), D4 := ((323528243660713990689 : Rat) / 6400000000000000000000), LB := ((2926463652608291 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((55996176959339284609191 : Rat) / 20480000000000000000000), R := ((139993184163124997234763 : Rat) / 51200000000000000000000), D0 := ((139993184163124997234763 : Rat) / 51200000000000000000000), D1 := ((46938459043124997234763 : Rat) / 51200000000000000000000), D2 := ((9026912163124997234763 : Rat) / 51200000000000000000000), D3 := ((3032391843124997234763 : Rat) / 51200000000000000000000), D4 := ((5170968369017852427453 : Rat) / 102400000000000000000000), LB := ((338481561379389 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139993184163124997234763 : Rat) / 51200000000000000000000), R := ((279991851855803565893097 : Rat) / 102400000000000000000000), D0 := ((279991851855803565893097 : Rat) / 102400000000000000000000), D1 := ((93882401615803565893097 : Rat) / 102400000000000000000000), D2 := ((18059307855803565893097 : Rat) / 102400000000000000000000), D3 := ((6070267215803565893097 : Rat) / 102400000000000000000000), D4 := ((2582742419732140501941 : Rat) / 51200000000000000000000), LB := ((4837695786935603 : Rat) / 125000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((279991851855803565893097 : Rat) / 102400000000000000000000), R := ((69999333846339284329167 : Rat) / 25600000000000000000000), D0 := ((69999333846339284329167 : Rat) / 25600000000000000000000), D1 := ((23471971286339284329167 : Rat) / 25600000000000000000000), D2 := ((4516197846339284329167 : Rat) / 25600000000000000000000), D3 := ((1518937686339284329167 : Rat) / 25600000000000000000000), D4 := ((5160001309910709580311 : Rat) / 102400000000000000000000), LB := ((8765082194939211 : Rat) / 200000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((69999333846339284329167 : Rat) / 25600000000000000000000), R := ((280002818914910708740239 : Rat) / 102400000000000000000000), D0 := ((280002818914910708740239 : Rat) / 102400000000000000000000), D1 := ((93893368674910708740239 : Rat) / 102400000000000000000000), D2 := ((18070274914910708740239 : Rat) / 102400000000000000000000), D3 := ((6081234274910708740239 : Rat) / 102400000000000000000000), D4 := ((257725889017856907837 : Rat) / 5120000000000000000000), LB := ((984404717765397 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280002818914910708740239 : Rat) / 102400000000000000000000), R := ((28000830244446428016381 : Rat) / 10240000000000000000000), D0 := ((28000830244446428016381 : Rat) / 10240000000000000000000), D1 := ((9389885220446428016381 : Rat) / 10240000000000000000000), D2 := ((1807575844446428016381 : Rat) / 10240000000000000000000), D3 := ((608671780446428016381 : Rat) / 10240000000000000000000), D4 := ((5149034250803566733169 : Rat) / 102400000000000000000000), LB := ((54886588497282673 : Rat) / 1000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((28000830244446428016381 : Rat) / 10240000000000000000000), R := ((280013785974017851587381 : Rat) / 102400000000000000000000), D0 := ((280013785974017851587381 : Rat) / 102400000000000000000000), D1 := ((93904335734017851587381 : Rat) / 102400000000000000000000), D2 := ((18081241974017851587381 : Rat) / 102400000000000000000000), D3 := ((6092201334017851587381 : Rat) / 102400000000000000000000), D4 := ((2571775360624997654799 : Rat) / 51200000000000000000000), LB := ((3041250900986947 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280013785974017851587381 : Rat) / 102400000000000000000000), R := ((35002408687946427876369 : Rat) / 12800000000000000000000), D0 := ((35002408687946427876369 : Rat) / 12800000000000000000000), D1 := ((11738727407946427876369 : Rat) / 12800000000000000000000), D2 := ((2260840687946427876369 : Rat) / 12800000000000000000000), D3 := ((762210607946427876369 : Rat) / 12800000000000000000000), D4 := ((5138067191696423886027 : Rat) / 102400000000000000000000), LB := ((6703607543390167 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((35002408687946427876369 : Rat) / 12800000000000000000000), R := ((280024753033124994434523 : Rat) / 102400000000000000000000), D0 := ((280024753033124994434523 : Rat) / 102400000000000000000000), D1 := ((93915302793124994434523 : Rat) / 102400000000000000000000), D2 := ((18092209033124994434523 : Rat) / 102400000000000000000000), D3 := ((6103168393124994434523 : Rat) / 102400000000000000000000), D4 := ((641572957767856557807 : Rat) / 12800000000000000000000), LB := ((147040626976791 : Rat) / 2000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280024753033124994434523 : Rat) / 102400000000000000000000), R := ((140015118281339282929047 : Rat) / 51200000000000000000000), D0 := ((140015118281339282929047 : Rat) / 51200000000000000000000), D1 := ((46960393161339282929047 : Rat) / 51200000000000000000000), D2 := ((9048846281339282929047 : Rat) / 51200000000000000000000), D3 := ((3054325961339282929047 : Rat) / 51200000000000000000000), D4 := ((1025420026517856207777 : Rat) / 20480000000000000000000), LB := ((8027828671375303 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140015118281339282929047 : Rat) / 51200000000000000000000), R := ((56007144018446427456333 : Rat) / 20480000000000000000000), D0 := ((56007144018446427456333 : Rat) / 20480000000000000000000), D1 := ((18785253970446427456333 : Rat) / 20480000000000000000000), D2 := ((3620635218446427456333 : Rat) / 20480000000000000000000), D3 := ((1222827090446427456333 : Rat) / 20480000000000000000000), D4 := ((2560808301517854807657 : Rat) / 51200000000000000000000), LB := ((2182763785421593 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((56007144018446427456333 : Rat) / 20480000000000000000000), R := ((70010300905446427176309 : Rat) / 25600000000000000000000), D0 := ((70010300905446427176309 : Rat) / 25600000000000000000000), D1 := ((23482938345446427176309 : Rat) / 25600000000000000000000), D2 := ((4527164905446427176309 : Rat) / 25600000000000000000000), D3 := ((1529904745446427176309 : Rat) / 25600000000000000000000), D4 := ((5116133073482138191743 : Rat) / 102400000000000000000000), LB := ((9461766570706409 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70010300905446427176309 : Rat) / 25600000000000000000000), R := ((280046687151339280128807 : Rat) / 102400000000000000000000), D0 := ((280046687151339280128807 : Rat) / 102400000000000000000000), D1 := ((93937236911339280128807 : Rat) / 102400000000000000000000), D2 := ((18114143151339280128807 : Rat) / 102400000000000000000000), D3 := ((6125102511339280128807 : Rat) / 102400000000000000000000), D4 := ((1277662385982141692043 : Rat) / 25600000000000000000000), LB := ((255500473723691 : Rat) / 2500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280046687151339280128807 : Rat) / 102400000000000000000000), R := ((140026085340446425776189 : Rat) / 51200000000000000000000), D0 := ((140026085340446425776189 : Rat) / 51200000000000000000000), D1 := ((46971360220446425776189 : Rat) / 51200000000000000000000), D2 := ((9059813340446425776189 : Rat) / 51200000000000000000000), D3 := ((3065293020446425776189 : Rat) / 51200000000000000000000), D4 := ((5105166014374995344601 : Rat) / 102400000000000000000000), LB := ((11005868447699907 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140026085340446425776189 : Rat) / 51200000000000000000000), R := ((280057654210446422975949 : Rat) / 102400000000000000000000), D0 := ((280057654210446422975949 : Rat) / 102400000000000000000000), D1 := ((93948203970446422975949 : Rat) / 102400000000000000000000), D2 := ((18125110210446422975949 : Rat) / 102400000000000000000000), D3 := ((6136069570446422975949 : Rat) / 102400000000000000000000), D4 := ((509968248482142392103 : Rat) / 10240000000000000000000), LB := ((1181937142004097 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280057654210446422975949 : Rat) / 102400000000000000000000), R := ((1750394610874999964997 : Rat) / 640000000000000000000), D0 := ((1750394610874999964997 : Rat) / 640000000000000000000), D1 := ((587210546874999964997 : Rat) / 640000000000000000000), D2 := ((113316210874999964997 : Rat) / 640000000000000000000), D3 := ((38384706874999964997 : Rat) / 640000000000000000000), D4 := ((5094198955267852497459 : Rat) / 102400000000000000000000), LB := ((12660584401391617 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((1750394610874999964997 : Rat) / 640000000000000000000), R := ((280068621269553565823091 : Rat) / 102400000000000000000000), D0 := ((280068621269553565823091 : Rat) / 102400000000000000000000), D1 := ((93959171029553565823091 : Rat) / 102400000000000000000000), D2 := ((18136077269553565823091 : Rat) / 102400000000000000000000), D3 := ((6147036629553565823091 : Rat) / 102400000000000000000000), D4 := ((159022357053571283559 : Rat) / 3200000000000000000000), LB := ((6764782055079799 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280068621269553565823091 : Rat) / 102400000000000000000000), R := ((140037052399553568623331 : Rat) / 51200000000000000000000), D0 := ((140037052399553568623331 : Rat) / 51200000000000000000000), D1 := ((46982327279553568623331 : Rat) / 51200000000000000000000), D2 := ((9070780399553568623331 : Rat) / 51200000000000000000000), D3 := ((3076260079553568623331 : Rat) / 51200000000000000000000), D4 := ((5083231896160709650317 : Rat) / 102400000000000000000000), LB := ((14426367449182909 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140037052399553568623331 : Rat) / 51200000000000000000000), R := ((280079588328660708670233 : Rat) / 102400000000000000000000), D0 := ((280079588328660708670233 : Rat) / 102400000000000000000000), D1 := ((93970138088660708670233 : Rat) / 102400000000000000000000), D2 := ((18147044328660708670233 : Rat) / 102400000000000000000000), D3 := ((6158003688660708670233 : Rat) / 102400000000000000000000), D4 := ((2538874183303569113373 : Rat) / 51200000000000000000000), LB := ((15351051505707591 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280079588328660708670233 : Rat) / 102400000000000000000000), R := ((70021267964553570023451 : Rat) / 25600000000000000000000), D0 := ((70021267964553570023451 : Rat) / 25600000000000000000000), D1 := ((23493905404553570023451 : Rat) / 25600000000000000000000), D2 := ((4538131964553570023451 : Rat) / 25600000000000000000000), D3 := ((1540871804553570023451 : Rat) / 25600000000000000000000), D4 := ((202890593482142672127 : Rat) / 4096000000000000000000), LB := ((16303673552608977 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70021267964553570023451 : Rat) / 25600000000000000000000), R := ((2240724443102142812139 : Rat) / 819200000000000000000), D0 := ((2240724443102142812139 : Rat) / 819200000000000000000), D1 := ((751848841182142812139 : Rat) / 819200000000000000000), D2 := ((145264091102142812139 : Rat) / 819200000000000000000), D3 := ((49351765982142812139 : Rat) / 819200000000000000000), D4 := ((1266695326874998844901 : Rat) / 25600000000000000000000), LB := ((17284291048969003 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((2240724443102142812139 : Rat) / 819200000000000000000), R := ((140048019458660711470473 : Rat) / 51200000000000000000000), D0 := ((140048019458660711470473 : Rat) / 51200000000000000000000), D1 := ((46993294338660711470473 : Rat) / 51200000000000000000000), D2 := ((9081747458660711470473 : Rat) / 51200000000000000000000), D3 := ((3087227138660711470473 : Rat) / 51200000000000000000000), D4 := ((5061297777946423956033 : Rat) / 102400000000000000000000), LB := ((9146480820693137 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140048019458660711470473 : Rat) / 51200000000000000000000), R := ((280101522446874994364517 : Rat) / 102400000000000000000000), D0 := ((280101522446874994364517 : Rat) / 102400000000000000000000), D1 := ((93992072206874994364517 : Rat) / 102400000000000000000000), D2 := ((18168978446874994364517 : Rat) / 102400000000000000000000), D3 := ((6179937806874994364517 : Rat) / 102400000000000000000000), D4 := ((2527907124196426266231 : Rat) / 51200000000000000000000), LB := ((483243579101067 : Rat) / 2500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280101522446874994364517 : Rat) / 102400000000000000000000), R := ((35013375747053570723511 : Rat) / 12800000000000000000000), D0 := ((35013375747053570723511 : Rat) / 12800000000000000000000), D1 := ((11749694467053570723511 : Rat) / 12800000000000000000000), D2 := ((2271807747053570723511 : Rat) / 12800000000000000000000), D3 := ((773177667053570723511 : Rat) / 12800000000000000000000), D4 := ((5050330718839281108891 : Rat) / 102400000000000000000000), LB := ((2039469364031321 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((35013375747053570723511 : Rat) / 12800000000000000000000), R := ((280112489505982137211659 : Rat) / 102400000000000000000000), D0 := ((280112489505982137211659 : Rat) / 102400000000000000000000), D1 := ((94003039265982137211659 : Rat) / 102400000000000000000000), D2 := ((18179945505982137211659 : Rat) / 102400000000000000000000), D3 := ((6190904865982137211659 : Rat) / 102400000000000000000000), D4 := ((126121179732142742133 : Rat) / 2560000000000000000000), LB := ((21487871283032423 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((280112489505982137211659 : Rat) / 102400000000000000000000), R := ((28011797303553570863523 : Rat) / 10240000000000000000000), D0 := ((28011797303553570863523 : Rat) / 10240000000000000000000), D1 := ((9400852279553570863523 : Rat) / 10240000000000000000000), D2 := ((1818542903553570863523 : Rat) / 10240000000000000000000), D3 := ((619638839553570863523 : Rat) / 10240000000000000000000), D4 := ((5039363659732138261749 : Rat) / 102400000000000000000000), LB := ((2260933449521607 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((28011797303553570863523 : Rat) / 10240000000000000000000), R := ((70032235023660712870593 : Rat) / 25600000000000000000000), D0 := ((70032235023660712870593 : Rat) / 25600000000000000000000), D1 := ((23504872463660712870593 : Rat) / 25600000000000000000000), D2 := ((4549099023660712870593 : Rat) / 25600000000000000000000), D3 := ((1551838863660712870593 : Rat) / 25600000000000000000000), D4 := ((2516940065089283419089 : Rat) / 51200000000000000000000), LB := ((2489522757942453 : Rat) / 5000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70032235023660712870593 : Rat) / 25600000000000000000000), R := ((140069953576874997164757 : Rat) / 51200000000000000000000), D0 := ((140069953576874997164757 : Rat) / 51200000000000000000000), D1 := ((47015228456874997164757 : Rat) / 51200000000000000000000), D2 := ((9103681576874997164757 : Rat) / 51200000000000000000000), D3 := ((3109161256874997164757 : Rat) / 51200000000000000000000), D4 := ((1255728267767855997759 : Rat) / 25600000000000000000000), LB := ((24372867306943213 : Rat) / 1000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140069953576874997164757 : Rat) / 51200000000000000000000), R := ((17509429638303571073541 : Rat) / 6400000000000000000000), D0 := ((17509429638303571073541 : Rat) / 6400000000000000000000), D1 := ((5877588998303571073541 : Rat) / 6400000000000000000000), D2 := ((1138645638303571073541 : Rat) / 6400000000000000000000), D3 := ((389330598303571073541 : Rat) / 6400000000000000000000), D4 := ((2505973005982140571947 : Rat) / 51200000000000000000000), LB := ((9877734035623753 : Rat) / 200000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17509429638303571073541 : Rat) / 6400000000000000000000), R := ((140080920635982140011899 : Rat) / 51200000000000000000000), D0 := ((140080920635982140011899 : Rat) / 51200000000000000000000), D1 := ((47026195515982140011899 : Rat) / 51200000000000000000000), D2 := ((9114648635982140011899 : Rat) / 51200000000000000000000), D3 := ((3120128315982140011899 : Rat) / 51200000000000000000000), D4 := ((312561184553571143547 : Rat) / 6400000000000000000000), LB := ((2951174626507 : Rat) / 39062500000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140080920635982140011899 : Rat) / 51200000000000000000000), R := ((14008640416553571143547 : Rat) / 5120000000000000000000), D0 := ((14008640416553571143547 : Rat) / 5120000000000000000000), D1 := ((4703167904553571143547 : Rat) / 5120000000000000000000), D2 := ((912013216553571143547 : Rat) / 5120000000000000000000), D3 := ((312561184553571143547 : Rat) / 5120000000000000000000), D4 := ((499001189374999544961 : Rat) / 10240000000000000000000), LB := ((10286185678443083 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((14008640416553571143547 : Rat) / 5120000000000000000000), R := ((140091887695089282859041 : Rat) / 51200000000000000000000), D0 := ((140091887695089282859041 : Rat) / 51200000000000000000000), D1 := ((47037162575089282859041 : Rat) / 51200000000000000000000), D2 := ((9125615695089282859041 : Rat) / 51200000000000000000000), D3 := ((3131095375089282859041 : Rat) / 51200000000000000000000), D4 := ((1244761208660713150617 : Rat) / 25600000000000000000000), LB := ((13132884959843327 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140091887695089282859041 : Rat) / 51200000000000000000000), R := ((35024342806160713570653 : Rat) / 12800000000000000000000), D0 := ((35024342806160713570653 : Rat) / 12800000000000000000000), D1 := ((11760661526160713570653 : Rat) / 12800000000000000000000), D2 := ((2282774806160713570653 : Rat) / 12800000000000000000000), D3 := ((784144726160713570653 : Rat) / 12800000000000000000000), D4 := ((2484038887767854877663 : Rat) / 51200000000000000000000), LB := ((4023897530897047 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((35024342806160713570653 : Rat) / 12800000000000000000000), R := ((140102854754196425706183 : Rat) / 51200000000000000000000), D0 := ((140102854754196425706183 : Rat) / 51200000000000000000000), D1 := ((47048129634196425706183 : Rat) / 51200000000000000000000), D2 := ((9136582754196425706183 : Rat) / 51200000000000000000000), D3 := ((3142062434196425706183 : Rat) / 51200000000000000000000), D4 := ((619638839553570863523 : Rat) / 12800000000000000000000), LB := ((9587394815141481 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140102854754196425706183 : Rat) / 51200000000000000000000), R := ((70054169141874998564877 : Rat) / 25600000000000000000000), D0 := ((70054169141874998564877 : Rat) / 25600000000000000000000), D1 := ((23526806581874998564877 : Rat) / 25600000000000000000000), D2 := ((4571033141874998564877 : Rat) / 25600000000000000000000), D3 := ((1573772981874998564877 : Rat) / 25600000000000000000000), D4 := ((2473071828660712030521 : Rat) / 51200000000000000000000), LB := ((11185487597503707 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70054169141874998564877 : Rat) / 25600000000000000000000), R := ((5604552872532142742133 : Rat) / 2048000000000000000000), D0 := ((5604552872532142742133 : Rat) / 2048000000000000000000), D1 := ((1882363867732142742133 : Rat) / 2048000000000000000000), D2 := ((365901992532142742133 : Rat) / 2048000000000000000000), D3 := ((126121179732142742133 : Rat) / 2048000000000000000000), D4 := ((49351765982142812139 : Rat) / 1024000000000000000000), LB := ((2568464181537111 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((5604552872532142742133 : Rat) / 2048000000000000000000), R := ((2189364145982142812139 : Rat) / 800000000000000000000), D0 := ((2189364145982142812139 : Rat) / 800000000000000000000), D1 := ((735384065982142812139 : Rat) / 800000000000000000000), D2 := ((143016145982142812139 : Rat) / 800000000000000000000), D3 := ((49351765982142812139 : Rat) / 800000000000000000000), D4 := ((2462104769553569183379 : Rat) / 51200000000000000000000), LB := ((1455814390047827 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((2189364145982142812139 : Rat) / 800000000000000000000), R := ((140124788872410711400467 : Rat) / 51200000000000000000000), D0 := ((140124788872410711400467 : Rat) / 51200000000000000000000), D1 := ((47070063752410711400467 : Rat) / 51200000000000000000000), D2 := ((9158516872410711400467 : Rat) / 51200000000000000000000), D3 := ((3163996552410711400467 : Rat) / 51200000000000000000000), D4 := ((38384706874999964997 : Rat) / 800000000000000000000), LB := ((6533282960634601 : Rat) / 20000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140124788872410711400467 : Rat) / 51200000000000000000000), R := ((70065136200982141412019 : Rat) / 25600000000000000000000), D0 := ((70065136200982141412019 : Rat) / 25600000000000000000000), D1 := ((23537773640982141412019 : Rat) / 25600000000000000000000), D2 := ((4582000200982141412019 : Rat) / 25600000000000000000000), D3 := ((1584740040982141412019 : Rat) / 25600000000000000000000), D4 := ((2451137710446426336237 : Rat) / 51200000000000000000000), LB := ((3633552784437777 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70065136200982141412019 : Rat) / 25600000000000000000000), R := ((140135755931517854247609 : Rat) / 51200000000000000000000), D0 := ((140135755931517854247609 : Rat) / 51200000000000000000000), D1 := ((47081030811517854247609 : Rat) / 51200000000000000000000), D2 := ((9169483931517854247609 : Rat) / 51200000000000000000000), D3 := ((3174963611517854247609 : Rat) / 51200000000000000000000), D4 := ((1222827090446427456333 : Rat) / 25600000000000000000000), LB := ((20062067674475603 : Rat) / 50000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((140135755931517854247609 : Rat) / 51200000000000000000000), R := ((7007061973053571283559 : Rat) / 2560000000000000000000), D0 := ((7007061973053571283559 : Rat) / 2560000000000000000000), D1 := ((2354325717053571283559 : Rat) / 2560000000000000000000), D2 := ((458748373053571283559 : Rat) / 2560000000000000000000), D3 := ((159022357053571283559 : Rat) / 2560000000000000000000), D4 := ((488034130267856697819 : Rat) / 10240000000000000000000), LB := ((4403274917359479 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((7007061973053571283559 : Rat) / 2560000000000000000000), R := ((70076103260089284259161 : Rat) / 25600000000000000000000), D0 := ((70076103260089284259161 : Rat) / 25600000000000000000000), D1 := ((23548740700089284259161 : Rat) / 25600000000000000000000), D2 := ((4592967260089284259161 : Rat) / 25600000000000000000000), D3 := ((1595707100089284259161 : Rat) / 25600000000000000000000), D4 := ((608671780446428016381 : Rat) / 12800000000000000000000), LB := ((7253743911750377 : Rat) / 1000000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70076103260089284259161 : Rat) / 25600000000000000000000), R := ((17520396697410713920683 : Rat) / 6400000000000000000000), D0 := ((17520396697410713920683 : Rat) / 6400000000000000000000), D1 := ((5888556057410713920683 : Rat) / 6400000000000000000000), D2 := ((1149612697410713920683 : Rat) / 6400000000000000000000), D3 := ((400297657410713920683 : Rat) / 6400000000000000000000), D4 := ((1211860031339284609191 : Rat) / 25600000000000000000000), LB := ((8943071319969 : Rat) / 97656250000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17520396697410713920683 : Rat) / 6400000000000000000000), R := ((70087070319196427106303 : Rat) / 25600000000000000000000), D0 := ((70087070319196427106303 : Rat) / 25600000000000000000000), D1 := ((23559707759196427106303 : Rat) / 25600000000000000000000), D2 := ((4603934319196427106303 : Rat) / 25600000000000000000000), D3 := ((1606674159196427106303 : Rat) / 25600000000000000000000), D4 := ((60318825089285659281 : Rat) / 1280000000000000000000), LB := ((18078389269726713 : Rat) / 100000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70087070319196427106303 : Rat) / 25600000000000000000000), R := ((35046276924374999264937 : Rat) / 12800000000000000000000), D0 := ((35046276924374999264937 : Rat) / 12800000000000000000000), D1 := ((11782595644374999264937 : Rat) / 12800000000000000000000), D2 := ((2304708924374999264937 : Rat) / 12800000000000000000000), D3 := ((806078844374999264937 : Rat) / 12800000000000000000000), D4 := ((1200892972232141762049 : Rat) / 25600000000000000000000), LB := ((42955746197091 : Rat) / 156250000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((35046276924374999264937 : Rat) / 12800000000000000000000), R := ((14019607475660713990689 : Rat) / 5120000000000000000000), D0 := ((14019607475660713990689 : Rat) / 5120000000000000000000), D1 := ((4714134963660713990689 : Rat) / 5120000000000000000000), D2 := ((922980275660713990689 : Rat) / 5120000000000000000000), D3 := ((323528243660713990689 : Rat) / 5120000000000000000000), D4 := ((597704721339285169239 : Rat) / 12800000000000000000000), LB := ((1870093943910911 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((14019607475660713990689 : Rat) / 5120000000000000000000), R := ((8762940113482142672127 : Rat) / 3200000000000000000000), D0 := ((8762940113482142672127 : Rat) / 3200000000000000000000), D1 := ((2947019793482142672127 : Rat) / 3200000000000000000000), D2 := ((577548113482142672127 : Rat) / 3200000000000000000000), D3 := ((202890593482142672127 : Rat) / 3200000000000000000000), D4 := ((1189925913124998914907 : Rat) / 25600000000000000000000), LB := ((4781336173471651 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((8762940113482142672127 : Rat) / 3200000000000000000000), R := ((70109004437410712800587 : Rat) / 25600000000000000000000), D0 := ((70109004437410712800587 : Rat) / 25600000000000000000000), D1 := ((23581641877410712800587 : Rat) / 25600000000000000000000), D2 := ((4625868437410712800587 : Rat) / 25600000000000000000000), D3 := ((1628608277410712800587 : Rat) / 25600000000000000000000), D4 := ((148055297946428436417 : Rat) / 3200000000000000000000), LB := ((587305553372941 : Rat) / 1000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70109004437410712800587 : Rat) / 25600000000000000000000), R := ((35057243983482142112079 : Rat) / 12800000000000000000000), D0 := ((35057243983482142112079 : Rat) / 12800000000000000000000), D1 := ((11793562703482142112079 : Rat) / 12800000000000000000000), D2 := ((2315675983482142112079 : Rat) / 12800000000000000000000), D3 := ((817045903482142112079 : Rat) / 12800000000000000000000), D4 := ((235791770803571213553 : Rat) / 5120000000000000000000), LB := ((7015795068577857 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((35057243983482142112079 : Rat) / 12800000000000000000000), R := ((70119971496517855647729 : Rat) / 25600000000000000000000), D0 := ((70119971496517855647729 : Rat) / 25600000000000000000000), D1 := ((23592608936517855647729 : Rat) / 25600000000000000000000), D2 := ((4636835496517855647729 : Rat) / 25600000000000000000000), D3 := ((1639575336517855647729 : Rat) / 25600000000000000000000), D4 := ((586737662232142322097 : Rat) / 12800000000000000000000), LB := ((8210010173079763 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((70119971496517855647729 : Rat) / 25600000000000000000000), R := ((701254550260714270713 : Rat) / 256000000000000000000), D0 := ((701254550260714270713 : Rat) / 256000000000000000000), D1 := ((235980924660714270713 : Rat) / 256000000000000000000), D2 := ((46423190260714270713 : Rat) / 256000000000000000000), D3 := ((16450588660714270713 : Rat) / 256000000000000000000), D4 := ((1167991794910713220623 : Rat) / 25600000000000000000000), LB := ((4728081327643463 : Rat) / 5000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((701254550260714270713 : Rat) / 256000000000000000000), R := ((35068211042589284959221 : Rat) / 12800000000000000000000), D0 := ((35068211042589284959221 : Rat) / 12800000000000000000000), D1 := ((11804529762589284959221 : Rat) / 12800000000000000000000), D2 := ((2326643042589284959221 : Rat) / 12800000000000000000000), D3 := ((828012962589284959221 : Rat) / 12800000000000000000000), D4 := ((290627066339285449263 : Rat) / 6400000000000000000000), LB := ((3274408688513919 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((35068211042589284959221 : Rat) / 12800000000000000000000), R := ((4384211821517857047849 : Rat) / 1600000000000000000000), D0 := ((4384211821517857047849 : Rat) / 1600000000000000000000), D1 := ((1476251661517857047849 : Rat) / 1600000000000000000000), D2 := ((291515821517857047849 : Rat) / 1600000000000000000000), D3 := ((104187061517857047849 : Rat) / 1600000000000000000000), D4 := ((115154120624999894991 : Rat) / 2560000000000000000000), LB := ((814029780791703 : Rat) / 2000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((4384211821517857047849 : Rat) / 1600000000000000000000), R := ((35079178101696427806363 : Rat) / 12800000000000000000000), D0 := ((35079178101696427806363 : Rat) / 12800000000000000000000), D1 := ((11815496821696427806363 : Rat) / 12800000000000000000000), D2 := ((2337610101696427806363 : Rat) / 12800000000000000000000), D3 := ((838980021696427806363 : Rat) / 12800000000000000000000), D4 := ((71285884196428506423 : Rat) / 1600000000000000000000), LB := ((1761485598836543 : Rat) / 2500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((35079178101696427806363 : Rat) / 12800000000000000000000), R := ((17542330815624999614967 : Rat) / 6400000000000000000000), D0 := ((17542330815624999614967 : Rat) / 6400000000000000000000), D1 := ((5910490175624999614967 : Rat) / 6400000000000000000000), D2 := ((1171546815624999614967 : Rat) / 6400000000000000000000), D3 := ((422231775624999614967 : Rat) / 6400000000000000000000), D4 := ((564803544017856627813 : Rat) / 12800000000000000000000), LB := ((1024113889207423 : Rat) / 1000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17542330815624999614967 : Rat) / 6400000000000000000000), R := ((7018029032160714130701 : Rat) / 2560000000000000000000), D0 := ((7018029032160714130701 : Rat) / 2560000000000000000000), D1 := ((2365292776160714130701 : Rat) / 2560000000000000000000), D2 := ((469715432160714130701 : Rat) / 2560000000000000000000), D3 := ((169989416160714130701 : Rat) / 2560000000000000000000), D4 := ((279660007232142602121 : Rat) / 6400000000000000000000), LB := ((682992524824233 : Rat) / 500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((7018029032160714130701 : Rat) / 2560000000000000000000), R := ((8773907172589285519269 : Rat) / 3200000000000000000000), D0 := ((8773907172589285519269 : Rat) / 3200000000000000000000), D1 := ((2957986852589285519269 : Rat) / 3200000000000000000000), D2 := ((588515172589285519269 : Rat) / 3200000000000000000000), D3 := ((213857652589285519269 : Rat) / 3200000000000000000000), D4 := ((553836484910713780671 : Rat) / 12800000000000000000000), LB := ((17306311087662563 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((8773907172589285519269 : Rat) / 3200000000000000000000), R := ((17553297874732142462109 : Rat) / 6400000000000000000000), D0 := ((17553297874732142462109 : Rat) / 6400000000000000000000), D1 := ((5921457234732142462109 : Rat) / 6400000000000000000000), D2 := ((1182513874732142462109 : Rat) / 6400000000000000000000), D3 := ((433198834732142462109 : Rat) / 6400000000000000000000), D4 := ((5483529553571423571 : Rat) / 128000000000000000000), LB := ((183654588809673 : Rat) / 781250000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17553297874732142462109 : Rat) / 6400000000000000000000), R := ((219484767553571423571 : Rat) / 80000000000000000000), D0 := ((219484767553571423571 : Rat) / 80000000000000000000), D1 := ((74086759553571423571 : Rat) / 80000000000000000000), D2 := ((14849967553571423571 : Rat) / 80000000000000000000), D3 := ((5483529553571423571 : Rat) / 80000000000000000000), D4 := ((268692948124999754979 : Rat) / 6400000000000000000000), LB := ((10838824705422523 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((219484767553571423571 : Rat) / 80000000000000000000), R := ((17564264933839285309251 : Rat) / 6400000000000000000000), D0 := ((17564264933839285309251 : Rat) / 6400000000000000000000), D1 := ((5932424293839285309251 : Rat) / 6400000000000000000000), D2 := ((1193480933839285309251 : Rat) / 6400000000000000000000), D3 := ((444165893839285309251 : Rat) / 6400000000000000000000), D4 := ((16450588660714270713 : Rat) / 400000000000000000000), LB := ((2031100119626039 : Rat) / 1000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((17564264933839285309251 : Rat) / 6400000000000000000000), R := ((8784874231696428366411 : Rat) / 3200000000000000000000), D0 := ((8784874231696428366411 : Rat) / 3200000000000000000000), D1 := ((2968953911696428366411 : Rat) / 3200000000000000000000), D2 := ((599482231696428366411 : Rat) / 3200000000000000000000), D3 := ((224824711696428366411 : Rat) / 3200000000000000000000), D4 := ((257725889017856907837 : Rat) / 6400000000000000000000), LB := ((1925456553465571 : Rat) / 625000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((8784874231696428366411 : Rat) / 3200000000000000000000), R := ((4395178880624999894991 : Rat) / 1600000000000000000000), D0 := ((4395178880624999894991 : Rat) / 1600000000000000000000), D1 := ((1487218720624999894991 : Rat) / 1600000000000000000000), D2 := ((302482880624999894991 : Rat) / 1600000000000000000000), D3 := ((115154120624999894991 : Rat) / 1600000000000000000000), D4 := ((126121179732142742133 : Rat) / 3200000000000000000000), LB := ((12145145878914021 : Rat) / 25000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((4395178880624999894991 : Rat) / 1600000000000000000000), R := ((8795841290803571213553 : Rat) / 3200000000000000000000), D0 := ((8795841290803571213553 : Rat) / 3200000000000000000000), D1 := ((2979920970803571213553 : Rat) / 3200000000000000000000), D2 := ((610449290803571213553 : Rat) / 3200000000000000000000), D3 := ((235791770803571213553 : Rat) / 3200000000000000000000), D4 := ((60318825089285659281 : Rat) / 1600000000000000000000), LB := ((628682206153397 : Rat) / 200000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((8795841290803571213553 : Rat) / 3200000000000000000000), R := ((2200331205089285659281 : Rat) / 800000000000000000000), D0 := ((2200331205089285659281 : Rat) / 800000000000000000000), D1 := ((746351125089285659281 : Rat) / 800000000000000000000), D2 := ((153983205089285659281 : Rat) / 800000000000000000000), D3 := ((60318825089285659281 : Rat) / 800000000000000000000), D4 := ((115154120624999894991 : Rat) / 3200000000000000000000), LB := ((12572610495034997 : Rat) / 2000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((2200331205089285659281 : Rat) / 800000000000000000000), R := ((4406145939732142742133 : Rat) / 1600000000000000000000), D0 := ((4406145939732142742133 : Rat) / 1600000000000000000000), D1 := ((1498185779732142742133 : Rat) / 1600000000000000000000), D2 := ((313449939732142742133 : Rat) / 1600000000000000000000), D3 := ((126121179732142742133 : Rat) / 1600000000000000000000), D4 := ((5483529553571423571 : Rat) / 160000000000000000000), LB := ((25067949568059467 : Rat) / 10000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((4406145939732142742133 : Rat) / 1600000000000000000000), R := ((551453683660714270713 : Rat) / 200000000000000000000), D0 := ((551453683660714270713 : Rat) / 200000000000000000000), D1 := ((187958663660714270713 : Rat) / 200000000000000000000), D2 := ((39866683660714270713 : Rat) / 200000000000000000000), D3 := ((16450588660714270713 : Rat) / 200000000000000000000), D4 := ((49351765982142812139 : Rat) / 1600000000000000000000), LB := ((11696258529583337 : Rat) / 1000000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((551453683660714270713 : Rat) / 200000000000000000000), R := ((2211298264196428506423 : Rat) / 800000000000000000000), D0 := ((2211298264196428506423 : Rat) / 800000000000000000000), D1 := ((757318184196428506423 : Rat) / 800000000000000000000), D2 := ((164950264196428506423 : Rat) / 800000000000000000000), D3 := ((71285884196428506423 : Rat) / 800000000000000000000), D4 := ((5483529553571423571 : Rat) / 200000000000000000000), LB := ((4503237439932639 : Rat) / 500000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((2211298264196428506423 : Rat) / 800000000000000000000), R := ((1108390896874999964997 : Rat) / 400000000000000000000), D0 := ((1108390896874999964997 : Rat) / 400000000000000000000), D1 := ((381400856874999964997 : Rat) / 400000000000000000000), D2 := ((85216896874999964997 : Rat) / 400000000000000000000), D3 := ((38384706874999964997 : Rat) / 400000000000000000000), D4 := ((16450588660714270713 : Rat) / 800000000000000000000), LB := ((14160504527863 : Rat) / 312500000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((1108390896874999964997 : Rat) / 400000000000000000000), R := ((139234303303571423571 : Rat) / 50000000000000000000), D0 := ((139234303303571423571 : Rat) / 50000000000000000000), D1 := ((48360548303571423571 : Rat) / 50000000000000000000), D2 := ((11337553303571423571 : Rat) / 50000000000000000000), D3 := ((5483529553571423571 : Rat) / 50000000000000000000), D4 := ((5483529553571423571 : Rat) / 400000000000000000000), LB := ((7971988613090097 : Rat) / 100000000000000000) },
  { w1 := ((116544253509057 : Rat) / 31250000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((22834335639335027 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((139234303303571423571 : Rat) / 50000000000000000000), L := ((139234303303571423571 : Rat) / 50000000000000000000), R := ((34993622767857142867 : Rat) / 12500000000000000000), D0 := ((34993622767857142867 : Rat) / 12500000000000000000), D1 := ((12275184017857142867 : Rat) / 12500000000000000000), D2 := ((3019435267857142867 : Rat) / 12500000000000000000), D3 := ((1555929330357142867 : Rat) / 12500000000000000000), D4 := ((740187767857147897 : Rat) / 50000000000000000000), LB := ((5663688143214829 : Rat) / 25000000000000000000) }
]

def block092RightChunk001L : Rat := ((559758878999910703419783 : Rat) / 204800000000000000000000)
def block092RightChunk001R : Rat := ((34993622767857142867 : Rat) / 12500000000000000000)

def block092RightChunk001Certificate : Bool :=
  allBoxesValid block092RightChunk001 &&
  coversFromBool block092RightChunk001 block092RightChunk001L block092RightChunk001R

theorem block092RightChunk001Certificate_eq_true :
    block092RightChunk001Certificate = true := by
  native_decide

def block092RightChainCertificate : Bool :=
  decide (
    block092RightL = ((89964716517857142897 : Rat) / 50000000000000000000) /\
    ((559758878999910703419783 : Rat) / 204800000000000000000000) = ((559758878999910703419783 : Rat) / 204800000000000000000000) /\
    ((34993622767857142867 : Rat) / 12500000000000000000) = block092RightR)

theorem block092RightChainCertificate_eq_true :
    block092RightChainCertificate = true := by
  native_decide

def block092LeftBoxCount : Nat := boxCount block092LeftBoxes
def block092RightBoxCount : Nat := 197

def block092_rational_certificate : Prop :=
    block092LeftCertificate = true /\
    block092RightChainCertificate = true /\
    block092RightChunk000Certificate = true /\
    block092RightChunk001Certificate = true

theorem block092_rational_certificate_proof :
    block092_rational_certificate := by
  exact ⟨block092LeftCertificate_eq_true, block092RightChainCertificate_eq_true, block092RightChunk000Certificate_eq_true, block092RightChunk001Certificate_eq_true⟩

end Block092
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block092

open Set

def block092W1 : Rat := ((116544253509057 : Rat) / 31250000000000)
def block092W2 : Rat := (0 : Rat)
def block092W3 : Rat := (0 : Rat)
def block092W4 : Rat := ((22834335639335027 : Rat) / 100000000000000000)
def block092S1 : Rat := ((18174751 : Rat) / 10000000)
def block092S2 : Rat := ((511587 : Rat) / 200000)
def block092S3 : Rat := ((107000619 : Rat) / 40000000)
def block092S4 : Rat := ((139234303303571423571 : Rat) / 50000000000000000000)

noncomputable def block092V (y : ℝ) : ℝ :=
  ratPotential block092W1 block092W2 block092W3 block092W4 block092S1 block092S2 block092S3 block092S4 y

def block092LeftParamsCertificate : Bool :=
  allBoxesSameParams block092LeftBoxes block092W1 block092W2 block092W3 block092W4 block092S1 block092S2 block092S3 block092S4

theorem block092LeftParamsCertificate_eq_true :
    block092LeftParamsCertificate = true := by
  native_decide

theorem block092_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block092LeftL : ℝ) (block092LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block092S1 : ℝ))
    (hy2ne : y ≠ (block092S2 : ℝ))
    (hy3ne : y ≠ (block092S3 : ℝ))
    (hy4ne : y ≠ (block092S4 : ℝ)) :
    0 < block092V y := by
  have hcert := block092LeftCertificate_eq_true
  unfold block092LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block092LeftBoxes) (lo := block092LeftL) (hi := block092LeftR)
    (w1 := block092W1) (w2 := block092W2) (w3 := block092W3) (w4 := block092W4)
    (s1 := block092S1) (s2 := block092S2) (s3 := block092S3) (s4 := block092S4)
    hboxes hcover block092LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block092RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block092RightChunk000 block092W1 block092W2 block092W3 block092W4 block092S1 block092S2 block092S3 block092S4

theorem block092RightChunk000ParamsCertificate_eq_true :
    block092RightChunk000ParamsCertificate = true := by
  native_decide

theorem block092_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block092RightChunk000L : ℝ) (block092RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block092S1 : ℝ))
    (hy2ne : y ≠ (block092S2 : ℝ))
    (hy3ne : y ≠ (block092S3 : ℝ))
    (hy4ne : y ≠ (block092S4 : ℝ)) :
    0 < block092V y := by
  have hcert := block092RightChunk000Certificate_eq_true
  unfold block092RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block092RightChunk000) (lo := block092RightChunk000L) (hi := block092RightChunk000R)
    (w1 := block092W1) (w2 := block092W2) (w3 := block092W3) (w4 := block092W4)
    (s1 := block092S1) (s2 := block092S2) (s3 := block092S3) (s4 := block092S4)
    hboxes hcover block092RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block092RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block092RightChunk001 block092W1 block092W2 block092W3 block092W4 block092S1 block092S2 block092S3 block092S4

theorem block092RightChunk001ParamsCertificate_eq_true :
    block092RightChunk001ParamsCertificate = true := by
  native_decide

theorem block092_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block092RightChunk001L : ℝ) (block092RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block092S1 : ℝ))
    (hy2ne : y ≠ (block092S2 : ℝ))
    (hy3ne : y ≠ (block092S3 : ℝ))
    (hy4ne : y ≠ (block092S4 : ℝ)) :
    0 < block092V y := by
  have hcert := block092RightChunk001Certificate_eq_true
  unfold block092RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block092RightChunk001) (lo := block092RightChunk001L) (hi := block092RightChunk001R)
    (w1 := block092W1) (w2 := block092W2) (w3 := block092W3) (w4 := block092W4)
    (s1 := block092S1) (s2 := block092S2) (s3 := block092S3) (s4 := block092S4)
    hboxes hcover block092RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block092_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block092RightL : ℝ) (block092RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block092S1 : ℝ))
    (hy2ne : y ≠ (block092S2 : ℝ))
    (hy3ne : y ≠ (block092S3 : ℝ))
    (hy4ne : y ≠ (block092S4 : ℝ)) :
    0 < block092V y := by
  by_cases h0 : y ≤ (block092RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block092RightChunk000L : ℝ) (block092RightChunk000R : ℝ) := by
      have hL : (block092RightChunk000L : ℝ) = (block092RightL : ℝ) := by
        norm_num [block092RightChunk000L, block092RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block092_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block092RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block092RightChunk001L : ℝ) = (block092RightChunk000R : ℝ) := by
      norm_num [block092RightChunk001L, block092RightChunk000R]
    have hR : (block092RightChunk001R : ℝ) = (block092RightR : ℝ) := by
      norm_num [block092RightChunk001R, block092RightR]
    have hyc : y ∈ Icc (block092RightChunk001L : ℝ) (block092RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block092_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block092_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block092LeftL : ℝ) (block092LeftR : ℝ) →
    y ≠ 0 → y ≠ (block092S1 : ℝ) → y ≠ (block092S2 : ℝ) →
    y ≠ (block092S3 : ℝ) → y ≠ (block092S4 : ℝ) → 0 < block092V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block092RightL : ℝ) (block092RightR : ℝ) →
    y ≠ 0 → y ≠ (block092S1 : ℝ) → y ≠ (block092S2 : ℝ) →
    y ≠ (block092S3 : ℝ) → y ≠ (block092S4 : ℝ) → 0 < block092V y)

theorem block092_reallog_certificate_proof :
    block092_reallog_certificate := by
  exact ⟨block092_left_V_pos, block092_right_V_pos⟩

end Block092
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block092.block092V
#check Erdos1038Lean.M1817475.Block092.block092_left_V_pos
#check Erdos1038Lean.M1817475.Block092.block092_right_V_pos
#check Erdos1038Lean.M1817475.Block092.block092_reallog_certificate_proof
