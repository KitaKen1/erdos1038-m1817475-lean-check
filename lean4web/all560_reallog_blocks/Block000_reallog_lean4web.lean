/-
Self-contained Lean4Web paste file.
Block 0 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block000

def block000LeftL : Rat := ((40863975446428571429 : Rat) / 50000000000000000000)
def block000LeftR : Rat := ((32699 : Rat) / 40000)
def block000RightL : Rat := ((90863975446428571429 : Rat) / 50000000000000000000)
def block000RightR : Rat := ((112699 : Rat) / 40000)

def block000LeftBoxes : List RatBox := [
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((40863975446428571429 : Rat) / 50000000000000000000), R := ((32699 : Rat) / 40000), D0 := ((32699 : Rat) / 40000), D1 := ((50009779553571428571 : Rat) / 50000000000000000000), D2 := ((87032774553571428571 : Rat) / 50000000000000000000), D3 := ((92886798303571428571 : Rat) / 50000000000000000000), D4 := ((98516946160714280707 : Rat) / 50000000000000000000), LB := ((206183606781013 : Rat) / 250000000000000000) }
]

def block000LeftCertificate : Bool :=
  allBoxesValid block000LeftBoxes &&
  coversFromBool block000LeftBoxes block000LeftL block000LeftR

theorem block000LeftCertificate_eq_true :
    block000LeftCertificate = true := by
  native_decide

def block000RightChunk000 : List RatBox := [
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((90863975446428571429 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((9779553571428571 : Rat) / 50000000000000000000), D2 := ((37032774553571428571 : Rat) / 50000000000000000000), D3 := ((42886798303571428571 : Rat) / 50000000000000000000), D4 := ((48516946160714280707 : Rat) / 50000000000000000000), LB := ((14689062724035843 : Rat) / 1000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((6063395825892856517 : Rat) / 6250000000000000000), LB := ((7194621680187141 : Rat) / 5000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((19492417 : Rat) / 40000000), D4 := ((3749458638392856517 : Rat) / 6250000000000000000), LB := ((5966621884415423 : Rat) / 10000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((6043909 : Rat) / 20000000), D4 := ((2592490044642856517 : Rat) / 6250000000000000000), LB := ((506351669815129 : Rat) / 1562500000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((197230201 : Rat) / 80000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((16771037 : Rat) / 80000000), D4 := ((2014005747767856517 : Rat) / 6250000000000000000), LB := ((3219769283583007 : Rat) / 50000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((511587 : Rat) / 200000), R := ((413952819 : Rat) / 160000000), D0 := ((413952819 : Rat) / 160000000), D1 := ((123156803 : Rat) / 160000000), D2 := ((4683219 : Rat) / 160000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((1435521450892856517 : Rat) / 6250000000000000000), LB := ((133336208065707 : Rat) / 2000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((413952819 : Rat) / 160000000), R := ((209318019 : Rat) / 80000000), D0 := ((209318019 : Rat) / 80000000), D1 := ((63920011 : Rat) / 80000000), D2 := ((4683219 : Rat) / 80000000), D3 := ((14049657 : Rat) / 160000000), D4 := ((1252583208705356517 : Rat) / 6250000000000000000), LB := ((6279389337041169 : Rat) / 500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((209318019 : Rat) / 80000000), R := ((168391059 : Rat) / 64000000), D0 := ((168391059 : Rat) / 64000000), D1 := ((260363263 : Rat) / 320000000), D2 := ((4683219 : Rat) / 64000000), D3 := ((4683219 : Rat) / 80000000), D4 := ((1069644966517856517 : Rat) / 6250000000000000000), LB := ((13180957120298209 : Rat) / 1000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((168391059 : Rat) / 64000000), R := ((1688593809 : Rat) / 640000000), D0 := ((1688593809 : Rat) / 640000000), D1 := ((105081949 : Rat) / 128000000), D2 := ((51515409 : Rat) / 640000000), D3 := ((14049657 : Rat) / 320000000), D4 := ((978175845424106517 : Rat) / 6250000000000000000), LB := ((168620096929869 : Rat) / 10000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1688593809 : Rat) / 640000000), R := ((423319257 : Rat) / 160000000), D0 := ((423319257 : Rat) / 160000000), D1 := ((132523241 : Rat) / 160000000), D2 := ((14049657 : Rat) / 160000000), D3 := ((4683219 : Rat) / 128000000), D4 := ((932441284877231517 : Rat) / 6250000000000000000), LB := ((2117488344539037 : Rat) / 250000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((423319257 : Rat) / 160000000), R := ((1697960247 : Rat) / 640000000), D0 := ((1697960247 : Rat) / 640000000), D1 := ((534776183 : Rat) / 640000000), D2 := ((60881847 : Rat) / 640000000), D3 := ((4683219 : Rat) / 160000000), D4 := ((886706724330356517 : Rat) / 6250000000000000000), LB := ((4853224677274781 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1697960247 : Rat) / 640000000), R := ((3400603713 : Rat) / 1280000000), D0 := ((3400603713 : Rat) / 1280000000), D1 := ((214847117 : Rat) / 256000000), D2 := ((126446913 : Rat) / 1280000000), D3 := ((14049657 : Rat) / 640000000), D4 := ((840972163783481517 : Rat) / 6250000000000000000), LB := ((5500334233004223 : Rat) / 1000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((3400603713 : Rat) / 1280000000), R := ((851321733 : Rat) / 320000000), D0 := ((851321733 : Rat) / 320000000), D1 := ((269729701 : Rat) / 320000000), D2 := ((32782533 : Rat) / 320000000), D3 := ((4683219 : Rat) / 256000000), D4 := ((818104883510044017 : Rat) / 6250000000000000000), LB := ((2577232621878589 : Rat) / 1000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((851321733 : Rat) / 320000000), R := ((6815257083 : Rat) / 2560000000), D0 := ((6815257083 : Rat) / 2560000000), D1 := ((2162520827 : Rat) / 2560000000), D2 := ((266943483 : Rat) / 2560000000), D3 := ((4683219 : Rat) / 320000000), D4 := ((795237603236606517 : Rat) / 6250000000000000000), LB := ((1086676633722039 : Rat) / 200000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((6815257083 : Rat) / 2560000000), R := ((3409970151 : Rat) / 1280000000), D0 := ((3409970151 : Rat) / 1280000000), D1 := ((1083602023 : Rat) / 1280000000), D2 := ((135813351 : Rat) / 1280000000), D3 := ((32782533 : Rat) / 2560000000), D4 := ((783803963099887767 : Rat) / 6250000000000000000), LB := ((2102667343277631 : Rat) / 500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((3409970151 : Rat) / 1280000000), R := ((6824623521 : Rat) / 2560000000), D0 := ((6824623521 : Rat) / 2560000000), D1 := ((434377453 : Rat) / 512000000), D2 := ((276309921 : Rat) / 2560000000), D3 := ((14049657 : Rat) / 1280000000), D4 := ((772370322963169017 : Rat) / 6250000000000000000), LB := ((11917974349877 : Rat) / 3906250000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((6824623521 : Rat) / 2560000000), R := ((341465337 : Rat) / 128000000), D0 := ((341465337 : Rat) / 128000000), D1 := ((544142621 : Rat) / 640000000), D2 := ((14049657 : Rat) / 128000000), D3 := ((4683219 : Rat) / 512000000), D4 := ((760936682826450267 : Rat) / 6250000000000000000), LB := ((19722125433242477 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((341465337 : Rat) / 128000000), R := ((6833989959 : Rat) / 2560000000), D0 := ((6833989959 : Rat) / 2560000000), D1 := ((2181253703 : Rat) / 2560000000), D2 := ((285676359 : Rat) / 2560000000), D3 := ((4683219 : Rat) / 640000000), D4 := ((749503042689731517 : Rat) / 6250000000000000000), LB := ((9708825866454607 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((6833989959 : Rat) / 2560000000), R := ((3419336589 : Rat) / 1280000000), D0 := ((3419336589 : Rat) / 1280000000), D1 := ((1092968461 : Rat) / 1280000000), D2 := ((145179789 : Rat) / 1280000000), D3 := ((14049657 : Rat) / 2560000000), D4 := ((738069402553012767 : Rat) / 6250000000000000000), LB := ((4901680510449591 : Rat) / 100000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((3419336589 : Rat) / 1280000000), R := ((547281183 : Rat) / 204800000), D0 := ((547281183 : Rat) / 204800000), D1 := ((4376557063 : Rat) / 5120000000), D2 := ((4683219 : Rat) / 40960000), D3 := ((4683219 : Rat) / 1280000000), D4 := ((726635762416294017 : Rat) / 6250000000000000000), LB := ((19327290207501457 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((547281183 : Rat) / 204800000), R := ((6843356397 : Rat) / 2560000000), D0 := ((6843356397 : Rat) / 2560000000), D1 := ((2190620141 : Rat) / 2560000000), D2 := ((295042797 : Rat) / 2560000000), D3 := ((14049657 : Rat) / 5120000000), D4 := ((360459471173967321 : Rat) / 3125000000000000000), LB := ((963243146940157 : Rat) / 625000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((6843356397 : Rat) / 2560000000), R := ((13691396013 : Rat) / 5120000000), D0 := ((13691396013 : Rat) / 5120000000), D1 := ((4385923501 : Rat) / 5120000000), D2 := ((594768813 : Rat) / 5120000000), D3 := ((4683219 : Rat) / 2560000000), D4 := ((715202122279575267 : Rat) / 6250000000000000000), LB := ((2927202076389579 : Rat) / 2500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((13691396013 : Rat) / 5120000000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 5120000000), D4 := ((177371325552803973 : Rat) / 1562500000000000000), LB := ((8220969644933129 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((2140716148482142856517 : Rat) / 800000000000000000000), D0 := ((2140716148482142856517 : Rat) / 800000000000000000000), D1 := ((686736068482142856517 : Rat) / 800000000000000000000), D2 := ((94368148482142856517 : Rat) / 800000000000000000000), D3 := ((703768482142856517 : Rat) / 800000000000000000000), D4 := ((703768482142856517 : Rat) / 6250000000000000000), LB := ((1197916885160133 : Rat) / 2000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2140716148482142856517 : Rat) / 800000000000000000000), R := ((1070709958482142856517 : Rat) / 400000000000000000000), D0 := ((1070709958482142856517 : Rat) / 400000000000000000000), D1 := ((343719918482142856517 : Rat) / 400000000000000000000), D2 := ((47535958482142856517 : Rat) / 400000000000000000000), D3 := ((703768482142856517 : Rat) / 400000000000000000000), D4 := ((89378597232142777659 : Rat) / 800000000000000000000), LB := ((3052797755402903 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1070709958482142856517 : Rat) / 400000000000000000000), R := ((2142123685446428569551 : Rat) / 800000000000000000000), D0 := ((2142123685446428569551 : Rat) / 800000000000000000000), D1 := ((688143605446428569551 : Rat) / 800000000000000000000), D2 := ((95775685446428569551 : Rat) / 800000000000000000000), D3 := ((2111305446428569551 : Rat) / 800000000000000000000), D4 := ((44337414374999960571 : Rat) / 400000000000000000000), LB := ((6470487426013527 : Rat) / 200000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2142123685446428569551 : Rat) / 800000000000000000000), R := ((4284951139374999995619 : Rat) / 1600000000000000000000), D0 := ((4284951139374999995619 : Rat) / 1600000000000000000000), D1 := ((1376990979374999995619 : Rat) / 1600000000000000000000), D2 := ((192255139374999995619 : Rat) / 1600000000000000000000), D3 := ((4926379374999995619 : Rat) / 1600000000000000000000), D4 := ((703768482142856517 : Rat) / 6400000000000000000), LB := ((541303597211773 : Rat) / 500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4284951139374999995619 : Rat) / 1600000000000000000000), R := ((535706863482142856517 : Rat) / 200000000000000000000), D0 := ((535706863482142856517 : Rat) / 200000000000000000000), D1 := ((172211843482142856517 : Rat) / 200000000000000000000), D2 := ((24119863482142856517 : Rat) / 200000000000000000000), D3 := ((703768482142856517 : Rat) / 200000000000000000000), D4 := ((175238352053571272733 : Rat) / 1600000000000000000000), LB := ((385614201166673 : Rat) / 400000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((535706863482142856517 : Rat) / 200000000000000000000), R := ((4286358676339285708653 : Rat) / 1600000000000000000000), D0 := ((4286358676339285708653 : Rat) / 1600000000000000000000), D1 := ((1378398516339285708653 : Rat) / 1600000000000000000000), D2 := ((193662676339285708653 : Rat) / 1600000000000000000000), D3 := ((6333916339285708653 : Rat) / 1600000000000000000000), D4 := ((21816822946428552027 : Rat) / 200000000000000000000), LB := ((8508347899885971 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4286358676339285708653 : Rat) / 1600000000000000000000), R := ((428706244482142856517 : Rat) / 160000000000000000000), D0 := ((428706244482142856517 : Rat) / 160000000000000000000), D1 := ((137910228482142856517 : Rat) / 160000000000000000000), D2 := ((19436644482142856517 : Rat) / 160000000000000000000), D3 := ((703768482142856517 : Rat) / 160000000000000000000), D4 := ((173830815089285559699 : Rat) / 1600000000000000000000), LB := ((7430429415831163 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((428706244482142856517 : Rat) / 160000000000000000000), R := ((4287766213303571421687 : Rat) / 1600000000000000000000), D0 := ((4287766213303571421687 : Rat) / 1600000000000000000000), D1 := ((1379806053303571421687 : Rat) / 1600000000000000000000), D2 := ((195070213303571421687 : Rat) / 1600000000000000000000), D3 := ((7741453303571421687 : Rat) / 1600000000000000000000), D4 := ((86563523303571351591 : Rat) / 800000000000000000000), LB := ((6406983129726429 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4287766213303571421687 : Rat) / 1600000000000000000000), R := ((1072117495446428569551 : Rat) / 400000000000000000000), D0 := ((1072117495446428569551 : Rat) / 400000000000000000000), D1 := ((345127455446428569551 : Rat) / 400000000000000000000), D2 := ((48943495446428569551 : Rat) / 400000000000000000000), D3 := ((2111305446428569551 : Rat) / 400000000000000000000), D4 := ((34484655624999969333 : Rat) / 320000000000000000000), LB := ((67979967048451 : Rat) / 125000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1072117495446428569551 : Rat) / 400000000000000000000), R := ((4289173750267857134721 : Rat) / 1600000000000000000000), D0 := ((4289173750267857134721 : Rat) / 1600000000000000000000), D1 := ((1381213590267857134721 : Rat) / 1600000000000000000000), D2 := ((196477750267857134721 : Rat) / 1600000000000000000000), D3 := ((9148990267857134721 : Rat) / 1600000000000000000000), D4 := ((42929877410714247537 : Rat) / 400000000000000000000), LB := ((1131266322017821 : Rat) / 2500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4289173750267857134721 : Rat) / 1600000000000000000000), R := ((2144938759374999995619 : Rat) / 800000000000000000000), D0 := ((2144938759374999995619 : Rat) / 800000000000000000000), D1 := ((690958679374999995619 : Rat) / 800000000000000000000), D2 := ((98590759374999995619 : Rat) / 800000000000000000000), D3 := ((4926379374999995619 : Rat) / 800000000000000000000), D4 := ((171015741160714133631 : Rat) / 1600000000000000000000), LB := ((1466953999597731 : Rat) / 4000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2144938759374999995619 : Rat) / 800000000000000000000), R := ((858116257446428569551 : Rat) / 320000000000000000000), D0 := ((858116257446428569551 : Rat) / 320000000000000000000), D1 := ((276524225446428569551 : Rat) / 320000000000000000000), D2 := ((39577057446428569551 : Rat) / 320000000000000000000), D3 := ((2111305446428569551 : Rat) / 320000000000000000000), D4 := ((85155986339285638557 : Rat) / 800000000000000000000), LB := ((2865759601408113 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((858116257446428569551 : Rat) / 320000000000000000000), R := ((268205315982142856517 : Rat) / 100000000000000000000), D0 := ((268205315982142856517 : Rat) / 100000000000000000000), D1 := ((86457805982142856517 : Rat) / 100000000000000000000), D2 := ((12411815982142856517 : Rat) / 100000000000000000000), D3 := ((703768482142856517 : Rat) / 100000000000000000000), D4 := ((169608204196428420597 : Rat) / 1600000000000000000000), LB := ((2650746613529209 : Rat) / 12500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((268205315982142856517 : Rat) / 100000000000000000000), R := ((4291988824196428560789 : Rat) / 1600000000000000000000), D0 := ((4291988824196428560789 : Rat) / 1600000000000000000000), D1 := ((1384028664196428560789 : Rat) / 1600000000000000000000), D2 := ((199292824196428560789 : Rat) / 1600000000000000000000), D3 := ((11964064196428560789 : Rat) / 1600000000000000000000), D4 := ((2111305446428569551 : Rat) / 20000000000000000000), LB := ((1432311438096523 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4291988824196428560789 : Rat) / 1600000000000000000000), R := ((2146346296339285708653 : Rat) / 800000000000000000000), D0 := ((2146346296339285708653 : Rat) / 800000000000000000000), D1 := ((692366216339285708653 : Rat) / 800000000000000000000), D2 := ((99998296339285708653 : Rat) / 800000000000000000000), D3 := ((6333916339285708653 : Rat) / 800000000000000000000), D4 := ((168200667232142707563 : Rat) / 1600000000000000000000), LB := ((4006603378153839 : Rat) / 50000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2146346296339285708653 : Rat) / 800000000000000000000), R := ((4293396361160714273823 : Rat) / 1600000000000000000000), D0 := ((4293396361160714273823 : Rat) / 1600000000000000000000), D1 := ((1385436201160714273823 : Rat) / 1600000000000000000000), D2 := ((200700361160714273823 : Rat) / 1600000000000000000000), D3 := ((13371601160714273823 : Rat) / 1600000000000000000000), D4 := ((83748449374999925523 : Rat) / 800000000000000000000), LB := ((11402449275332849 : Rat) / 500000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4293396361160714273823 : Rat) / 1600000000000000000000), R := ((8587496490803571404163 : Rat) / 3200000000000000000000), D0 := ((8587496490803571404163 : Rat) / 3200000000000000000000), D1 := ((2771576170803571404163 : Rat) / 3200000000000000000000), D2 := ((402104490803571404163 : Rat) / 3200000000000000000000), D3 := ((27446970803571404163 : Rat) / 3200000000000000000000), D4 := ((166793130267856994529 : Rat) / 1600000000000000000000), LB := ((3093302535785991 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8587496490803571404163 : Rat) / 3200000000000000000000), R := ((214705006482142856517 : Rat) / 80000000000000000000), D0 := ((214705006482142856517 : Rat) / 80000000000000000000), D1 := ((69306998482142856517 : Rat) / 80000000000000000000), D2 := ((10070206482142856517 : Rat) / 80000000000000000000), D3 := ((703768482142856517 : Rat) / 80000000000000000000), D4 := ((332882492053571132541 : Rat) / 3200000000000000000000), LB := ((2974741263565561 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((214705006482142856517 : Rat) / 80000000000000000000), R := ((8588904027767857117197 : Rat) / 3200000000000000000000), D0 := ((8588904027767857117197 : Rat) / 3200000000000000000000), D1 := ((2772983707767857117197 : Rat) / 3200000000000000000000), D2 := ((403512027767857117197 : Rat) / 3200000000000000000000), D3 := ((28854507767857117197 : Rat) / 3200000000000000000000), D4 := ((41522340446428534503 : Rat) / 400000000000000000000), LB := ((229082455609797 : Rat) / 400000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8588904027767857117197 : Rat) / 3200000000000000000000), R := ((4294803898124999986857 : Rat) / 1600000000000000000000), D0 := ((4294803898124999986857 : Rat) / 1600000000000000000000), D1 := ((1386843738124999986857 : Rat) / 1600000000000000000000), D2 := ((202107898124999986857 : Rat) / 1600000000000000000000), D3 := ((14779138124999986857 : Rat) / 1600000000000000000000), D4 := ((331474955089285419507 : Rat) / 3200000000000000000000), LB := ((5519396909121621 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4294803898124999986857 : Rat) / 1600000000000000000000), R := ((8590311564732142830231 : Rat) / 3200000000000000000000), D0 := ((8590311564732142830231 : Rat) / 3200000000000000000000), D1 := ((2774391244732142830231 : Rat) / 3200000000000000000000), D2 := ((404919564732142830231 : Rat) / 3200000000000000000000), D3 := ((30262044732142830231 : Rat) / 3200000000000000000000), D4 := ((33077118660714256299 : Rat) / 320000000000000000000), LB := ((5326544689591151 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8590311564732142830231 : Rat) / 3200000000000000000000), R := ((2147753833303571421687 : Rat) / 800000000000000000000), D0 := ((2147753833303571421687 : Rat) / 800000000000000000000), D1 := ((693773753303571421687 : Rat) / 800000000000000000000), D2 := ((101405833303571421687 : Rat) / 800000000000000000000), D3 := ((7741453303571421687 : Rat) / 800000000000000000000), D4 := ((330067418124999706473 : Rat) / 3200000000000000000000), LB := ((1029712139599459 : Rat) / 2000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2147753833303571421687 : Rat) / 800000000000000000000), R := ((1718343820339285708653 : Rat) / 640000000000000000000), D0 := ((1718343820339285708653 : Rat) / 640000000000000000000), D1 := ((555159756339285708653 : Rat) / 640000000000000000000), D2 := ((81265420339285708653 : Rat) / 640000000000000000000), D3 := ((6333916339285708653 : Rat) / 640000000000000000000), D4 := ((82340912410714212489 : Rat) / 800000000000000000000), LB := ((498550126439401 : Rat) / 1000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1718343820339285708653 : Rat) / 640000000000000000000), R := ((4296211435089285699891 : Rat) / 1600000000000000000000), D0 := ((4296211435089285699891 : Rat) / 1600000000000000000000), D1 := ((1388251275089285699891 : Rat) / 1600000000000000000000), D2 := ((203515435089285699891 : Rat) / 1600000000000000000000), D3 := ((16186675089285699891 : Rat) / 1600000000000000000000), D4 := ((328659881160713993439 : Rat) / 3200000000000000000000), LB := ((12093557713946379 : Rat) / 25000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4296211435089285699891 : Rat) / 1600000000000000000000), R := ((8593126638660714256299 : Rat) / 3200000000000000000000), D0 := ((8593126638660714256299 : Rat) / 3200000000000000000000), D1 := ((2777206318660714256299 : Rat) / 3200000000000000000000), D2 := ((407734638660714256299 : Rat) / 3200000000000000000000), D3 := ((33077118660714256299 : Rat) / 3200000000000000000000), D4 := ((163978056339285568461 : Rat) / 1600000000000000000000), LB := ((9408766456553419 : Rat) / 20000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8593126638660714256299 : Rat) / 3200000000000000000000), R := ((537114400446428569551 : Rat) / 200000000000000000000), D0 := ((537114400446428569551 : Rat) / 200000000000000000000), D1 := ((173619380446428569551 : Rat) / 200000000000000000000), D2 := ((25527400446428569551 : Rat) / 200000000000000000000), D3 := ((2111305446428569551 : Rat) / 200000000000000000000), D4 := ((65450468839285656081 : Rat) / 640000000000000000000), LB := ((9172878264520623 : Rat) / 20000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((537114400446428569551 : Rat) / 200000000000000000000), R := ((8594534175624999969333 : Rat) / 3200000000000000000000), D0 := ((8594534175624999969333 : Rat) / 3200000000000000000000), D1 := ((2778613855624999969333 : Rat) / 3200000000000000000000), D2 := ((409142175624999969333 : Rat) / 3200000000000000000000), D3 := ((34484655624999969333 : Rat) / 3200000000000000000000), D4 := ((20409285982142838993 : Rat) / 200000000000000000000), LB := ((22418243068050847 : Rat) / 50000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8594534175624999969333 : Rat) / 3200000000000000000000), R := ((171904758882142856517 : Rat) / 64000000000000000000), D0 := ((171904758882142856517 : Rat) / 64000000000000000000), D1 := ((55586352482142856517 : Rat) / 64000000000000000000), D2 := ((8196918882142856517 : Rat) / 64000000000000000000), D3 := ((703768482142856517 : Rat) / 64000000000000000000), D4 := ((325844807232142567371 : Rat) / 3200000000000000000000), LB := ((10990174669847641 : Rat) / 25000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((171904758882142856517 : Rat) / 64000000000000000000), R := ((8595941712589285682367 : Rat) / 3200000000000000000000), D0 := ((8595941712589285682367 : Rat) / 3200000000000000000000), D1 := ((2780021392589285682367 : Rat) / 3200000000000000000000), D2 := ((410549712589285682367 : Rat) / 3200000000000000000000), D3 := ((35892192589285682367 : Rat) / 3200000000000000000000), D4 := ((162570519374999855427 : Rat) / 1600000000000000000000), LB := ((21618807368173343 : Rat) / 50000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8595941712589285682367 : Rat) / 3200000000000000000000), R := ((2149161370267857134721 : Rat) / 800000000000000000000), D0 := ((2149161370267857134721 : Rat) / 800000000000000000000), D1 := ((695181290267857134721 : Rat) / 800000000000000000000), D2 := ((102813370267857134721 : Rat) / 800000000000000000000), D3 := ((9148990267857134721 : Rat) / 800000000000000000000), D4 := ((324437270267856854337 : Rat) / 3200000000000000000000), LB := ((4266782395236923 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2149161370267857134721 : Rat) / 800000000000000000000), R := ((8597349249553571395401 : Rat) / 3200000000000000000000), D0 := ((8597349249553571395401 : Rat) / 3200000000000000000000), D1 := ((2781428929553571395401 : Rat) / 3200000000000000000000), D2 := ((411957249553571395401 : Rat) / 3200000000000000000000), D3 := ((37299729553571395401 : Rat) / 3200000000000000000000), D4 := ((16186675089285699891 : Rat) / 160000000000000000000), LB := ((528148998343303 : Rat) / 1250000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8597349249553571395401 : Rat) / 3200000000000000000000), R := ((4299026509017857125959 : Rat) / 1600000000000000000000), D0 := ((4299026509017857125959 : Rat) / 1600000000000000000000), D1 := ((1391066349017857125959 : Rat) / 1600000000000000000000), D2 := ((206330509017857125959 : Rat) / 1600000000000000000000), D3 := ((19001749017857125959 : Rat) / 1600000000000000000000), D4 := ((323029733303571141303 : Rat) / 3200000000000000000000), LB := ((4199049995007309 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4299026509017857125959 : Rat) / 1600000000000000000000), R := ((1719751357303571421687 : Rat) / 640000000000000000000), D0 := ((1719751357303571421687 : Rat) / 640000000000000000000), D1 := ((556567293303571421687 : Rat) / 640000000000000000000), D2 := ((82672957303571421687 : Rat) / 640000000000000000000), D3 := ((7741453303571421687 : Rat) / 640000000000000000000), D4 := ((161162982410714142393 : Rat) / 1600000000000000000000), LB := ((4188416563121189 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1719751357303571421687 : Rat) / 640000000000000000000), R := ((1074932569374999995619 : Rat) / 400000000000000000000), D0 := ((1074932569374999995619 : Rat) / 400000000000000000000), D1 := ((347942529374999995619 : Rat) / 400000000000000000000), D2 := ((51758569374999995619 : Rat) / 400000000000000000000), D3 := ((4926379374999995619 : Rat) / 400000000000000000000), D4 := ((321622196339285428269 : Rat) / 3200000000000000000000), LB := ((4193352233962111 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1074932569374999995619 : Rat) / 400000000000000000000), R := ((8600164323482142821469 : Rat) / 3200000000000000000000), D0 := ((8600164323482142821469 : Rat) / 3200000000000000000000), D1 := ((2784244003482142821469 : Rat) / 3200000000000000000000), D2 := ((414772323482142821469 : Rat) / 3200000000000000000000), D3 := ((40114803482142821469 : Rat) / 3200000000000000000000), D4 := ((40114803482142821469 : Rat) / 400000000000000000000), LB := ((1316849360496683 : Rat) / 3125000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8600164323482142821469 : Rat) / 3200000000000000000000), R := ((4300434045982142838993 : Rat) / 1600000000000000000000), D0 := ((4300434045982142838993 : Rat) / 1600000000000000000000), D1 := ((1392473885982142838993 : Rat) / 1600000000000000000000), D2 := ((207738045982142838993 : Rat) / 1600000000000000000000), D3 := ((20409285982142838993 : Rat) / 1600000000000000000000), D4 := ((64042931874999943047 : Rat) / 640000000000000000000), LB := ((8500350149747149 : Rat) / 20000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4300434045982142838993 : Rat) / 1600000000000000000000), R := ((8601571860446428534503 : Rat) / 3200000000000000000000), D0 := ((8601571860446428534503 : Rat) / 3200000000000000000000), D1 := ((2785651540446428534503 : Rat) / 3200000000000000000000), D2 := ((416179860446428534503 : Rat) / 3200000000000000000000), D3 := ((41522340446428534503 : Rat) / 3200000000000000000000), D4 := ((159755445446428429359 : Rat) / 1600000000000000000000), LB := ((2151092680492961 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8601571860446428534503 : Rat) / 3200000000000000000000), R := ((430113781446428569551 : Rat) / 160000000000000000000), D0 := ((430113781446428569551 : Rat) / 160000000000000000000), D1 := ((139317765446428569551 : Rat) / 160000000000000000000), D2 := ((20844181446428569551 : Rat) / 160000000000000000000), D3 := ((2111305446428569551 : Rat) / 160000000000000000000), D4 := ((318807122410714002201 : Rat) / 3200000000000000000000), LB := ((10925027472688531 : Rat) / 25000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((430113781446428569551 : Rat) / 160000000000000000000), R := ((8602979397410714247537 : Rat) / 3200000000000000000000), D0 := ((8602979397410714247537 : Rat) / 3200000000000000000000), D1 := ((2787059077410714247537 : Rat) / 3200000000000000000000), D2 := ((417587397410714247537 : Rat) / 3200000000000000000000), D3 := ((42929877410714247537 : Rat) / 3200000000000000000000), D4 := ((79525838482142786421 : Rat) / 800000000000000000000), LB := ((445371455389143 : Rat) / 1000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8602979397410714247537 : Rat) / 3200000000000000000000), R := ((4301841582946428552027 : Rat) / 1600000000000000000000), D0 := ((4301841582946428552027 : Rat) / 1600000000000000000000), D1 := ((1393881422946428552027 : Rat) / 1600000000000000000000), D2 := ((209145582946428552027 : Rat) / 1600000000000000000000), D3 := ((21816822946428552027 : Rat) / 1600000000000000000000), D4 := ((317399585446428289167 : Rat) / 3200000000000000000000), LB := ((4553359071483021 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4301841582946428552027 : Rat) / 1600000000000000000000), R := ((8604386934374999960571 : Rat) / 3200000000000000000000), D0 := ((8604386934374999960571 : Rat) / 3200000000000000000000), D1 := ((2788466614374999960571 : Rat) / 3200000000000000000000), D2 := ((418994934374999960571 : Rat) / 3200000000000000000000), D3 := ((44337414374999960571 : Rat) / 3200000000000000000000), D4 := ((6333916339285708653 : Rat) / 64000000000000000000), LB := ((46690079829336817 : Rat) / 100000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8604386934374999960571 : Rat) / 3200000000000000000000), R := ((134454542232142856517 : Rat) / 50000000000000000000), D0 := ((134454542232142856517 : Rat) / 50000000000000000000), D1 := ((43580787232142856517 : Rat) / 50000000000000000000), D2 := ((6557792232142856517 : Rat) / 50000000000000000000), D3 := ((703768482142856517 : Rat) / 50000000000000000000), D4 := ((315992048482142576133 : Rat) / 3200000000000000000000), LB := ((1500226611928987 : Rat) / 3125000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((134454542232142856517 : Rat) / 50000000000000000000), R := ((1721158894267857134721 : Rat) / 640000000000000000000), D0 := ((1721158894267857134721 : Rat) / 640000000000000000000), D1 := ((557974830267857134721 : Rat) / 640000000000000000000), D2 := ((84080494267857134721 : Rat) / 640000000000000000000), D3 := ((9148990267857134721 : Rat) / 640000000000000000000), D4 := ((4926379374999995619 : Rat) / 50000000000000000000), LB := ((989714979943379 : Rat) / 2000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1721158894267857134721 : Rat) / 640000000000000000000), R := ((4303249119910714265061 : Rat) / 1600000000000000000000), D0 := ((4303249119910714265061 : Rat) / 1600000000000000000000), D1 := ((1395288959910714265061 : Rat) / 1600000000000000000000), D2 := ((210553119910714265061 : Rat) / 1600000000000000000000), D3 := ((23224359910714265061 : Rat) / 1600000000000000000000), D4 := ((314584511517856863099 : Rat) / 3200000000000000000000), LB := ((5112621946600227 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4303249119910714265061 : Rat) / 1600000000000000000000), R := ((8607202008303571386639 : Rat) / 3200000000000000000000), D0 := ((8607202008303571386639 : Rat) / 3200000000000000000000), D1 := ((2791281688303571386639 : Rat) / 3200000000000000000000), D2 := ((421810008303571386639 : Rat) / 3200000000000000000000), D3 := ((47152488303571386639 : Rat) / 3200000000000000000000), D4 := ((156940371517857003291 : Rat) / 1600000000000000000000), LB := ((1323232869567259 : Rat) / 2500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8607202008303571386639 : Rat) / 3200000000000000000000), R := ((2151976444196428560789 : Rat) / 800000000000000000000), D0 := ((2151976444196428560789 : Rat) / 800000000000000000000), D1 := ((697996364196428560789 : Rat) / 800000000000000000000), D2 := ((105628444196428560789 : Rat) / 800000000000000000000), D3 := ((11964064196428560789 : Rat) / 800000000000000000000), D4 := ((62635394910714230013 : Rat) / 640000000000000000000), LB := ((219582764739501 : Rat) / 400000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2151976444196428560789 : Rat) / 800000000000000000000), R := ((8608609545267857099673 : Rat) / 3200000000000000000000), D0 := ((8608609545267857099673 : Rat) / 3200000000000000000000), D1 := ((2792689225267857099673 : Rat) / 3200000000000000000000), D2 := ((423217545267857099673 : Rat) / 3200000000000000000000), D3 := ((48560025267857099673 : Rat) / 3200000000000000000000), D4 := ((78118301517857073387 : Rat) / 800000000000000000000), LB := ((2851300469701723 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8608609545267857099673 : Rat) / 3200000000000000000000), R := ((860931331374999995619 : Rat) / 320000000000000000000), D0 := ((860931331374999995619 : Rat) / 320000000000000000000), D1 := ((279339299374999995619 : Rat) / 320000000000000000000), D2 := ((42392131374999995619 : Rat) / 320000000000000000000), D3 := ((4926379374999995619 : Rat) / 320000000000000000000), D4 := ((311769437589285437031 : Rat) / 3200000000000000000000), LB := ((5932093465511601 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((860931331374999995619 : Rat) / 320000000000000000000), R := ((8610017082232142812707 : Rat) / 3200000000000000000000), D0 := ((8610017082232142812707 : Rat) / 3200000000000000000000), D1 := ((2794096762232142812707 : Rat) / 3200000000000000000000), D2 := ((424625082232142812707 : Rat) / 3200000000000000000000), D3 := ((49967562232142812707 : Rat) / 3200000000000000000000), D4 := ((155532834553571290257 : Rat) / 1600000000000000000000), LB := ((6178113677782759 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((8610017082232142812707 : Rat) / 3200000000000000000000), R := ((1076340106339285708653 : Rat) / 400000000000000000000), D0 := ((1076340106339285708653 : Rat) / 400000000000000000000), D1 := ((349350066339285708653 : Rat) / 400000000000000000000), D2 := ((53166106339285708653 : Rat) / 400000000000000000000), D3 := ((6333916339285708653 : Rat) / 400000000000000000000), D4 := ((310361900624999723997 : Rat) / 3200000000000000000000), LB := ((3220364508892959 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1076340106339285708653 : Rat) / 400000000000000000000), R := ((4306064193839285691129 : Rat) / 1600000000000000000000), D0 := ((4306064193839285691129 : Rat) / 1600000000000000000000), D1 := ((1398104033839285691129 : Rat) / 1600000000000000000000), D2 := ((213368193839285691129 : Rat) / 1600000000000000000000), D3 := ((26039433839285691129 : Rat) / 1600000000000000000000), D4 := ((7741453303571421687 : Rat) / 80000000000000000000), LB := ((928112605345921 : Rat) / 31250000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4306064193839285691129 : Rat) / 1600000000000000000000), R := ((2153383981160714273823 : Rat) / 800000000000000000000), D0 := ((2153383981160714273823 : Rat) / 800000000000000000000), D1 := ((699403901160714273823 : Rat) / 800000000000000000000), D2 := ((107035981160714273823 : Rat) / 800000000000000000000), D3 := ((13371601160714273823 : Rat) / 800000000000000000000), D4 := ((154125297589285577223 : Rat) / 1600000000000000000000), LB := ((9087701489474131 : Rat) / 100000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2153383981160714273823 : Rat) / 800000000000000000000), R := ((4307471730803571404163 : Rat) / 1600000000000000000000), D0 := ((4307471730803571404163 : Rat) / 1600000000000000000000), D1 := ((1399511570803571404163 : Rat) / 1600000000000000000000), D2 := ((214775730803571404163 : Rat) / 1600000000000000000000), D3 := ((27446970803571404163 : Rat) / 1600000000000000000000), D4 := ((76710764553571360353 : Rat) / 800000000000000000000), LB := ((1985025252494721 : Rat) / 12500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4307471730803571404163 : Rat) / 1600000000000000000000), R := ((107704387482142856517 : Rat) / 40000000000000000000), D0 := ((107704387482142856517 : Rat) / 40000000000000000000), D1 := ((35005383482142856517 : Rat) / 40000000000000000000), D2 := ((5386987482142856517 : Rat) / 40000000000000000000), D3 := ((703768482142856517 : Rat) / 40000000000000000000), D4 := ((152717760624999864189 : Rat) / 1600000000000000000000), LB := ((2335306616825239 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((107704387482142856517 : Rat) / 40000000000000000000), R := ((4308879267767857117197 : Rat) / 1600000000000000000000), D0 := ((4308879267767857117197 : Rat) / 1600000000000000000000), D1 := ((1400919107767857117197 : Rat) / 1600000000000000000000), D2 := ((216183267767857117197 : Rat) / 1600000000000000000000), D3 := ((28854507767857117197 : Rat) / 1600000000000000000000), D4 := ((19001749017857125959 : Rat) / 200000000000000000000), LB := ((19694985446711 : Rat) / 62500000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4308879267767857117197 : Rat) / 1600000000000000000000), R := ((2154791518124999986857 : Rat) / 800000000000000000000), D0 := ((2154791518124999986857 : Rat) / 800000000000000000000), D1 := ((700811438124999986857 : Rat) / 800000000000000000000), D2 := ((108443518124999986857 : Rat) / 800000000000000000000), D3 := ((14779138124999986857 : Rat) / 800000000000000000000), D4 := ((30262044732142830231 : Rat) / 320000000000000000000), LB := ((40362696436813117 : Rat) / 100000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2154791518124999986857 : Rat) / 800000000000000000000), R := ((4310286804732142830231 : Rat) / 1600000000000000000000), D0 := ((4310286804732142830231 : Rat) / 1600000000000000000000), D1 := ((1402326644732142830231 : Rat) / 1600000000000000000000), D2 := ((217590804732142830231 : Rat) / 1600000000000000000000), D3 := ((30262044732142830231 : Rat) / 1600000000000000000000), D4 := ((75303227589285647319 : Rat) / 800000000000000000000), LB := ((2495553479936463 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4310286804732142830231 : Rat) / 1600000000000000000000), R := ((1077747643303571421687 : Rat) / 400000000000000000000), D0 := ((1077747643303571421687 : Rat) / 400000000000000000000), D1 := ((350757603303571421687 : Rat) / 400000000000000000000), D2 := ((54573643303571421687 : Rat) / 400000000000000000000), D3 := ((7741453303571421687 : Rat) / 400000000000000000000), D4 := ((149902686696428438121 : Rat) / 1600000000000000000000), LB := ((6016302347648939 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1077747643303571421687 : Rat) / 400000000000000000000), R := ((862338868339285708653 : Rat) / 320000000000000000000), D0 := ((862338868339285708653 : Rat) / 320000000000000000000), D1 := ((280746836339285708653 : Rat) / 320000000000000000000), D2 := ((43799668339285708653 : Rat) / 320000000000000000000), D3 := ((6333916339285708653 : Rat) / 320000000000000000000), D4 := ((37299729553571395401 : Rat) / 400000000000000000000), LB := ((7112456991920091 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((862338868339285708653 : Rat) / 320000000000000000000), R := ((2156199055089285699891 : Rat) / 800000000000000000000), D0 := ((2156199055089285699891 : Rat) / 800000000000000000000), D1 := ((702218975089285699891 : Rat) / 800000000000000000000), D2 := ((109851055089285699891 : Rat) / 800000000000000000000), D3 := ((16186675089285699891 : Rat) / 800000000000000000000), D4 := ((148495149732142725087 : Rat) / 1600000000000000000000), LB := ((4140090347299341 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2156199055089285699891 : Rat) / 800000000000000000000), R := ((4313101878660714256299 : Rat) / 1600000000000000000000), D0 := ((4313101878660714256299 : Rat) / 1600000000000000000000), D1 := ((1405141718660714256299 : Rat) / 1600000000000000000000), D2 := ((220405878660714256299 : Rat) / 1600000000000000000000), D3 := ((33077118660714256299 : Rat) / 1600000000000000000000), D4 := ((14779138124999986857 : Rat) / 160000000000000000000), LB := ((4760046019106623 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4313101878660714256299 : Rat) / 1600000000000000000000), R := ((269612852946428569551 : Rat) / 100000000000000000000), D0 := ((269612852946428569551 : Rat) / 100000000000000000000), D1 := ((87865342946428569551 : Rat) / 100000000000000000000), D2 := ((13819352946428569551 : Rat) / 100000000000000000000), D3 := ((2111305446428569551 : Rat) / 100000000000000000000), D4 := ((147087612767857012053 : Rat) / 1600000000000000000000), LB := ((5416409276697287 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((269612852946428569551 : Rat) / 100000000000000000000), R := ((4314509415624999969333 : Rat) / 1600000000000000000000), D0 := ((4314509415624999969333 : Rat) / 1600000000000000000000), D1 := ((1406549255624999969333 : Rat) / 1600000000000000000000), D2 := ((221813415624999969333 : Rat) / 1600000000000000000000), D3 := ((34484655624999969333 : Rat) / 1600000000000000000000), D4 := ((9148990267857134721 : Rat) / 100000000000000000000), LB := ((1527374611288157 : Rat) / 1250000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((4314509415624999969333 : Rat) / 1600000000000000000000), R := ((86304263682142856517 : Rat) / 32000000000000000000), D0 := ((86304263682142856517 : Rat) / 32000000000000000000), D1 := ((28145060482142856517 : Rat) / 32000000000000000000), D2 := ((4450343682142856517 : Rat) / 32000000000000000000), D3 := ((703768482142856517 : Rat) / 32000000000000000000), D4 := ((145680075803571299019 : Rat) / 1600000000000000000000), LB := ((6839636497156243 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((86304263682142856517 : Rat) / 32000000000000000000), R := ((1079155180267857134721 : Rat) / 400000000000000000000), D0 := ((1079155180267857134721 : Rat) / 400000000000000000000), D1 := ((352165140267857134721 : Rat) / 400000000000000000000), D2 := ((55981180267857134721 : Rat) / 400000000000000000000), D3 := ((9148990267857134721 : Rat) / 400000000000000000000), D4 := ((72488153660714221251 : Rat) / 800000000000000000000), LB := ((24548503558141643 : Rat) / 100000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1079155180267857134721 : Rat) / 400000000000000000000), R := ((2159014129017857125959 : Rat) / 800000000000000000000), D0 := ((2159014129017857125959 : Rat) / 800000000000000000000), D1 := ((705034049017857125959 : Rat) / 800000000000000000000), D2 := ((112666129017857125959 : Rat) / 800000000000000000000), D3 := ((19001749017857125959 : Rat) / 800000000000000000000), D4 := ((35892192589285682367 : Rat) / 400000000000000000000), LB := ((360217621810377 : Rat) / 625000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2159014129017857125959 : Rat) / 800000000000000000000), R := ((539929474374999995619 : Rat) / 200000000000000000000), D0 := ((539929474374999995619 : Rat) / 200000000000000000000), D1 := ((176434454374999995619 : Rat) / 200000000000000000000), D2 := ((28342474374999995619 : Rat) / 200000000000000000000), D3 := ((4926379374999995619 : Rat) / 200000000000000000000), D4 := ((71080616696428508217 : Rat) / 800000000000000000000), LB := ((1875842785147741 : Rat) / 2000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((539929474374999995619 : Rat) / 200000000000000000000), R := ((2160421665982142838993 : Rat) / 800000000000000000000), D0 := ((2160421665982142838993 : Rat) / 800000000000000000000), D1 := ((706441585982142838993 : Rat) / 800000000000000000000), D2 := ((114073665982142838993 : Rat) / 800000000000000000000), D3 := ((20409285982142838993 : Rat) / 800000000000000000000), D4 := ((703768482142856517 : Rat) / 8000000000000000000), LB := ((532306008244543 : Rat) / 400000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2160421665982142838993 : Rat) / 800000000000000000000), R := ((216112543446428569551 : Rat) / 80000000000000000000), D0 := ((216112543446428569551 : Rat) / 80000000000000000000), D1 := ((70714535446428569551 : Rat) / 80000000000000000000), D2 := ((11477743446428569551 : Rat) / 80000000000000000000), D3 := ((2111305446428569551 : Rat) / 80000000000000000000), D4 := ((69673079732142795183 : Rat) / 800000000000000000000), LB := ((8777282582764223 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((216112543446428569551 : Rat) / 80000000000000000000), R := ((2161829202946428552027 : Rat) / 800000000000000000000), D0 := ((2161829202946428552027 : Rat) / 800000000000000000000), D1 := ((707849122946428552027 : Rat) / 800000000000000000000), D2 := ((115481202946428552027 : Rat) / 800000000000000000000), D3 := ((21816822946428552027 : Rat) / 800000000000000000000), D4 := ((34484655624999969333 : Rat) / 400000000000000000000), LB := ((442518211025833 : Rat) / 200000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((2161829202946428552027 : Rat) / 800000000000000000000), R := ((67579155357142856517 : Rat) / 25000000000000000000), D0 := ((67579155357142856517 : Rat) / 25000000000000000000), D1 := ((22142277857142856517 : Rat) / 25000000000000000000), D2 := ((3630780357142856517 : Rat) / 25000000000000000000), D3 := ((703768482142856517 : Rat) / 25000000000000000000), D4 := ((68265542767857082149 : Rat) / 800000000000000000000), LB := ((135139113768723 : Rat) / 50000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((67579155357142856517 : Rat) / 25000000000000000000), R := ((1081970254196428560789 : Rat) / 400000000000000000000), D0 := ((1081970254196428560789 : Rat) / 400000000000000000000), D1 := ((354980214196428560789 : Rat) / 400000000000000000000), D2 := ((58796254196428560789 : Rat) / 400000000000000000000), D3 := ((11964064196428560789 : Rat) / 400000000000000000000), D4 := ((2111305446428569551 : Rat) / 25000000000000000000), LB := ((6927024973432117 : Rat) / 10000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1081970254196428560789 : Rat) / 400000000000000000000), R := ((541337011339285708653 : Rat) / 200000000000000000000), D0 := ((541337011339285708653 : Rat) / 200000000000000000000), D1 := ((177841991339285708653 : Rat) / 200000000000000000000), D2 := ((29750011339285708653 : Rat) / 200000000000000000000), D3 := ((6333916339285708653 : Rat) / 200000000000000000000), D4 := ((33077118660714256299 : Rat) / 400000000000000000000), LB := ((1155468117842659 : Rat) / 625000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((541337011339285708653 : Rat) / 200000000000000000000), R := ((1083377791160714273823 : Rat) / 400000000000000000000), D0 := ((1083377791160714273823 : Rat) / 400000000000000000000), D1 := ((356387751160714273823 : Rat) / 400000000000000000000), D2 := ((60203791160714273823 : Rat) / 400000000000000000000), D3 := ((13371601160714273823 : Rat) / 400000000000000000000), D4 := ((16186675089285699891 : Rat) / 200000000000000000000), LB := ((393455976844731 : Rat) / 125000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((1083377791160714273823 : Rat) / 400000000000000000000), R := ((54204077982142856517 : Rat) / 20000000000000000000), D0 := ((54204077982142856517 : Rat) / 20000000000000000000), D1 := ((17854575982142856517 : Rat) / 20000000000000000000), D2 := ((3045377982142856517 : Rat) / 20000000000000000000), D3 := ((703768482142856517 : Rat) / 20000000000000000000), D4 := ((6333916339285708653 : Rat) / 80000000000000000000), LB := ((2297621065229627 : Rat) / 500000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((54204077982142856517 : Rat) / 20000000000000000000), R := ((542744548303571421687 : Rat) / 200000000000000000000), D0 := ((542744548303571421687 : Rat) / 200000000000000000000), D1 := ((179249528303571421687 : Rat) / 200000000000000000000), D2 := ((31157548303571421687 : Rat) / 200000000000000000000), D3 := ((7741453303571421687 : Rat) / 200000000000000000000), D4 := ((7741453303571421687 : Rat) / 100000000000000000000), LB := ((5865423566593919 : Rat) / 5000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((542744548303571421687 : Rat) / 200000000000000000000), R := ((135862079196428569551 : Rat) / 50000000000000000000), D0 := ((135862079196428569551 : Rat) / 50000000000000000000), D1 := ((44988324196428569551 : Rat) / 50000000000000000000), D2 := ((7965329196428569551 : Rat) / 50000000000000000000), D3 := ((2111305446428569551 : Rat) / 50000000000000000000), D4 := ((14779138124999986857 : Rat) / 200000000000000000000), LB := ((977617017504473 : Rat) / 200000000000000000) }
]

def block000RightChunk000L : Rat := ((90863975446428571429 : Rat) / 50000000000000000000)
def block000RightChunk000R : Rat := ((135862079196428569551 : Rat) / 50000000000000000000)

def block000RightChunk000Certificate : Bool :=
  allBoxesValid block000RightChunk000 &&
  coversFromBool block000RightChunk000 block000RightChunk000L block000RightChunk000R

theorem block000RightChunk000Certificate_eq_true :
    block000RightChunk000Certificate = true := by
  native_decide

def block000RightChunk001 : List RatBox := [
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((135862079196428569551 : Rat) / 50000000000000000000), R := ((544152085267857134721 : Rat) / 200000000000000000000), D0 := ((544152085267857134721 : Rat) / 200000000000000000000), D1 := ((180657065267857134721 : Rat) / 200000000000000000000), D2 := ((32565085267857134721 : Rat) / 200000000000000000000), D3 := ((9148990267857134721 : Rat) / 200000000000000000000), D4 := ((703768482142856517 : Rat) / 10000000000000000000), LB := ((9309200937978379 : Rat) / 1000000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((544152085267857134721 : Rat) / 200000000000000000000), R := ((272427926874999995619 : Rat) / 100000000000000000000), D0 := ((272427926874999995619 : Rat) / 100000000000000000000), D1 := ((90680416874999995619 : Rat) / 100000000000000000000), D2 := ((16634426874999995619 : Rat) / 100000000000000000000), D3 := ((4926379374999995619 : Rat) / 100000000000000000000), D4 := ((13371601160714273823 : Rat) / 200000000000000000000), LB := ((906560172044199 : Rat) / 62500000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((272427926874999995619 : Rat) / 100000000000000000000), R := ((34141461919642856517 : Rat) / 12500000000000000000), D0 := ((34141461919642856517 : Rat) / 12500000000000000000), D1 := ((11423023169642856517 : Rat) / 12500000000000000000), D2 := ((2167274419642856517 : Rat) / 12500000000000000000), D3 := ((703768482142856517 : Rat) / 12500000000000000000), D4 := ((6333916339285708653 : Rat) / 100000000000000000000), LB := ((2668505721022757 : Rat) / 250000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((34141461919642856517 : Rat) / 12500000000000000000), R := ((27453923232142856517 : Rat) / 10000000000000000000), D0 := ((27453923232142856517 : Rat) / 10000000000000000000), D1 := ((9279172232142856517 : Rat) / 10000000000000000000), D2 := ((1874573232142856517 : Rat) / 10000000000000000000), D3 := ((703768482142856517 : Rat) / 10000000000000000000), D4 := ((703768482142856517 : Rat) / 12500000000000000000), LB := ((313775373733699 : Rat) / 50000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((27453923232142856517 : Rat) / 10000000000000000000), R := ((68986692321428569551 : Rat) / 25000000000000000000), D0 := ((68986692321428569551 : Rat) / 25000000000000000000), D1 := ((23549814821428569551 : Rat) / 25000000000000000000), D2 := ((5038317321428569551 : Rat) / 25000000000000000000), D3 := ((2111305446428569551 : Rat) / 25000000000000000000), D4 := ((2111305446428569551 : Rat) / 50000000000000000000), LB := ((13146770908156441 : Rat) / 250000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((68986692321428569551 : Rat) / 25000000000000000000), R := ((17422615200892856517 : Rat) / 6250000000000000000), D0 := ((17422615200892856517 : Rat) / 6250000000000000000), D1 := ((6063395825892856517 : Rat) / 6250000000000000000), D2 := ((1435521450892856517 : Rat) / 6250000000000000000), D3 := ((703768482142856517 : Rat) / 6250000000000000000), D4 := ((703768482142856517 : Rat) / 25000000000000000000), LB := ((9659398058854907 : Rat) / 100000000000000000) },
  { w1 := ((22270102833143817 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((5906017035486959 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17422615200892856517 : Rat) / 6250000000000000000), L := ((17422615200892856517 : Rat) / 6250000000000000000), R := ((112699 : Rat) / 40000), D0 := ((112699 : Rat) / 40000), D1 := ((9999999 : Rat) / 10000000), D2 := ((12977 : Rat) / 50000), D3 := ((5698381 : Rat) / 40000000), D4 := ((186603549107143483 : Rat) / 6250000000000000000), LB := ((33246965304011 : Rat) / 31250000000000000) }
]

def block000RightChunk001L : Rat := ((135862079196428569551 : Rat) / 50000000000000000000)
def block000RightChunk001R : Rat := ((112699 : Rat) / 40000)

def block000RightChunk001Certificate : Bool :=
  allBoxesValid block000RightChunk001 &&
  coversFromBool block000RightChunk001 block000RightChunk001L block000RightChunk001R

theorem block000RightChunk001Certificate_eq_true :
    block000RightChunk001Certificate = true := by
  native_decide

def block000RightChainCertificate : Bool :=
  decide (
    block000RightL = ((90863975446428571429 : Rat) / 50000000000000000000) /\
    ((135862079196428569551 : Rat) / 50000000000000000000) = ((135862079196428569551 : Rat) / 50000000000000000000) /\
    ((112699 : Rat) / 40000) = block000RightR)

theorem block000RightChainCertificate_eq_true :
    block000RightChainCertificate = true := by
  native_decide

def block000LeftBoxCount : Nat := boxCount block000LeftBoxes
def block000RightBoxCount : Nat := 107

def block000_rational_certificate : Prop :=
    block000LeftCertificate = true /\
    block000RightChainCertificate = true /\
    block000RightChunk000Certificate = true /\
    block000RightChunk001Certificate = true

theorem block000_rational_certificate_proof :
    block000_rational_certificate := by
  exact ⟨block000LeftCertificate_eq_true, block000RightChainCertificate_eq_true, block000RightChunk000Certificate_eq_true, block000RightChunk001Certificate_eq_true⟩

end Block000
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block000

open Set

def block000W1 : Rat := ((22270102833143817 : Rat) / 10000000000000000)
def block000W2 : Rat := (0 : Rat)
def block000W3 : Rat := (0 : Rat)
def block000W4 : Rat := ((5906017035486959 : Rat) / 20000000000000000)
def block000S1 : Rat := ((18174751 : Rat) / 10000000)
def block000S2 : Rat := ((511587 : Rat) / 200000)
def block000S3 : Rat := ((107000619 : Rat) / 40000000)
def block000S4 : Rat := ((17422615200892856517 : Rat) / 6250000000000000000)

noncomputable def block000V (y : ℝ) : ℝ :=
  ratPotential block000W1 block000W2 block000W3 block000W4 block000S1 block000S2 block000S3 block000S4 y

def block000LeftParamsCertificate : Bool :=
  allBoxesSameParams block000LeftBoxes block000W1 block000W2 block000W3 block000W4 block000S1 block000S2 block000S3 block000S4

theorem block000LeftParamsCertificate_eq_true :
    block000LeftParamsCertificate = true := by
  native_decide

theorem block000_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block000LeftL : ℝ) (block000LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block000S1 : ℝ))
    (hy2ne : y ≠ (block000S2 : ℝ))
    (hy3ne : y ≠ (block000S3 : ℝ))
    (hy4ne : y ≠ (block000S4 : ℝ)) :
    0 < block000V y := by
  have hcert := block000LeftCertificate_eq_true
  unfold block000LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block000LeftBoxes) (lo := block000LeftL) (hi := block000LeftR)
    (w1 := block000W1) (w2 := block000W2) (w3 := block000W3) (w4 := block000W4)
    (s1 := block000S1) (s2 := block000S2) (s3 := block000S3) (s4 := block000S4)
    hboxes hcover block000LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block000RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block000RightChunk000 block000W1 block000W2 block000W3 block000W4 block000S1 block000S2 block000S3 block000S4

theorem block000RightChunk000ParamsCertificate_eq_true :
    block000RightChunk000ParamsCertificate = true := by
  native_decide

theorem block000_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block000RightChunk000L : ℝ) (block000RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block000S1 : ℝ))
    (hy2ne : y ≠ (block000S2 : ℝ))
    (hy3ne : y ≠ (block000S3 : ℝ))
    (hy4ne : y ≠ (block000S4 : ℝ)) :
    0 < block000V y := by
  have hcert := block000RightChunk000Certificate_eq_true
  unfold block000RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block000RightChunk000) (lo := block000RightChunk000L) (hi := block000RightChunk000R)
    (w1 := block000W1) (w2 := block000W2) (w3 := block000W3) (w4 := block000W4)
    (s1 := block000S1) (s2 := block000S2) (s3 := block000S3) (s4 := block000S4)
    hboxes hcover block000RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block000RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block000RightChunk001 block000W1 block000W2 block000W3 block000W4 block000S1 block000S2 block000S3 block000S4

theorem block000RightChunk001ParamsCertificate_eq_true :
    block000RightChunk001ParamsCertificate = true := by
  native_decide

theorem block000_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block000RightChunk001L : ℝ) (block000RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block000S1 : ℝ))
    (hy2ne : y ≠ (block000S2 : ℝ))
    (hy3ne : y ≠ (block000S3 : ℝ))
    (hy4ne : y ≠ (block000S4 : ℝ)) :
    0 < block000V y := by
  have hcert := block000RightChunk001Certificate_eq_true
  unfold block000RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block000RightChunk001) (lo := block000RightChunk001L) (hi := block000RightChunk001R)
    (w1 := block000W1) (w2 := block000W2) (w3 := block000W3) (w4 := block000W4)
    (s1 := block000S1) (s2 := block000S2) (s3 := block000S3) (s4 := block000S4)
    hboxes hcover block000RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block000_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block000RightL : ℝ) (block000RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block000S1 : ℝ))
    (hy2ne : y ≠ (block000S2 : ℝ))
    (hy3ne : y ≠ (block000S3 : ℝ))
    (hy4ne : y ≠ (block000S4 : ℝ)) :
    0 < block000V y := by
  by_cases h0 : y ≤ (block000RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block000RightChunk000L : ℝ) (block000RightChunk000R : ℝ) := by
      have hL : (block000RightChunk000L : ℝ) = (block000RightL : ℝ) := by
        norm_num [block000RightChunk000L, block000RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block000_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block000RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block000RightChunk001L : ℝ) = (block000RightChunk000R : ℝ) := by
      norm_num [block000RightChunk001L, block000RightChunk000R]
    have hR : (block000RightChunk001R : ℝ) = (block000RightR : ℝ) := by
      norm_num [block000RightChunk001R, block000RightR]
    have hyc : y ∈ Icc (block000RightChunk001L : ℝ) (block000RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block000_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block000_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block000LeftL : ℝ) (block000LeftR : ℝ) →
    y ≠ 0 → y ≠ (block000S1 : ℝ) → y ≠ (block000S2 : ℝ) →
    y ≠ (block000S3 : ℝ) → y ≠ (block000S4 : ℝ) → 0 < block000V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block000RightL : ℝ) (block000RightR : ℝ) →
    y ≠ 0 → y ≠ (block000S1 : ℝ) → y ≠ (block000S2 : ℝ) →
    y ≠ (block000S3 : ℝ) → y ≠ (block000S4 : ℝ) → 0 < block000V y)

theorem block000_reallog_certificate_proof :
    block000_reallog_certificate := by
  exact ⟨block000_left_V_pos, block000_right_V_pos⟩

end Block000
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block000.block000V
#check Erdos1038Lean.M1817475.Block000.block000_left_V_pos
#check Erdos1038Lean.M1817475.Block000.block000_right_V_pos
#check Erdos1038Lean.M1817475.Block000.block000_reallog_certificate_proof
