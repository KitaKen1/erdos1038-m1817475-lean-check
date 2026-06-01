/-
Self-contained Lean4Web paste file.
Block 1 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block001

def block001LeftL : Rat := ((20427100446428571429 : Rat) / 25000000000000000000)
def block001LeftR : Rat := ((40863975446428571429 : Rat) / 50000000000000000000)
def block001RightL : Rat := ((45427100446428571429 : Rat) / 25000000000000000000)
def block001RightR : Rat := ((140863975446428571429 : Rat) / 50000000000000000000)

def block001LeftBoxes : List RatBox := [
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((20427100446428571429 : Rat) / 25000000000000000000), R := ((40863975446428571429 : Rat) / 50000000000000000000), D0 := ((40863975446428571429 : Rat) / 50000000000000000000), D1 := ((25009777053571428571 : Rat) / 25000000000000000000), D2 := ((43521274553571428571 : Rat) / 25000000000000000000), D3 := ((46448286428571428571 : Rat) / 25000000000000000000), D4 := ((50358110357142854591 : Rat) / 25000000000000000000), LB := ((11044369959227057 : Rat) / 500000000000000000) }
]

def block001LeftCertificate : Bool :=
  allBoxesValid block001LeftBoxes &&
  coversFromBool block001LeftBoxes block001LeftL block001LeftR

theorem block001LeftCertificate_eq_true :
    block001LeftCertificate = true := by
  native_decide

def block001RightChunk000 : List RatBox := [
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((45427100446428571429 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((9777053571428571 : Rat) / 25000000000000000000), D2 := ((18521274553571428571 : Rat) / 25000000000000000000), D3 := ((21448286428571428571 : Rat) / 25000000000000000000), D4 := ((25358110357142854591 : Rat) / 25000000000000000000), LB := ((31276173585941 : Rat) / 312500000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((1267416665178571301 : Rat) / 1250000000000000000), LB := ((1768874210528323 : Rat) / 500000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((341841790178571301 : Rat) / 1250000000000000000), LB := ((16294923556533099 : Rat) / 10000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((274614749196428571429 : Rat) / 100000000000000000000), D0 := ((274614749196428571429 : Rat) / 100000000000000000000), D1 := ((92867239196428571429 : Rat) / 100000000000000000000), D2 := ((18821249196428571429 : Rat) / 100000000000000000000), D3 := ((7113201696428571429 : Rat) / 100000000000000000000), D4 := ((195491196428571301 : Rat) / 1250000000000000000), LB := ((692245860713527 : Rat) / 1250000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((274614749196428571429 : Rat) / 100000000000000000000), R := ((556342700089285714287 : Rat) / 200000000000000000000), D0 := ((556342700089285714287 : Rat) / 200000000000000000000), D1 := ((192847680089285714287 : Rat) / 200000000000000000000), D2 := ((44755700089285714287 : Rat) / 200000000000000000000), D3 := ((21339605089285714287 : Rat) / 200000000000000000000), D4 := ((8526094017857132651 : Rat) / 100000000000000000000), LB := ((2623246670630499 : Rat) / 20000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((556342700089285714287 : Rat) / 200000000000000000000), R := ((2232484002053571428577 : Rat) / 800000000000000000000), D0 := ((2232484002053571428577 : Rat) / 800000000000000000000), D1 := ((778503922053571428577 : Rat) / 800000000000000000000), D2 := ((186136002053571428577 : Rat) / 800000000000000000000), D3 := ((92471622053571428577 : Rat) / 800000000000000000000), D4 := ((9938986339285693873 : Rat) / 200000000000000000000), LB := ((3128074449577531 : Rat) / 25000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2232484002053571428577 : Rat) / 800000000000000000000), R := ((1119798601875000000003 : Rat) / 400000000000000000000), D0 := ((1119798601875000000003 : Rat) / 400000000000000000000), D1 := ((392808561875000000003 : Rat) / 400000000000000000000), D2 := ((96624601875000000003 : Rat) / 400000000000000000000), D3 := ((49792411875000000003 : Rat) / 400000000000000000000), D4 := ((32642743660714204063 : Rat) / 800000000000000000000), LB := ((3526435510832171 : Rat) / 100000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1119798601875000000003 : Rat) / 400000000000000000000), R := ((4486307609196428571441 : Rat) / 1600000000000000000000), D0 := ((4486307609196428571441 : Rat) / 1600000000000000000000), D1 := ((1578347449196428571441 : Rat) / 1600000000000000000000), D2 := ((393611609196428571441 : Rat) / 1600000000000000000000), D3 := ((206282849196428571441 : Rat) / 1600000000000000000000), D4 := ((12764770982142816317 : Rat) / 400000000000000000000), LB := ((1367375894424061 : Rat) / 50000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4486307609196428571441 : Rat) / 1600000000000000000000), R := ((8979728420089285714311 : Rat) / 3200000000000000000000), D0 := ((8979728420089285714311 : Rat) / 3200000000000000000000), D1 := ((3163808100089285714311 : Rat) / 3200000000000000000000), D2 := ((794336420089285714311 : Rat) / 3200000000000000000000), D3 := ((419678900089285714311 : Rat) / 3200000000000000000000), D4 := ((43945882232142693839 : Rat) / 1600000000000000000000), LB := ((755988207772651 : Rat) / 25000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8979728420089285714311 : Rat) / 3200000000000000000000), R := ((449342081089285714287 : Rat) / 160000000000000000000), D0 := ((449342081089285714287 : Rat) / 160000000000000000000), D1 := ((158546065089285714287 : Rat) / 160000000000000000000), D2 := ((40072481089285714287 : Rat) / 160000000000000000000), D3 := ((21339605089285714287 : Rat) / 160000000000000000000), D4 := ((80778562767856816249 : Rat) / 3200000000000000000000), LB := ((16913956067598823 : Rat) / 1000000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((449342081089285714287 : Rat) / 160000000000000000000), R := ((8993954823482142857169 : Rat) / 3200000000000000000000), D0 := ((8993954823482142857169 : Rat) / 3200000000000000000000), D1 := ((3178034503482142857169 : Rat) / 3200000000000000000000), D2 := ((808562823482142857169 : Rat) / 3200000000000000000000), D3 := ((433905303482142857169 : Rat) / 3200000000000000000000), D4 := ((3683268053571412241 : Rat) / 160000000000000000000), LB := ((11193259508630371 : Rat) / 2000000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8993954823482142857169 : Rat) / 3200000000000000000000), R := ((17995022848660714285767 : Rat) / 6400000000000000000000), D0 := ((17995022848660714285767 : Rat) / 6400000000000000000000), D1 := ((6363182208660714285767 : Rat) / 6400000000000000000000), D2 := ((1624238848660714285767 : Rat) / 6400000000000000000000), D3 := ((874923808660714285767 : Rat) / 6400000000000000000000), D4 := ((66552159374999673391 : Rat) / 3200000000000000000000), LB := ((13734221188090201 : Rat) / 1000000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17995022848660714285767 : Rat) / 6400000000000000000000), R := ((4500534012589285714299 : Rat) / 1600000000000000000000), D0 := ((4500534012589285714299 : Rat) / 1600000000000000000000), D1 := ((1592573852589285714299 : Rat) / 1600000000000000000000), D2 := ((407838012589285714299 : Rat) / 1600000000000000000000), D3 := ((220509252589285714299 : Rat) / 1600000000000000000000), D4 := ((125991117053570775353 : Rat) / 6400000000000000000000), LB := ((206305791297261 : Rat) / 20000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4500534012589285714299 : Rat) / 1600000000000000000000), R := ((144073994016428571429 : Rat) / 51200000000000000000), D0 := ((144073994016428571429 : Rat) / 51200000000000000000), D1 := ((51019268896428571429 : Rat) / 51200000000000000000), D2 := ((13107722016428571429 : Rat) / 51200000000000000000), D3 := ((7113201696428571429 : Rat) / 51200000000000000000), D4 := ((29719478839285550981 : Rat) / 1600000000000000000000), LB := ((48172702596639 : Rat) / 6250000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((144073994016428571429 : Rat) / 51200000000000000000), R := ((9008181226875000000027 : Rat) / 3200000000000000000000), D0 := ((9008181226875000000027 : Rat) / 3200000000000000000000), D1 := ((3192260906875000000027 : Rat) / 3200000000000000000000), D2 := ((822789226875000000027 : Rat) / 3200000000000000000000), D3 := ((448131706875000000027 : Rat) / 3200000000000000000000), D4 := ((22352942732142726499 : Rat) / 1280000000000000000000), LB := ((3004494967915383 : Rat) / 500000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((9008181226875000000027 : Rat) / 3200000000000000000000), R := ((18023475655446428571483 : Rat) / 6400000000000000000000), D0 := ((18023475655446428571483 : Rat) / 6400000000000000000000), D1 := ((6391635015446428571483 : Rat) / 6400000000000000000000), D2 := ((1652691655446428571483 : Rat) / 6400000000000000000000), D3 := ((903376615446428571483 : Rat) / 6400000000000000000000), D4 := ((52325755982142530533 : Rat) / 3200000000000000000000), LB := ((5336335703739703 : Rat) / 1000000000000000000) },
  { w1 := ((3727641881858767 : Rat) / 250000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((2482639961852091 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18023475655446428571483 : Rat) / 6400000000000000000000), R := ((140863975446428571429 : Rat) / 50000000000000000000), D0 := ((140863975446428571429 : Rat) / 50000000000000000000), D1 := ((49990220446428571429 : Rat) / 50000000000000000000), D2 := ((12967225446428571429 : Rat) / 50000000000000000000), D3 := ((7113201696428571429 : Rat) / 50000000000000000000), D4 := ((97538310267856489637 : Rat) / 6400000000000000000000), LB := ((5831222878884601 : Rat) / 1000000000000000000) }
]

def block001RightChunk000L : Rat := ((45427100446428571429 : Rat) / 25000000000000000000)
def block001RightChunk000R : Rat := ((140863975446428571429 : Rat) / 50000000000000000000)

def block001RightChunk000Certificate : Bool :=
  allBoxesValid block001RightChunk000 &&
  coversFromBool block001RightChunk000 block001RightChunk000L block001RightChunk000R

theorem block001RightChunk000Certificate_eq_true :
    block001RightChunk000Certificate = true := by
  native_decide

def block001RightChainCertificate : Bool :=
  decide (
    block001RightL = ((45427100446428571429 : Rat) / 25000000000000000000) /\
    ((140863975446428571429 : Rat) / 50000000000000000000) = block001RightR)

theorem block001RightChainCertificate_eq_true :
    block001RightChainCertificate = true := by
  native_decide

def block001LeftBoxCount : Nat := boxCount block001LeftBoxes
def block001RightBoxCount : Nat := 17

def block001_rational_certificate : Prop :=
    block001LeftCertificate = true /\
    block001RightChainCertificate = true /\
    block001RightChunk000Certificate = true

theorem block001_rational_certificate_proof :
    block001_rational_certificate := by
  exact ⟨block001LeftCertificate_eq_true, block001RightChainCertificate_eq_true, block001RightChunk000Certificate_eq_true⟩

end Block001
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block001

open Set

def block001W1 : Rat := ((3727641881858767 : Rat) / 250000000000000)
def block001W2 : Rat := (0 : Rat)
def block001W3 : Rat := (0 : Rat)
def block001W4 : Rat := ((2482639961852091 : Rat) / 10000000000000000)
def block001S1 : Rat := ((18174751 : Rat) / 10000000)
def block001S2 : Rat := ((511587 : Rat) / 200000)
def block001S3 : Rat := ((107000619 : Rat) / 40000000)
def block001S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block001V (y : ℝ) : ℝ :=
  ratPotential block001W1 block001W2 block001W3 block001W4 block001S1 block001S2 block001S3 block001S4 y

def block001LeftParamsCertificate : Bool :=
  allBoxesSameParams block001LeftBoxes block001W1 block001W2 block001W3 block001W4 block001S1 block001S2 block001S3 block001S4

theorem block001LeftParamsCertificate_eq_true :
    block001LeftParamsCertificate = true := by
  native_decide

theorem block001_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block001LeftL : ℝ) (block001LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block001S1 : ℝ))
    (hy2ne : y ≠ (block001S2 : ℝ))
    (hy3ne : y ≠ (block001S3 : ℝ))
    (hy4ne : y ≠ (block001S4 : ℝ)) :
    0 < block001V y := by
  have hcert := block001LeftCertificate_eq_true
  unfold block001LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block001LeftBoxes) (lo := block001LeftL) (hi := block001LeftR)
    (w1 := block001W1) (w2 := block001W2) (w3 := block001W3) (w4 := block001W4)
    (s1 := block001S1) (s2 := block001S2) (s3 := block001S3) (s4 := block001S4)
    hboxes hcover block001LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block001RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block001RightChunk000 block001W1 block001W2 block001W3 block001W4 block001S1 block001S2 block001S3 block001S4

theorem block001RightChunk000ParamsCertificate_eq_true :
    block001RightChunk000ParamsCertificate = true := by
  native_decide

theorem block001_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block001RightChunk000L : ℝ) (block001RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block001S1 : ℝ))
    (hy2ne : y ≠ (block001S2 : ℝ))
    (hy3ne : y ≠ (block001S3 : ℝ))
    (hy4ne : y ≠ (block001S4 : ℝ)) :
    0 < block001V y := by
  have hcert := block001RightChunk000Certificate_eq_true
  unfold block001RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block001RightChunk000) (lo := block001RightChunk000L) (hi := block001RightChunk000R)
    (w1 := block001W1) (w2 := block001W2) (w3 := block001W3) (w4 := block001W4)
    (s1 := block001S1) (s2 := block001S2) (s3 := block001S3) (s4 := block001S4)
    hboxes hcover block001RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block001_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block001RightL : ℝ) (block001RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block001S1 : ℝ))
    (hy2ne : y ≠ (block001S2 : ℝ))
    (hy3ne : y ≠ (block001S3 : ℝ))
    (hy4ne : y ≠ (block001S4 : ℝ)) :
    0 < block001V y := by
  have hL : (block001RightChunk000L : ℝ) = (block001RightL : ℝ) := by
    norm_num [block001RightChunk000L, block001RightL]
  have hR : (block001RightChunk000R : ℝ) = (block001RightR : ℝ) := by
    norm_num [block001RightChunk000R, block001RightR]
  have hyc : y ∈ Icc (block001RightChunk000L : ℝ) (block001RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block001_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block001_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block001LeftL : ℝ) (block001LeftR : ℝ) →
    y ≠ 0 → y ≠ (block001S1 : ℝ) → y ≠ (block001S2 : ℝ) →
    y ≠ (block001S3 : ℝ) → y ≠ (block001S4 : ℝ) → 0 < block001V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block001RightL : ℝ) (block001RightR : ℝ) →
    y ≠ 0 → y ≠ (block001S1 : ℝ) → y ≠ (block001S2 : ℝ) →
    y ≠ (block001S3 : ℝ) → y ≠ (block001S4 : ℝ) → 0 < block001V y)

theorem block001_reallog_certificate_proof :
    block001_reallog_certificate := by
  exact ⟨block001_left_V_pos, block001_right_V_pos⟩

end Block001
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block001.block001V
#check Erdos1038Lean.M1817475.Block001.block001_left_V_pos
#check Erdos1038Lean.M1817475.Block001.block001_right_V_pos
#check Erdos1038Lean.M1817475.Block001.block001_reallog_certificate_proof
