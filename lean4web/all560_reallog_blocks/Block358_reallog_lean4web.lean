/-
Self-contained Lean4Web paste file.
Block 358 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block358

def block358LeftL : Rat := ((37364685267857143011 : Rat) / 50000000000000000000)
def block358LeftR : Rat := ((18687229910714285791 : Rat) / 25000000000000000000)
def block358RightL : Rat := ((87364685267857143011 : Rat) / 50000000000000000000)
def block358RightR : Rat := ((68687229910714285791 : Rat) / 25000000000000000000)

def block358LeftBoxes : List RatBox := [
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37364685267857143011 : Rat) / 50000000000000000000), R := ((18687229910714285791 : Rat) / 25000000000000000000), D0 := ((18687229910714285791 : Rat) / 25000000000000000000), D1 := ((53509069732142856989 : Rat) / 50000000000000000000), D2 := ((90532064732142856989 : Rat) / 50000000000000000000), D3 := ((11971286450892857127 : Rat) / 6250000000000000000), D4 := ((101253821160714280587 : Rat) / 50000000000000000000), LB := ((3095318397357133 : Rat) / 500000000000000000) }
]

def block358LeftCertificate : Bool :=
  allBoxesValid block358LeftBoxes &&
  coversFromBool block358LeftBoxes block358LeftL block358LeftR

theorem block358LeftCertificate_eq_true :
    block358LeftCertificate = true := by
  native_decide

def block358RightChunk000 : List RatBox := [
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87364685267857143011 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3509069732142856989 : Rat) / 50000000000000000000), D2 := ((40532064732142856989 : Rat) / 50000000000000000000), D3 := ((5721286450892857127 : Rat) / 6250000000000000000), D4 := ((51253821160714280587 : Rat) / 50000000000000000000), LB := ((4467883131924421 : Rat) / 2500000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42261221875000000027 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((369231842564467 : Rat) / 2500000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23749724375000000027 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((2396017241487029 : Rat) / 25000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19121850000000000027 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((6129061266955757 : Rat) / 100000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16807912812500000027 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((6028493374929861 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14493975625000000027 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((4104619416951019 : Rat) / 500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13337007031250000027 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((6487860740174073 : Rat) / 500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12758522734375000027 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((1365028480176833 : Rat) / 250000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12180038437500000027 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((615585945561891 : Rat) / 62500000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((11890796289062500027 : Rat) / 50000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((6979226753726919 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11601554140625000027 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((8823774783435101 : Rat) / 2000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11312311992187500027 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((216006093650023 : Rat) / 100000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11023069843750000027 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((11906893593306711 : Rat) / 50000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10733827695312500027 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((1948526225466457 : Rat) / 500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10589206621093750027 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((1290017789278719 : Rat) / 400000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10444585546875000027 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((3308748824556347 : Rat) / 1250000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10299964472656250027 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((5414239448319827 : Rat) / 2500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10155343398437500027 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((3568251446485371 : Rat) / 2000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10010722324218750027 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((3763784808446663 : Rat) / 2500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((9866101250000000027 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((1666681314419563 : Rat) / 1250000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9721480175781250027 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((317848251813177 : Rat) / 250000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9576859101562500027 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((13237551424903071 : Rat) / 10000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9432238027343750027 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((7474460231864377 : Rat) / 5000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9287616953125000027 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((357934807605631 : Rat) / 200000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9142995878906250027 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((44268716110199 : Rat) / 20000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((8998374804687500027 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((8662628143607 : Rat) / 3125000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((8853753730468750027 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((34719591373825187 : Rat) / 10000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8709132656250000027 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((4320357649224699 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8564511582031250027 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((665651642319999 : Rat) / 125000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8419890507812500027 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((15582351187584387 : Rat) / 10000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8130648359375000027 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((558847712845461 : Rat) / 125000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7841406210937500027 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((8183405818945833 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7552164062500000027 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((6407455121684169 : Rat) / 2000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((6973679765625000027 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((8091286930395847 : Rat) / 500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6395195468750000027 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((8902677867672973 : Rat) / 500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516825226875000000027 : Rat) / 200000000000000000000), D0 := ((516825226875000000027 : Rat) / 200000000000000000000), D1 := ((153330206875000000027 : Rat) / 200000000000000000000), D2 := ((5238226875000000027 : Rat) / 200000000000000000000), D3 := ((5238226875000000027 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((607756138733363 : Rat) / 40000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516825226875000000027 : Rat) / 200000000000000000000), R := ((261031726875000000027 : Rat) / 100000000000000000000), D0 := ((261031726875000000027 : Rat) / 100000000000000000000), D1 := ((79284216875000000027 : Rat) / 100000000000000000000), D2 := ((5238226875000000027 : Rat) / 100000000000000000000), D3 := ((15714680625000000081 : Rat) / 200000000000000000000), D4 := ((7529759767857138873 : Rat) / 40000000000000000000), LB := ((38491770907738143 : Rat) / 10000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261031726875000000027 : Rat) / 100000000000000000000), R := ((527301680625000000081 : Rat) / 200000000000000000000), D0 := ((527301680625000000081 : Rat) / 200000000000000000000), D1 := ((163806660625000000081 : Rat) / 200000000000000000000), D2 := ((15714680625000000081 : Rat) / 200000000000000000000), D3 := ((5238226875000000027 : Rat) / 100000000000000000000), D4 := ((16205285982142847169 : Rat) / 100000000000000000000), LB := ((13887582171789037 : Rat) / 500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527301680625000000081 : Rat) / 200000000000000000000), R := ((133134976875000000027 : Rat) / 50000000000000000000), D0 := ((133134976875000000027 : Rat) / 50000000000000000000), D1 := ((42261221875000000027 : Rat) / 50000000000000000000), D2 := ((5238226875000000027 : Rat) / 50000000000000000000), D3 := ((5238226875000000027 : Rat) / 200000000000000000000), D4 := ((27172345089285694311 : Rat) / 200000000000000000000), LB := ((659270724530369 : Rat) / 6250000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133134976875000000027 : Rat) / 50000000000000000000), R := ((536779390446428571663 : Rat) / 200000000000000000000), D0 := ((536779390446428571663 : Rat) / 200000000000000000000), D1 := ((173284370446428571663 : Rat) / 200000000000000000000), D2 := ((25192390446428571663 : Rat) / 200000000000000000000), D3 := ((847896589285714311 : Rat) / 40000000000000000000), D4 := ((5483529553571423571 : Rat) / 50000000000000000000), LB := ((3211780494133601 : Rat) / 25000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((536779390446428571663 : Rat) / 200000000000000000000), R := ((270509436696428571609 : Rat) / 100000000000000000000), D0 := ((270509436696428571609 : Rat) / 100000000000000000000), D1 := ((88761926696428571609 : Rat) / 100000000000000000000), D2 := ((14715936696428571609 : Rat) / 100000000000000000000), D3 := ((847896589285714311 : Rat) / 20000000000000000000), D4 := ((17694635267857122729 : Rat) / 200000000000000000000), LB := ((16713837932627817 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270509436696428571609 : Rat) / 100000000000000000000), R := ((1086277229732142857991 : Rat) / 400000000000000000000), D0 := ((1086277229732142857991 : Rat) / 400000000000000000000), D1 := ((359287189732142857991 : Rat) / 400000000000000000000), D2 := ((63103229732142857991 : Rat) / 400000000000000000000), D3 := ((847896589285714311 : Rat) / 16000000000000000000), D4 := ((6727576160714275587 : Rat) / 100000000000000000000), LB := ((3225167073475199 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1086277229732142857991 : Rat) / 400000000000000000000), R := ((2176793942410714287537 : Rat) / 800000000000000000000), D0 := ((2176793942410714287537 : Rat) / 800000000000000000000), D1 := ((722813862410714287537 : Rat) / 800000000000000000000), D2 := ((130445942410714287537 : Rat) / 800000000000000000000), D3 := ((9326862482142857421 : Rat) / 160000000000000000000), D4 := ((22670821696428530793 : Rat) / 400000000000000000000), LB := ((1931192791233327 : Rat) / 500000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2176793942410714287537 : Rat) / 800000000000000000000), R := ((4357827367767857146629 : Rat) / 1600000000000000000000), D0 := ((4357827367767857146629 : Rat) / 1600000000000000000000), D1 := ((1449867207767857146629 : Rat) / 1600000000000000000000), D2 := ((265131367767857146629 : Rat) / 1600000000000000000000), D3 := ((19501621553571429153 : Rat) / 320000000000000000000), D4 := ((41102160446428490031 : Rat) / 800000000000000000000), LB := ((12852184011450607 : Rat) / 2000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4357827367767857146629 : Rat) / 1600000000000000000000), R := ((545258356339285714773 : Rat) / 200000000000000000000), D0 := ((545258356339285714773 : Rat) / 200000000000000000000), D1 := ((181763336339285714773 : Rat) / 200000000000000000000), D2 := ((33671356339285714773 : Rat) / 200000000000000000000), D3 := ((2543689767857142933 : Rat) / 40000000000000000000), D4 := ((77964837946428408507 : Rat) / 1600000000000000000000), LB := ((3018104913166897 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545258356339285714773 : Rat) / 200000000000000000000), R := ((4366306333660714289739 : Rat) / 1600000000000000000000), D0 := ((4366306333660714289739 : Rat) / 1600000000000000000000), D1 := ((1458346173660714289739 : Rat) / 1600000000000000000000), D2 := ((273610333660714289739 : Rat) / 1600000000000000000000), D3 := ((847896589285714311 : Rat) / 12800000000000000000), D4 := ((9215669374999979619 : Rat) / 200000000000000000000), LB := ((30432968938925997 : Rat) / 100000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4366306333660714289739 : Rat) / 1600000000000000000000), R := ((8736852150267857151033 : Rat) / 3200000000000000000000), D0 := ((8736852150267857151033 : Rat) / 3200000000000000000000), D1 := ((2920931830267857151033 : Rat) / 3200000000000000000000), D2 := ((551460150267857151033 : Rat) / 3200000000000000000000), D3 := ((43242726053571429861 : Rat) / 640000000000000000000), D4 := ((69485872053571265397 : Rat) / 1600000000000000000000), LB := ((3388688574677723 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8736852150267857151033 : Rat) / 3200000000000000000000), R := ((2185272908303571430647 : Rat) / 800000000000000000000), D0 := ((2185272908303571430647 : Rat) / 800000000000000000000), D1 := ((731292828303571430647 : Rat) / 800000000000000000000), D2 := ((138924908303571430647 : Rat) / 800000000000000000000), D3 := ((11022655660714286043 : Rat) / 160000000000000000000), D4 := ((134732261160713959239 : Rat) / 3200000000000000000000), LB := ((2614447130611819 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2185272908303571430647 : Rat) / 800000000000000000000), R := ((8745331116160714294143 : Rat) / 3200000000000000000000), D0 := ((8745331116160714294143 : Rat) / 3200000000000000000000), D1 := ((2929410796160714294143 : Rat) / 3200000000000000000000), D2 := ((559939116160714294143 : Rat) / 3200000000000000000000), D3 := ((44938519232142858483 : Rat) / 640000000000000000000), D4 := ((32623194553571346921 : Rat) / 800000000000000000000), LB := ((20385590393653397 : Rat) / 10000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8745331116160714294143 : Rat) / 3200000000000000000000), R := ((4374785299553571432849 : Rat) / 1600000000000000000000), D0 := ((4374785299553571432849 : Rat) / 1600000000000000000000), D1 := ((1466825139553571432849 : Rat) / 1600000000000000000000), D2 := ((282089299553571432849 : Rat) / 1600000000000000000000), D3 := ((22893207910714286397 : Rat) / 320000000000000000000), D4 := ((126253295267856816129 : Rat) / 3200000000000000000000), LB := ((8339868027199271 : Rat) / 5000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4374785299553571432849 : Rat) / 1600000000000000000000), R := ((8753810082053571437253 : Rat) / 3200000000000000000000), D0 := ((8753810082053571437253 : Rat) / 3200000000000000000000), D1 := ((2937889762053571437253 : Rat) / 3200000000000000000000), D2 := ((568418082053571437253 : Rat) / 3200000000000000000000), D3 := ((9326862482142857421 : Rat) / 128000000000000000000), D4 := ((61006906160714122287 : Rat) / 1600000000000000000000), LB := ((118022473146219 : Rat) / 78125000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8753810082053571437253 : Rat) / 3200000000000000000000), R := ((1094756195625000001101 : Rat) / 400000000000000000000), D0 := ((1094756195625000001101 : Rat) / 400000000000000000000), D1 := ((367766155625000001101 : Rat) / 400000000000000000000), D2 := ((71582195625000001101 : Rat) / 400000000000000000000), D3 := ((5935276125000000177 : Rat) / 80000000000000000000), D4 := ((117774329374999673019 : Rat) / 3200000000000000000000), LB := ((1575869025599197 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094756195625000001101 : Rat) / 400000000000000000000), R := ((8762289047946428580363 : Rat) / 3200000000000000000000), D0 := ((8762289047946428580363 : Rat) / 3200000000000000000000), D1 := ((2946368727946428580363 : Rat) / 3200000000000000000000), D2 := ((576897047946428580363 : Rat) / 3200000000000000000000), D3 := ((48330105589285715727 : Rat) / 640000000000000000000), D4 := ((14191855803571387683 : Rat) / 400000000000000000000), LB := ((9370024726769177 : Rat) / 5000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8762289047946428580363 : Rat) / 3200000000000000000000), R := ((4383264265446428575959 : Rat) / 1600000000000000000000), D0 := ((4383264265446428575959 : Rat) / 1600000000000000000000), D1 := ((1475304105446428575959 : Rat) / 1600000000000000000000), D2 := ((290568265446428575959 : Rat) / 1600000000000000000000), D3 := ((24589001089285715019 : Rat) / 320000000000000000000), D4 := ((109295363482142529909 : Rat) / 3200000000000000000000), LB := ((2417080792343429 : Rat) / 1000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4383264265446428575959 : Rat) / 1600000000000000000000), R := ((8770768013839285723473 : Rat) / 3200000000000000000000), D0 := ((8770768013839285723473 : Rat) / 3200000000000000000000), D1 := ((2954847693839285723473 : Rat) / 3200000000000000000000), D2 := ((585376013839285723473 : Rat) / 3200000000000000000000), D3 := ((50025898767857144349 : Rat) / 640000000000000000000), D4 := ((52527940267856979177 : Rat) / 1600000000000000000000), LB := ((6437592351396293 : Rat) / 2000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8770768013839285723473 : Rat) / 3200000000000000000000), R := ((2193751874196428573757 : Rat) / 800000000000000000000), D0 := ((2193751874196428573757 : Rat) / 800000000000000000000), D1 := ((739771794196428573757 : Rat) / 800000000000000000000), D2 := ((147403874196428573757 : Rat) / 800000000000000000000), D3 := ((2543689767857142933 : Rat) / 32000000000000000000), D4 := ((100816397589285386799 : Rat) / 3200000000000000000000), LB := ((858965478839091 : Rat) / 200000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2193751874196428573757 : Rat) / 800000000000000000000), R := ((4391743231339285719069 : Rat) / 1600000000000000000000), D0 := ((4391743231339285719069 : Rat) / 1600000000000000000000), D1 := ((1483783071339285719069 : Rat) / 1600000000000000000000), D2 := ((299047231339285719069 : Rat) / 1600000000000000000000), D3 := ((26284794267857143641 : Rat) / 320000000000000000000), D4 := ((24144228660714203811 : Rat) / 800000000000000000000), LB := ((11110645374376449 : Rat) / 10000000000000000000) },
  { w1 := ((2225243964898163 : Rat) / 2500000000000000), w2 := ((4753310348523179 : Rat) / 100000000000000000), w3 := ((1890056571812761 : Rat) / 12500000000000000), w4 := ((1735726401084859 : Rat) / 12500000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133134976875000000027 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4391743231339285719069 : Rat) / 1600000000000000000000), R := ((68687229910714285791 : Rat) / 25000000000000000000), D0 := ((68687229910714285791 : Rat) / 25000000000000000000), D1 := ((23250352410714285791 : Rat) / 25000000000000000000), D2 := ((4738854910714285791 : Rat) / 25000000000000000000), D3 := ((847896589285714311 : Rat) / 10000000000000000000), D4 := ((44048974374999836067 : Rat) / 1600000000000000000000), LB := ((1224173229510947 : Rat) / 250000000000000000) }
]

def block358RightChunk000L : Rat := ((87364685267857143011 : Rat) / 50000000000000000000)
def block358RightChunk000R : Rat := ((68687229910714285791 : Rat) / 25000000000000000000)

def block358RightChunk000Certificate : Bool :=
  allBoxesValid block358RightChunk000 &&
  coversFromBool block358RightChunk000 block358RightChunk000L block358RightChunk000R

theorem block358RightChunk000Certificate_eq_true :
    block358RightChunk000Certificate = true := by
  native_decide

def block358RightChainCertificate : Bool :=
  decide (
    block358RightL = ((87364685267857143011 : Rat) / 50000000000000000000) /\
    ((68687229910714285791 : Rat) / 25000000000000000000) = block358RightR)

theorem block358RightChainCertificate_eq_true :
    block358RightChainCertificate = true := by
  native_decide

def block358LeftBoxCount : Nat := boxCount block358LeftBoxes
def block358RightBoxCount : Nat := 58

def block358_rational_certificate : Prop :=
    block358LeftCertificate = true /\
    block358RightChainCertificate = true /\
    block358RightChunk000Certificate = true

theorem block358_rational_certificate_proof :
    block358_rational_certificate := by
  exact ⟨block358LeftCertificate_eq_true, block358RightChainCertificate_eq_true, block358RightChunk000Certificate_eq_true⟩

end Block358
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block358

open Set

def block358W1 : Rat := ((2225243964898163 : Rat) / 2500000000000000)
def block358W2 : Rat := ((4753310348523179 : Rat) / 100000000000000000)
def block358W3 : Rat := ((1890056571812761 : Rat) / 12500000000000000)
def block358W4 : Rat := ((1735726401084859 : Rat) / 12500000000000000)
def block358S1 : Rat := ((18174751 : Rat) / 10000000)
def block358S2 : Rat := ((511587 : Rat) / 200000)
def block358S3 : Rat := ((133134976875000000027 : Rat) / 50000000000000000000)
def block358S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block358V (y : ℝ) : ℝ :=
  ratPotential block358W1 block358W2 block358W3 block358W4 block358S1 block358S2 block358S3 block358S4 y

def block358LeftParamsCertificate : Bool :=
  allBoxesSameParams block358LeftBoxes block358W1 block358W2 block358W3 block358W4 block358S1 block358S2 block358S3 block358S4

theorem block358LeftParamsCertificate_eq_true :
    block358LeftParamsCertificate = true := by
  native_decide

theorem block358_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block358LeftL : ℝ) (block358LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block358S1 : ℝ))
    (hy2ne : y ≠ (block358S2 : ℝ))
    (hy3ne : y ≠ (block358S3 : ℝ))
    (hy4ne : y ≠ (block358S4 : ℝ)) :
    0 < block358V y := by
  have hcert := block358LeftCertificate_eq_true
  unfold block358LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block358LeftBoxes) (lo := block358LeftL) (hi := block358LeftR)
    (w1 := block358W1) (w2 := block358W2) (w3 := block358W3) (w4 := block358W4)
    (s1 := block358S1) (s2 := block358S2) (s3 := block358S3) (s4 := block358S4)
    hboxes hcover block358LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block358RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block358RightChunk000 block358W1 block358W2 block358W3 block358W4 block358S1 block358S2 block358S3 block358S4

theorem block358RightChunk000ParamsCertificate_eq_true :
    block358RightChunk000ParamsCertificate = true := by
  native_decide

theorem block358_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block358RightChunk000L : ℝ) (block358RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block358S1 : ℝ))
    (hy2ne : y ≠ (block358S2 : ℝ))
    (hy3ne : y ≠ (block358S3 : ℝ))
    (hy4ne : y ≠ (block358S4 : ℝ)) :
    0 < block358V y := by
  have hcert := block358RightChunk000Certificate_eq_true
  unfold block358RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block358RightChunk000) (lo := block358RightChunk000L) (hi := block358RightChunk000R)
    (w1 := block358W1) (w2 := block358W2) (w3 := block358W3) (w4 := block358W4)
    (s1 := block358S1) (s2 := block358S2) (s3 := block358S3) (s4 := block358S4)
    hboxes hcover block358RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block358_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block358RightL : ℝ) (block358RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block358S1 : ℝ))
    (hy2ne : y ≠ (block358S2 : ℝ))
    (hy3ne : y ≠ (block358S3 : ℝ))
    (hy4ne : y ≠ (block358S4 : ℝ)) :
    0 < block358V y := by
  have hL : (block358RightChunk000L : ℝ) = (block358RightL : ℝ) := by
    norm_num [block358RightChunk000L, block358RightL]
  have hR : (block358RightChunk000R : ℝ) = (block358RightR : ℝ) := by
    norm_num [block358RightChunk000R, block358RightR]
  have hyc : y ∈ Icc (block358RightChunk000L : ℝ) (block358RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block358_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block358_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block358LeftL : ℝ) (block358LeftR : ℝ) →
    y ≠ 0 → y ≠ (block358S1 : ℝ) → y ≠ (block358S2 : ℝ) →
    y ≠ (block358S3 : ℝ) → y ≠ (block358S4 : ℝ) → 0 < block358V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block358RightL : ℝ) (block358RightR : ℝ) →
    y ≠ 0 → y ≠ (block358S1 : ℝ) → y ≠ (block358S2 : ℝ) →
    y ≠ (block358S3 : ℝ) → y ≠ (block358S4 : ℝ) → 0 < block358V y)

theorem block358_reallog_certificate_proof :
    block358_reallog_certificate := by
  exact ⟨block358_left_V_pos, block358_right_V_pos⟩

end Block358
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block358.block358V
#check Erdos1038Lean.M1817475.Block358.block358_left_V_pos
#check Erdos1038Lean.M1817475.Block358.block358_right_V_pos
#check Erdos1038Lean.M1817475.Block358.block358_reallog_certificate_proof
