/-
Self-contained Lean4Web paste file.
Block 12 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block012

def block012LeftL : Rat := ((40746680803571428577 : Rat) / 50000000000000000000)
def block012LeftR : Rat := ((10189113839285714287 : Rat) / 12500000000000000000)
def block012RightL : Rat := ((90746680803571428577 : Rat) / 50000000000000000000)
def block012RightR : Rat := ((35189113839285714287 : Rat) / 12500000000000000000)

def block012LeftBoxes : List RatBox := [
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((40746680803571428577 : Rat) / 50000000000000000000), R := ((10189113839285714287 : Rat) / 12500000000000000000), D0 := ((10189113839285714287 : Rat) / 12500000000000000000), D1 := ((50127074196428571423 : Rat) / 50000000000000000000), D2 := ((87150069196428571423 : Rat) / 50000000000000000000), D3 := ((93004092946428571423 : Rat) / 50000000000000000000), D4 := ((100823740803571423463 : Rat) / 50000000000000000000), LB := ((223426931594781 : Rat) / 62500000000000000) }
]

def block012LeftCertificate : Bool :=
  allBoxesValid block012LeftBoxes &&
  coversFromBool block012LeftBoxes block012LeftL block012LeftR

theorem block012LeftCertificate_eq_true :
    block012LeftCertificate = true := by
  native_decide

def block012RightChunk000 : List RatBox := [
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((90746680803571428577 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((127074196428571423 : Rat) / 50000000000000000000), D2 := ((37150069196428571423 : Rat) / 50000000000000000000), D3 := ((43004092946428571423 : Rat) / 50000000000000000000), D4 := ((50823740803571423463 : Rat) / 50000000000000000000), LB := ((5206081227991701 : Rat) / 100000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((1267416665178571301 : Rat) / 1250000000000000000), LB := ((3498220497196931 : Rat) / 2000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((341841790178571301 : Rat) / 1250000000000000000), LB := ((7220551136852931 : Rat) / 10000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((68626807276785714287 : Rat) / 25000000000000000000), D0 := ((68626807276785714287 : Rat) / 25000000000000000000), D1 := ((23189929776785714287 : Rat) / 25000000000000000000), D2 := ((4678432276785714287 : Rat) / 25000000000000000000), D3 := ((1751420401785714287 : Rat) / 25000000000000000000), D4 := ((195491196428571301 : Rat) / 1250000000000000000), LB := ((13461916464655277 : Rat) / 100000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((68626807276785714287 : Rat) / 25000000000000000000), R := ((55251729901785714287 : Rat) / 20000000000000000000), D0 := ((55251729901785714287 : Rat) / 20000000000000000000), D1 := ((18902227901785714287 : Rat) / 20000000000000000000), D2 := ((4093029901785714287 : Rat) / 20000000000000000000), D3 := ((1751420401785714287 : Rat) / 20000000000000000000), D4 := ((2158403526785711733 : Rat) / 25000000000000000000), LB := ((11155917889507727 : Rat) / 100000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((55251729901785714287 : Rat) / 20000000000000000000), R := ((554268719419642857157 : Rat) / 200000000000000000000), D0 := ((554268719419642857157 : Rat) / 200000000000000000000), D1 := ((190773699419642857157 : Rat) / 200000000000000000000), D2 := ((42681719419642857157 : Rat) / 200000000000000000000), D3 := ((19265624419642857157 : Rat) / 200000000000000000000), D4 := ((1376438741071426529 : Rat) / 20000000000000000000), LB := ((130226011480831 : Rat) / 1562500000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((554268719419642857157 : Rat) / 200000000000000000000), R := ((139005034955357142861 : Rat) / 50000000000000000000), D0 := ((139005034955357142861 : Rat) / 50000000000000000000), D1 := ((48131279955357142861 : Rat) / 50000000000000000000), D2 := ((11108284955357142861 : Rat) / 50000000000000000000), D3 := ((5254261205357142861 : Rat) / 50000000000000000000), D4 := ((12012967008928551003 : Rat) / 200000000000000000000), LB := ((16440940066205223 : Rat) / 500000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((139005034955357142861 : Rat) / 50000000000000000000), R := ((44551668001785714287 : Rat) / 16000000000000000000), D0 := ((44551668001785714287 : Rat) / 16000000000000000000), D1 := ((15472066401785714287 : Rat) / 16000000000000000000), D2 := ((3624708001785714287 : Rat) / 16000000000000000000), D3 := ((1751420401785714287 : Rat) / 16000000000000000000), D4 := ((2565386651785709179 : Rat) / 50000000000000000000), LB := ((7667164188595893 : Rat) / 250000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((44551668001785714287 : Rat) / 16000000000000000000), R := ((557771560223214285731 : Rat) / 200000000000000000000), D0 := ((557771560223214285731 : Rat) / 200000000000000000000), D1 := ((194276540223214285731 : Rat) / 200000000000000000000), D2 := ((46184560223214285731 : Rat) / 200000000000000000000), D3 := ((22768465223214285731 : Rat) / 200000000000000000000), D4 := ((3754334562499991829 : Rat) / 80000000000000000000), LB := ((2255474594469331 : Rat) / 200000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((557771560223214285731 : Rat) / 200000000000000000000), R := ((2232837661294642857211 : Rat) / 800000000000000000000), D0 := ((2232837661294642857211 : Rat) / 800000000000000000000), D1 := ((778857581294642857211 : Rat) / 800000000000000000000), D2 := ((186489661294642857211 : Rat) / 800000000000000000000), D3 := ((92825281294642857211 : Rat) / 800000000000000000000), D4 := ((8510126205357122429 : Rat) / 200000000000000000000), LB := ((474899864497471 : Rat) / 31250000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2232837661294642857211 : Rat) / 800000000000000000000), R := ((1117294540848214285749 : Rat) / 400000000000000000000), D0 := ((1117294540848214285749 : Rat) / 400000000000000000000), D1 := ((390304500848214285749 : Rat) / 400000000000000000000), D2 := ((94120540848214285749 : Rat) / 400000000000000000000), D3 := ((47288350848214285749 : Rat) / 400000000000000000000), D4 := ((32289084419642775429 : Rat) / 800000000000000000000), LB := ((7703930191861663 : Rat) / 1000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1117294540848214285749 : Rat) / 400000000000000000000), R := ((447268100419642857157 : Rat) / 160000000000000000000), D0 := ((447268100419642857157 : Rat) / 160000000000000000000), D1 := ((156472084419642857157 : Rat) / 160000000000000000000), D2 := ((37998500419642857157 : Rat) / 160000000000000000000), D3 := ((19265624419642857157 : Rat) / 160000000000000000000), D4 := ((15268832008928530571 : Rat) / 400000000000000000000), LB := ((2512476035741451 : Rat) / 2500000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((447268100419642857157 : Rat) / 160000000000000000000), R := ((4474432424598214285857 : Rat) / 1600000000000000000000), D0 := ((4474432424598214285857 : Rat) / 1600000000000000000000), D1 := ((1566472264598214285857 : Rat) / 1600000000000000000000), D2 := ((381736424598214285857 : Rat) / 1600000000000000000000), D3 := ((194407664598214285857 : Rat) / 1600000000000000000000), D4 := ((5757248723214269371 : Rat) / 160000000000000000000), LB := ((5589939004714717 : Rat) / 1000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4474432424598214285857 : Rat) / 1600000000000000000000), R := ((279761490312500000009 : Rat) / 100000000000000000000), D0 := ((279761490312500000009 : Rat) / 100000000000000000000), D1 := ((98013980312500000009 : Rat) / 100000000000000000000), D2 := ((23967990312500000009 : Rat) / 100000000000000000000), D3 := ((12259942812500000009 : Rat) / 100000000000000000000), D4 := ((55821066830356979423 : Rat) / 1600000000000000000000), LB := ((7582610056352801 : Rat) / 2500000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((279761490312500000009 : Rat) / 100000000000000000000), R := ((4477935265401785714431 : Rat) / 1600000000000000000000), D0 := ((4477935265401785714431 : Rat) / 1600000000000000000000), D1 := ((1569975105401785714431 : Rat) / 1600000000000000000000), D2 := ((385239265401785714431 : Rat) / 1600000000000000000000), D3 := ((197910505401785714431 : Rat) / 1600000000000000000000), D4 := ((3379352901785704071 : Rat) / 100000000000000000000), LB := ((7375769242097263 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4477935265401785714431 : Rat) / 1600000000000000000000), R := ((8957621951205357143149 : Rat) / 3200000000000000000000), D0 := ((8957621951205357143149 : Rat) / 3200000000000000000000), D1 := ((3141701631205357143149 : Rat) / 3200000000000000000000), D2 := ((772229951205357143149 : Rat) / 3200000000000000000000), D3 := ((397572431205357143149 : Rat) / 3200000000000000000000), D4 := ((52318226026785550849 : Rat) / 1600000000000000000000), LB := ((195406403419629 : Rat) / 50000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8957621951205357143149 : Rat) / 3200000000000000000000), R := ((2239843342901785714359 : Rat) / 800000000000000000000), D0 := ((2239843342901785714359 : Rat) / 800000000000000000000), D1 := ((785863262901785714359 : Rat) / 800000000000000000000), D2 := ((193495342901785714359 : Rat) / 800000000000000000000), D3 := ((99830962901785714359 : Rat) / 800000000000000000000), D4 := ((102885031651785387411 : Rat) / 3200000000000000000000), LB := ((3006311463692901 : Rat) / 1000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2239843342901785714359 : Rat) / 800000000000000000000), R := ((8961124792008928571723 : Rat) / 3200000000000000000000), D0 := ((8961124792008928571723 : Rat) / 3200000000000000000000), D1 := ((3145204472008928571723 : Rat) / 3200000000000000000000), D2 := ((775732792008928571723 : Rat) / 3200000000000000000000), D3 := ((401075272008928571723 : Rat) / 3200000000000000000000), D4 := ((25283402812499918281 : Rat) / 800000000000000000000), LB := ((272613806962127 : Rat) / 125000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8961124792008928571723 : Rat) / 3200000000000000000000), R := ((896287621241071428601 : Rat) / 320000000000000000000), D0 := ((896287621241071428601 : Rat) / 320000000000000000000), D1 := ((314695589241071428601 : Rat) / 320000000000000000000), D2 := ((77748421241071428601 : Rat) / 320000000000000000000), D3 := ((40282669241071428601 : Rat) / 320000000000000000000), D4 := ((99382190848213958837 : Rat) / 3200000000000000000000), LB := ((3586233645365977 : Rat) / 2500000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((896287621241071428601 : Rat) / 320000000000000000000), R := ((8964627632812500000297 : Rat) / 3200000000000000000000), D0 := ((8964627632812500000297 : Rat) / 3200000000000000000000), D1 := ((3148707312812500000297 : Rat) / 3200000000000000000000), D2 := ((779235632812500000297 : Rat) / 3200000000000000000000), D3 := ((404578112812500000297 : Rat) / 3200000000000000000000), D4 := ((1952615408928564891 : Rat) / 64000000000000000000), LB := ((3848830331525943 : Rat) / 5000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8964627632812500000297 : Rat) / 3200000000000000000000), R := ((1120797381651785714323 : Rat) / 400000000000000000000), D0 := ((1120797381651785714323 : Rat) / 400000000000000000000), D1 := ((393807341651785714323 : Rat) / 400000000000000000000), D2 := ((97623381651785714323 : Rat) / 400000000000000000000), D3 := ((50791191651785714323 : Rat) / 400000000000000000000), D4 := ((95879350044642530263 : Rat) / 3200000000000000000000), LB := ((9479049515326299 : Rat) / 50000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1120797381651785714323 : Rat) / 400000000000000000000), R := ((3586901905366071428691 : Rat) / 1280000000000000000000), D0 := ((3586901905366071428691 : Rat) / 1280000000000000000000), D1 := ((1260533777366071428691 : Rat) / 1280000000000000000000), D2 := ((312745105366071428691 : Rat) / 1280000000000000000000), D3 := ((162882097366071428691 : Rat) / 1280000000000000000000), D4 := ((11765991205357101997 : Rat) / 400000000000000000000), LB := ((22836367895520127 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3586901905366071428691 : Rat) / 1280000000000000000000), R := ((8968130473616071428871 : Rat) / 3200000000000000000000), D0 := ((8968130473616071428871 : Rat) / 3200000000000000000000), D1 := ((3152210153616071428871 : Rat) / 3200000000000000000000), D2 := ((782738473616071428871 : Rat) / 3200000000000000000000), D3 := ((408080953616071428871 : Rat) / 3200000000000000000000), D4 := ((37300887776785583533 : Rat) / 1280000000000000000000), LB := ((1035219565269141 : Rat) / 500000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8968130473616071428871 : Rat) / 3200000000000000000000), R := ((17938012367633928572029 : Rat) / 6400000000000000000000), D0 := ((17938012367633928572029 : Rat) / 6400000000000000000000), D1 := ((6306171727633928572029 : Rat) / 6400000000000000000000), D2 := ((1567228367633928572029 : Rat) / 6400000000000000000000), D3 := ((817913327633928572029 : Rat) / 6400000000000000000000), D4 := ((92376509241071101689 : Rat) / 3200000000000000000000), LB := ((940168378507189 : Rat) / 500000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17938012367633928572029 : Rat) / 6400000000000000000000), R := ((4484940947008928571579 : Rat) / 1600000000000000000000), D0 := ((4484940947008928571579 : Rat) / 1600000000000000000000), D1 := ((1576980787008928571579 : Rat) / 1600000000000000000000), D2 := ((392244947008928571579 : Rat) / 1600000000000000000000), D3 := ((204916187008928571579 : Rat) / 1600000000000000000000), D4 := ((183001598080356489091 : Rat) / 6400000000000000000000), LB := ((17137559010299563 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4484940947008928571579 : Rat) / 1600000000000000000000), R := ((17941515208437500000603 : Rat) / 6400000000000000000000), D0 := ((17941515208437500000603 : Rat) / 6400000000000000000000), D1 := ((6309674568437500000603 : Rat) / 6400000000000000000000), D2 := ((1570731208437500000603 : Rat) / 6400000000000000000000), D3 := ((821416168437500000603 : Rat) / 6400000000000000000000), D4 := ((45312544419642693701 : Rat) / 1600000000000000000000), LB := ((15711351027590803 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17941515208437500000603 : Rat) / 6400000000000000000000), R := ((1794326662883928571489 : Rat) / 640000000000000000000), D0 := ((1794326662883928571489 : Rat) / 640000000000000000000), D1 := ((631142598883928571489 : Rat) / 640000000000000000000), D2 := ((157248262883928571489 : Rat) / 640000000000000000000), D3 := ((82316758883928571489 : Rat) / 640000000000000000000), D4 := ((179498757276785060517 : Rat) / 6400000000000000000000), LB := ((14529256884990849 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1794326662883928571489 : Rat) / 640000000000000000000), R := ((17945018049241071429177 : Rat) / 6400000000000000000000), D0 := ((17945018049241071429177 : Rat) / 6400000000000000000000), D1 := ((6313177409241071429177 : Rat) / 6400000000000000000000), D2 := ((1574234049241071429177 : Rat) / 6400000000000000000000), D3 := ((824919009241071429177 : Rat) / 6400000000000000000000), D4 := ((17774733687499934623 : Rat) / 640000000000000000000), LB := ((6797961360421323 : Rat) / 5000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17945018049241071429177 : Rat) / 6400000000000000000000), R := ((2243346183705357142933 : Rat) / 800000000000000000000), D0 := ((2243346183705357142933 : Rat) / 800000000000000000000), D1 := ((789366103705357142933 : Rat) / 800000000000000000000), D2 := ((196998183705357142933 : Rat) / 800000000000000000000), D3 := ((103333803705357142933 : Rat) / 800000000000000000000), D4 := ((175995916473213631943 : Rat) / 6400000000000000000000), LB := ((3229033202760967 : Rat) / 2500000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2243346183705357142933 : Rat) / 800000000000000000000), R := ((17948520890044642857751 : Rat) / 6400000000000000000000), D0 := ((17948520890044642857751 : Rat) / 6400000000000000000000), D1 := ((6316680250044642857751 : Rat) / 6400000000000000000000), D2 := ((1577736890044642857751 : Rat) / 6400000000000000000000), D3 := ((828421850044642857751 : Rat) / 6400000000000000000000), D4 := ((21780562008928489707 : Rat) / 800000000000000000000), LB := ((6247407547259609 : Rat) / 5000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17948520890044642857751 : Rat) / 6400000000000000000000), R := ((8975136155223214286019 : Rat) / 3200000000000000000000), D0 := ((8975136155223214286019 : Rat) / 3200000000000000000000), D1 := ((3159215835223214286019 : Rat) / 3200000000000000000000), D2 := ((789744155223214286019 : Rat) / 3200000000000000000000), D3 := ((415086635223214286019 : Rat) / 3200000000000000000000), D4 := ((172493075669642203369 : Rat) / 6400000000000000000000), LB := ((6168523488644939 : Rat) / 5000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8975136155223214286019 : Rat) / 3200000000000000000000), R := ((718080949233928571453 : Rat) / 256000000000000000000), D0 := ((718080949233928571453 : Rat) / 256000000000000000000), D1 := ((252807323633928571453 : Rat) / 256000000000000000000), D2 := ((63249589233928571453 : Rat) / 256000000000000000000), D3 := ((33276987633928571453 : Rat) / 256000000000000000000), D4 := ((85370827633928244541 : Rat) / 3200000000000000000000), LB := ((194500959887281 : Rat) / 156250000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((718080949233928571453 : Rat) / 256000000000000000000), R := ((4488443787812500000153 : Rat) / 1600000000000000000000), D0 := ((4488443787812500000153 : Rat) / 1600000000000000000000), D1 := ((1580483627812500000153 : Rat) / 1600000000000000000000), D2 := ((395747787812500000153 : Rat) / 1600000000000000000000), D3 := ((208419027812500000153 : Rat) / 1600000000000000000000), D4 := ((33798046973214154959 : Rat) / 1280000000000000000000), LB := ((12833253416221213 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4488443787812500000153 : Rat) / 1600000000000000000000), R := ((17955526571651785714899 : Rat) / 6400000000000000000000), D0 := ((17955526571651785714899 : Rat) / 6400000000000000000000), D1 := ((6323685931651785714899 : Rat) / 6400000000000000000000), D2 := ((1584742571651785714899 : Rat) / 6400000000000000000000), D3 := ((835427531651785714899 : Rat) / 6400000000000000000000), D4 := ((41809703616071265127 : Rat) / 1600000000000000000000), LB := ((13498186612946883 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17955526571651785714899 : Rat) / 6400000000000000000000), R := ((8978638996026785714593 : Rat) / 3200000000000000000000), D0 := ((8978638996026785714593 : Rat) / 3200000000000000000000), D1 := ((3162718676026785714593 : Rat) / 3200000000000000000000), D2 := ((793246996026785714593 : Rat) / 3200000000000000000000), D3 := ((418589476026785714593 : Rat) / 3200000000000000000000), D4 := ((165487394062499346221 : Rat) / 6400000000000000000000), LB := ((1444860054154451 : Rat) / 1000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8978638996026785714593 : Rat) / 3200000000000000000000), R := ((17959029412455357143473 : Rat) / 6400000000000000000000), D0 := ((17959029412455357143473 : Rat) / 6400000000000000000000), D1 := ((6327188772455357143473 : Rat) / 6400000000000000000000), D2 := ((1588245412455357143473 : Rat) / 6400000000000000000000), D3 := ((838930372455357143473 : Rat) / 6400000000000000000000), D4 := ((81867986830356815967 : Rat) / 3200000000000000000000), LB := ((7845209017269261 : Rat) / 5000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17959029412455357143473 : Rat) / 6400000000000000000000), R := ((112254880205357142861 : Rat) / 40000000000000000000), D0 := ((112254880205357142861 : Rat) / 40000000000000000000), D1 := ((39555876205357142861 : Rat) / 40000000000000000000), D2 := ((9937480205357142861 : Rat) / 40000000000000000000), D3 := ((5254261205357142861 : Rat) / 40000000000000000000), D4 := ((161984553258927917647 : Rat) / 6400000000000000000000), LB := ((4307438280203857 : Rat) / 2500000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((112254880205357142861 : Rat) / 40000000000000000000), R := ((17962532253258928572047 : Rat) / 6400000000000000000000), D0 := ((17962532253258928572047 : Rat) / 6400000000000000000000), D1 := ((6330691613258928572047 : Rat) / 6400000000000000000000), D2 := ((1591748253258928572047 : Rat) / 6400000000000000000000), D3 := ((842433213258928572047 : Rat) / 6400000000000000000000), D4 := ((1001457080357138771 : Rat) / 40000000000000000000), LB := ((19072919335827443 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17962532253258928572047 : Rat) / 6400000000000000000000), R := ((8982141836830357143167 : Rat) / 3200000000000000000000), D0 := ((8982141836830357143167 : Rat) / 3200000000000000000000), D1 := ((3166221516830357143167 : Rat) / 3200000000000000000000), D2 := ((796749836830357143167 : Rat) / 3200000000000000000000), D3 := ((422092316830357143167 : Rat) / 3200000000000000000000), D4 := ((158481712455356489073 : Rat) / 6400000000000000000000), LB := ((2122643848785577 : Rat) / 1000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8982141836830357143167 : Rat) / 3200000000000000000000), R := ((17966035094062500000621 : Rat) / 6400000000000000000000), D0 := ((17966035094062500000621 : Rat) / 6400000000000000000000), D1 := ((6334194454062500000621 : Rat) / 6400000000000000000000), D2 := ((1595251094062500000621 : Rat) / 6400000000000000000000), D3 := ((845936054062500000621 : Rat) / 6400000000000000000000), D4 := ((78365146026785387393 : Rat) / 3200000000000000000000), LB := ((37026640485157 : Rat) / 15625000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((17966035094062500000621 : Rat) / 6400000000000000000000), R := ((4491946628616071428727 : Rat) / 1600000000000000000000), D0 := ((4491946628616071428727 : Rat) / 1600000000000000000000), D1 := ((1583986468616071428727 : Rat) / 1600000000000000000000), D2 := ((399250628616071428727 : Rat) / 1600000000000000000000), D3 := ((211921868616071428727 : Rat) / 1600000000000000000000), D4 := ((154978871651785060499 : Rat) / 6400000000000000000000), LB := ((2649172023417079 : Rat) / 1000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4491946628616071428727 : Rat) / 1600000000000000000000), R := ((8985644677633928571741 : Rat) / 3200000000000000000000), D0 := ((8985644677633928571741 : Rat) / 3200000000000000000000), D1 := ((3169724357633928571741 : Rat) / 3200000000000000000000), D2 := ((800252677633928571741 : Rat) / 3200000000000000000000), D3 := ((425595157633928571741 : Rat) / 3200000000000000000000), D4 := ((38306862812499836553 : Rat) / 1600000000000000000000), LB := ((778045632124913 : Rat) / 2000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8985644677633928571741 : Rat) / 3200000000000000000000), R := ((2246849024508928571507 : Rat) / 800000000000000000000), D0 := ((2246849024508928571507 : Rat) / 800000000000000000000), D1 := ((792868944508928571507 : Rat) / 800000000000000000000), D2 := ((200501024508928571507 : Rat) / 800000000000000000000), D3 := ((106836644508928571507 : Rat) / 800000000000000000000), D4 := ((74862305223213958819 : Rat) / 3200000000000000000000), LB := ((11179817188556873 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2246849024508928571507 : Rat) / 800000000000000000000), R := ((1797829503687500000063 : Rat) / 640000000000000000000), D0 := ((1797829503687500000063 : Rat) / 640000000000000000000), D1 := ((634645439687500000063 : Rat) / 640000000000000000000), D2 := ((160751103687500000063 : Rat) / 640000000000000000000), D3 := ((85819599687500000063 : Rat) / 640000000000000000000), D4 := ((18277721205357061133 : Rat) / 800000000000000000000), LB := ((79549329757449 : Rat) / 40000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1797829503687500000063 : Rat) / 640000000000000000000), R := ((4495449469419642857301 : Rat) / 1600000000000000000000), D0 := ((4495449469419642857301 : Rat) / 1600000000000000000000), D1 := ((1587489309419642857301 : Rat) / 1600000000000000000000), D2 := ((402753469419642857301 : Rat) / 1600000000000000000000), D3 := ((215424709419642857301 : Rat) / 1600000000000000000000), D4 := ((14271892883928506049 : Rat) / 640000000000000000000), LB := ((15040081019035423 : Rat) / 5000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4495449469419642857301 : Rat) / 1600000000000000000000), R := ((8992650359241071428889 : Rat) / 3200000000000000000000), D0 := ((8992650359241071428889 : Rat) / 3200000000000000000000), D1 := ((3176730039241071428889 : Rat) / 3200000000000000000000), D2 := ((807258359241071428889 : Rat) / 3200000000000000000000), D3 := ((432600839241071428889 : Rat) / 3200000000000000000000), D4 := ((34804022008928407979 : Rat) / 1600000000000000000000), LB := ((167322873518283 : Rat) / 40000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8992650359241071428889 : Rat) / 3200000000000000000000), R := ((1124300222455357142897 : Rat) / 400000000000000000000), D0 := ((1124300222455357142897 : Rat) / 400000000000000000000), D1 := ((397310182455357142897 : Rat) / 400000000000000000000), D2 := ((101126222455357142897 : Rat) / 400000000000000000000), D3 := ((54294032455357142897 : Rat) / 400000000000000000000), D4 := ((67856623616071101671 : Rat) / 3200000000000000000000), LB := ((5521694935444299 : Rat) / 1000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1124300222455357142897 : Rat) / 400000000000000000000), R := ((35991618481785714287 : Rat) / 12800000000000000000), D0 := ((35991618481785714287 : Rat) / 12800000000000000000), D1 := ((12727937201785714287 : Rat) / 12800000000000000000), D2 := ((3250050481785714287 : Rat) / 12800000000000000000), D3 := ((1751420401785714287 : Rat) / 12800000000000000000), D4 := ((8263150401785673423 : Rat) / 400000000000000000000), LB := ((19054605110507827 : Rat) / 10000000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((35991618481785714287 : Rat) / 12800000000000000000), R := ((2250351865312500000081 : Rat) / 800000000000000000000), D0 := ((2250351865312500000081 : Rat) / 800000000000000000000), D1 := ((796371785312500000081 : Rat) / 800000000000000000000), D2 := ((204003865312500000081 : Rat) / 800000000000000000000), D3 := ((110339485312500000081 : Rat) / 800000000000000000000), D4 := ((6260236241071395881 : Rat) / 320000000000000000000), LB := ((1371289530475689 : Rat) / 250000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2250351865312500000081 : Rat) / 800000000000000000000), R := ((4502455151026785714449 : Rat) / 1600000000000000000000), D0 := ((4502455151026785714449 : Rat) / 1600000000000000000000), D1 := ((1594494991026785714449 : Rat) / 1600000000000000000000), D2 := ((409759151026785714449 : Rat) / 1600000000000000000000), D3 := ((222430391026785714449 : Rat) / 1600000000000000000000), D4 := ((14774880401785632559 : Rat) / 800000000000000000000), LB := ((394880795680983 : Rat) / 40000000000000000) },
  { w1 := ((1119787590785889 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1269660112738711 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4502455151026785714449 : Rat) / 1600000000000000000000), R := ((35189113839285714287 : Rat) / 12500000000000000000), D0 := ((35189113839285714287 : Rat) / 12500000000000000000), D1 := ((12470675089285714287 : Rat) / 12500000000000000000), D2 := ((3214926339285714287 : Rat) / 12500000000000000000), D3 := ((1751420401785714287 : Rat) / 12500000000000000000), D4 := ((27798340401785550831 : Rat) / 1600000000000000000000), LB := ((15163291070511287 : Rat) / 1000000000000000000) }
]

def block012RightChunk000L : Rat := ((90746680803571428577 : Rat) / 50000000000000000000)
def block012RightChunk000R : Rat := ((35189113839285714287 : Rat) / 12500000000000000000)

def block012RightChunk000Certificate : Bool :=
  allBoxesValid block012RightChunk000 &&
  coversFromBool block012RightChunk000 block012RightChunk000L block012RightChunk000R

theorem block012RightChunk000Certificate_eq_true :
    block012RightChunk000Certificate = true := by
  native_decide

def block012RightChainCertificate : Bool :=
  decide (
    block012RightL = ((90746680803571428577 : Rat) / 50000000000000000000) /\
    ((35189113839285714287 : Rat) / 12500000000000000000) = block012RightR)

theorem block012RightChainCertificate_eq_true :
    block012RightChainCertificate = true := by
  native_decide

def block012LeftBoxCount : Nat := boxCount block012LeftBoxes
def block012RightBoxCount : Nat := 51

def block012_rational_certificate : Prop :=
    block012LeftCertificate = true /\
    block012RightChainCertificate = true /\
    block012RightChunk000Certificate = true

theorem block012_rational_certificate_proof :
    block012_rational_certificate := by
  exact ⟨block012LeftCertificate_eq_true, block012RightChainCertificate_eq_true, block012RightChunk000Certificate_eq_true⟩

end Block012
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block012

open Set

def block012W1 : Rat := ((1119787590785889 : Rat) / 125000000000000)
def block012W2 : Rat := (0 : Rat)
def block012W3 : Rat := (0 : Rat)
def block012W4 : Rat := ((1269660112738711 : Rat) / 5000000000000000)
def block012S1 : Rat := ((18174751 : Rat) / 10000000)
def block012S2 : Rat := ((511587 : Rat) / 200000)
def block012S3 : Rat := ((107000619 : Rat) / 40000000)
def block012S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block012V (y : ℝ) : ℝ :=
  ratPotential block012W1 block012W2 block012W3 block012W4 block012S1 block012S2 block012S3 block012S4 y

def block012LeftParamsCertificate : Bool :=
  allBoxesSameParams block012LeftBoxes block012W1 block012W2 block012W3 block012W4 block012S1 block012S2 block012S3 block012S4

theorem block012LeftParamsCertificate_eq_true :
    block012LeftParamsCertificate = true := by
  native_decide

theorem block012_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block012LeftL : ℝ) (block012LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block012S1 : ℝ))
    (hy2ne : y ≠ (block012S2 : ℝ))
    (hy3ne : y ≠ (block012S3 : ℝ))
    (hy4ne : y ≠ (block012S4 : ℝ)) :
    0 < block012V y := by
  have hcert := block012LeftCertificate_eq_true
  unfold block012LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block012LeftBoxes) (lo := block012LeftL) (hi := block012LeftR)
    (w1 := block012W1) (w2 := block012W2) (w3 := block012W3) (w4 := block012W4)
    (s1 := block012S1) (s2 := block012S2) (s3 := block012S3) (s4 := block012S4)
    hboxes hcover block012LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block012RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block012RightChunk000 block012W1 block012W2 block012W3 block012W4 block012S1 block012S2 block012S3 block012S4

theorem block012RightChunk000ParamsCertificate_eq_true :
    block012RightChunk000ParamsCertificate = true := by
  native_decide

theorem block012_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block012RightChunk000L : ℝ) (block012RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block012S1 : ℝ))
    (hy2ne : y ≠ (block012S2 : ℝ))
    (hy3ne : y ≠ (block012S3 : ℝ))
    (hy4ne : y ≠ (block012S4 : ℝ)) :
    0 < block012V y := by
  have hcert := block012RightChunk000Certificate_eq_true
  unfold block012RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block012RightChunk000) (lo := block012RightChunk000L) (hi := block012RightChunk000R)
    (w1 := block012W1) (w2 := block012W2) (w3 := block012W3) (w4 := block012W4)
    (s1 := block012S1) (s2 := block012S2) (s3 := block012S3) (s4 := block012S4)
    hboxes hcover block012RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block012_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block012RightL : ℝ) (block012RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block012S1 : ℝ))
    (hy2ne : y ≠ (block012S2 : ℝ))
    (hy3ne : y ≠ (block012S3 : ℝ))
    (hy4ne : y ≠ (block012S4 : ℝ)) :
    0 < block012V y := by
  have hL : (block012RightChunk000L : ℝ) = (block012RightL : ℝ) := by
    norm_num [block012RightChunk000L, block012RightL]
  have hR : (block012RightChunk000R : ℝ) = (block012RightR : ℝ) := by
    norm_num [block012RightChunk000R, block012RightR]
  have hyc : y ∈ Icc (block012RightChunk000L : ℝ) (block012RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block012_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block012_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block012LeftL : ℝ) (block012LeftR : ℝ) →
    y ≠ 0 → y ≠ (block012S1 : ℝ) → y ≠ (block012S2 : ℝ) →
    y ≠ (block012S3 : ℝ) → y ≠ (block012S4 : ℝ) → 0 < block012V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block012RightL : ℝ) (block012RightR : ℝ) →
    y ≠ 0 → y ≠ (block012S1 : ℝ) → y ≠ (block012S2 : ℝ) →
    y ≠ (block012S3 : ℝ) → y ≠ (block012S4 : ℝ) → 0 < block012V y)

theorem block012_reallog_certificate_proof :
    block012_reallog_certificate := by
  exact ⟨block012_left_V_pos, block012_right_V_pos⟩

end Block012
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block012.block012V
#check Erdos1038Lean.M1817475.Block012.block012_left_V_pos
#check Erdos1038Lean.M1817475.Block012.block012_right_V_pos
#check Erdos1038Lean.M1817475.Block012.block012_reallog_certificate_proof
