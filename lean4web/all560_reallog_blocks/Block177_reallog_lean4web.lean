/-
Self-contained Lean4Web paste file.
Block 177 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block177

def block177LeftL : Rat := ((19566939732142857181 : Rat) / 25000000000000000000)
def block177LeftR : Rat := ((39143654017857142933 : Rat) / 50000000000000000000)
def block177RightL : Rat := ((44566939732142857181 : Rat) / 25000000000000000000)
def block177RightR : Rat := ((139143654017857142933 : Rat) / 50000000000000000000)

def block177LeftBoxes : List RatBox := [
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((19566939732142857181 : Rat) / 25000000000000000000), R := ((39143654017857142933 : Rat) / 50000000000000000000), D0 := ((39143654017857142933 : Rat) / 50000000000000000000), D1 := ((25869937767857142819 : Rat) / 25000000000000000000), D2 := ((44381435267857142819 : Rat) / 25000000000000000000), D3 := ((6068726930803571417 : Rat) / 3125000000000000000), D4 := ((50045324642857140319 : Rat) / 25000000000000000000), LB := ((6958830310297079 : Rat) / 5000000000000000000) }
]

def block177LeftCertificate : Bool :=
  allBoxesValid block177LeftBoxes &&
  coversFromBool block177LeftBoxes block177LeftL block177LeftR

theorem block177LeftCertificate_eq_true :
    block177LeftCertificate = true := by
  native_decide

def block177RightChunk000 : List RatBox := [
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((44566939732142857181 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((869937767857142819 : Rat) / 25000000000000000000), D2 := ((19381435267857142819 : Rat) / 25000000000000000000), D3 := ((2943726930803571417 : Rat) / 3125000000000000000), D4 := ((25045324642857140319 : Rat) / 25000000000000000000), LB := ((11281832909755611 : Rat) / 2000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((22679877678571428517 : Rat) / 25000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((337519761208011 : Rat) / 312500000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((13424128928571428517 : Rat) / 25000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((38304241369222747 : Rat) / 100000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((8796254553571428517 : Rat) / 25000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((1670340375436521 : Rat) / 10000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((6482317366071428517 : Rat) / 25000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((9733976892492899 : Rat) / 100000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((5325348772321428517 : Rat) / 25000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((2054410686143343 : Rat) / 250000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((515755380178571428517 : Rat) / 200000000000000000000), D0 := ((515755380178571428517 : Rat) / 200000000000000000000), D1 := ((152260360178571428517 : Rat) / 200000000000000000000), D2 := ((4168380178571428517 : Rat) / 200000000000000000000), D3 := ((4168380178571428517 : Rat) / 25000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((1720643774790881 : Rat) / 200000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((515755380178571428517 : Rat) / 200000000000000000000), R := ((1035679140535714285551 : Rat) / 400000000000000000000), D0 := ((1035679140535714285551 : Rat) / 400000000000000000000), D1 := ((308689100535714285551 : Rat) / 400000000000000000000), D2 := ((12505140535714285551 : Rat) / 400000000000000000000), D3 := ((29178661249999999619 : Rat) / 200000000000000000000), D4 := ((41142734821428551483 : Rat) / 200000000000000000000), LB := ((11612507153021229 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1035679140535714285551 : Rat) / 400000000000000000000), R := ((259961880178571428517 : Rat) / 100000000000000000000), D0 := ((259961880178571428517 : Rat) / 100000000000000000000), D1 := ((78214370178571428517 : Rat) / 100000000000000000000), D2 := ((4168380178571428517 : Rat) / 100000000000000000000), D3 := ((54188942321428570721 : Rat) / 400000000000000000000), D4 := ((78117089464285674449 : Rat) / 400000000000000000000), LB := ((955500694977407 : Rat) / 2000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((259961880178571428517 : Rat) / 100000000000000000000), R := ((2083863421607142856653 : Rat) / 800000000000000000000), D0 := ((2083863421607142856653 : Rat) / 800000000000000000000), D1 := ((629883341607142856653 : Rat) / 800000000000000000000), D2 := ((37515421607142856653 : Rat) / 800000000000000000000), D3 := ((12505140535714285551 : Rat) / 100000000000000000000), D4 := ((18487177321428561483 : Rat) / 100000000000000000000), LB := ((2610594306920913 : Rat) / 500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2083863421607142856653 : Rat) / 800000000000000000000), R := ((208803180178571428517 : Rat) / 80000000000000000000), D0 := ((208803180178571428517 : Rat) / 80000000000000000000), D1 := ((63405172178571428517 : Rat) / 80000000000000000000), D2 := ((4168380178571428517 : Rat) / 80000000000000000000), D3 := ((95872744107142855891 : Rat) / 800000000000000000000), D4 := ((143729038392857063347 : Rat) / 800000000000000000000), LB := ((2681061454666983 : Rat) / 2500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((208803180178571428517 : Rat) / 80000000000000000000), R := ((4180231983749999998857 : Rat) / 1600000000000000000000), D0 := ((4180231983749999998857 : Rat) / 1600000000000000000000), D1 := ((1272271823749999998857 : Rat) / 1600000000000000000000), D2 := ((87535983749999998857 : Rat) / 1600000000000000000000), D3 := ((45852181964285713687 : Rat) / 400000000000000000000), D4 := ((13956065821428563483 : Rat) / 80000000000000000000), LB := ((1119910223855193 : Rat) / 250000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4180231983749999998857 : Rat) / 1600000000000000000000), R := ((2092200181964285713687 : Rat) / 800000000000000000000), D0 := ((2092200181964285713687 : Rat) / 800000000000000000000), D1 := ((638220101964285713687 : Rat) / 800000000000000000000), D2 := ((45852181964285713687 : Rat) / 800000000000000000000), D3 := ((179240347678571426231 : Rat) / 1600000000000000000000), D4 := ((274952936249999841143 : Rat) / 1600000000000000000000), LB := ((176656521617009 : Rat) / 62500000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2092200181964285713687 : Rat) / 800000000000000000000), R := ((4188568744107142855891 : Rat) / 1600000000000000000000), D0 := ((4188568744107142855891 : Rat) / 1600000000000000000000), D1 := ((1280608584107142855891 : Rat) / 1600000000000000000000), D2 := ((95872744107142855891 : Rat) / 1600000000000000000000), D3 := ((87535983749999998857 : Rat) / 800000000000000000000), D4 := ((135392278035714206313 : Rat) / 800000000000000000000), LB := ((818791775836613 : Rat) / 625000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4188568744107142855891 : Rat) / 1600000000000000000000), R := ((8381305868392857140299 : Rat) / 3200000000000000000000), D0 := ((8381305868392857140299 : Rat) / 3200000000000000000000), D1 := ((2565385548392857140299 : Rat) / 3200000000000000000000), D2 := ((195913868392857140299 : Rat) / 3200000000000000000000), D3 := ((170903587321428569197 : Rat) / 1600000000000000000000), D4 := ((266616175892856984109 : Rat) / 1600000000000000000000), LB := ((1721806343636001 : Rat) / 500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8381305868392857140299 : Rat) / 3200000000000000000000), R := ((524092140535714285551 : Rat) / 200000000000000000000), D0 := ((524092140535714285551 : Rat) / 200000000000000000000), D1 := ((160597120535714285551 : Rat) / 200000000000000000000), D2 := ((12505140535714285551 : Rat) / 200000000000000000000), D3 := ((337638794464285709877 : Rat) / 3200000000000000000000), D4 := ((529063971607142539701 : Rat) / 3200000000000000000000), LB := ((14030148758550909 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((524092140535714285551 : Rat) / 200000000000000000000), R := ((8389642628749999997333 : Rat) / 3200000000000000000000), D0 := ((8389642628749999997333 : Rat) / 3200000000000000000000), D1 := ((2573722308749999997333 : Rat) / 3200000000000000000000), D2 := ((204250628749999997333 : Rat) / 3200000000000000000000), D3 := ((4168380178571428517 : Rat) / 40000000000000000000), D4 := ((32805974464285694449 : Rat) / 200000000000000000000), LB := ((2205992518512251 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8389642628749999997333 : Rat) / 3200000000000000000000), R := ((167876220178571428517 : Rat) / 64000000000000000000), D0 := ((167876220178571428517 : Rat) / 64000000000000000000), D1 := ((51557813778571428517 : Rat) / 64000000000000000000), D2 := ((4168380178571428517 : Rat) / 64000000000000000000), D3 := ((329302034107142852843 : Rat) / 3200000000000000000000), D4 := ((520727211249999682667 : Rat) / 3200000000000000000000), LB := ((131539853626641 : Rat) / 80000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((167876220178571428517 : Rat) / 64000000000000000000), R := ((8397979389107142854367 : Rat) / 3200000000000000000000), D0 := ((8397979389107142854367 : Rat) / 3200000000000000000000), D1 := ((2582059069107142854367 : Rat) / 3200000000000000000000), D2 := ((212587389107142854367 : Rat) / 3200000000000000000000), D3 := ((162566826964285712163 : Rat) / 1600000000000000000000), D4 := ((10331176621428565083 : Rat) / 64000000000000000000), LB := ((1121571857566811 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8397979389107142854367 : Rat) / 3200000000000000000000), R := ((2100536942321428570721 : Rat) / 800000000000000000000), D0 := ((2100536942321428570721 : Rat) / 800000000000000000000), D1 := ((646556862321428570721 : Rat) / 800000000000000000000), D2 := ((54188942321428570721 : Rat) / 800000000000000000000), D3 := ((320965273749999995809 : Rat) / 3200000000000000000000), D4 := ((512390450892856825633 : Rat) / 3200000000000000000000), LB := ((6387680955054209 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2100536942321428570721 : Rat) / 800000000000000000000), R := ((8406316149464285711401 : Rat) / 3200000000000000000000), D0 := ((8406316149464285711401 : Rat) / 3200000000000000000000), D1 := ((2590395829464285711401 : Rat) / 3200000000000000000000), D2 := ((220924149464285711401 : Rat) / 3200000000000000000000), D3 := ((79199223392857141823 : Rat) / 800000000000000000000), D4 := ((127055517678571349279 : Rat) / 800000000000000000000), LB := ((491680627781807 : Rat) / 2500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8406316149464285711401 : Rat) / 3200000000000000000000), R := ((16816800679107142851319 : Rat) / 6400000000000000000000), D0 := ((16816800679107142851319 : Rat) / 6400000000000000000000), D1 := ((5184960039107142851319 : Rat) / 6400000000000000000000), D2 := ((446016679107142851319 : Rat) / 6400000000000000000000), D3 := ((12505140535714285551 : Rat) / 128000000000000000000), D4 := ((504053690535713968599 : Rat) / 3200000000000000000000), LB := ((15343530767726599 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16816800679107142851319 : Rat) / 6400000000000000000000), R := ((4205242264821428569959 : Rat) / 1600000000000000000000), D0 := ((4205242264821428569959 : Rat) / 1600000000000000000000), D1 := ((1297282104821428569959 : Rat) / 1600000000000000000000), D2 := ((112546264821428569959 : Rat) / 1600000000000000000000), D3 := ((621088646607142849033 : Rat) / 6400000000000000000000), D4 := ((1003939000892856508681 : Rat) / 6400000000000000000000), LB := ((1348706256880161 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4205242264821428569959 : Rat) / 1600000000000000000000), R := ((16825137439464285708353 : Rat) / 6400000000000000000000), D0 := ((16825137439464285708353 : Rat) / 6400000000000000000000), D1 := ((5193296799464285708353 : Rat) / 6400000000000000000000), D2 := ((454353439464285708353 : Rat) / 6400000000000000000000), D3 := ((154230066607142855129 : Rat) / 1600000000000000000000), D4 := ((249942655178571270041 : Rat) / 1600000000000000000000), LB := ((5868981511129717 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16825137439464285708353 : Rat) / 6400000000000000000000), R := ((1682930581964285713687 : Rat) / 640000000000000000000), D0 := ((1682930581964285713687 : Rat) / 640000000000000000000), D1 := ((519746517964285713687 : Rat) / 640000000000000000000), D2 := ((45852181964285713687 : Rat) / 640000000000000000000), D3 := ((612751886249999991999 : Rat) / 6400000000000000000000), D4 := ((995602240535713651647 : Rat) / 6400000000000000000000), LB := ((10097415758746897 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1682930581964285713687 : Rat) / 640000000000000000000), R := ((16833474199821428565387 : Rat) / 6400000000000000000000), D0 := ((16833474199821428565387 : Rat) / 6400000000000000000000), D1 := ((5201633559821428565387 : Rat) / 6400000000000000000000), D2 := ((462690199821428565387 : Rat) / 6400000000000000000000), D3 := ((304291753035714281741 : Rat) / 3200000000000000000000), D4 := ((99143386035714222313 : Rat) / 640000000000000000000), LB := ((8566628052515957 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16833474199821428565387 : Rat) / 6400000000000000000000), R := ((1052352661249999999619 : Rat) / 400000000000000000000), D0 := ((1052352661249999999619 : Rat) / 400000000000000000000), D1 := ((325362621249999999619 : Rat) / 400000000000000000000), D2 := ((29178661249999999619 : Rat) / 400000000000000000000), D3 := ((120883025178571426993 : Rat) / 1280000000000000000000), D4 := ((987265480178570794613 : Rat) / 6400000000000000000000), LB := ((7146831452345959 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1052352661249999999619 : Rat) / 400000000000000000000), R := ((16841810960178571422421 : Rat) / 6400000000000000000000), D0 := ((16841810960178571422421 : Rat) / 6400000000000000000000), D1 := ((5209970320178571422421 : Rat) / 6400000000000000000000), D2 := ((471026960178571422421 : Rat) / 6400000000000000000000), D3 := ((37515421607142856653 : Rat) / 400000000000000000000), D4 := ((61443568749999960381 : Rat) / 400000000000000000000), LB := ((5839282433941217 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16841810960178571422421 : Rat) / 6400000000000000000000), R := ((8422989670178571425469 : Rat) / 3200000000000000000000), D0 := ((8422989670178571425469 : Rat) / 3200000000000000000000), D1 := ((2607069350178571425469 : Rat) / 3200000000000000000000), D2 := ((237597670178571425469 : Rat) / 3200000000000000000000), D3 := ((596078365535714277931 : Rat) / 6400000000000000000000), D4 := ((978928719821427937579 : Rat) / 6400000000000000000000), LB := ((4645263074654349 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8422989670178571425469 : Rat) / 3200000000000000000000), R := ((3370029544107142855891 : Rat) / 1280000000000000000000), D0 := ((3370029544107142855891 : Rat) / 1280000000000000000000), D1 := ((1043661416107142855891 : Rat) / 1280000000000000000000), D2 := ((95872744107142855891 : Rat) / 1280000000000000000000), D3 := ((295954992678571424707 : Rat) / 3200000000000000000000), D4 := ((487380169821428254531 : Rat) / 3200000000000000000000), LB := ((7132163502994171 : Rat) / 20000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370029544107142855891 : Rat) / 1280000000000000000000), R := ((4213579025178571426993 : Rat) / 1600000000000000000000), D0 := ((4213579025178571426993 : Rat) / 1600000000000000000000), D1 := ((1305618865178571426993 : Rat) / 1600000000000000000000), D2 := ((120883025178571426993 : Rat) / 1600000000000000000000), D3 := ((587741605178571420897 : Rat) / 6400000000000000000000), D4 := ((194118391892857016109 : Rat) / 1280000000000000000000), LB := ((2603073863422789 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4213579025178571426993 : Rat) / 1600000000000000000000), R := ((16858484480892857136489 : Rat) / 6400000000000000000000), D0 := ((16858484480892857136489 : Rat) / 6400000000000000000000), D1 := ((5226643840892857136489 : Rat) / 6400000000000000000000), D2 := ((487700480892857136489 : Rat) / 6400000000000000000000), D3 := ((29178661249999999619 : Rat) / 320000000000000000000), D4 := ((241605894821428413007 : Rat) / 1600000000000000000000), LB := ((1098501611784819 : Rat) / 6250000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16858484480892857136489 : Rat) / 6400000000000000000000), R := ((8431326430535714282503 : Rat) / 3200000000000000000000), D0 := ((8431326430535714282503 : Rat) / 3200000000000000000000), D1 := ((2615406110535714282503 : Rat) / 3200000000000000000000), D2 := ((245934430535714282503 : Rat) / 3200000000000000000000), D3 := ((579404844821428563863 : Rat) / 6400000000000000000000), D4 := ((962255199107142223511 : Rat) / 6400000000000000000000), LB := ((1288824512019407 : Rat) / 12500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8431326430535714282503 : Rat) / 3200000000000000000000), R := ((16866821241249999993523 : Rat) / 6400000000000000000000), D0 := ((16866821241249999993523 : Rat) / 6400000000000000000000), D1 := ((5234980601249999993523 : Rat) / 6400000000000000000000), D2 := ((496037241249999993523 : Rat) / 6400000000000000000000), D3 := ((287618232321428567673 : Rat) / 3200000000000000000000), D4 := ((479043409464285397497 : Rat) / 3200000000000000000000), LB := ((26554125770583 : Rat) / 625000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16866821241249999993523 : Rat) / 6400000000000000000000), R := ((33737810862678571415563 : Rat) / 12800000000000000000000), D0 := ((33737810862678571415563 : Rat) / 12800000000000000000000), D1 := ((10474129582678571415563 : Rat) / 12800000000000000000000), D2 := ((996242862678571415563 : Rat) / 12800000000000000000000), D3 := ((571068084464285706829 : Rat) / 6400000000000000000000), D4 := ((953918438749999366477 : Rat) / 6400000000000000000000), LB := ((8555084122580381 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33737810862678571415563 : Rat) / 12800000000000000000000), R := ((421774740535714285551 : Rat) / 160000000000000000000), D0 := ((421774740535714285551 : Rat) / 160000000000000000000), D1 := ((130978724535714285551 : Rat) / 160000000000000000000), D2 := ((12505140535714285551 : Rat) / 160000000000000000000), D3 := ((1137967788749999985141 : Rat) / 12800000000000000000000), D4 := ((1903668497321427304437 : Rat) / 12800000000000000000000), LB := ((8355937281874781 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((421774740535714285551 : Rat) / 160000000000000000000), R := ((33746147623035714272597 : Rat) / 12800000000000000000000), D0 := ((33746147623035714272597 : Rat) / 12800000000000000000000), D1 := ((10482466343035714272597 : Rat) / 12800000000000000000000), D2 := ((1004579623035714272597 : Rat) / 12800000000000000000000), D3 := ((70862463035714284789 : Rat) / 800000000000000000000), D4 := ((23743751464285698449 : Rat) / 160000000000000000000), LB := ((8187801286208551 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33746147623035714272597 : Rat) / 12800000000000000000000), R := ((16875158001607142850557 : Rat) / 6400000000000000000000), D0 := ((16875158001607142850557 : Rat) / 6400000000000000000000), D1 := ((5243317361607142850557 : Rat) / 6400000000000000000000), D2 := ((504374001607142850557 : Rat) / 6400000000000000000000), D3 := ((1129631028392857128107 : Rat) / 12800000000000000000000), D4 := ((1895331736964284447403 : Rat) / 12800000000000000000000), LB := ((4025433205737533 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16875158001607142850557 : Rat) / 6400000000000000000000), R := ((33754484383392857129631 : Rat) / 12800000000000000000000), D0 := ((33754484383392857129631 : Rat) / 12800000000000000000000), D1 := ((10490803103392857129631 : Rat) / 12800000000000000000000), D2 := ((1012916383392857129631 : Rat) / 12800000000000000000000), D3 := ((112546264821428569959 : Rat) / 1280000000000000000000), D4 := ((945581678392856509443 : Rat) / 6400000000000000000000), LB := ((3972662493226947 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33754484383392857129631 : Rat) / 12800000000000000000000), R := ((8439663190892857139537 : Rat) / 3200000000000000000000), D0 := ((8439663190892857139537 : Rat) / 3200000000000000000000), D1 := ((2623742870892857139537 : Rat) / 3200000000000000000000), D2 := ((254271190892857139537 : Rat) / 3200000000000000000000), D3 := ((1121294268035714271073 : Rat) / 12800000000000000000000), D4 := ((1886994976607141590369 : Rat) / 12800000000000000000000), LB := ((983921427803007 : Rat) / 1250000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8439663190892857139537 : Rat) / 3200000000000000000000), R := ((6752564228749999997333 : Rat) / 2560000000000000000000), D0 := ((6752564228749999997333 : Rat) / 2560000000000000000000), D1 := ((2099827972749999997333 : Rat) / 2560000000000000000000), D2 := ((204250628749999997333 : Rat) / 2560000000000000000000), D3 := ((279281471964285710639 : Rat) / 3200000000000000000000), D4 := ((470706649107142540463 : Rat) / 3200000000000000000000), LB := ((7829202243376243 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((6752564228749999997333 : Rat) / 2560000000000000000000), R := ((16883494761964285707591 : Rat) / 6400000000000000000000), D0 := ((16883494761964285707591 : Rat) / 6400000000000000000000), D1 := ((5251654121964285707591 : Rat) / 6400000000000000000000), D2 := ((512710761964285707591 : Rat) / 6400000000000000000000), D3 := ((1112957507678571414039 : Rat) / 12800000000000000000000), D4 := ((375731643249999746667 : Rat) / 2560000000000000000000), LB := ((7819016116795141 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16883494761964285707591 : Rat) / 6400000000000000000000), R := ((33771157904107142843699 : Rat) / 12800000000000000000000), D0 := ((33771157904107142843699 : Rat) / 12800000000000000000000), D1 := ((10507476624107142843699 : Rat) / 12800000000000000000000), D2 := ((1029589904107142843699 : Rat) / 12800000000000000000000), D3 := ((554394563749999992761 : Rat) / 6400000000000000000000), D4 := ((937244918035713652409 : Rat) / 6400000000000000000000), LB := ((3920506942478169 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33771157904107142843699 : Rat) / 12800000000000000000000), R := ((4221915785535714284027 : Rat) / 1600000000000000000000), D0 := ((4221915785535714284027 : Rat) / 1600000000000000000000), D1 := ((1313955625535714284027 : Rat) / 1600000000000000000000), D2 := ((129219785535714284027 : Rat) / 1600000000000000000000), D3 := ((220924149464285711401 : Rat) / 2560000000000000000000), D4 := ((1870321455892855876301 : Rat) / 12800000000000000000000), LB := ((1973849649211587 : Rat) / 2500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4221915785535714284027 : Rat) / 1600000000000000000000), R := ((33779494664464285700733 : Rat) / 12800000000000000000000), D0 := ((33779494664464285700733 : Rat) / 12800000000000000000000), D1 := ((10515813384464285700733 : Rat) / 12800000000000000000000), D2 := ((1037926664464285700733 : Rat) / 12800000000000000000000), D3 := ((137556545892857141061 : Rat) / 1600000000000000000000), D4 := ((233269134464285555973 : Rat) / 1600000000000000000000), LB := ((7982375540627751 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33779494664464285700733 : Rat) / 12800000000000000000000), R := ((135134652178571428517 : Rat) / 51200000000000000000), D0 := ((135134652178571428517 : Rat) / 51200000000000000000), D1 := ((42079927058571428517 : Rat) / 51200000000000000000), D2 := ((4168380178571428517 : Rat) / 51200000000000000000), D3 := ((1096283986964285699971 : Rat) / 12800000000000000000000), D4 := ((1861984695535713019267 : Rat) / 12800000000000000000000), LB := ((324086091073017 : Rat) / 400000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((135134652178571428517 : Rat) / 51200000000000000000), R := ((33787831424821428557767 : Rat) / 12800000000000000000000), D0 := ((33787831424821428557767 : Rat) / 12800000000000000000000), D1 := ((10524150144821428557767 : Rat) / 12800000000000000000000), D2 := ((1046263424821428557767 : Rat) / 12800000000000000000000), D3 := ((546057803392857135727 : Rat) / 6400000000000000000000), D4 := ((7431265261428566363 : Rat) / 51200000000000000000), LB := ((8254938671972689 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((33787831424821428557767 : Rat) / 12800000000000000000000), R := ((8447999951249999996571 : Rat) / 3200000000000000000000), D0 := ((8447999951249999996571 : Rat) / 3200000000000000000000), D1 := ((2632079631249999996571 : Rat) / 3200000000000000000000), D2 := ((262607951249999996571 : Rat) / 3200000000000000000000), D3 := ((1087947226607142842937 : Rat) / 12800000000000000000000), D4 := ((1853647935178570162233 : Rat) / 12800000000000000000000), LB := ((8440946933007953 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8447999951249999996571 : Rat) / 3200000000000000000000), R := ((16900168282678571421659 : Rat) / 6400000000000000000000), D0 := ((16900168282678571421659 : Rat) / 6400000000000000000000), D1 := ((5268327642678571421659 : Rat) / 6400000000000000000000), D2 := ((529384282678571421659 : Rat) / 6400000000000000000000), D3 := ((54188942321428570721 : Rat) / 640000000000000000000), D4 := ((462369888749999683429 : Rat) / 3200000000000000000000), LB := ((2219783500380379 : Rat) / 250000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16900168282678571421659 : Rat) / 6400000000000000000000), R := ((132065130178571428517 : Rat) / 50000000000000000000), D0 := ((132065130178571428517 : Rat) / 50000000000000000000), D1 := ((41191375178571428517 : Rat) / 50000000000000000000), D2 := ((4168380178571428517 : Rat) / 50000000000000000000), D3 := ((537721043035714278693 : Rat) / 6400000000000000000000), D4 := ((920571397321427938341 : Rat) / 6400000000000000000000), LB := ((3174836911820633 : Rat) / 50000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((132065130178571428517 : Rat) / 50000000000000000000), R := ((16908505043035714278693 : Rat) / 6400000000000000000000), D0 := ((16908505043035714278693 : Rat) / 6400000000000000000000), D1 := ((5276664403035714278693 : Rat) / 6400000000000000000000), D2 := ((537721043035714278693 : Rat) / 6400000000000000000000), D3 := ((4168380178571428517 : Rat) / 50000000000000000000), D4 := ((7159398571428566483 : Rat) / 50000000000000000000), LB := ((1317515859820817 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16908505043035714278693 : Rat) / 6400000000000000000000), R := ((1691267342321428570721 : Rat) / 640000000000000000000), D0 := ((1691267342321428570721 : Rat) / 640000000000000000000), D1 := ((528083278321428570721 : Rat) / 640000000000000000000), D2 := ((54188942321428570721 : Rat) / 640000000000000000000), D3 := ((529384282678571421659 : Rat) / 6400000000000000000000), D4 := ((912234636964285081307 : Rat) / 6400000000000000000000), LB := ((21382426969709933 : Rat) / 100000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1691267342321428570721 : Rat) / 640000000000000000000), R := ((16916841803392857135727 : Rat) / 6400000000000000000000), D0 := ((16916841803392857135727 : Rat) / 6400000000000000000000), D1 := ((5285001163392857135727 : Rat) / 6400000000000000000000), D2 := ((546057803392857135727 : Rat) / 6400000000000000000000), D3 := ((262607951249999996571 : Rat) / 3200000000000000000000), D4 := ((90806625678571365279 : Rat) / 640000000000000000000), LB := ((15494977123518827 : Rat) / 50000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16916841803392857135727 : Rat) / 6400000000000000000000), R := ((4230252545892857141061 : Rat) / 1600000000000000000000), D0 := ((4230252545892857141061 : Rat) / 1600000000000000000000), D1 := ((1322292385892857141061 : Rat) / 1600000000000000000000), D2 := ((137556545892857141061 : Rat) / 1600000000000000000000), D3 := ((4168380178571428517 : Rat) / 51200000000000000000), D4 := ((903897876607142224273 : Rat) / 6400000000000000000000), LB := ((42016644732456587 : Rat) / 100000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4230252545892857141061 : Rat) / 1600000000000000000000), R := ((16925178563749999992761 : Rat) / 6400000000000000000000), D0 := ((16925178563749999992761 : Rat) / 6400000000000000000000), D1 := ((5293337923749999992761 : Rat) / 6400000000000000000000), D2 := ((554394563749999992761 : Rat) / 6400000000000000000000), D3 := ((129219785535714284027 : Rat) / 1600000000000000000000), D4 := ((224932374107142698939 : Rat) / 1600000000000000000000), LB := ((5448184516215759 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16925178563749999992761 : Rat) / 6400000000000000000000), R := ((8464673471964285710639 : Rat) / 3200000000000000000000), D0 := ((8464673471964285710639 : Rat) / 3200000000000000000000), D1 := ((2648753151964285710639 : Rat) / 3200000000000000000000), D2 := ((279281471964285710639 : Rat) / 3200000000000000000000), D3 := ((512710761964285707591 : Rat) / 6400000000000000000000), D4 := ((895561116249999367239 : Rat) / 6400000000000000000000), LB := ((855066983558167 : Rat) / 1250000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8464673471964285710639 : Rat) / 3200000000000000000000), R := ((3386703064821428569959 : Rat) / 1280000000000000000000), D0 := ((3386703064821428569959 : Rat) / 1280000000000000000000), D1 := ((1060334936821428569959 : Rat) / 1280000000000000000000), D2 := ((112546264821428569959 : Rat) / 1280000000000000000000), D3 := ((254271190892857139537 : Rat) / 3200000000000000000000), D4 := ((445696368035713969361 : Rat) / 3200000000000000000000), LB := ((8380745940100021 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386703064821428569959 : Rat) / 1280000000000000000000), R := ((2117210463035714284789 : Rat) / 800000000000000000000), D0 := ((2117210463035714284789 : Rat) / 800000000000000000000), D1 := ((663230383035714284789 : Rat) / 800000000000000000000), D2 := ((70862463035714284789 : Rat) / 800000000000000000000), D3 := ((504374001607142850557 : Rat) / 6400000000000000000000), D4 := ((177444871178571302041 : Rat) / 1280000000000000000000), LB := ((10070890749580563 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2117210463035714284789 : Rat) / 800000000000000000000), R := ((16941852084464285706829 : Rat) / 6400000000000000000000), D0 := ((16941852084464285706829 : Rat) / 6400000000000000000000), D1 := ((5310011444464285706829 : Rat) / 6400000000000000000000), D2 := ((571068084464285706829 : Rat) / 6400000000000000000000), D3 := ((12505140535714285551 : Rat) / 160000000000000000000), D4 := ((110381996964285635211 : Rat) / 800000000000000000000), LB := ((29782741246763 : Rat) / 25000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16941852084464285706829 : Rat) / 6400000000000000000000), R := ((8473010232321428567673 : Rat) / 3200000000000000000000), D0 := ((8473010232321428567673 : Rat) / 3200000000000000000000), D1 := ((2657089912321428567673 : Rat) / 3200000000000000000000), D2 := ((287618232321428567673 : Rat) / 3200000000000000000000), D3 := ((496037241249999993523 : Rat) / 6400000000000000000000), D4 := ((878887595535713653171 : Rat) / 6400000000000000000000), LB := ((13909541212716037 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8473010232321428567673 : Rat) / 3200000000000000000000), R := ((16950188844821428563863 : Rat) / 6400000000000000000000), D0 := ((16950188844821428563863 : Rat) / 6400000000000000000000), D1 := ((5318348204821428563863 : Rat) / 6400000000000000000000), D2 := ((579404844821428563863 : Rat) / 6400000000000000000000), D3 := ((245934430535714282503 : Rat) / 3200000000000000000000), D4 := ((437359607678571112327 : Rat) / 3200000000000000000000), LB := ((8031228224294057 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((16950188844821428563863 : Rat) / 6400000000000000000000), R := ((847717861249999999619 : Rat) / 320000000000000000000), D0 := ((847717861249999999619 : Rat) / 320000000000000000000), D1 := ((266125829249999999619 : Rat) / 320000000000000000000), D2 := ((29178661249999999619 : Rat) / 320000000000000000000), D3 := ((487700480892857136489 : Rat) / 6400000000000000000000), D4 := ((870550835178570796137 : Rat) / 6400000000000000000000), LB := ((18374129075107437 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((847717861249999999619 : Rat) / 320000000000000000000), R := ((8481346992678571424707 : Rat) / 3200000000000000000000), D0 := ((8481346992678571424707 : Rat) / 3200000000000000000000), D1 := ((2665426672678571424707 : Rat) / 3200000000000000000000), D2 := ((295954992678571424707 : Rat) / 3200000000000000000000), D3 := ((120883025178571426993 : Rat) / 1600000000000000000000), D4 := ((43319122749999968381 : Rat) / 320000000000000000000), LB := ((970495688988049 : Rat) / 2500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8481346992678571424707 : Rat) / 3200000000000000000000), R := ((1060689421607142856653 : Rat) / 400000000000000000000), D0 := ((1060689421607142856653 : Rat) / 400000000000000000000), D1 := ((333699381607142856653 : Rat) / 400000000000000000000), D2 := ((37515421607142856653 : Rat) / 400000000000000000000), D3 := ((237597670178571425469 : Rat) / 3200000000000000000000), D4 := ((429022847321428255293 : Rat) / 3200000000000000000000), LB := ((2336094279433501 : Rat) / 2500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1060689421607142856653 : Rat) / 400000000000000000000), R := ((8489683753035714281741 : Rat) / 3200000000000000000000), D0 := ((8489683753035714281741 : Rat) / 3200000000000000000000), D1 := ((2673763433035714281741 : Rat) / 3200000000000000000000), D2 := ((304291753035714281741 : Rat) / 3200000000000000000000), D3 := ((29178661249999999619 : Rat) / 400000000000000000000), D4 := ((53106808392857103347 : Rat) / 400000000000000000000), LB := ((3870187567934849 : Rat) / 2500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8489683753035714281741 : Rat) / 3200000000000000000000), R := ((4246926066607142855129 : Rat) / 1600000000000000000000), D0 := ((4246926066607142855129 : Rat) / 1600000000000000000000), D1 := ((1338965906607142855129 : Rat) / 1600000000000000000000), D2 := ((154230066607142855129 : Rat) / 1600000000000000000000), D3 := ((45852181964285713687 : Rat) / 640000000000000000000), D4 := ((420686086964285398259 : Rat) / 3200000000000000000000), LB := ((22312121411233177 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4246926066607142855129 : Rat) / 1600000000000000000000), R := ((339920820535714285551 : Rat) / 128000000000000000000), D0 := ((339920820535714285551 : Rat) / 128000000000000000000), D1 := ((107284007735714285551 : Rat) / 128000000000000000000), D2 := ((12505140535714285551 : Rat) / 128000000000000000000), D3 := ((112546264821428569959 : Rat) / 1600000000000000000000), D4 := ((208258853392856984871 : Rat) / 1600000000000000000000), LB := ((14930316253952691 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((339920820535714285551 : Rat) / 128000000000000000000), R := ((2125547223392857141823 : Rat) / 800000000000000000000), D0 := ((2125547223392857141823 : Rat) / 800000000000000000000), D1 := ((671567143392857141823 : Rat) / 800000000000000000000), D2 := ((79199223392857141823 : Rat) / 800000000000000000000), D3 := ((220924149464285711401 : Rat) / 3200000000000000000000), D4 := ((16493973064285701649 : Rat) / 128000000000000000000), LB := ((19074815228630193 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2125547223392857141823 : Rat) / 800000000000000000000), R := ((4255262826964285712163 : Rat) / 1600000000000000000000), D0 := ((4255262826964285712163 : Rat) / 1600000000000000000000), D1 := ((1347302666964285712163 : Rat) / 1600000000000000000000), D2 := ((162566826964285712163 : Rat) / 1600000000000000000000), D3 := ((54188942321428570721 : Rat) / 800000000000000000000), D4 := ((102045236607142778177 : Rat) / 800000000000000000000), LB := ((1359336474067857 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4255262826964285712163 : Rat) / 1600000000000000000000), R := ((106485780178571428517 : Rat) / 40000000000000000000), D0 := ((106485780178571428517 : Rat) / 40000000000000000000), D1 := ((33786776178571428517 : Rat) / 40000000000000000000), D2 := ((4168380178571428517 : Rat) / 40000000000000000000), D3 := ((4168380178571428517 : Rat) / 64000000000000000000), D4 := ((199922093035714127837 : Rat) / 1600000000000000000000), LB := ((683921277063243 : Rat) / 200000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((106485780178571428517 : Rat) / 40000000000000000000), R := ((4263599587321428569197 : Rat) / 1600000000000000000000), D0 := ((4263599587321428569197 : Rat) / 1600000000000000000000), D1 := ((1355639427321428569197 : Rat) / 1600000000000000000000), D2 := ((170903587321428569197 : Rat) / 1600000000000000000000), D3 := ((12505140535714285551 : Rat) / 200000000000000000000), D4 := ((4893842821428567483 : Rat) / 40000000000000000000), LB := ((5819138757261921 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4263599587321428569197 : Rat) / 1600000000000000000000), R := ((2133883983749999998857 : Rat) / 800000000000000000000), D0 := ((2133883983749999998857 : Rat) / 800000000000000000000), D1 := ((679903903749999998857 : Rat) / 800000000000000000000), D2 := ((87535983749999998857 : Rat) / 800000000000000000000), D3 := ((95872744107142855891 : Rat) / 1600000000000000000000), D4 := ((191585332678571270803 : Rat) / 1600000000000000000000), LB := ((107293123802853 : Rat) / 12500000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2133883983749999998857 : Rat) / 800000000000000000000), R := ((1069026181964285713687 : Rat) / 400000000000000000000), D0 := ((1069026181964285713687 : Rat) / 400000000000000000000), D1 := ((342036141964285713687 : Rat) / 400000000000000000000), D2 := ((45852181964285713687 : Rat) / 400000000000000000000), D3 := ((45852181964285713687 : Rat) / 800000000000000000000), D4 := ((93708476249999921143 : Rat) / 800000000000000000000), LB := ((2553523365676963 : Rat) / 500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1069026181964285713687 : Rat) / 400000000000000000000), R := ((2142220744107142855891 : Rat) / 800000000000000000000), D0 := ((2142220744107142855891 : Rat) / 800000000000000000000), D1 := ((688240664107142855891 : Rat) / 800000000000000000000), D2 := ((95872744107142855891 : Rat) / 800000000000000000000), D3 := ((4168380178571428517 : Rat) / 80000000000000000000), D4 := ((44770048035714246313 : Rat) / 400000000000000000000), LB := ((12775468347383717 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2142220744107142855891 : Rat) / 800000000000000000000), R := ((268298640535714285551 : Rat) / 100000000000000000000), D0 := ((268298640535714285551 : Rat) / 100000000000000000000), D1 := ((86551130535714285551 : Rat) / 100000000000000000000), D2 := ((12505140535714285551 : Rat) / 100000000000000000000), D3 := ((37515421607142856653 : Rat) / 800000000000000000000), D4 := ((85371715892857064109 : Rat) / 800000000000000000000), LB := ((1123854461947027 : Rat) / 50000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((268298640535714285551 : Rat) / 100000000000000000000), R := ((1077362942321428570721 : Rat) / 400000000000000000000), D0 := ((1077362942321428570721 : Rat) / 400000000000000000000), D1 := ((350372902321428570721 : Rat) / 400000000000000000000), D2 := ((54188942321428570721 : Rat) / 400000000000000000000), D3 := ((4168380178571428517 : Rat) / 100000000000000000000), D4 := ((10150416964285704449 : Rat) / 100000000000000000000), LB := ((432915374877641 : Rat) / 20000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1077362942321428570721 : Rat) / 400000000000000000000), R := ((540765661249999999619 : Rat) / 200000000000000000000), D0 := ((540765661249999999619 : Rat) / 200000000000000000000), D1 := ((177270641249999999619 : Rat) / 200000000000000000000), D2 := ((29178661249999999619 : Rat) / 200000000000000000000), D3 := ((12505140535714285551 : Rat) / 400000000000000000000), D4 := ((36433287678571389279 : Rat) / 400000000000000000000), LB := ((1757050855905537 : Rat) / 31250000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((540765661249999999619 : Rat) / 200000000000000000000), R := ((68116755178571428517 : Rat) / 25000000000000000000), D0 := ((68116755178571428517 : Rat) / 25000000000000000000), D1 := ((22679877678571428517 : Rat) / 25000000000000000000), D2 := ((4168380178571428517 : Rat) / 25000000000000000000), D3 := ((4168380178571428517 : Rat) / 200000000000000000000), D4 := ((16132453749999980381 : Rat) / 200000000000000000000), LB := ((219206007308781 : Rat) / 2500000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((68116755178571428517 : Rat) / 25000000000000000000), R := ((109568837017857142807 : Rat) / 40000000000000000000), D0 := ((109568837017857142807 : Rat) / 40000000000000000000), D1 := ((36869833017857142807 : Rat) / 40000000000000000000), D2 := ((7251437017857142807 : Rat) / 40000000000000000000), D3 := ((2910143660714285899 : Rat) / 200000000000000000000), D4 := ((1495509196428568983 : Rat) / 25000000000000000000), LB := ((7161741787347667 : Rat) / 50000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((109568837017857142807 : Rat) / 40000000000000000000), R := ((275377164374999999967 : Rat) / 100000000000000000000), D0 := ((275377164374999999967 : Rat) / 100000000000000000000), D1 := ((93629654374999999967 : Rat) / 100000000000000000000), D2 := ((19583664374999999967 : Rat) / 100000000000000000000), D3 := ((2910143660714285899 : Rat) / 100000000000000000000), D4 := ((1810785982142853193 : Rat) / 40000000000000000000), LB := ((12838058124290397 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((275377164374999999967 : Rat) / 100000000000000000000), R := ((441185491732142857127 : Rat) / 160000000000000000000), D0 := ((441185491732142857127 : Rat) / 160000000000000000000), D1 := ((150389475732142857127 : Rat) / 160000000000000000000), D2 := ((31915891732142857127 : Rat) / 160000000000000000000), D3 := ((26191292946428573091 : Rat) / 800000000000000000000), D4 := ((3071893124999990033 : Rat) / 100000000000000000000), LB := ((4792660002112703 : Rat) / 250000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((441185491732142857127 : Rat) / 160000000000000000000), R := ((1104418801160714285767 : Rat) / 400000000000000000000), D0 := ((1104418801160714285767 : Rat) / 400000000000000000000), D1 := ((377428761160714285767 : Rat) / 400000000000000000000), D2 := ((81244801160714285767 : Rat) / 400000000000000000000), D3 := ((2910143660714285899 : Rat) / 80000000000000000000), D4 := ((4333000267857126873 : Rat) / 160000000000000000000), LB := ((37490294442493743 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1104418801160714285767 : Rat) / 400000000000000000000), R := ((4420585348303571428967 : Rat) / 1600000000000000000000), D0 := ((4420585348303571428967 : Rat) / 1600000000000000000000), D1 := ((1512625188303571428967 : Rat) / 1600000000000000000000), D2 := ((327889348303571428967 : Rat) / 1600000000000000000000), D3 := ((61113016875000003879 : Rat) / 1600000000000000000000), D4 := ((9377428839285674233 : Rat) / 400000000000000000000), LB := ((521054188883277 : Rat) / 125000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4420585348303571428967 : Rat) / 1600000000000000000000), R := ((8844080840267857143833 : Rat) / 3200000000000000000000), D0 := ((8844080840267857143833 : Rat) / 3200000000000000000000), D1 := ((3028160520267857143833 : Rat) / 3200000000000000000000), D2 := ((658688840267857143833 : Rat) / 3200000000000000000000), D3 := ((125136177410714293657 : Rat) / 3200000000000000000000), D4 := ((34599571696428411033 : Rat) / 1600000000000000000000), LB := ((2661599986858859 : Rat) / 500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8844080840267857143833 : Rat) / 3200000000000000000000), R := ((2211747745982142857433 : Rat) / 800000000000000000000), D0 := ((2211747745982142857433 : Rat) / 800000000000000000000), D1 := ((757767665982142857433 : Rat) / 800000000000000000000), D2 := ((165399745982142857433 : Rat) / 800000000000000000000), D3 := ((32011580267857144889 : Rat) / 800000000000000000000), D4 := ((66288999732142536167 : Rat) / 3200000000000000000000), LB := ((311432172972137 : Rat) / 100000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2211747745982142857433 : Rat) / 800000000000000000000), R := ((8849901127589285715631 : Rat) / 3200000000000000000000), D0 := ((8849901127589285715631 : Rat) / 3200000000000000000000), D1 := ((3033980807589285715631 : Rat) / 3200000000000000000000), D2 := ((664509127589285715631 : Rat) / 3200000000000000000000), D3 := ((26191292946428573091 : Rat) / 640000000000000000000), D4 := ((15844714017857062567 : Rat) / 800000000000000000000), LB := ((11744977379458121 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8849901127589285715631 : Rat) / 3200000000000000000000), R := ((17702712398839285717161 : Rat) / 6400000000000000000000), D0 := ((17702712398839285717161 : Rat) / 6400000000000000000000), D1 := ((6070871758839285717161 : Rat) / 6400000000000000000000), D2 := ((1331928398839285717161 : Rat) / 6400000000000000000000), D3 := ((264823073125000016809 : Rat) / 6400000000000000000000), D4 := ((60468712410713964369 : Rat) / 3200000000000000000000), LB := ((24863836828252217 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17702712398839285717161 : Rat) / 6400000000000000000000), R := ((885281127125000000153 : Rat) / 320000000000000000000), D0 := ((885281127125000000153 : Rat) / 320000000000000000000), D1 := ((303689095125000000153 : Rat) / 320000000000000000000), D2 := ((66741927125000000153 : Rat) / 320000000000000000000), D3 := ((66933304196428575677 : Rat) / 1600000000000000000000), D4 := ((118027281160713642839 : Rat) / 6400000000000000000000), LB := ((8732136621985853 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((885281127125000000153 : Rat) / 320000000000000000000), R := ((17708532686160714288959 : Rat) / 6400000000000000000000), D0 := ((17708532686160714288959 : Rat) / 6400000000000000000000), D1 := ((6076692046160714288959 : Rat) / 6400000000000000000000), D2 := ((1337748686160714288959 : Rat) / 6400000000000000000000), D3 := ((270643360446428588607 : Rat) / 6400000000000000000000), D4 := ((5755856874999967847 : Rat) / 320000000000000000000), LB := ((10833153877590207 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17708532686160714288959 : Rat) / 6400000000000000000000), R := ((8855721414910714287429 : Rat) / 3200000000000000000000), D0 := ((8855721414910714287429 : Rat) / 3200000000000000000000), D1 := ((3039801094910714287429 : Rat) / 3200000000000000000000), D2 := ((670329414910714287429 : Rat) / 3200000000000000000000), D3 := ((136776752053571437253 : Rat) / 3200000000000000000000), D4 := ((112206993839285071041 : Rat) / 6400000000000000000000), LB := ((4994520692791493 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8855721414910714287429 : Rat) / 3200000000000000000000), R := ((7085159160660714287123 : Rat) / 2560000000000000000000), D0 := ((7085159160660714287123 : Rat) / 2560000000000000000000), D1 := ((2432422904660714287123 : Rat) / 2560000000000000000000), D2 := ((536845560660714287123 : Rat) / 2560000000000000000000), D3 := ((550017151875000034911 : Rat) / 12800000000000000000000), D4 := ((54648425089285392571 : Rat) / 3200000000000000000000), LB := ((3622205804018619 : Rat) / 2500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7085159160660714287123 : Rat) / 2560000000000000000000), R := ((17714352973482142860757 : Rat) / 6400000000000000000000), D0 := ((17714352973482142860757 : Rat) / 6400000000000000000000), D1 := ((6082512333482142860757 : Rat) / 6400000000000000000000), D2 := ((1343568973482142860757 : Rat) / 6400000000000000000000), D3 := ((55292729553571432081 : Rat) / 1280000000000000000000), D4 := ((43136711339285456877 : Rat) / 2560000000000000000000), LB := ((2449059048853397 : Rat) / 2000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17714352973482142860757 : Rat) / 6400000000000000000000), R := ((35431616090625000007413 : Rat) / 12800000000000000000000), D0 := ((35431616090625000007413 : Rat) / 12800000000000000000000), D1 := ((12167934810625000007413 : Rat) / 12800000000000000000000), D2 := ((2690048090625000007413 : Rat) / 12800000000000000000000), D3 := ((555837439196428606709 : Rat) / 12800000000000000000000), D4 := ((106386706517856499243 : Rat) / 6400000000000000000000), LB := ((5109051913741447 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35431616090625000007413 : Rat) / 12800000000000000000000), R := ((553664472410714285833 : Rat) / 200000000000000000000), D0 := ((553664472410714285833 : Rat) / 200000000000000000000), D1 := ((190169452410714285833 : Rat) / 200000000000000000000), D2 := ((42077472410714285833 : Rat) / 200000000000000000000), D3 := ((8730430982142857697 : Rat) / 200000000000000000000), D4 := ((209863269374998712587 : Rat) / 12800000000000000000000), LB := ((8411320234550379 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553664472410714285833 : Rat) / 200000000000000000000), R := ((35437436377946428579211 : Rat) / 12800000000000000000000), D0 := ((35437436377946428579211 : Rat) / 12800000000000000000000), D1 := ((12173755097946428579211 : Rat) / 12800000000000000000000), D2 := ((2695868377946428579211 : Rat) / 12800000000000000000000), D3 := ((561657726517857178507 : Rat) / 12800000000000000000000), D4 := ((3233642589285694167 : Rat) / 200000000000000000000), LB := ((6829213965443559 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35437436377946428579211 : Rat) / 12800000000000000000000), R := ((3544034652160714286511 : Rat) / 1280000000000000000000), D0 := ((3544034652160714286511 : Rat) / 1280000000000000000000), D1 := ((1217666524160714286511 : Rat) / 1280000000000000000000), D2 := ((269877852160714286511 : Rat) / 1280000000000000000000), D3 := ((282283935089285732203 : Rat) / 6400000000000000000000), D4 := ((204042982053570140789 : Rat) / 12800000000000000000000), LB := ((2738131572400937 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3544034652160714286511 : Rat) / 1280000000000000000000), R := ((35443256665267857151009 : Rat) / 12800000000000000000000), D0 := ((35443256665267857151009 : Rat) / 12800000000000000000000), D1 := ((12179575385267857151009 : Rat) / 12800000000000000000000), D2 := ((2701688665267857151009 : Rat) / 12800000000000000000000), D3 := ((113495602767857150061 : Rat) / 2560000000000000000000), D4 := ((20113283839285585489 : Rat) / 1280000000000000000000), LB := ((4357165644482963 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35443256665267857151009 : Rat) / 12800000000000000000000), R := ((8861541702232142859227 : Rat) / 3200000000000000000000), D0 := ((8861541702232142859227 : Rat) / 3200000000000000000000), D1 := ((3045621382232142859227 : Rat) / 3200000000000000000000), D2 := ((676149702232142859227 : Rat) / 3200000000000000000000), D3 := ((142597039375000009051 : Rat) / 3200000000000000000000), D4 := ((198222694732141568991 : Rat) / 12800000000000000000000), LB := ((4346063742116657 : Rat) / 12500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8861541702232142859227 : Rat) / 3200000000000000000000), R := ((35449076952589285722807 : Rat) / 12800000000000000000000), D0 := ((35449076952589285722807 : Rat) / 12800000000000000000000), D1 := ((12185395672589285722807 : Rat) / 12800000000000000000000), D2 := ((2707508952589285722807 : Rat) / 12800000000000000000000), D3 := ((573298301160714322103 : Rat) / 12800000000000000000000), D4 := ((48828137767856820773 : Rat) / 3200000000000000000000), LB := ((28404931402170597 : Rat) / 100000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35449076952589285722807 : Rat) / 12800000000000000000000), R := ((17725993548125000004353 : Rat) / 6400000000000000000000), D0 := ((17725993548125000004353 : Rat) / 6400000000000000000000), D1 := ((6094152908125000004353 : Rat) / 6400000000000000000000), D2 := ((1355209548125000004353 : Rat) / 6400000000000000000000), D3 := ((288104222410714304001 : Rat) / 6400000000000000000000), D4 := ((192402407410712997193 : Rat) / 12800000000000000000000), LB := ((490704826482613 : Rat) / 2000000000000000000) }
]

def block177RightChunk000L : Rat := ((44566939732142857181 : Rat) / 25000000000000000000)
def block177RightChunk000R : Rat := ((17725993548125000004353 : Rat) / 6400000000000000000000)

def block177RightChunk000Certificate : Bool :=
  allBoxesValid block177RightChunk000 &&
  coversFromBool block177RightChunk000 block177RightChunk000L block177RightChunk000R

theorem block177RightChunk000Certificate_eq_true :
    block177RightChunk000Certificate = true := by
  native_decide

def block177RightChunk001 : List RatBox := [
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17725993548125000004353 : Rat) / 6400000000000000000000), R := ((7090979447982142858921 : Rat) / 2560000000000000000000), D0 := ((7090979447982142858921 : Rat) / 2560000000000000000000), D1 := ((2438243191982142858921 : Rat) / 2560000000000000000000), D2 := ((542665847982142858921 : Rat) / 2560000000000000000000), D3 := ((579118588482142893901 : Rat) / 12800000000000000000000), D4 := ((94746131874999355647 : Rat) / 6400000000000000000000), LB := ((23216487976385203 : Rat) / 100000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7090979447982142858921 : Rat) / 2560000000000000000000), R := ((4432225922946428572563 : Rat) / 1600000000000000000000), D0 := ((4432225922946428572563 : Rat) / 1600000000000000000000), D1 := ((1524265762946428572563 : Rat) / 1600000000000000000000), D2 := ((339529922946428572563 : Rat) / 1600000000000000000000), D3 := ((2910143660714285899 : Rat) / 64000000000000000000), D4 := ((37316424017856885079 : Rat) / 2560000000000000000000), LB := ((2450860500456953 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4432225922946428572563 : Rat) / 1600000000000000000000), R := ((35460717527232142866403 : Rat) / 12800000000000000000000), D0 := ((35460717527232142866403 : Rat) / 12800000000000000000000), D1 := ((12197036247232142866403 : Rat) / 12800000000000000000000), D2 := ((2719149527232142866403 : Rat) / 12800000000000000000000), D3 := ((584938875803571465699 : Rat) / 12800000000000000000000), D4 := ((22958997053571267437 : Rat) / 1600000000000000000000), LB := ((1423729035641419 : Rat) / 5000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35460717527232142866403 : Rat) / 12800000000000000000000), R := ((17731813835446428576151 : Rat) / 6400000000000000000000), D0 := ((17731813835446428576151 : Rat) / 6400000000000000000000), D1 := ((6099973195446428576151 : Rat) / 6400000000000000000000), D2 := ((1361029835446428576151 : Rat) / 6400000000000000000000), D3 := ((293924509732142875799 : Rat) / 6400000000000000000000), D4 := ((180761832767855853597 : Rat) / 12800000000000000000000), LB := ((3518064004891519 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17731813835446428576151 : Rat) / 6400000000000000000000), R := ((35466537814553571438201 : Rat) / 12800000000000000000000), D0 := ((35466537814553571438201 : Rat) / 12800000000000000000000), D1 := ((12202856534553571438201 : Rat) / 12800000000000000000000), D2 := ((2724969814553571438201 : Rat) / 12800000000000000000000), D3 := ((590759163125000037497 : Rat) / 12800000000000000000000), D4 := ((88925844553570783849 : Rat) / 6400000000000000000000), LB := ((1787857615183297 : Rat) / 4000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35466537814553571438201 : Rat) / 12800000000000000000000), R := ((354694479582142857241 : Rat) / 128000000000000000000), D0 := ((354694479582142857241 : Rat) / 128000000000000000000), D1 := ((122057666782142857241 : Rat) / 128000000000000000000), D2 := ((27278799582142857241 : Rat) / 128000000000000000000), D3 := ((148417326696428580849 : Rat) / 3200000000000000000000), D4 := ((174941545446427281799 : Rat) / 12800000000000000000000), LB := ((1427382056166937 : Rat) / 2500000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((354694479582142857241 : Rat) / 128000000000000000000), R := ((35472358101875000009999 : Rat) / 12800000000000000000000), D0 := ((35472358101875000009999 : Rat) / 12800000000000000000000), D1 := ((12208676821875000009999 : Rat) / 12800000000000000000000), D2 := ((2730790101875000009999 : Rat) / 12800000000000000000000), D3 := ((119315890089285721859 : Rat) / 2560000000000000000000), D4 := ((1720314017857129959 : Rat) / 128000000000000000000), LB := ((452839602613081 : Rat) / 625000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35472358101875000009999 : Rat) / 12800000000000000000000), R := ((17737634122767857147949 : Rat) / 6400000000000000000000), D0 := ((17737634122767857147949 : Rat) / 6400000000000000000000), D1 := ((6105793482767857147949 : Rat) / 6400000000000000000000), D2 := ((1366850122767857147949 : Rat) / 6400000000000000000000), D3 := ((299744797053571447597 : Rat) / 6400000000000000000000), D4 := ((169121258124998710001 : Rat) / 12800000000000000000000), LB := ((14536782186787 : Rat) / 16000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17737634122767857147949 : Rat) / 6400000000000000000000), R := ((35478178389196428581797 : Rat) / 12800000000000000000000), D0 := ((35478178389196428581797 : Rat) / 12800000000000000000000), D1 := ((12214497109196428581797 : Rat) / 12800000000000000000000), D2 := ((2736610389196428581797 : Rat) / 12800000000000000000000), D3 := ((602399737767857181093 : Rat) / 12800000000000000000000), D4 := ((83105557232142212051 : Rat) / 6400000000000000000000), LB := ((11238260386258747 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((35478178389196428581797 : Rat) / 12800000000000000000000), R := ((2217568033303571429231 : Rat) / 800000000000000000000), D0 := ((2217568033303571429231 : Rat) / 800000000000000000000), D1 := ((763587953303571429231 : Rat) / 800000000000000000000), D2 := ((171220033303571429231 : Rat) / 800000000000000000000), D3 := ((37831867589285716687 : Rat) / 800000000000000000000), D4 := ((163300970803570138203 : Rat) / 12800000000000000000000), LB := ((1714097638717757 : Rat) / 1250000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2217568033303571429231 : Rat) / 800000000000000000000), R := ((17743454410089285719747 : Rat) / 6400000000000000000000), D0 := ((17743454410089285719747 : Rat) / 6400000000000000000000), D1 := ((6111613770089285719747 : Rat) / 6400000000000000000000), D2 := ((1372670410089285719747 : Rat) / 6400000000000000000000), D3 := ((61113016875000003879 : Rat) / 1280000000000000000000), D4 := ((10024426696428490769 : Rat) / 800000000000000000000), LB := ((2910611357255233 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17743454410089285719747 : Rat) / 6400000000000000000000), R := ((8873182276875000002823 : Rat) / 3200000000000000000000), D0 := ((8873182276875000002823 : Rat) / 3200000000000000000000), D1 := ((3057261956875000002823 : Rat) / 3200000000000000000000), D2 := ((687790276875000002823 : Rat) / 3200000000000000000000), D3 := ((154237614017857152647 : Rat) / 3200000000000000000000), D4 := ((77285269910713640253 : Rat) / 6400000000000000000000), LB := ((602391420199723 : Rat) / 625000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8873182276875000002823 : Rat) / 3200000000000000000000), R := ((3549854939482142858309 : Rat) / 1280000000000000000000), D0 := ((3549854939482142858309 : Rat) / 1280000000000000000000), D1 := ((1223486811482142858309 : Rat) / 1280000000000000000000), D2 := ((275698139482142858309 : Rat) / 1280000000000000000000), D3 := ((311385371696428591193 : Rat) / 6400000000000000000000), D4 := ((37187563124999677177 : Rat) / 3200000000000000000000), LB := ((17817877616694289 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3549854939482142858309 : Rat) / 1280000000000000000000), R := ((4438046210267857144361 : Rat) / 1600000000000000000000), D0 := ((4438046210267857144361 : Rat) / 1600000000000000000000), D1 := ((1530086050267857144361 : Rat) / 1600000000000000000000), D2 := ((345350210267857144361 : Rat) / 1600000000000000000000), D3 := ((78573878839285719273 : Rat) / 1600000000000000000000), D4 := ((14292996517857013691 : Rat) / 1280000000000000000000), LB := ((688685380103693 : Rat) / 250000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4438046210267857144361 : Rat) / 1600000000000000000000), R := ((8879002564196428574621 : Rat) / 3200000000000000000000), D0 := ((8879002564196428574621 : Rat) / 3200000000000000000000), D1 := ((3063082244196428574621 : Rat) / 3200000000000000000000), D2 := ((693610564196428574621 : Rat) / 3200000000000000000000), D3 := ((32011580267857144889 : Rat) / 640000000000000000000), D4 := ((17138709732142695639 : Rat) / 1600000000000000000000), LB := ((12468286348057411 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8879002564196428574621 : Rat) / 3200000000000000000000), R := ((222047817696428571513 : Rat) / 80000000000000000000), D0 := ((222047817696428571513 : Rat) / 80000000000000000000), D1 := ((76649809696428571513 : Rat) / 80000000000000000000), D2 := ((17413017696428571513 : Rat) / 80000000000000000000), D3 := ((20371005625000001293 : Rat) / 400000000000000000000), D4 := ((31367275803571105379 : Rat) / 3200000000000000000000), LB := ((4103308096961633 : Rat) / 1000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((222047817696428571513 : Rat) / 80000000000000000000), R := ((4443866497589285716159 : Rat) / 1600000000000000000000), D0 := ((4443866497589285716159 : Rat) / 1600000000000000000000), D1 := ((1535906337589285716159 : Rat) / 1600000000000000000000), D2 := ((351170497589285716159 : Rat) / 1600000000000000000000), D3 := ((84394166160714291071 : Rat) / 1600000000000000000000), D4 := ((711428303571420487 : Rat) / 80000000000000000000), LB := ((26576502483359743 : Rat) / 10000000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4443866497589285716159 : Rat) / 1600000000000000000000), R := ((2223388320625000001029 : Rat) / 800000000000000000000), D0 := ((2223388320625000001029 : Rat) / 800000000000000000000), D1 := ((769408240625000001029 : Rat) / 800000000000000000000), D2 := ((177040320625000001029 : Rat) / 800000000000000000000), D3 := ((8730430982142857697 : Rat) / 160000000000000000000), D4 := ((11318422410714123841 : Rat) / 1600000000000000000000), LB := ((2661985680563539 : Rat) / 200000000000000000) },
  { w1 := ((18545744845872927 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1753914171366439 : Rat) / 10000000000000000), w4 := ((915577353760947 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((68116755178571428517 : Rat) / 25000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2223388320625000001029 : Rat) / 800000000000000000000), R := ((139143654017857142933 : Rat) / 50000000000000000000), D0 := ((139143654017857142933 : Rat) / 50000000000000000000), D1 := ((48269899017857142933 : Rat) / 50000000000000000000), D2 := ((11246904017857142933 : Rat) / 50000000000000000000), D3 := ((2910143660714285899 : Rat) / 50000000000000000000), D4 := ((4204139374999918971 : Rat) / 800000000000000000000), LB := ((20166929091586017 : Rat) / 1000000000000000000) }
]

def block177RightChunk001L : Rat := ((17725993548125000004353 : Rat) / 6400000000000000000000)
def block177RightChunk001R : Rat := ((139143654017857142933 : Rat) / 50000000000000000000)

def block177RightChunk001Certificate : Bool :=
  allBoxesValid block177RightChunk001 &&
  coversFromBool block177RightChunk001 block177RightChunk001L block177RightChunk001R

theorem block177RightChunk001Certificate_eq_true :
    block177RightChunk001Certificate = true := by
  native_decide

def block177RightChainCertificate : Bool :=
  decide (
    block177RightL = ((44566939732142857181 : Rat) / 25000000000000000000) /\
    ((17725993548125000004353 : Rat) / 6400000000000000000000) = ((17725993548125000004353 : Rat) / 6400000000000000000000) /\
    ((139143654017857142933 : Rat) / 50000000000000000000) = block177RightR)

theorem block177RightChainCertificate_eq_true :
    block177RightChainCertificate = true := by
  native_decide

def block177LeftBoxCount : Nat := boxCount block177LeftBoxes
def block177RightBoxCount : Nat := 119

def block177_rational_certificate : Prop :=
    block177LeftCertificate = true /\
    block177RightChainCertificate = true /\
    block177RightChunk000Certificate = true /\
    block177RightChunk001Certificate = true

theorem block177_rational_certificate_proof :
    block177_rational_certificate := by
  exact ⟨block177LeftCertificate_eq_true, block177RightChainCertificate_eq_true, block177RightChunk000Certificate_eq_true, block177RightChunk001Certificate_eq_true⟩

end Block177
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block177

open Set

def block177W1 : Rat := ((18545744845872927 : Rat) / 10000000000000000)
def block177W2 : Rat := (0 : Rat)
def block177W3 : Rat := ((1753914171366439 : Rat) / 10000000000000000)
def block177W4 : Rat := ((915577353760947 : Rat) / 10000000000000000)
def block177S1 : Rat := ((18174751 : Rat) / 10000000)
def block177S2 : Rat := ((511587 : Rat) / 200000)
def block177S3 : Rat := ((68116755178571428517 : Rat) / 25000000000000000000)
def block177S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block177V (y : ℝ) : ℝ :=
  ratPotential block177W1 block177W2 block177W3 block177W4 block177S1 block177S2 block177S3 block177S4 y

def block177LeftParamsCertificate : Bool :=
  allBoxesSameParams block177LeftBoxes block177W1 block177W2 block177W3 block177W4 block177S1 block177S2 block177S3 block177S4

theorem block177LeftParamsCertificate_eq_true :
    block177LeftParamsCertificate = true := by
  native_decide

theorem block177_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block177LeftL : ℝ) (block177LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block177S1 : ℝ))
    (hy2ne : y ≠ (block177S2 : ℝ))
    (hy3ne : y ≠ (block177S3 : ℝ))
    (hy4ne : y ≠ (block177S4 : ℝ)) :
    0 < block177V y := by
  have hcert := block177LeftCertificate_eq_true
  unfold block177LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block177LeftBoxes) (lo := block177LeftL) (hi := block177LeftR)
    (w1 := block177W1) (w2 := block177W2) (w3 := block177W3) (w4 := block177W4)
    (s1 := block177S1) (s2 := block177S2) (s3 := block177S3) (s4 := block177S4)
    hboxes hcover block177LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block177RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block177RightChunk000 block177W1 block177W2 block177W3 block177W4 block177S1 block177S2 block177S3 block177S4

theorem block177RightChunk000ParamsCertificate_eq_true :
    block177RightChunk000ParamsCertificate = true := by
  native_decide

theorem block177_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block177RightChunk000L : ℝ) (block177RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block177S1 : ℝ))
    (hy2ne : y ≠ (block177S2 : ℝ))
    (hy3ne : y ≠ (block177S3 : ℝ))
    (hy4ne : y ≠ (block177S4 : ℝ)) :
    0 < block177V y := by
  have hcert := block177RightChunk000Certificate_eq_true
  unfold block177RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block177RightChunk000) (lo := block177RightChunk000L) (hi := block177RightChunk000R)
    (w1 := block177W1) (w2 := block177W2) (w3 := block177W3) (w4 := block177W4)
    (s1 := block177S1) (s2 := block177S2) (s3 := block177S3) (s4 := block177S4)
    hboxes hcover block177RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block177RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block177RightChunk001 block177W1 block177W2 block177W3 block177W4 block177S1 block177S2 block177S3 block177S4

theorem block177RightChunk001ParamsCertificate_eq_true :
    block177RightChunk001ParamsCertificate = true := by
  native_decide

theorem block177_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block177RightChunk001L : ℝ) (block177RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block177S1 : ℝ))
    (hy2ne : y ≠ (block177S2 : ℝ))
    (hy3ne : y ≠ (block177S3 : ℝ))
    (hy4ne : y ≠ (block177S4 : ℝ)) :
    0 < block177V y := by
  have hcert := block177RightChunk001Certificate_eq_true
  unfold block177RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block177RightChunk001) (lo := block177RightChunk001L) (hi := block177RightChunk001R)
    (w1 := block177W1) (w2 := block177W2) (w3 := block177W3) (w4 := block177W4)
    (s1 := block177S1) (s2 := block177S2) (s3 := block177S3) (s4 := block177S4)
    hboxes hcover block177RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block177_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block177RightL : ℝ) (block177RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block177S1 : ℝ))
    (hy2ne : y ≠ (block177S2 : ℝ))
    (hy3ne : y ≠ (block177S3 : ℝ))
    (hy4ne : y ≠ (block177S4 : ℝ)) :
    0 < block177V y := by
  by_cases h0 : y ≤ (block177RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block177RightChunk000L : ℝ) (block177RightChunk000R : ℝ) := by
      have hL : (block177RightChunk000L : ℝ) = (block177RightL : ℝ) := by
        norm_num [block177RightChunk000L, block177RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block177_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block177RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block177RightChunk001L : ℝ) = (block177RightChunk000R : ℝ) := by
      norm_num [block177RightChunk001L, block177RightChunk000R]
    have hR : (block177RightChunk001R : ℝ) = (block177RightR : ℝ) := by
      norm_num [block177RightChunk001R, block177RightR]
    have hyc : y ∈ Icc (block177RightChunk001L : ℝ) (block177RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block177_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block177_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block177LeftL : ℝ) (block177LeftR : ℝ) →
    y ≠ 0 → y ≠ (block177S1 : ℝ) → y ≠ (block177S2 : ℝ) →
    y ≠ (block177S3 : ℝ) → y ≠ (block177S4 : ℝ) → 0 < block177V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block177RightL : ℝ) (block177RightR : ℝ) →
    y ≠ 0 → y ≠ (block177S1 : ℝ) → y ≠ (block177S2 : ℝ) →
    y ≠ (block177S3 : ℝ) → y ≠ (block177S4 : ℝ) → 0 < block177V y)

theorem block177_reallog_certificate_proof :
    block177_reallog_certificate := by
  exact ⟨block177_left_V_pos, block177_right_V_pos⟩

end Block177
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block177.block177V
#check Erdos1038Lean.M1817475.Block177.block177_left_V_pos
#check Erdos1038Lean.M1817475.Block177.block177_right_V_pos
#check Erdos1038Lean.M1817475.Block177.block177_reallog_certificate_proof
