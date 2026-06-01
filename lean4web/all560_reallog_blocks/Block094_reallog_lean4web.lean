/-
Self-contained Lean4Web paste file.
Block 94 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block094

def block094LeftL : Rat := ((7989033482142857151 : Rat) / 10000000000000000000)
def block094LeftR : Rat := ((19977470982142857163 : Rat) / 25000000000000000000)
def block094RightL : Rat := ((17989033482142857151 : Rat) / 10000000000000000000)
def block094RightR : Rat := ((69977470982142857163 : Rat) / 25000000000000000000)

def block094LeftBoxes : List RatBox := [
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((7989033482142857151 : Rat) / 10000000000000000000), R := ((19977470982142857163 : Rat) / 25000000000000000000), D0 := ((19977470982142857163 : Rat) / 25000000000000000000), D1 := ((10185717517857142849 : Rat) / 10000000000000000000), D2 := ((17590316517857142849 : Rat) / 10000000000000000000), D3 := ((47699429285714285659 : Rat) / 25000000000000000000), D4 := ((19855872267857141849 : Rat) / 10000000000000000000), LB := ((12135556444758333 : Rat) / 2000000000000000000) }
]

def block094LeftCertificate : Bool :=
  allBoxesValid block094LeftBoxes &&
  coversFromBool block094LeftBoxes block094LeftL block094LeftR

theorem block094LeftCertificate_eq_true :
    block094LeftCertificate = true := by
  native_decide

def block094RightChunk000 : List RatBox := [
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17989033482142857151 : Rat) / 10000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((185717517857142849 : Rat) / 10000000000000000000), D2 := ((7590316517857142849 : Rat) / 10000000000000000000), D3 := ((22699429285714285659 : Rat) / 25000000000000000000), D4 := ((9855872267857141849 : Rat) / 10000000000000000000), LB := ((4049035919846741 : Rat) / 500000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((44470270982142857073 : Rat) / 50000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((2793264162097143 : Rat) / 2000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((25958773482142857073 : Rat) / 50000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((5625062131467099 : Rat) / 10000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((16703024732142857073 : Rat) / 50000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((7264277444819181 : Rat) / 25000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((12075150357142857073 : Rat) / 50000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((8566576157401029 : Rat) / 250000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((519034275982142857073 : Rat) / 200000000000000000000), D0 := ((519034275982142857073 : Rat) / 200000000000000000000), D1 := ((155539255982142857073 : Rat) / 200000000000000000000), D2 := ((7447275982142857073 : Rat) / 200000000000000000000), D3 := ((7447275982142857073 : Rat) / 50000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((3029721894178633 : Rat) / 250000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((519034275982142857073 : Rat) / 200000000000000000000), R := ((1045515827946428571219 : Rat) / 400000000000000000000), D0 := ((1045515827946428571219 : Rat) / 400000000000000000000), D1 := ((318525787946428571219 : Rat) / 400000000000000000000), D2 := ((22341827946428571219 : Rat) / 400000000000000000000), D3 := ((22341827946428571219 : Rat) / 200000000000000000000), D4 := ((37863839017857122927 : Rat) / 200000000000000000000), LB := ((7623346671628117 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1045515827946428571219 : Rat) / 400000000000000000000), R := ((2098478931874999999511 : Rat) / 800000000000000000000), D0 := ((2098478931874999999511 : Rat) / 800000000000000000000), D1 := ((644498851874999999511 : Rat) / 800000000000000000000), D2 := ((52130931874999999511 : Rat) / 800000000000000000000), D3 := ((7447275982142857073 : Rat) / 80000000000000000000), D4 := ((68280402053571388781 : Rat) / 400000000000000000000), LB := ((552356560500919 : Rat) / 50000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2098478931874999999511 : Rat) / 800000000000000000000), R := ((263240775982142857073 : Rat) / 100000000000000000000), D0 := ((263240775982142857073 : Rat) / 100000000000000000000), D1 := ((81493265982142857073 : Rat) / 100000000000000000000), D2 := ((7447275982142857073 : Rat) / 100000000000000000000), D3 := ((67025483839285713657 : Rat) / 800000000000000000000), D4 := ((129113528124999920489 : Rat) / 800000000000000000000), LB := ((39067532435910213 : Rat) / 100000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((263240775982142857073 : Rat) / 100000000000000000000), R := ((4219299691696428570241 : Rat) / 1600000000000000000000), D0 := ((4219299691696428570241 : Rat) / 1600000000000000000000), D1 := ((1311339531696428570241 : Rat) / 1600000000000000000000), D2 := ((126603691696428570241 : Rat) / 1600000000000000000000), D3 := ((7447275982142857073 : Rat) / 100000000000000000000), D4 := ((15208281517857132927 : Rat) / 100000000000000000000), LB := ((5594688208426013 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4219299691696428570241 : Rat) / 1600000000000000000000), R := ((2113373483839285713657 : Rat) / 800000000000000000000), D0 := ((2113373483839285713657 : Rat) / 800000000000000000000), D1 := ((659393403839285713657 : Rat) / 800000000000000000000), D2 := ((67025483839285713657 : Rat) / 800000000000000000000), D3 := ((22341827946428571219 : Rat) / 320000000000000000000), D4 := ((235885228303571269759 : Rat) / 1600000000000000000000), LB := ((18173260731483287 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2113373483839285713657 : Rat) / 800000000000000000000), R := ((8460941211339285711701 : Rat) / 3200000000000000000000), D0 := ((8460941211339285711701 : Rat) / 3200000000000000000000), D1 := ((2645020891339285711701 : Rat) / 3200000000000000000000), D2 := ((275549211339285711701 : Rat) / 3200000000000000000000), D3 := ((52130931874999999511 : Rat) / 800000000000000000000), D4 := ((114218976160714206343 : Rat) / 800000000000000000000), LB := ((1120646334751707 : Rat) / 200000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8460941211339285711701 : Rat) / 3200000000000000000000), R := ((4234194243660714284387 : Rat) / 1600000000000000000000), D0 := ((4234194243660714284387 : Rat) / 1600000000000000000000), D1 := ((1326234083660714284387 : Rat) / 1600000000000000000000), D2 := ((141498243660714284387 : Rat) / 1600000000000000000000), D3 := ((201076451517857140971 : Rat) / 3200000000000000000000), D4 := ((449428628660713968299 : Rat) / 3200000000000000000000), LB := ((4200140075163061 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4234194243660714284387 : Rat) / 1600000000000000000000), R := ((8475835763303571425847 : Rat) / 3200000000000000000000), D0 := ((8475835763303571425847 : Rat) / 3200000000000000000000), D1 := ((2659915443303571425847 : Rat) / 3200000000000000000000), D2 := ((290443763303571425847 : Rat) / 3200000000000000000000), D3 := ((96814587767857141949 : Rat) / 1600000000000000000000), D4 := ((220990676339285555613 : Rat) / 1600000000000000000000), LB := ((7393946983394739 : Rat) / 2500000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8475835763303571425847 : Rat) / 3200000000000000000000), R := ((212082075982142857073 : Rat) / 80000000000000000000), D0 := ((212082075982142857073 : Rat) / 80000000000000000000), D1 := ((66684067982142857073 : Rat) / 80000000000000000000), D2 := ((7447275982142857073 : Rat) / 80000000000000000000), D3 := ((7447275982142857073 : Rat) / 128000000000000000000), D4 := ((434534076696428254153 : Rat) / 3200000000000000000000), LB := ((753680756697217 : Rat) / 400000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((212082075982142857073 : Rat) / 80000000000000000000), R := ((8490730315267857139993 : Rat) / 3200000000000000000000), D0 := ((8490730315267857139993 : Rat) / 3200000000000000000000), D1 := ((2674809995267857139993 : Rat) / 3200000000000000000000), D2 := ((305338315267857139993 : Rat) / 3200000000000000000000), D3 := ((22341827946428571219 : Rat) / 400000000000000000000), D4 := ((10677170017857134927 : Rat) / 80000000000000000000), LB := ((9896049240661897 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8490730315267857139993 : Rat) / 3200000000000000000000), R := ((4249088795624999998533 : Rat) / 1600000000000000000000), D0 := ((4249088795624999998533 : Rat) / 1600000000000000000000), D1 := ((1341128635624999998533 : Rat) / 1600000000000000000000), D2 := ((156392795624999998533 : Rat) / 1600000000000000000000), D3 := ((171287347589285712679 : Rat) / 3200000000000000000000), D4 := ((419639524732142540007 : Rat) / 3200000000000000000000), LB := ((2844755043847069 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4249088795624999998533 : Rat) / 1600000000000000000000), R := ((3400760491696428570241 : Rat) / 1280000000000000000000), D0 := ((3400760491696428570241 : Rat) / 1280000000000000000000), D1 := ((1074392363696428570241 : Rat) / 1280000000000000000000), D2 := ((126603691696428570241 : Rat) / 1280000000000000000000), D3 := ((81920035803571427803 : Rat) / 1600000000000000000000), D4 := ((206096124374999841467 : Rat) / 1600000000000000000000), LB := ((809402782574617 : Rat) / 250000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3400760491696428570241 : Rat) / 1280000000000000000000), R := ((8505624867232142854139 : Rat) / 3200000000000000000000), D0 := ((8505624867232142854139 : Rat) / 3200000000000000000000), D1 := ((2689704547232142854139 : Rat) / 3200000000000000000000), D2 := ((320232867232142854139 : Rat) / 3200000000000000000000), D3 := ((320232867232142854139 : Rat) / 6400000000000000000000), D4 := ((163387444303571301759 : Rat) / 1280000000000000000000), LB := ((3061071138916349 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8505624867232142854139 : Rat) / 3200000000000000000000), R := ((17018697010446428565351 : Rat) / 6400000000000000000000), D0 := ((17018697010446428565351 : Rat) / 6400000000000000000000), D1 := ((5386856370446428565351 : Rat) / 6400000000000000000000), D2 := ((647913010446428565351 : Rat) / 6400000000000000000000), D3 := ((156392795624999998533 : Rat) / 3200000000000000000000), D4 := ((404744972767856825861 : Rat) / 3200000000000000000000), LB := ((229693792929077 : Rat) / 78125000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17018697010446428565351 : Rat) / 6400000000000000000000), R := ((2128268035803571427803 : Rat) / 800000000000000000000), D0 := ((2128268035803571427803 : Rat) / 800000000000000000000), D1 := ((674287955803571427803 : Rat) / 800000000000000000000), D2 := ((81920035803571427803 : Rat) / 800000000000000000000), D3 := ((305338315267857139993 : Rat) / 6400000000000000000000), D4 := ((802042669553570794649 : Rat) / 6400000000000000000000), LB := ((28766021575967193 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2128268035803571427803 : Rat) / 800000000000000000000), R := ((17033591562410714279497 : Rat) / 6400000000000000000000), D0 := ((17033591562410714279497 : Rat) / 6400000000000000000000), D1 := ((5401750922410714279497 : Rat) / 6400000000000000000000), D2 := ((662807562410714279497 : Rat) / 6400000000000000000000), D3 := ((7447275982142857073 : Rat) / 160000000000000000000), D4 := ((99324424196428492197 : Rat) / 800000000000000000000), LB := ((89772842895703 : Rat) / 31250000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17033591562410714279497 : Rat) / 6400000000000000000000), R := ((1704103883839285713657 : Rat) / 640000000000000000000), D0 := ((1704103883839285713657 : Rat) / 640000000000000000000), D1 := ((540919819839285713657 : Rat) / 640000000000000000000), D2 := ((67025483839285713657 : Rat) / 640000000000000000000), D3 := ((290443763303571425847 : Rat) / 6400000000000000000000), D4 := ((787148117589285080503 : Rat) / 6400000000000000000000), LB := ((2930707059549731 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1704103883839285713657 : Rat) / 640000000000000000000), R := ((17048486114374999993643 : Rat) / 6400000000000000000000), D0 := ((17048486114374999993643 : Rat) / 6400000000000000000000), D1 := ((5416645474374999993643 : Rat) / 6400000000000000000000), D2 := ((677702114374999993643 : Rat) / 6400000000000000000000), D3 := ((141498243660714284387 : Rat) / 3200000000000000000000), D4 := ((77970084160714222343 : Rat) / 640000000000000000000), LB := ((30529300218116173 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((17048486114374999993643 : Rat) / 6400000000000000000000), R := ((4263983347589285712679 : Rat) / 1600000000000000000000), D0 := ((4263983347589285712679 : Rat) / 1600000000000000000000), D1 := ((1356023187589285712679 : Rat) / 1600000000000000000000), D2 := ((171287347589285712679 : Rat) / 1600000000000000000000), D3 := ((275549211339285711701 : Rat) / 6400000000000000000000), D4 := ((772253565624999366357 : Rat) / 6400000000000000000000), LB := ((3241975387853979 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4263983347589285712679 : Rat) / 1600000000000000000000), R := ((8535413971160714282431 : Rat) / 3200000000000000000000), D0 := ((8535413971160714282431 : Rat) / 3200000000000000000000), D1 := ((2719493651160714282431 : Rat) / 3200000000000000000000), D2 := ((350021971160714282431 : Rat) / 3200000000000000000000), D3 := ((67025483839285713657 : Rat) / 1600000000000000000000), D4 := ((191201572410714127321 : Rat) / 1600000000000000000000), LB := ((244997310958929 : Rat) / 3125000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8535413971160714282431 : Rat) / 3200000000000000000000), R := ((533928827946428571219 : Rat) / 200000000000000000000), D0 := ((533928827946428571219 : Rat) / 200000000000000000000), D1 := ((170433807946428571219 : Rat) / 200000000000000000000), D2 := ((22341827946428571219 : Rat) / 200000000000000000000), D3 := ((126603691696428570241 : Rat) / 3200000000000000000000), D4 := ((374955868839285397569 : Rat) / 3200000000000000000000), LB := ((8251755903525559 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((533928827946428571219 : Rat) / 200000000000000000000), R := ((8550308523124999996577 : Rat) / 3200000000000000000000), D0 := ((8550308523124999996577 : Rat) / 3200000000000000000000), D1 := ((2734388203124999996577 : Rat) / 3200000000000000000000), D2 := ((364916523124999996577 : Rat) / 3200000000000000000000), D3 := ((7447275982142857073 : Rat) / 200000000000000000000), D4 := ((22969287053571408781 : Rat) / 200000000000000000000), LB := ((9446980333445987 : Rat) / 5000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8550308523124999996577 : Rat) / 3200000000000000000000), R := ((171155115982142857073 : Rat) / 64000000000000000000), D0 := ((171155115982142857073 : Rat) / 64000000000000000000), D1 := ((54836709582142857073 : Rat) / 64000000000000000000), D2 := ((7447275982142857073 : Rat) / 64000000000000000000), D3 := ((22341827946428571219 : Rat) / 640000000000000000000), D4 := ((360061316874999683423 : Rat) / 3200000000000000000000), LB := ((33028339578562993 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((171155115982142857073 : Rat) / 64000000000000000000), R := ((8565203075089285710723 : Rat) / 3200000000000000000000), D0 := ((8565203075089285710723 : Rat) / 3200000000000000000000), D1 := ((2749282755089285710723 : Rat) / 3200000000000000000000), D2 := ((379811075089285710723 : Rat) / 3200000000000000000000), D3 := ((52130931874999999511 : Rat) / 1600000000000000000000), D4 := ((7052280817857136527 : Rat) / 64000000000000000000), LB := ((1020679957447057 : Rat) / 200000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8565203075089285710723 : Rat) / 3200000000000000000000), R := ((2143162587767857141949 : Rat) / 800000000000000000000), D0 := ((2143162587767857141949 : Rat) / 800000000000000000000), D1 := ((689182507767857141949 : Rat) / 800000000000000000000), D2 := ((96814587767857141949 : Rat) / 800000000000000000000), D3 := ((96814587767857141949 : Rat) / 3200000000000000000000), D4 := ((345166764910713969277 : Rat) / 3200000000000000000000), LB := ((1467384063829269 : Rat) / 200000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2143162587767857141949 : Rat) / 800000000000000000000), R := ((4293772451517857140971 : Rat) / 1600000000000000000000), D0 := ((4293772451517857140971 : Rat) / 1600000000000000000000), D1 := ((1385812291517857140971 : Rat) / 1600000000000000000000), D2 := ((201076451517857140971 : Rat) / 1600000000000000000000), D3 := ((22341827946428571219 : Rat) / 800000000000000000000), D4 := ((84429872232142778051 : Rat) / 800000000000000000000), LB := ((33287613367732893 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4293772451517857140971 : Rat) / 1600000000000000000000), R := ((1075304931874999999511 : Rat) / 400000000000000000000), D0 := ((1075304931874999999511 : Rat) / 400000000000000000000), D1 := ((348314891874999999511 : Rat) / 400000000000000000000), D2 := ((52130931874999999511 : Rat) / 400000000000000000000), D3 := ((7447275982142857073 : Rat) / 320000000000000000000), D4 := ((161412468482142699029 : Rat) / 1600000000000000000000), LB := ((10574649352520893 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1075304931874999999511 : Rat) / 400000000000000000000), R := ((431611427946428571219 : Rat) / 160000000000000000000), D0 := ((431611427946428571219 : Rat) / 160000000000000000000), D1 := ((140815411946428571219 : Rat) / 160000000000000000000), D2 := ((22341827946428571219 : Rat) / 160000000000000000000), D3 := ((7447275982142857073 : Rat) / 400000000000000000000), D4 := ((38491298124999960489 : Rat) / 400000000000000000000), LB := ((7639774057312643 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((431611427946428571219 : Rat) / 160000000000000000000), R := ((135344025982142857073 : Rat) / 50000000000000000000), D0 := ((135344025982142857073 : Rat) / 50000000000000000000), D1 := ((44470270982142857073 : Rat) / 50000000000000000000), D2 := ((7447275982142857073 : Rat) / 50000000000000000000), D3 := ((7447275982142857073 : Rat) / 800000000000000000000), D4 := ((13907064053571412781 : Rat) / 160000000000000000000), LB := ((2293077006951577 : Rat) / 50000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((135344025982142857073 : Rat) / 50000000000000000000), R := ((1086632710624999994511 : Rat) / 400000000000000000000), D0 := ((1086632710624999994511 : Rat) / 400000000000000000000), D1 := ((359642670624999994511 : Rat) / 400000000000000000000), D2 := ((63458710624999994511 : Rat) / 400000000000000000000), D3 := ((3880502767857137927 : Rat) / 400000000000000000000), D4 := ((3880502767857137927 : Rat) / 50000000000000000000), LB := ((3860046693563507 : Rat) / 100000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1086632710624999994511 : Rat) / 400000000000000000000), R := ((2177145924017857126949 : Rat) / 800000000000000000000), D0 := ((2177145924017857126949 : Rat) / 800000000000000000000), D1 := ((723165844017857126949 : Rat) / 800000000000000000000), D2 := ((130797924017857126949 : Rat) / 800000000000000000000), D3 := ((11641508303571413781 : Rat) / 800000000000000000000), D4 := ((27163519374999965489 : Rat) / 400000000000000000000), LB := ((25804941373377077 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2177145924017857126949 : Rat) / 800000000000000000000), R := ((545256606696428566219 : Rat) / 200000000000000000000), D0 := ((545256606696428566219 : Rat) / 200000000000000000000), D1 := ((181761586696428566219 : Rat) / 200000000000000000000), D2 := ((33669606696428566219 : Rat) / 200000000000000000000), D3 := ((3880502767857137927 : Rat) / 200000000000000000000), D4 := ((50446535982142793051 : Rat) / 800000000000000000000), LB := ((8735378792439463 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((545256606696428566219 : Rat) / 200000000000000000000), R := ((4365933356339285667679 : Rat) / 1600000000000000000000), D0 := ((4365933356339285667679 : Rat) / 1600000000000000000000), D1 := ((1457973196339285667679 : Rat) / 1600000000000000000000), D2 := ((273237356339285667679 : Rat) / 1600000000000000000000), D3 := ((34924524910714241343 : Rat) / 1600000000000000000000), D4 := ((11641508303571413781 : Rat) / 200000000000000000000), LB := ((1046368182932167 : Rat) / 100000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4365933356339285667679 : Rat) / 1600000000000000000000), R := ((2184906929553571402803 : Rat) / 800000000000000000000), D0 := ((2184906929553571402803 : Rat) / 800000000000000000000), D1 := ((730926849553571402803 : Rat) / 800000000000000000000), D2 := ((138558929553571402803 : Rat) / 800000000000000000000), D3 := ((3880502767857137927 : Rat) / 160000000000000000000), D4 := ((89251563660714172321 : Rat) / 1600000000000000000000), LB := ((691098288851319 : Rat) / 125000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2184906929553571402803 : Rat) / 800000000000000000000), R := ((4373694361874999943533 : Rat) / 1600000000000000000000), D0 := ((4373694361874999943533 : Rat) / 1600000000000000000000), D1 := ((1465734201874999943533 : Rat) / 1600000000000000000000), D2 := ((280998361874999943533 : Rat) / 1600000000000000000000), D3 := ((42685530446428517197 : Rat) / 1600000000000000000000), D4 := ((42685530446428517197 : Rat) / 800000000000000000000), LB := ((8151522655674981 : Rat) / 5000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4373694361874999943533 : Rat) / 1600000000000000000000), R := ((8751269226517857024993 : Rat) / 3200000000000000000000), D0 := ((8751269226517857024993 : Rat) / 3200000000000000000000), D1 := ((2935348906517857024993 : Rat) / 3200000000000000000000), D2 := ((565877226517857024993 : Rat) / 3200000000000000000000), D3 := ((89251563660714172321 : Rat) / 3200000000000000000000), D4 := ((81490558124999896467 : Rat) / 1600000000000000000000), LB := ((4736285924481387 : Rat) / 1000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8751269226517857024993 : Rat) / 3200000000000000000000), R := ((218878743232142854073 : Rat) / 80000000000000000000), D0 := ((218878743232142854073 : Rat) / 80000000000000000000), D1 := ((73480735232142854073 : Rat) / 80000000000000000000), D2 := ((14243943232142854073 : Rat) / 80000000000000000000), D3 := ((11641508303571413781 : Rat) / 400000000000000000000), D4 := ((159100613482142655007 : Rat) / 3200000000000000000000), LB := ((1748138787226683 : Rat) / 500000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((218878743232142854073 : Rat) / 80000000000000000000), R := ((8759030232053571300847 : Rat) / 3200000000000000000000), D0 := ((8759030232053571300847 : Rat) / 3200000000000000000000), D1 := ((2943109912053571300847 : Rat) / 3200000000000000000000), D2 := ((573638232053571300847 : Rat) / 3200000000000000000000), D3 := ((3880502767857137927 : Rat) / 128000000000000000000), D4 := ((3880502767857137927 : Rat) / 80000000000000000000), LB := ((4980170817329821 : Rat) / 2000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8759030232053571300847 : Rat) / 3200000000000000000000), R := ((4381455367410714219387 : Rat) / 1600000000000000000000), D0 := ((4381455367410714219387 : Rat) / 1600000000000000000000), D1 := ((1473495207410714219387 : Rat) / 1600000000000000000000), D2 := ((288759367410714219387 : Rat) / 1600000000000000000000), D3 := ((50446535982142793051 : Rat) / 1600000000000000000000), D4 := ((151339607946428379153 : Rat) / 3200000000000000000000), LB := ((857492840974361 : Rat) / 500000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4381455367410714219387 : Rat) / 1600000000000000000000), R := ((8766791237589285576701 : Rat) / 3200000000000000000000), D0 := ((8766791237589285576701 : Rat) / 3200000000000000000000), D1 := ((2950870917589285576701 : Rat) / 3200000000000000000000), D2 := ((581399237589285576701 : Rat) / 3200000000000000000000), D3 := ((104773574732142724029 : Rat) / 3200000000000000000000), D4 := ((73729552589285620613 : Rat) / 1600000000000000000000), LB := ((2339421864002933 : Rat) / 2000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8766791237589285576701 : Rat) / 3200000000000000000000), R := ((2192667935089285678657 : Rat) / 800000000000000000000), D0 := ((2192667935089285678657 : Rat) / 800000000000000000000), D1 := ((738687855089285678657 : Rat) / 800000000000000000000), D2 := ((146319935089285678657 : Rat) / 800000000000000000000), D3 := ((27163519374999965489 : Rat) / 800000000000000000000), D4 := ((143578602410714103299 : Rat) / 3200000000000000000000), LB := ((266986303182927 : Rat) / 312500000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2192667935089285678657 : Rat) / 800000000000000000000), R := ((1754910448624999970511 : Rat) / 640000000000000000000), D0 := ((1754910448624999970511 : Rat) / 640000000000000000000), D1 := ((591726384624999970511 : Rat) / 640000000000000000000), D2 := ((117832048624999970511 : Rat) / 640000000000000000000), D3 := ((112534580267856999883 : Rat) / 3200000000000000000000), D4 := ((34924524910714241343 : Rat) / 800000000000000000000), LB := ((481448223561623 : Rat) / 625000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1754910448624999970511 : Rat) / 640000000000000000000), R := ((4389216372946428495241 : Rat) / 1600000000000000000000), D0 := ((4389216372946428495241 : Rat) / 1600000000000000000000), D1 := ((1481256212946428495241 : Rat) / 1600000000000000000000), D2 := ((296520372946428495241 : Rat) / 1600000000000000000000), D3 := ((11641508303571413781 : Rat) / 320000000000000000000), D4 := ((27163519374999965489 : Rat) / 640000000000000000000), LB := ((143790123358703 : Rat) / 156250000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4389216372946428495241 : Rat) / 1600000000000000000000), R := ((8782313248660714128409 : Rat) / 3200000000000000000000), D0 := ((8782313248660714128409 : Rat) / 3200000000000000000000), D1 := ((2966392928660714128409 : Rat) / 3200000000000000000000), D2 := ((596921248660714128409 : Rat) / 3200000000000000000000), D3 := ((120295585803571275737 : Rat) / 3200000000000000000000), D4 := ((65968547053571344759 : Rat) / 1600000000000000000000), LB := ((3270242555327707 : Rat) / 2500000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8782313248660714128409 : Rat) / 3200000000000000000000), R := ((274568554732142852073 : Rat) / 100000000000000000000), D0 := ((274568554732142852073 : Rat) / 100000000000000000000), D1 := ((92821044732142852073 : Rat) / 100000000000000000000), D2 := ((18775054732142852073 : Rat) / 100000000000000000000), D3 := ((3880502767857137927 : Rat) / 100000000000000000000), D4 := ((128056591339285551591 : Rat) / 3200000000000000000000), LB := ((4847587381276719 : Rat) / 2500000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((274568554732142852073 : Rat) / 100000000000000000000), R := ((8790074254196428404263 : Rat) / 3200000000000000000000), D0 := ((8790074254196428404263 : Rat) / 3200000000000000000000), D1 := ((2974153934196428404263 : Rat) / 3200000000000000000000), D2 := ((604682254196428404263 : Rat) / 3200000000000000000000), D3 := ((128056591339285551591 : Rat) / 3200000000000000000000), D4 := ((3880502767857137927 : Rat) / 100000000000000000000), LB := ((28195826804374713 : Rat) / 10000000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((8790074254196428404263 : Rat) / 3200000000000000000000), R := ((879395475696428554219 : Rat) / 320000000000000000000), D0 := ((879395475696428554219 : Rat) / 320000000000000000000), D1 := ((297803443696428554219 : Rat) / 320000000000000000000), D2 := ((60856275696428554219 : Rat) / 320000000000000000000), D3 := ((65968547053571344759 : Rat) / 1600000000000000000000), D4 := ((120295585803571275737 : Rat) / 3200000000000000000000), LB := ((1978815773854059 : Rat) / 500000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((879395475696428554219 : Rat) / 320000000000000000000), R := ((2200428940624999954511 : Rat) / 800000000000000000000), D0 := ((2200428940624999954511 : Rat) / 800000000000000000000), D1 := ((746448860624999954511 : Rat) / 800000000000000000000), D2 := ((154080940624999954511 : Rat) / 800000000000000000000), D3 := ((34924524910714241343 : Rat) / 800000000000000000000), D4 := ((11641508303571413781 : Rat) / 320000000000000000000), LB := ((22287741357329 : Rat) / 78125000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((2200428940624999954511 : Rat) / 800000000000000000000), R := ((4404738384017857046949 : Rat) / 1600000000000000000000), D0 := ((4404738384017857046949 : Rat) / 1600000000000000000000), D1 := ((1496778224017857046949 : Rat) / 1600000000000000000000), D2 := ((312042384017857046949 : Rat) / 1600000000000000000000), D3 := ((73729552589285620613 : Rat) / 1600000000000000000000), D4 := ((27163519374999965489 : Rat) / 800000000000000000000), LB := ((1011274451500399 : Rat) / 250000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((4404738384017857046949 : Rat) / 1600000000000000000000), R := ((1102154721696428546219 : Rat) / 400000000000000000000), D0 := ((1102154721696428546219 : Rat) / 400000000000000000000), D1 := ((375164681696428546219 : Rat) / 400000000000000000000), D2 := ((78980721696428546219 : Rat) / 400000000000000000000), D3 := ((3880502767857137927 : Rat) / 80000000000000000000), D4 := ((50446535982142793051 : Rat) / 1600000000000000000000), LB := ((1127219179902203 : Rat) / 125000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1102154721696428546219 : Rat) / 400000000000000000000), R := ((441637989232142846073 : Rat) / 160000000000000000000), D0 := ((441637989232142846073 : Rat) / 160000000000000000000), D1 := ((150841973232142846073 : Rat) / 160000000000000000000), D2 := ((32368389232142846073 : Rat) / 160000000000000000000), D3 := ((42685530446428517197 : Rat) / 800000000000000000000), D4 := ((11641508303571413781 : Rat) / 400000000000000000000), LB := ((367548544751177 : Rat) / 62500000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((441637989232142846073 : Rat) / 160000000000000000000), R := ((553017612232142842073 : Rat) / 200000000000000000000), D0 := ((553017612232142842073 : Rat) / 200000000000000000000), D1 := ((189522592232142842073 : Rat) / 200000000000000000000), D2 := ((41430612232142842073 : Rat) / 200000000000000000000), D3 := ((11641508303571413781 : Rat) / 200000000000000000000), D4 := ((3880502767857137927 : Rat) / 160000000000000000000), LB := ((4745986451917239 : Rat) / 200000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((553017612232142842073 : Rat) / 200000000000000000000), R := ((1109915727232142822073 : Rat) / 400000000000000000000), D0 := ((1109915727232142822073 : Rat) / 400000000000000000000), D1 := ((382925687232142822073 : Rat) / 400000000000000000000), D2 := ((86741727232142822073 : Rat) / 400000000000000000000), D3 := ((27163519374999965489 : Rat) / 400000000000000000000), D4 := ((3880502767857137927 : Rat) / 200000000000000000000), LB := ((816608452391987 : Rat) / 25000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1109915727232142822073 : Rat) / 400000000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((3880502767857137927 : Rat) / 50000000000000000000), D4 := ((3880502767857137927 : Rat) / 400000000000000000000), LB := ((13678486120634903 : Rat) / 100000000000000000) },
  { w1 := ((2179178215080593 : Rat) / 1000000000000000), w2 := (0 : Rat), w3 := ((6397602518619737 : Rat) / 100000000000000000), w4 := ((1994003341453323 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((135344025982142857073 : Rat) / 50000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((69977470982142857163 : Rat) / 25000000000000000000), D0 := ((69977470982142857163 : Rat) / 25000000000000000000), D1 := ((24540593482142857163 : Rat) / 25000000000000000000), D2 := ((6029095982142857163 : Rat) / 25000000000000000000), D3 := ((4610915982142857253 : Rat) / 50000000000000000000), D4 := ((365206607142859663 : Rat) / 25000000000000000000), LB := ((1261846773040487 : Rat) / 200000000000000000) }
]

def block094RightChunk000L : Rat := ((17989033482142857151 : Rat) / 10000000000000000000)
def block094RightChunk000R : Rat := ((69977470982142857163 : Rat) / 25000000000000000000)

def block094RightChunk000Certificate : Bool :=
  allBoxesValid block094RightChunk000 &&
  coversFromBool block094RightChunk000 block094RightChunk000L block094RightChunk000R

theorem block094RightChunk000Certificate_eq_true :
    block094RightChunk000Certificate = true := by
  native_decide

def block094RightChainCertificate : Bool :=
  decide (
    block094RightL = ((17989033482142857151 : Rat) / 10000000000000000000) /\
    ((69977470982142857163 : Rat) / 25000000000000000000) = block094RightR)

theorem block094RightChainCertificate_eq_true :
    block094RightChainCertificate = true := by
  native_decide

def block094LeftBoxCount : Nat := boxCount block094LeftBoxes
def block094RightBoxCount : Nat := 61

def block094_rational_certificate : Prop :=
    block094LeftCertificate = true /\
    block094RightChainCertificate = true /\
    block094RightChunk000Certificate = true

theorem block094_rational_certificate_proof :
    block094_rational_certificate := by
  exact ⟨block094LeftCertificate_eq_true, block094RightChainCertificate_eq_true, block094RightChunk000Certificate_eq_true⟩

end Block094
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block094

open Set

def block094W1 : Rat := ((2179178215080593 : Rat) / 1000000000000000)
def block094W2 : Rat := (0 : Rat)
def block094W3 : Rat := ((6397602518619737 : Rat) / 100000000000000000)
def block094W4 : Rat := ((1994003341453323 : Rat) / 10000000000000000)
def block094S1 : Rat := ((18174751 : Rat) / 10000000)
def block094S2 : Rat := ((511587 : Rat) / 200000)
def block094S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block094S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block094V (y : ℝ) : ℝ :=
  ratPotential block094W1 block094W2 block094W3 block094W4 block094S1 block094S2 block094S3 block094S4 y

def block094LeftParamsCertificate : Bool :=
  allBoxesSameParams block094LeftBoxes block094W1 block094W2 block094W3 block094W4 block094S1 block094S2 block094S3 block094S4

theorem block094LeftParamsCertificate_eq_true :
    block094LeftParamsCertificate = true := by
  native_decide

theorem block094_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block094LeftL : ℝ) (block094LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block094S1 : ℝ))
    (hy2ne : y ≠ (block094S2 : ℝ))
    (hy3ne : y ≠ (block094S3 : ℝ))
    (hy4ne : y ≠ (block094S4 : ℝ)) :
    0 < block094V y := by
  have hcert := block094LeftCertificate_eq_true
  unfold block094LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block094LeftBoxes) (lo := block094LeftL) (hi := block094LeftR)
    (w1 := block094W1) (w2 := block094W2) (w3 := block094W3) (w4 := block094W4)
    (s1 := block094S1) (s2 := block094S2) (s3 := block094S3) (s4 := block094S4)
    hboxes hcover block094LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block094RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block094RightChunk000 block094W1 block094W2 block094W3 block094W4 block094S1 block094S2 block094S3 block094S4

theorem block094RightChunk000ParamsCertificate_eq_true :
    block094RightChunk000ParamsCertificate = true := by
  native_decide

theorem block094_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block094RightChunk000L : ℝ) (block094RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block094S1 : ℝ))
    (hy2ne : y ≠ (block094S2 : ℝ))
    (hy3ne : y ≠ (block094S3 : ℝ))
    (hy4ne : y ≠ (block094S4 : ℝ)) :
    0 < block094V y := by
  have hcert := block094RightChunk000Certificate_eq_true
  unfold block094RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block094RightChunk000) (lo := block094RightChunk000L) (hi := block094RightChunk000R)
    (w1 := block094W1) (w2 := block094W2) (w3 := block094W3) (w4 := block094W4)
    (s1 := block094S1) (s2 := block094S2) (s3 := block094S3) (s4 := block094S4)
    hboxes hcover block094RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block094_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block094RightL : ℝ) (block094RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block094S1 : ℝ))
    (hy2ne : y ≠ (block094S2 : ℝ))
    (hy3ne : y ≠ (block094S3 : ℝ))
    (hy4ne : y ≠ (block094S4 : ℝ)) :
    0 < block094V y := by
  have hL : (block094RightChunk000L : ℝ) = (block094RightL : ℝ) := by
    norm_num [block094RightChunk000L, block094RightL]
  have hR : (block094RightChunk000R : ℝ) = (block094RightR : ℝ) := by
    norm_num [block094RightChunk000R, block094RightR]
  have hyc : y ∈ Icc (block094RightChunk000L : ℝ) (block094RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block094_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block094_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block094LeftL : ℝ) (block094LeftR : ℝ) →
    y ≠ 0 → y ≠ (block094S1 : ℝ) → y ≠ (block094S2 : ℝ) →
    y ≠ (block094S3 : ℝ) → y ≠ (block094S4 : ℝ) → 0 < block094V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block094RightL : ℝ) (block094RightR : ℝ) →
    y ≠ 0 → y ≠ (block094S1 : ℝ) → y ≠ (block094S2 : ℝ) →
    y ≠ (block094S3 : ℝ) → y ≠ (block094S4 : ℝ) → 0 < block094V y)

theorem block094_reallog_certificate_proof :
    block094_reallog_certificate := by
  exact ⟨block094_left_V_pos, block094_right_V_pos⟩

end Block094
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block094.block094V
#check Erdos1038Lean.M1817475.Block094.block094_left_V_pos
#check Erdos1038Lean.M1817475.Block094.block094_right_V_pos
#check Erdos1038Lean.M1817475.Block094.block094_reallog_certificate_proof
