/-
Self-contained Lean4Web paste file.
Block 240 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block240

def block240LeftL : Rat := ((38518082589285714389 : Rat) / 50000000000000000000)
def block240LeftR : Rat := ((481598214285714287 : Rat) / 625000000000000000)
def block240RightL : Rat := ((88518082589285714389 : Rat) / 50000000000000000000)
def block240RightR : Rat := ((1731598214285714287 : Rat) / 625000000000000000)

def block240LeftBoxes : List RatBox := [
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((38518082589285714389 : Rat) / 50000000000000000000), R := ((481598214285714287 : Rat) / 625000000000000000), D0 := ((481598214285714287 : Rat) / 625000000000000000), D1 := ((52355672410714285611 : Rat) / 50000000000000000000), D2 := ((89378667410714285611 : Rat) / 50000000000000000000), D3 := ((24382427812499999949 : Rat) / 12500000000000000000), D4 := ((98360553303571423571 : Rat) / 50000000000000000000), LB := ((280317735317559 : Rat) / 200000000000000000) }
]

def block240LeftCertificate : Bool :=
  allBoxesValid block240LeftBoxes &&
  coversFromBool block240LeftBoxes block240LeftL block240LeftR

theorem block240LeftCertificate_eq_true :
    block240LeftCertificate = true := by
  native_decide

def block240RightChunk000 : List RatBox := [
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((88518082589285714389 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((2355672410714285611 : Rat) / 50000000000000000000), D2 := ((39378667410714285611 : Rat) / 50000000000000000000), D3 := ((11882427812499999949 : Rat) / 12500000000000000000), D4 := ((48360553303571423571 : Rat) / 50000000000000000000), LB := ((2576359269536399 : Rat) / 1250000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((1150122022321428449 : Rat) / 1250000000000000000), LB := ((5959695447846819 : Rat) / 50000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((687334584821428449 : Rat) / 1250000000000000000), LB := ((465477756086829 : Rat) / 6250000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((4406933392857142837 : Rat) / 10000000000000000000), D4 := ((571637725446428449 : Rat) / 1250000000000000000), LB := ((2165614894740009 : Rat) / 50000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((74449321 : Rat) / 32000000), R := ((751897809 : Rat) / 320000000), D0 := ((751897809 : Rat) / 320000000), D1 := ((170305777 : Rat) / 320000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3944145955357142837 : Rat) / 10000000000000000000), D4 := ((513789295758928449 : Rat) / 1250000000000000000), LB := ((9393668203340061 : Rat) / 250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((751897809 : Rat) / 320000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((66641391 : Rat) / 320000000), D3 := ((3712752236607142837 : Rat) / 10000000000000000000), D4 := ((484865080915178449 : Rat) / 1250000000000000000), LB := ((7359770681367589 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((94912801 : Rat) / 40000000), R := ((305201883 : Rat) / 128000000), D0 := ((305201883 : Rat) / 128000000), D1 := ((362825351 : Rat) / 640000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((455940866071428449 : Rat) / 1250000000000000000), LB := ((551155999347833 : Rat) / 31250000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((305201883 : Rat) / 128000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((22213797 : Rat) / 128000000), D3 := ((3365661658482142837 : Rat) / 10000000000000000000), D4 := ((441478758649553449 : Rat) / 1250000000000000000), LB := ((564045957672751 : Rat) / 62500000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((3249964799107142837 : Rat) / 10000000000000000000), D4 := ((427016651227678449 : Rat) / 1250000000000000000), LB := ((14285514491887419 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((123561673 : Rat) / 51200000), D0 := ((123561673 : Rat) / 51200000), D1 := ((762673697 : Rat) / 1280000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((3134267939732142837 : Rat) / 10000000000000000000), D4 := ((412554543805803449 : Rat) / 1250000000000000000), LB := ((11238359679861809 : Rat) / 2000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((123561673 : Rat) / 51200000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((7404599 : Rat) / 51200000), D3 := ((3076419510044642837 : Rat) / 10000000000000000000), D4 := ((405323490094865949 : Rat) / 1250000000000000000), LB := ((1350704846129619 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((3018571080357142837 : Rat) / 10000000000000000000), D4 := ((398092436383928449 : Rat) / 1250000000000000000), LB := ((1695583012131241 : Rat) / 20000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1243021329 : Rat) / 512000000), D0 := ((1243021329 : Rat) / 512000000), D1 := ((1562370389 : Rat) / 2560000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((2960722650669642837 : Rat) / 10000000000000000000), D4 := ((390861382672990949 : Rat) / 1250000000000000000), LB := ((30422293861372407 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1243021329 : Rat) / 512000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((66641391 : Rat) / 512000000), D3 := ((2931798435825892837 : Rat) / 10000000000000000000), D4 := ((387245855817522199 : Rat) / 1250000000000000000), LB := ((4981581853495537 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((6229915843 : Rat) / 2560000000), D0 := ((6229915843 : Rat) / 2560000000), D1 := ((1577179587 : Rat) / 2560000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2902874220982142837 : Rat) / 10000000000000000000), D4 := ((383630328962053449 : Rat) / 1250000000000000000), LB := ((5136845718378691 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6229915843 : Rat) / 2560000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((318397757 : Rat) / 2560000000), D3 := ((2873950006138392837 : Rat) / 10000000000000000000), D4 := ((380014802106584699 : Rat) / 1250000000000000000), LB := ((1857318111828099 : Rat) / 12500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((12482045483 : Rat) / 5120000000), D0 := ((12482045483 : Rat) / 5120000000), D1 := ((3176572971 : Rat) / 5120000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2845025791294642837 : Rat) / 10000000000000000000), D4 := ((376399275251115949 : Rat) / 1250000000000000000), LB := ((4888767958205753 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12482045483 : Rat) / 5120000000), R := ((6244725041 : Rat) / 2560000000), D0 := ((6244725041 : Rat) / 2560000000), D1 := ((318397757 : Rat) / 512000000), D2 := ((614581717 : Rat) / 5120000000), D3 := ((2830563683872767837 : Rat) / 10000000000000000000), D4 := ((187295755911690787 : Rat) / 625000000000000000), LB := ((7947747635716207 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6244725041 : Rat) / 2560000000), R := ((12496854681 : Rat) / 5120000000), D0 := ((12496854681 : Rat) / 5120000000), D1 := ((3191382169 : Rat) / 5120000000), D2 := ((303588559 : Rat) / 2560000000), D3 := ((2816101576450892837 : Rat) / 10000000000000000000), D4 := ((372783748395647199 : Rat) / 1250000000000000000), LB := ((1246743290301111 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12496854681 : Rat) / 5120000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((599772519 : Rat) / 5120000000), D3 := ((2801639469029017837 : Rat) / 10000000000000000000), D4 := ((46371998120989103 : Rat) / 156250000000000000), LB := ((1159279371472019 : Rat) / 1250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((156303241 : Rat) / 64000000), R := ((12511663879 : Rat) / 5120000000), D0 := ((12511663879 : Rat) / 5120000000), D1 := ((3206191367 : Rat) / 5120000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2787177361607142837 : Rat) / 10000000000000000000), D4 := ((369168221540178449 : Rat) / 1250000000000000000), LB := ((3159686535672279 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12511663879 : Rat) / 5120000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((584963321 : Rat) / 5120000000), D3 := ((2772715254185267837 : Rat) / 10000000000000000000), D4 := ((183680229056222037 : Rat) / 625000000000000000), LB := ((225402868509611 : Rat) / 625000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((12526473077 : Rat) / 5120000000), D0 := ((12526473077 : Rat) / 5120000000), D1 := ((644200113 : Rat) / 1024000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((2758253146763392837 : Rat) / 10000000000000000000), D4 := ((365552694684709699 : Rat) / 1250000000000000000), LB := ((1423981692113413 : Rat) / 12500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12526473077 : Rat) / 5120000000), R := ((25060350753 : Rat) / 10240000000), D0 := ((25060350753 : Rat) / 10240000000), D1 := ((6449405729 : Rat) / 10240000000), D2 := ((570154123 : Rat) / 5120000000), D3 := ((2743791039341517837 : Rat) / 10000000000000000000), D4 := ((90936232814243831 : Rat) / 312500000000000000), LB := ((1468930950475969 : Rat) / 1250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25060350753 : Rat) / 10240000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((1132903647 : Rat) / 10240000000), D3 := ((2736559985630580337 : Rat) / 10000000000000000000), D4 := ((725682099086216273 : Rat) / 2500000000000000000), LB := ((2145044339365243 : Rat) / 2000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((25075159951 : Rat) / 10240000000), D0 := ((25075159951 : Rat) / 10240000000), D1 := ((6464214927 : Rat) / 10240000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2729328931919642837 : Rat) / 10000000000000000000), D4 := ((361937167829240949 : Rat) / 1250000000000000000), LB := ((9762925482301177 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25075159951 : Rat) / 10240000000), R := ((501651291 : Rat) / 204800000), D0 := ((501651291 : Rat) / 204800000), D1 := ((3235809763 : Rat) / 5120000000), D2 := ((1118094449 : Rat) / 10240000000), D3 := ((2722097878208705337 : Rat) / 10000000000000000000), D4 := ((722066572230747523 : Rat) / 2500000000000000000), LB := ((2216271318307983 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((501651291 : Rat) / 204800000), R := ((25089969149 : Rat) / 10240000000), D0 := ((25089969149 : Rat) / 10240000000), D1 := ((51832193 : Rat) / 81920000), D2 := ((22213797 : Rat) / 204800000), D3 := ((2714866824497767837 : Rat) / 10000000000000000000), D4 := ((180064702200753287 : Rat) / 625000000000000000), LB := ((251007421728823 : Rat) / 312500000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25089969149 : Rat) / 10240000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((1103285251 : Rat) / 10240000000), D3 := ((2707635770786830337 : Rat) / 10000000000000000000), D4 := ((718451045375278773 : Rat) / 2500000000000000000), LB := ((1452985788924277 : Rat) / 2000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((25104778347 : Rat) / 10240000000), D0 := ((25104778347 : Rat) / 10240000000), D1 := ((6493833323 : Rat) / 10240000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((2700404717075892837 : Rat) / 10000000000000000000), D4 := ((358321640973772199 : Rat) / 1250000000000000000), LB := ((6563717053705287 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25104778347 : Rat) / 10240000000), R := ((12556091473 : Rat) / 5120000000), D0 := ((12556091473 : Rat) / 5120000000), D1 := ((3250618961 : Rat) / 5120000000), D2 := ((1088476053 : Rat) / 10240000000), D3 := ((2693173663364955337 : Rat) / 10000000000000000000), D4 := ((714835518519810023 : Rat) / 2500000000000000000), LB := ((2964585083372051 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12556091473 : Rat) / 5120000000), R := ((5023917509 : Rat) / 2048000000), D0 := ((5023917509 : Rat) / 2048000000), D1 := ((6508642521 : Rat) / 10240000000), D2 := ((540535727 : Rat) / 5120000000), D3 := ((2685942609654017837 : Rat) / 10000000000000000000), D4 := ((5570529336656841 : Rat) / 19531250000000000), LB := ((268093391192159 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((5023917509 : Rat) / 2048000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((214733371 : Rat) / 2048000000), D3 := ((2678711555943080337 : Rat) / 10000000000000000000), D4 := ((711219991664341273 : Rat) / 2500000000000000000), LB := ((9724802110187003 : Rat) / 20000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((25134396743 : Rat) / 10240000000), D0 := ((25134396743 : Rat) / 10240000000), D1 := ((6523451719 : Rat) / 10240000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2671480502232142837 : Rat) / 10000000000000000000), D4 := ((354706114118303449 : Rat) / 1250000000000000000), LB := ((173100495491239 : Rat) / 390625000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25134396743 : Rat) / 10240000000), R := ((12570900671 : Rat) / 5120000000), D0 := ((12570900671 : Rat) / 5120000000), D1 := ((3265428159 : Rat) / 5120000000), D2 := ((1058857657 : Rat) / 10240000000), D3 := ((2664249448521205337 : Rat) / 10000000000000000000), D4 := ((707604464808872523 : Rat) / 2500000000000000000), LB := ((40693976448991087 : Rat) / 100000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12570900671 : Rat) / 5120000000), R := ((25149205941 : Rat) / 10240000000), D0 := ((25149205941 : Rat) / 10240000000), D1 := ((6538260917 : Rat) / 10240000000), D2 := ((525726529 : Rat) / 5120000000), D3 := ((2657018394810267837 : Rat) / 10000000000000000000), D4 := ((176449175345284537 : Rat) / 625000000000000000), LB := ((18885516513039713 : Rat) / 50000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25149205941 : Rat) / 10240000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((1044048459 : Rat) / 10240000000), D3 := ((2649787341099330337 : Rat) / 10000000000000000000), D4 := ((703988937953403773 : Rat) / 2500000000000000000), LB := ((3555129794971523 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((25164015139 : Rat) / 10240000000), D0 := ((25164015139 : Rat) / 10240000000), D1 := ((1310614023 : Rat) / 2048000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((2642556287388392837 : Rat) / 10000000000000000000), D4 := ((351090587262834699 : Rat) / 1250000000000000000), LB := ((1361652151449233 : Rat) / 4000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25164015139 : Rat) / 10240000000), R := ((12585709869 : Rat) / 5120000000), D0 := ((12585709869 : Rat) / 5120000000), D1 := ((3280237357 : Rat) / 5120000000), D2 := ((1029239261 : Rat) / 10240000000), D3 := ((2635325233677455337 : Rat) / 10000000000000000000), D4 := ((700373411097935023 : Rat) / 2500000000000000000), LB := ((831192947624293 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12585709869 : Rat) / 5120000000), R := ((25178824337 : Rat) / 10240000000), D0 := ((25178824337 : Rat) / 10240000000), D1 := ((6567879313 : Rat) / 10240000000), D2 := ((510917331 : Rat) / 5120000000), D3 := ((2628094179966517837 : Rat) / 10000000000000000000), D4 := ((87320705958775081 : Rat) / 312500000000000000), LB := ((414716827717293 : Rat) / 1250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25178824337 : Rat) / 10240000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((1014430063 : Rat) / 10240000000), D3 := ((2620863126255580337 : Rat) / 10000000000000000000), D4 := ((696757884242466273 : Rat) / 2500000000000000000), LB := ((3383713705004121 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((5038726707 : Rat) / 2048000000), D0 := ((5038726707 : Rat) / 2048000000), D1 := ((6582688511 : Rat) / 10240000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2613632072544642837 : Rat) / 10000000000000000000), D4 := ((347475060407365949 : Rat) / 1250000000000000000), LB := ((7046837031587927 : Rat) / 20000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((5038726707 : Rat) / 2048000000), R := ((12600519067 : Rat) / 5120000000), D0 := ((12600519067 : Rat) / 5120000000), D1 := ((659009311 : Rat) / 1024000000), D2 := ((199924173 : Rat) / 2048000000), D3 := ((2606401018833705337 : Rat) / 10000000000000000000), D4 := ((693142357386997523 : Rat) / 2500000000000000000), LB := ((4671966985556053 : Rat) / 12500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12600519067 : Rat) / 5120000000), R := ((25208442733 : Rat) / 10240000000), D0 := ((25208442733 : Rat) / 10240000000), D1 := ((6597497709 : Rat) / 10240000000), D2 := ((496108133 : Rat) / 5120000000), D3 := ((2599169965122767837 : Rat) / 10000000000000000000), D4 := ((172833648489815787 : Rat) / 625000000000000000), LB := ((402691894745677 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25208442733 : Rat) / 10240000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((984811667 : Rat) / 10240000000), D3 := ((2591938911411830337 : Rat) / 10000000000000000000), D4 := ((689526830531528773 : Rat) / 2500000000000000000), LB := ((4392210554747811 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((25223251931 : Rat) / 10240000000), D0 := ((25223251931 : Rat) / 10240000000), D1 := ((6612306907 : Rat) / 10240000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((2584707857700892837 : Rat) / 10000000000000000000), D4 := ((343859533551897199 : Rat) / 1250000000000000000), LB := ((483422077365403 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25223251931 : Rat) / 10240000000), R := ((2523065653 : Rat) / 1024000000), D0 := ((2523065653 : Rat) / 1024000000), D1 := ((3309855753 : Rat) / 5120000000), D2 := ((970002469 : Rat) / 10240000000), D3 := ((2577476803989955337 : Rat) / 10000000000000000000), D4 := ((685911303676060023 : Rat) / 2500000000000000000), LB := ((5353738850408241 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((2523065653 : Rat) / 1024000000), R := ((25238061129 : Rat) / 10240000000), D0 := ((25238061129 : Rat) / 10240000000), D1 := ((1325423221 : Rat) / 2048000000), D2 := ((96259787 : Rat) / 1024000000), D3 := ((2570245750279017837 : Rat) / 10000000000000000000), D4 := ((42756471265520353 : Rat) / 156250000000000000), LB := ((23248325835383 : Rat) / 39062500000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25238061129 : Rat) / 10240000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((955193271 : Rat) / 10240000000), D3 := ((2563014696568080337 : Rat) / 10000000000000000000), D4 := ((682295776820591273 : Rat) / 2500000000000000000), LB := ((6628542994299713 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((197230201 : Rat) / 80000000), R := ((25252870327 : Rat) / 10240000000), D0 := ((25252870327 : Rat) / 10240000000), D1 := ((6641925303 : Rat) / 10240000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((340244006696428449 : Rat) / 1250000000000000000), LB := ((184637414058067 : Rat) / 250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25252870327 : Rat) / 10240000000), R := ((12630137463 : Rat) / 5120000000), D0 := ((12630137463 : Rat) / 5120000000), D1 := ((3324664951 : Rat) / 5120000000), D2 := ((940384073 : Rat) / 10240000000), D3 := ((2548552589146205337 : Rat) / 10000000000000000000), D4 := ((678680249965122523 : Rat) / 2500000000000000000), LB := ((8223294088607891 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12630137463 : Rat) / 5120000000), R := ((1010707181 : Rat) / 409600000), D0 := ((1010707181 : Rat) / 409600000), D1 := ((6656734501 : Rat) / 10240000000), D2 := ((466489737 : Rat) / 5120000000), D3 := ((2541321535435267837 : Rat) / 10000000000000000000), D4 := ((169218121634347037 : Rat) / 625000000000000000), LB := ((571426070349601 : Rat) / 625000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1010707181 : Rat) / 409600000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 81920000), D3 := ((2534090481724330337 : Rat) / 10000000000000000000), D4 := ((675064723109653773 : Rat) / 2500000000000000000), LB := ((1268120926521607 : Rat) / 1250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((25282488723 : Rat) / 10240000000), D0 := ((25282488723 : Rat) / 10240000000), D1 := ((6671543699 : Rat) / 10240000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((2526859428013392837 : Rat) / 10000000000000000000), D4 := ((336628479840959699 : Rat) / 1250000000000000000), LB := ((5615333751226581 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((25282488723 : Rat) / 10240000000), R := ((12644946661 : Rat) / 5120000000), D0 := ((12644946661 : Rat) / 5120000000), D1 := ((3339474149 : Rat) / 5120000000), D2 := ((910765677 : Rat) / 10240000000), D3 := ((2519628374302455337 : Rat) / 10000000000000000000), D4 := ((671449196254185023 : Rat) / 2500000000000000000), LB := ((1240086141973129 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12644946661 : Rat) / 5120000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((451680539 : Rat) / 5120000000), D3 := ((2512397320591517837 : Rat) / 10000000000000000000), D4 := ((83705179103306331 : Rat) / 312500000000000000), LB := ((12039742603014991 : Rat) / 100000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((632617563 : Rat) / 256000000), R := ((12659755859 : Rat) / 5120000000), D0 := ((12659755859 : Rat) / 5120000000), D1 := ((3354283347 : Rat) / 5120000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((2497935213169642837 : Rat) / 10000000000000000000), D4 := ((333012952985490949 : Rat) / 1250000000000000000), LB := ((39983939888216247 : Rat) / 100000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12659755859 : Rat) / 5120000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((436871341 : Rat) / 5120000000), D3 := ((2483473105747767837 : Rat) / 10000000000000000000), D4 := ((165602594778878287 : Rat) / 625000000000000000), LB := ((3573369362928347 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((12674565057 : Rat) / 5120000000), D0 := ((12674565057 : Rat) / 5120000000), D1 := ((673818509 : Rat) / 1024000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((2469010998325892837 : Rat) / 10000000000000000000), D4 := ((329397426130022199 : Rat) / 1250000000000000000), LB := ((2664403000968707 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((12674565057 : Rat) / 5120000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((422062143 : Rat) / 5120000000), D3 := ((2454548890904017837 : Rat) / 10000000000000000000), D4 := ((20474353918892989 : Rat) / 78125000000000000), LB := ((1454004752064919 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((2537874851 : Rat) / 1024000000), D0 := ((2537874851 : Rat) / 1024000000), D1 := ((3383901743 : Rat) / 5120000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((2440086783482142837 : Rat) / 10000000000000000000), D4 := ((325781899274553449 : Rat) / 1250000000000000000), LB := ((9401769410631311 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((2537874851 : Rat) / 1024000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((81450589 : Rat) / 1024000000), D3 := ((2425624676060267837 : Rat) / 10000000000000000000), D4 := ((161987067923409537 : Rat) / 625000000000000000), LB := ((1172903581802831 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((2411162568638392837 : Rat) / 10000000000000000000), D4 := ((322166372419084699 : Rat) / 1250000000000000000), LB := ((1978417495259177 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((2382238353794642837 : Rat) / 10000000000000000000), D4 := ((318550845563615949 : Rat) / 1250000000000000000), LB := ((3851638573491717 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((2353314138950892837 : Rat) / 10000000000000000000), D4 := ((314935318708147199 : Rat) / 1250000000000000000), LB := ((3575364571894793 : Rat) / 1250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((2324389924107142837 : Rat) / 10000000000000000000), D4 := ((311319791852678449 : Rat) / 1250000000000000000), LB := ((1091336835238807 : Rat) / 250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((2295465709263392837 : Rat) / 10000000000000000000), D4 := ((307704264997209699 : Rat) / 1250000000000000000), LB := ((606789971210181 : Rat) / 100000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((2266541494419642837 : Rat) / 10000000000000000000), D4 := ((304088738141740949 : Rat) / 1250000000000000000), LB := ((19808329585079 : Rat) / 6250000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((2208693064732142837 : Rat) / 10000000000000000000), D4 := ((296857684430803449 : Rat) / 1250000000000000000), LB := ((15455183541176143 : Rat) / 2000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((2150844635044642837 : Rat) / 10000000000000000000), D4 := ((289626630719865949 : Rat) / 1250000000000000000), LB := ((6673375820035493 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((282395577008928449 : Rat) / 1250000000000000000), LB := ((1356652480847001 : Rat) / 125000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1977299345982142837 : Rat) / 10000000000000000000), D4 := ((267933469587053449 : Rat) / 1250000000000000000), LB := ((29821898561414817 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1861602486607142837 : Rat) / 10000000000000000000), D4 := ((253471362165178449 : Rat) / 1250000000000000000), LB := ((1662573121776747 : Rat) / 40000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((224547147321428449 : Rat) / 1250000000000000000), LB := ((2598609051592471 : Rat) / 50000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((12740808660714277899 : Rat) / 80000000000000000000), LB := ((134257149457931 : Rat) / 4000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((23851408553571412961 : Rat) / 160000000000000000000), LB := ((175993746317233 : Rat) / 15625000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((5555299946428567531 : Rat) / 40000000000000000000), LB := ((6044476957556333 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((42812190803571397411 : Rat) / 320000000000000000000), LB := ((5393799328287707 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((1671312784124999999577 : Rat) / 640000000000000000000), D0 := ((1671312784124999999577 : Rat) / 640000000000000000000), D1 := ((508128720124999999577 : Rat) / 640000000000000000000), D2 := ((34234384124999999577 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((20590991017857127287 : Rat) / 160000000000000000000), LB := ((1897032636408641 : Rat) / 250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1671312784124999999577 : Rat) / 640000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((70098977017857141991 : Rat) / 640000000000000000000), D4 := ((80733755303571366311 : Rat) / 640000000000000000000), LB := ((5125278617617357 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((39551773267857111737 : Rat) / 320000000000000000000), LB := ((738280453316309 : Rat) / 250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((77473337767857080637 : Rat) / 640000000000000000000), LB := ((2122941495217301 : Rat) / 2000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((3354037029624999999013 : Rat) / 1280000000000000000000), D0 := ((3354037029624999999013 : Rat) / 1280000000000000000000), D1 := ((1027668901624999999013 : Rat) / 1280000000000000000000), D2 := ((79880229624999999013 : Rat) / 1280000000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((379215644999999689 : Rat) / 3200000000000000000), LB := ((2983666922480699 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3354037029624999999013 : Rat) / 1280000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((128786492660714284123 : Rat) / 1280000000000000000000), D4 := ((150056049232142732763 : Rat) / 1280000000000000000000), LB := ((2238314779276107 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((3357297447160714284687 : Rat) / 1280000000000000000000), D0 := ((3357297447160714284687 : Rat) / 1280000000000000000000), D1 := ((1030929319160714284687 : Rat) / 1280000000000000000000), D2 := ((83140647160714284687 : Rat) / 1280000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((74212920232142794963 : Rat) / 640000000000000000000), LB := ((7800880119932241 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3357297447160714284687 : Rat) / 1280000000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((125526075124999998449 : Rat) / 1280000000000000000000), D4 := ((146795631696428447089 : Rat) / 1280000000000000000000), LB := ((9486551348516503 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((36291355732142826063 : Rat) / 320000000000000000000), LB := ((4032556405854093 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((6722745938160714283559 : Rat) / 2560000000000000000000), D0 := ((6722745938160714283559 : Rat) / 2560000000000000000000), D1 := ((2070009682160714283559 : Rat) / 2560000000000000000000), D2 := ((174432338160714283559 : Rat) / 2560000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((28707042832142832283 : Rat) / 256000000000000000000), LB := ((4055838394321637 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6722745938160714283559 : Rat) / 2560000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((242901106410714282713 : Rat) / 2560000000000000000000), D4 := ((285440219553571179993 : Rat) / 2560000000000000000000), LB := ((13992702845132543 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((6726006355696428569233 : Rat) / 2560000000000000000000), D0 := ((6726006355696428569233 : Rat) / 2560000000000000000000), D1 := ((2073270099696428569233 : Rat) / 2560000000000000000000), D2 := ((177692755696428569233 : Rat) / 2560000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((70952502696428509289 : Rat) / 640000000000000000000), LB := ((596328678427599 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6726006355696428569233 : Rat) / 2560000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((239640688874999997039 : Rat) / 2560000000000000000000), D4 := ((282179802017856894319 : Rat) / 2560000000000000000000), LB := ((10024677906850243 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((6729266773232142854907 : Rat) / 2560000000000000000000), D0 := ((6729266773232142854907 : Rat) / 2560000000000000000000), D1 := ((2076530517232142854907 : Rat) / 2560000000000000000000), D2 := ((180953173232142854907 : Rat) / 2560000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((140274796624999875741 : Rat) / 1280000000000000000000), LB := ((8286782216108679 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6729266773232142854907 : Rat) / 2560000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((47276054267857142273 : Rat) / 512000000000000000000), D4 := ((55783876896428521729 : Rat) / 512000000000000000000), LB := ((104886034737817 : Rat) / 156250000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((6732527190767857140581 : Rat) / 2560000000000000000000), D0 := ((6732527190767857140581 : Rat) / 2560000000000000000000), D1 := ((2079790934767857140581 : Rat) / 2560000000000000000000), D2 := ((184213590767857140581 : Rat) / 2560000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((17330573482142841613 : Rat) / 160000000000000000000), LB := ((5302322270667181 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6732527190767857140581 : Rat) / 2560000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((233119853803571425691 : Rat) / 2560000000000000000000), D4 := ((275658966946428322971 : Rat) / 2560000000000000000000), LB := ((5069443286526143 : Rat) / 12500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1347157521660714285251 : Rat) / 512000000000000000000), D0 := ((1347157521660714285251 : Rat) / 512000000000000000000), D1 := ((416610270460714285251 : Rat) / 512000000000000000000), D2 := ((37494801660714285251 : Rat) / 512000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((137014379089285590067 : Rat) / 1280000000000000000000), LB := ((3715473595913843 : Rat) / 12500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1347157521660714285251 : Rat) / 512000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((229859436267857140017 : Rat) / 2560000000000000000000), D4 := ((272398549410714037297 : Rat) / 2560000000000000000000), LB := ((2566026675512173 : Rat) / 12500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((6739048025839285711929 : Rat) / 2560000000000000000000), D0 := ((6739048025839285711929 : Rat) / 2560000000000000000000), D1 := ((2086311769839285711929 : Rat) / 2560000000000000000000), D2 := ((190734425839285711929 : Rat) / 2560000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((13538417032142844723 : Rat) / 128000000000000000000), LB := ((1621198251455791 : Rat) / 12500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6739048025839285711929 : Rat) / 2560000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((226599018732142854343 : Rat) / 2560000000000000000000), D4 := ((269138131874999751623 : Rat) / 2560000000000000000000), LB := ((440573161232527 : Rat) / 6250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((6742308443374999997603 : Rat) / 2560000000000000000000), D0 := ((6742308443374999997603 : Rat) / 2560000000000000000000), D1 := ((2089572187374999997603 : Rat) / 2560000000000000000000), D2 := ((193994843374999997603 : Rat) / 2560000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((133753961553571304393 : Rat) / 1280000000000000000000), LB := ((138436275416709 : Rat) / 5000000000000000000) }
]

def block240RightChunk000L : Rat := ((88518082589285714389 : Rat) / 50000000000000000000)
def block240RightChunk000R : Rat := ((6742308443374999997603 : Rat) / 2560000000000000000000)

def block240RightChunk000Certificate : Bool :=
  allBoxesValid block240RightChunk000 &&
  coversFromBool block240RightChunk000 block240RightChunk000L block240RightChunk000R

theorem block240RightChunk000Certificate_eq_true :
    block240RightChunk000Certificate = true := by
  native_decide

def block240RightChunk001 : List RatBox := [
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6742308443374999997603 : Rat) / 2560000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((223338601196428568669 : Rat) / 2560000000000000000000), D4 := ((265877714339285465949 : Rat) / 2560000000000000000000), LB := ((13050040927886641 : Rat) / 10000000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((13489507513053571423717 : Rat) / 5120000000000000000000), D0 := ((13489507513053571423717 : Rat) / 5120000000000000000000), D1 := ((4184035001053571423717 : Rat) / 5120000000000000000000), D2 := ((392880313053571423717 : Rat) / 5120000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((33030938196428540389 : Rat) / 320000000000000000000), LB := ((7941379645170499 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((13489507513053571423717 : Rat) / 5120000000000000000000), R := ((6745568860910714283277 : Rat) / 2560000000000000000000), D0 := ((6745568860910714283277 : Rat) / 2560000000000000000000), D1 := ((2092832604910714283277 : Rat) / 2560000000000000000000), D2 := ((197255260910714283277 : Rat) / 2560000000000000000000), D3 := ((441786576089285708827 : Rat) / 5120000000000000000000), D4 := ((526864802374999503387 : Rat) / 5120000000000000000000), LB := ((3968877341735677 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6745568860910714283277 : Rat) / 2560000000000000000000), R := ((13492767930589285709391 : Rat) / 5120000000000000000000), D0 := ((13492767930589285709391 : Rat) / 5120000000000000000000), D1 := ((4187295418589285709391 : Rat) / 5120000000000000000000), D2 := ((396140730589285709391 : Rat) / 5120000000000000000000), D3 := ((44015636732142856599 : Rat) / 512000000000000000000), D4 := ((10504691872142847211 : Rat) / 102400000000000000000), LB := ((7975496855729403 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((13492767930589285709391 : Rat) / 5120000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((438526158553571423153 : Rat) / 5120000000000000000000), D4 := ((523604384839285217713 : Rat) / 5120000000000000000000), LB := ((2013663151060191 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((6748829278446428568951 : Rat) / 2560000000000000000000), D0 := ((6748829278446428568951 : Rat) / 2560000000000000000000), D1 := ((2096093022446428568951 : Rat) / 2560000000000000000000), D2 := ((200515678446428568951 : Rat) / 2560000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((130493544017857018719 : Rat) / 1280000000000000000000), LB := ((20989576389518483 : Rat) / 1000000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6748829278446428568951 : Rat) / 2560000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((216817766124999997321 : Rat) / 2560000000000000000000), D4 := ((259356879267856894601 : Rat) / 2560000000000000000000), LB := ((6061851846439481 : Rat) / 100000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((54016717567857142837 : Rat) / 20480000000000000000), D0 := ((54016717567857142837 : Rat) / 20480000000000000000), D1 := ((16794827519857142837 : Rat) / 20480000000000000000), D2 := ((1630208767857142837 : Rat) / 20480000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((64431667624999937941 : Rat) / 640000000000000000000), LB := ((11685508873482409 : Rat) / 100000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((54016717567857142837 : Rat) / 20480000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((213557348589285711647 : Rat) / 2560000000000000000000), D4 := ((256096461732142608927 : Rat) / 2560000000000000000000), LB := ((18975089049610983 : Rat) / 100000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((6755350113517857140299 : Rat) / 2560000000000000000000), D0 := ((6755350113517857140299 : Rat) / 2560000000000000000000), D1 := ((2102613857517857140299 : Rat) / 2560000000000000000000), D2 := ((207036513517857140299 : Rat) / 2560000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((25446625296428546609 : Rat) / 256000000000000000000), LB := ((6984059165165979 : Rat) / 25000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6755350113517857140299 : Rat) / 2560000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((210296931053571425973 : Rat) / 2560000000000000000000), D4 := ((252836044196428323253 : Rat) / 2560000000000000000000), LB := ((3857508098774609 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((6758610531053571425973 : Rat) / 2560000000000000000000), D0 := ((6758610531053571425973 : Rat) / 2560000000000000000000), D1 := ((2105874275053571425973 : Rat) / 2560000000000000000000), D2 := ((210296931053571425973 : Rat) / 2560000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((1962545589285712347 : Rat) / 20000000000000000000), LB := ((1017964757127121 : Rat) / 2000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6758610531053571425973 : Rat) / 2560000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((207036513517857140299 : Rat) / 2560000000000000000000), D4 := ((249575626660714037579 : Rat) / 2560000000000000000000), LB := ((6491281169060947 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((6761870948589285711647 : Rat) / 2560000000000000000000), D0 := ((6761870948589285711647 : Rat) / 2560000000000000000000), D1 := ((2109134692589285711647 : Rat) / 2560000000000000000000), D2 := ((213557348589285711647 : Rat) / 2560000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((123972708946428447371 : Rat) / 1280000000000000000000), LB := ((8062639807422389 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6761870948589285711647 : Rat) / 2560000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((1630208767857142837 : Rat) / 20480000000000000000), D4 := ((49263041824999950381 : Rat) / 512000000000000000000), LB := ((9804708681984131 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((6765131366124999997321 : Rat) / 2560000000000000000000), D0 := ((6765131366124999997321 : Rat) / 2560000000000000000000), D1 := ((2112395110124999997321 : Rat) / 2560000000000000000000), D2 := ((216817766124999997321 : Rat) / 2560000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((61171250089285652267 : Rat) / 640000000000000000000), LB := ((2343669310961527 : Rat) / 2000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((6765131366124999997321 : Rat) / 2560000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((200515678446428568951 : Rat) / 2560000000000000000000), D4 := ((243054791589285466231 : Rat) / 2560000000000000000000), LB := ((13804462378165239 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((120712291410714161697 : Rat) / 1280000000000000000000), LB := ((4240743195266239 : Rat) / 50000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((5954104132142850943 : Rat) / 64000000000000000000), LB := ((2996443025744533 : Rat) / 5000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((117451873874999876023 : Rat) / 1280000000000000000000), LB := ((11841569897385051 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((57910832553571366593 : Rat) / 640000000000000000000), LB := ((18403869208853951 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((114191456339285590349 : Rat) / 1280000000000000000000), LB := ((6422580045810089 : Rat) / 2500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((14070155946428555939 : Rat) / 160000000000000000000), LB := ((43768826430889973 : Rat) / 100000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((54650415017857080919 : Rat) / 640000000000000000000), LB := ((23024462723592043 : Rat) / 10000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((26510103124999969041 : Rat) / 320000000000000000000), LB := ((2237983189732673 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((10277999496428559049 : Rat) / 128000000000000000000), LB := ((6971123680251323 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((6219973589285706551 : Rat) / 80000000000000000000), LB := ((1059540479736859 : Rat) / 250000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((23249685589285683367 : Rat) / 320000000000000000000), LB := ((11089818629487103 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((2161947682142854053 : Rat) / 32000000000000000000), LB := ((4474652822466063 : Rat) / 500000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((2294882410714281857 : Rat) / 40000000000000000000), LB := ((11803602133703461 : Rat) / 1000000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((2959556053571420877 : Rat) / 80000000000000000000), LB := ((9326423787083193 : Rat) / 100000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((3421965897321428449 : Rat) / 1250000000000000000), D0 := ((3421965897321428449 : Rat) / 1250000000000000000), D1 := ((1150122022321428449 : Rat) / 1250000000000000000), D2 := ((224547147321428449 : Rat) / 1250000000000000000), D3 := ((33233682142856951 : Rat) / 2000000000000000000), D4 := ((33233682142856951 : Rat) / 2000000000000000000), LB := ((4910712856342947 : Rat) / 20000000000000000) },
  { w1 := ((4303341955056173 : Rat) / 5000000000000000), w2 := ((8371569579727087 : Rat) / 100000000000000000), w3 := ((17130433459541447 : Rat) / 500000000000000000), w4 := ((10944094503469147 : Rat) / 50000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((3421965897321428449 : Rat) / 1250000000000000000), L := ((3421965897321428449 : Rat) / 1250000000000000000), R := ((1731598214285714287 : Rat) / 625000000000000000), D0 := ((1731598214285714287 : Rat) / 625000000000000000), D1 := ((595676276785714287 : Rat) / 625000000000000000), D2 := ((132888839285714287 : Rat) / 625000000000000000), D3 := ((99202532142857151 : Rat) / 2000000000000000000), D4 := ((329844250000001 : Rat) / 10000000000000000), LB := ((7983141589167353 : Rat) / 5000000000000000000) }
]

def block240RightChunk001L : Rat := ((6742308443374999997603 : Rat) / 2560000000000000000000)
def block240RightChunk001R : Rat := ((1731598214285714287 : Rat) / 625000000000000000)

def block240RightChunk001Certificate : Bool :=
  allBoxesValid block240RightChunk001 &&
  coversFromBool block240RightChunk001 block240RightChunk001L block240RightChunk001R

theorem block240RightChunk001Certificate_eq_true :
    block240RightChunk001Certificate = true := by
  native_decide

def block240RightChainCertificate : Bool :=
  decide (
    block240RightL = ((88518082589285714389 : Rat) / 50000000000000000000) /\
    ((6742308443374999997603 : Rat) / 2560000000000000000000) = ((6742308443374999997603 : Rat) / 2560000000000000000000) /\
    ((1731598214285714287 : Rat) / 625000000000000000) = block240RightR)

theorem block240RightChainCertificate_eq_true :
    block240RightChainCertificate = true := by
  native_decide

def block240LeftBoxCount : Nat := boxCount block240LeftBoxes
def block240RightBoxCount : Nat := 133

def block240_rational_certificate : Prop :=
    block240LeftCertificate = true /\
    block240RightChainCertificate = true /\
    block240RightChunk000Certificate = true /\
    block240RightChunk001Certificate = true

theorem block240_rational_certificate_proof :
    block240_rational_certificate := by
  exact ⟨block240LeftCertificate_eq_true, block240RightChainCertificate_eq_true, block240RightChunk000Certificate_eq_true, block240RightChunk001Certificate_eq_true⟩

end Block240
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block240

open Set

def block240W1 : Rat := ((4303341955056173 : Rat) / 5000000000000000)
def block240W2 : Rat := ((8371569579727087 : Rat) / 100000000000000000)
def block240W3 : Rat := ((17130433459541447 : Rat) / 500000000000000000)
def block240W4 : Rat := ((10944094503469147 : Rat) / 50000000000000000)
def block240S1 : Rat := ((18174751 : Rat) / 10000000)
def block240S2 : Rat := ((511587 : Rat) / 200000)
def block240S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block240S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block240V (y : ℝ) : ℝ :=
  ratPotential block240W1 block240W2 block240W3 block240W4 block240S1 block240S2 block240S3 block240S4 y

def block240LeftParamsCertificate : Bool :=
  allBoxesSameParams block240LeftBoxes block240W1 block240W2 block240W3 block240W4 block240S1 block240S2 block240S3 block240S4

theorem block240LeftParamsCertificate_eq_true :
    block240LeftParamsCertificate = true := by
  native_decide

theorem block240_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block240LeftL : ℝ) (block240LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block240S1 : ℝ))
    (hy2ne : y ≠ (block240S2 : ℝ))
    (hy3ne : y ≠ (block240S3 : ℝ))
    (hy4ne : y ≠ (block240S4 : ℝ)) :
    0 < block240V y := by
  have hcert := block240LeftCertificate_eq_true
  unfold block240LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block240LeftBoxes) (lo := block240LeftL) (hi := block240LeftR)
    (w1 := block240W1) (w2 := block240W2) (w3 := block240W3) (w4 := block240W4)
    (s1 := block240S1) (s2 := block240S2) (s3 := block240S3) (s4 := block240S4)
    hboxes hcover block240LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block240RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block240RightChunk000 block240W1 block240W2 block240W3 block240W4 block240S1 block240S2 block240S3 block240S4

theorem block240RightChunk000ParamsCertificate_eq_true :
    block240RightChunk000ParamsCertificate = true := by
  native_decide

theorem block240_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block240RightChunk000L : ℝ) (block240RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block240S1 : ℝ))
    (hy2ne : y ≠ (block240S2 : ℝ))
    (hy3ne : y ≠ (block240S3 : ℝ))
    (hy4ne : y ≠ (block240S4 : ℝ)) :
    0 < block240V y := by
  have hcert := block240RightChunk000Certificate_eq_true
  unfold block240RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block240RightChunk000) (lo := block240RightChunk000L) (hi := block240RightChunk000R)
    (w1 := block240W1) (w2 := block240W2) (w3 := block240W3) (w4 := block240W4)
    (s1 := block240S1) (s2 := block240S2) (s3 := block240S3) (s4 := block240S4)
    hboxes hcover block240RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block240RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block240RightChunk001 block240W1 block240W2 block240W3 block240W4 block240S1 block240S2 block240S3 block240S4

theorem block240RightChunk001ParamsCertificate_eq_true :
    block240RightChunk001ParamsCertificate = true := by
  native_decide

theorem block240_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block240RightChunk001L : ℝ) (block240RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block240S1 : ℝ))
    (hy2ne : y ≠ (block240S2 : ℝ))
    (hy3ne : y ≠ (block240S3 : ℝ))
    (hy4ne : y ≠ (block240S4 : ℝ)) :
    0 < block240V y := by
  have hcert := block240RightChunk001Certificate_eq_true
  unfold block240RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block240RightChunk001) (lo := block240RightChunk001L) (hi := block240RightChunk001R)
    (w1 := block240W1) (w2 := block240W2) (w3 := block240W3) (w4 := block240W4)
    (s1 := block240S1) (s2 := block240S2) (s3 := block240S3) (s4 := block240S4)
    hboxes hcover block240RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block240_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block240RightL : ℝ) (block240RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block240S1 : ℝ))
    (hy2ne : y ≠ (block240S2 : ℝ))
    (hy3ne : y ≠ (block240S3 : ℝ))
    (hy4ne : y ≠ (block240S4 : ℝ)) :
    0 < block240V y := by
  by_cases h0 : y ≤ (block240RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block240RightChunk000L : ℝ) (block240RightChunk000R : ℝ) := by
      have hL : (block240RightChunk000L : ℝ) = (block240RightL : ℝ) := by
        norm_num [block240RightChunk000L, block240RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block240_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block240RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block240RightChunk001L : ℝ) = (block240RightChunk000R : ℝ) := by
      norm_num [block240RightChunk001L, block240RightChunk000R]
    have hR : (block240RightChunk001R : ℝ) = (block240RightR : ℝ) := by
      norm_num [block240RightChunk001R, block240RightR]
    have hyc : y ∈ Icc (block240RightChunk001L : ℝ) (block240RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block240_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block240_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block240LeftL : ℝ) (block240LeftR : ℝ) →
    y ≠ 0 → y ≠ (block240S1 : ℝ) → y ≠ (block240S2 : ℝ) →
    y ≠ (block240S3 : ℝ) → y ≠ (block240S4 : ℝ) → 0 < block240V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block240RightL : ℝ) (block240RightR : ℝ) →
    y ≠ 0 → y ≠ (block240S1 : ℝ) → y ≠ (block240S2 : ℝ) →
    y ≠ (block240S3 : ℝ) → y ≠ (block240S4 : ℝ) → 0 < block240V y)

theorem block240_reallog_certificate_proof :
    block240_reallog_certificate := by
  exact ⟨block240_left_V_pos, block240_right_V_pos⟩

end Block240
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block240.block240V
#check Erdos1038Lean.M1817475.Block240.block240_left_V_pos
#check Erdos1038Lean.M1817475.Block240.block240_right_V_pos
#check Erdos1038Lean.M1817475.Block240.block240_reallog_certificate_proof
