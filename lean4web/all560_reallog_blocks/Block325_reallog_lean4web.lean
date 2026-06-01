/-
Self-contained Lean4Web paste file.
Block 325 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block325

def block325LeftL : Rat := ((18843622767857142927 : Rat) / 25000000000000000000)
def block325LeftR : Rat := ((1507880803571428577 : Rat) / 2000000000000000000)
def block325RightL : Rat := ((43843622767857142927 : Rat) / 25000000000000000000)
def block325RightR : Rat := ((5507880803571428577 : Rat) / 2000000000000000000)

def block325LeftBoxes : List RatBox := [
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18843622767857142927 : Rat) / 25000000000000000000), R := ((1507880803571428577 : Rat) / 2000000000000000000), D0 := ((1507880803571428577 : Rat) / 2000000000000000000), D1 := ((26593254732142857073 : Rat) / 25000000000000000000), D2 := ((45104752232142857073 : Rat) / 25000000000000000000), D3 := ((48031764107142857073 : Rat) / 25000000000000000000), D4 := ((6308203805803571109 : Rat) / 3125000000000000000), LB := ((13169211643233647 : Rat) / 2000000000000000000) }
]

def block325LeftCertificate : Bool :=
  allBoxesValid block325LeftBoxes &&
  coversFromBool block325LeftBoxes block325LeftL block325LeftR

theorem block325LeftCertificate_eq_true :
    block325LeftCertificate = true := by
  native_decide

def block325RightChunk000 : List RatBox := [
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43843622767857142927 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1593254732142857073 : Rat) / 25000000000000000000), D2 := ((20104752232142857073 : Rat) / 25000000000000000000), D3 := ((23031764107142857073 : Rat) / 25000000000000000000), D4 := ((3183203805803571109 : Rat) / 3125000000000000000), LB := ((516387543831823 : Rat) / 250000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((1334310350142757 : Rat) / 6250000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((19492417 : Rat) / 40000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((688164050303037 : Rat) / 5000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((6316047 : Rat) / 16000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((4649156573412813 : Rat) / 50000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((55755871 : Rat) / 160000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((5897789323364211 : Rat) / 200000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((6043909 : Rat) / 20000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((26257034640111337 : Rat) / 1000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((17859589 : Rat) / 64000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((188223524173311 : Rat) / 40000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((40946673 : Rat) / 160000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((4912752570512907 : Rat) / 500000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((156382093 : Rat) / 640000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((2321669060785153 : Rat) / 1000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((74488747 : Rat) / 320000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((716235803943463 : Rat) / 100000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((290550389 : Rat) / 1280000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((8845008896781803 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((28314579 : Rat) / 128000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((254092614730507 : Rat) / 125000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((275741191 : Rat) / 1280000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((6441727908743089 : Rat) / 500000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((16771037 : Rat) / 80000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((3815486964602849 : Rat) / 1000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((105853717 : Rat) / 512000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((156873158080309 : Rat) / 50000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((260931993 : Rat) / 1280000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((5136647489371149 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((514459387 : Rat) / 2560000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((1320138601353521 : Rat) / 625000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((126763697 : Rat) / 640000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((8868500358714809 : Rat) / 5000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((499650189 : Rat) / 2560000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((194717995806417 : Rat) / 125000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((49224559 : Rat) / 256000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((2939686946614839 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((484840991 : Rat) / 2560000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((1516067577766067 : Rat) / 1000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((59679549 : Rat) / 320000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((4257883172121349 : Rat) / 2500000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((470031793 : Rat) / 2560000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((101930657997297 : Rat) / 50000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((231313597 : Rat) / 1280000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((5061733212407049 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((91044519 : Rat) / 512000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((7973502098245419 : Rat) / 2500000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((111954499 : Rat) / 640000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((8049941730023491 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((440413397 : Rat) / 2560000000), D4 := ((6734778419363836799 : Rat) / 25000000000000000000), LB := ((2524925003517503 : Rat) / 500000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((216504399 : Rat) / 1280000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((11164409910424389 : Rat) / 10000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1045499 : Rat) / 6400000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((4287328945622199 : Rat) / 1000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((201695201 : Rat) / 1280000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((4254031454559881 : Rat) / 500000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((97145301 : Rat) / 640000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((990116211446769 : Rat) / 250000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((44870351 : Rat) / 320000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((2106922968681979 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((823222419 : Rat) / 320000000), D0 := ((823222419 : Rat) / 320000000), D1 := ((241630387 : Rat) / 320000000), D2 := ((4683219 : Rat) / 320000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((469794730976137 : Rat) / 12500000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((823222419 : Rat) / 320000000), R := ((413952819 : Rat) / 160000000), D0 := ((413952819 : Rat) / 160000000), D1 := ((123156803 : Rat) / 160000000), D2 := ((4683219 : Rat) / 160000000), D3 := ((32782533 : Rat) / 320000000), D4 := ((4995001729910711799 : Rat) / 25000000000000000000), LB := ((310000655805393 : Rat) / 31250000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((413952819 : Rat) / 160000000), R := ((332098899 : Rat) / 128000000), D0 := ((332098899 : Rat) / 128000000), D1 := ((497310431 : Rat) / 640000000), D2 := ((4683219 : Rat) / 128000000), D3 := ((14049657 : Rat) / 160000000), D4 := ((4629125245535711799 : Rat) / 25000000000000000000), LB := ((1999674706287219 : Rat) / 100000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((332098899 : Rat) / 128000000), R := ((832588857 : Rat) / 320000000), D0 := ((832588857 : Rat) / 320000000), D1 := ((10039873 : Rat) / 12800000), D2 := ((14049657 : Rat) / 320000000), D3 := ((51515409 : Rat) / 640000000), D4 := ((4446187003348211799 : Rat) / 25000000000000000000), LB := ((17609905730059883 : Rat) / 1000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((832588857 : Rat) / 320000000), R := ((209318019 : Rat) / 80000000), D0 := ((209318019 : Rat) / 80000000), D1 := ((63920011 : Rat) / 80000000), D2 := ((4683219 : Rat) / 80000000), D3 := ((4683219 : Rat) / 64000000), D4 := ((4263248761160711799 : Rat) / 25000000000000000000), LB := ((4773313686200209 : Rat) / 25000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((209318019 : Rat) / 80000000), R := ((168391059 : Rat) / 64000000), D0 := ((168391059 : Rat) / 64000000), D1 := ((260363263 : Rat) / 320000000), D2 := ((4683219 : Rat) / 64000000), D3 := ((4683219 : Rat) / 80000000), D4 := ((3897372276785711799 : Rat) / 25000000000000000000), LB := ((2718048121729419 : Rat) / 250000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((168391059 : Rat) / 64000000), R := ((423319257 : Rat) / 160000000), D0 := ((423319257 : Rat) / 160000000), D1 := ((132523241 : Rat) / 160000000), D2 := ((14049657 : Rat) / 160000000), D3 := ((14049657 : Rat) / 320000000), D4 := ((3531495792410711799 : Rat) / 25000000000000000000), LB := ((3420477254931903 : Rat) / 100000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((423319257 : Rat) / 160000000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 160000000), D4 := ((3165619308035711799 : Rat) / 25000000000000000000), LB := ((39372120200089 : Rat) / 800000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((107000619 : Rat) / 40000000), R := ((21557973653571428577 : Rat) / 8000000000000000000), D0 := ((21557973653571428577 : Rat) / 8000000000000000000), D1 := ((7018172853571428577 : Rat) / 8000000000000000000), D2 := ((1094493653571428577 : Rat) / 8000000000000000000), D3 := ((157849853571428577 : Rat) / 8000000000000000000), D4 := ((2433866339285711799 : Rat) / 25000000000000000000), LB := ((2098289027566873 : Rat) / 20000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21557973653571428577 : Rat) / 8000000000000000000), R := ((10857911753571428577 : Rat) / 4000000000000000000), D0 := ((10857911753571428577 : Rat) / 4000000000000000000), D1 := ((3588011353571428577 : Rat) / 4000000000000000000), D2 := ((626171753571428577 : Rat) / 4000000000000000000), D3 := ((157849853571428577 : Rat) / 4000000000000000000), D4 := ((15524684374999979967 : Rat) / 200000000000000000000), LB := ((4253990053724399 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((10857911753571428577 : Rat) / 4000000000000000000), R := ((87021143882142857193 : Rat) / 32000000000000000000), D0 := ((87021143882142857193 : Rat) / 32000000000000000000), D1 := ((28861940682142857193 : Rat) / 32000000000000000000), D2 := ((5167223882142857193 : Rat) / 32000000000000000000), D3 := ((1420648682142857193 : Rat) / 32000000000000000000), D4 := ((5789219017857132771 : Rat) / 100000000000000000000), LB := ((4221820210476443 : Rat) / 250000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87021143882142857193 : Rat) / 32000000000000000000), R := ((8717899373571428577 : Rat) / 3200000000000000000), D0 := ((8717899373571428577 : Rat) / 3200000000000000000), D1 := ((2901979053571428577 : Rat) / 3200000000000000000), D2 := ((532507373571428577 : Rat) / 3200000000000000000), D3 := ((157849853571428577 : Rat) / 3200000000000000000), D4 := ((42367505803571347743 : Rat) / 800000000000000000000), LB := ((2793338722903327 : Rat) / 500000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8717899373571428577 : Rat) / 3200000000000000000), R := ((174515837325000000117 : Rat) / 64000000000000000000), D0 := ((174515837325000000117 : Rat) / 64000000000000000000), D1 := ((58197430925000000117 : Rat) / 64000000000000000000), D2 := ((10807997325000000117 : Rat) / 64000000000000000000), D3 := ((3314846925000000117 : Rat) / 64000000000000000000), D4 := ((19210629732142816659 : Rat) / 400000000000000000000), LB := ((15587390456765271 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((174515837325000000117 : Rat) / 64000000000000000000), R := ((87336843589285714347 : Rat) / 32000000000000000000), D0 := ((87336843589285714347 : Rat) / 32000000000000000000), D1 := ((29177640389285714347 : Rat) / 32000000000000000000), D2 := ((5482923589285714347 : Rat) / 32000000000000000000), D3 := ((1736348389285714347 : Rat) / 32000000000000000000), D4 := ((72896272589285552211 : Rat) / 1600000000000000000000), LB := ((2093098786176001 : Rat) / 500000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87336843589285714347 : Rat) / 32000000000000000000), R := ((174831537032142857271 : Rat) / 64000000000000000000), D0 := ((174831537032142857271 : Rat) / 64000000000000000000), D1 := ((58513130632142857271 : Rat) / 64000000000000000000), D2 := ((11123697032142857271 : Rat) / 64000000000000000000), D3 := ((3630546632142857271 : Rat) / 64000000000000000000), D4 := ((34475013124999918893 : Rat) / 800000000000000000000), LB := ((2584155884576833 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((174831537032142857271 : Rat) / 64000000000000000000), R := ((349820923917857143119 : Rat) / 128000000000000000000), D0 := ((349820923917857143119 : Rat) / 128000000000000000000), D1 := ((117184111117857143119 : Rat) / 128000000000000000000), D2 := ((22405243917857143119 : Rat) / 128000000000000000000), D3 := ((7418943117857143119 : Rat) / 128000000000000000000), D4 := ((65003779910714123361 : Rat) / 1600000000000000000000), LB := ((1051247008687639 : Rat) / 250000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((349820923917857143119 : Rat) / 128000000000000000000), R := ((21873673360714285731 : Rat) / 8000000000000000000), D0 := ((21873673360714285731 : Rat) / 8000000000000000000), D1 := ((7333872560714285731 : Rat) / 8000000000000000000), D2 := ((1410193360714285731 : Rat) / 8000000000000000000), D3 := ((473549560714285731 : Rat) / 8000000000000000000), D4 := ((126061313482142532297 : Rat) / 3200000000000000000000), LB := ((6690484069986291 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21873673360714285731 : Rat) / 8000000000000000000), R := ((350136623625000000273 : Rat) / 128000000000000000000), D0 := ((350136623625000000273 : Rat) / 128000000000000000000), D1 := ((117499810825000000273 : Rat) / 128000000000000000000), D2 := ((22720943625000000273 : Rat) / 128000000000000000000), D3 := ((7734642825000000273 : Rat) / 128000000000000000000), D4 := ((7632191696428551117 : Rat) / 200000000000000000000), LB := ((537115027400803 : Rat) / 200000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((350136623625000000273 : Rat) / 128000000000000000000), R := ((7005889469571428577 : Rat) / 2560000000000000000), D0 := ((7005889469571428577 : Rat) / 2560000000000000000), D1 := ((2353153213571428577 : Rat) / 2560000000000000000), D2 := ((457575869571428577 : Rat) / 2560000000000000000), D3 := ((157849853571428577 : Rat) / 2560000000000000000), D4 := ((118168820803571103447 : Rat) / 3200000000000000000000), LB := ((446450713679003 : Rat) / 200000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((7005889469571428577 : Rat) / 2560000000000000000), R := ((350452323332142857427 : Rat) / 128000000000000000000), D0 := ((350452323332142857427 : Rat) / 128000000000000000000), D1 := ((117815510532142857427 : Rat) / 128000000000000000000), D2 := ((23036643332142857427 : Rat) / 128000000000000000000), D3 := ((8050342532142857427 : Rat) / 128000000000000000000), D4 := ((57111287232142694511 : Rat) / 1600000000000000000000), LB := ((2490737598878287 : Rat) / 1250000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((350452323332142857427 : Rat) / 128000000000000000000), R := ((87652543296428571501 : Rat) / 32000000000000000000), D0 := ((87652543296428571501 : Rat) / 32000000000000000000), D1 := ((29493340096428571501 : Rat) / 32000000000000000000), D2 := ((5798623296428571501 : Rat) / 32000000000000000000), D3 := ((2052048096428571501 : Rat) / 32000000000000000000), D4 := ((110276328124999674597 : Rat) / 3200000000000000000000), LB := ((9875293100409521 : Rat) / 5000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87652543296428571501 : Rat) / 32000000000000000000), R := ((350768023039285714581 : Rat) / 128000000000000000000), D0 := ((350768023039285714581 : Rat) / 128000000000000000000), D1 := ((118131210239285714581 : Rat) / 128000000000000000000), D2 := ((23352343039285714581 : Rat) / 128000000000000000000), D3 := ((8366042239285714581 : Rat) / 128000000000000000000), D4 := ((26582520446428490043 : Rat) / 800000000000000000000), LB := ((2736791418300813 : Rat) / 1250000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((350768023039285714581 : Rat) / 128000000000000000000), R := ((175462936446428571579 : Rat) / 64000000000000000000), D0 := ((175462936446428571579 : Rat) / 64000000000000000000), D1 := ((59144530046428571579 : Rat) / 64000000000000000000), D2 := ((11755096446428571579 : Rat) / 64000000000000000000), D3 := ((4261946046428571579 : Rat) / 64000000000000000000), D4 := ((102383835446428245747 : Rat) / 3200000000000000000000), LB := ((330869445489039 : Rat) / 125000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((175462936446428571579 : Rat) / 64000000000000000000), R := ((70216744549285714347 : Rat) / 25600000000000000000), D0 := ((70216744549285714347 : Rat) / 25600000000000000000), D1 := ((23689381989285714347 : Rat) / 25600000000000000000), D2 := ((4733608549285714347 : Rat) / 25600000000000000000), D3 := ((1736348389285714347 : Rat) / 25600000000000000000), D4 := ((49218794553571265661 : Rat) / 1600000000000000000000), LB := ((420067452774453 : Rat) / 125000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((70216744549285714347 : Rat) / 25600000000000000000), R := ((43905196575000000039 : Rat) / 16000000000000000000), D0 := ((43905196575000000039 : Rat) / 16000000000000000000), D1 := ((14825594975000000039 : Rat) / 16000000000000000000), D2 := ((2978236575000000039 : Rat) / 16000000000000000000), D3 := ((1104948975000000039 : Rat) / 16000000000000000000), D4 := ((94491342767856816897 : Rat) / 3200000000000000000000), LB := ((8690037641059023 : Rat) / 2000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43905196575000000039 : Rat) / 16000000000000000000), R := ((175778636153571428733 : Rat) / 64000000000000000000), D0 := ((175778636153571428733 : Rat) / 64000000000000000000), D1 := ((59460229753571428733 : Rat) / 64000000000000000000), D2 := ((12070796153571428733 : Rat) / 64000000000000000000), D3 := ((4577645753571428733 : Rat) / 64000000000000000000), D4 := ((11318137053571387809 : Rat) / 400000000000000000000), LB := ((277076436777407 : Rat) / 250000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((175778636153571428733 : Rat) / 64000000000000000000), R := ((17593648600714285731 : Rat) / 6400000000000000000), D0 := ((17593648600714285731 : Rat) / 6400000000000000000), D1 := ((5961807960714285731 : Rat) / 6400000000000000000), D2 := ((1222864600714285731 : Rat) / 6400000000000000000), D3 := ((473549560714285731 : Rat) / 6400000000000000000), D4 := ((41326301874999836811 : Rat) / 1600000000000000000000), LB := ((4689771491052597 : Rat) / 1000000000000000000) },
  { w1 := ((4801301767797357 : Rat) / 5000000000000000), w2 := ((23266081636169257 : Rat) / 500000000000000000), w3 := ((14255829249693697 : Rat) / 100000000000000000), w4 := ((1366466809614847 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((17593648600714285731 : Rat) / 6400000000000000000), R := ((5507880803571428577 : Rat) / 2000000000000000000), D0 := ((5507880803571428577 : Rat) / 2000000000000000000), D1 := ((1872930603571428577 : Rat) / 2000000000000000000), D2 := ((392010803571428577 : Rat) / 2000000000000000000), D3 := ((157849853571428577 : Rat) / 2000000000000000000), D4 := ((18690027767857061193 : Rat) / 800000000000000000000), LB := ((2306052187154739 : Rat) / 2000000000000000000) }
]

def block325RightChunk000L : Rat := ((43843622767857142927 : Rat) / 25000000000000000000)
def block325RightChunk000R : Rat := ((5507880803571428577 : Rat) / 2000000000000000000)

def block325RightChunk000Certificate : Bool :=
  allBoxesValid block325RightChunk000 &&
  coversFromBool block325RightChunk000 block325RightChunk000L block325RightChunk000R

theorem block325RightChunk000Certificate_eq_true :
    block325RightChunk000Certificate = true := by
  native_decide

def block325RightChainCertificate : Bool :=
  decide (
    block325RightL = ((43843622767857142927 : Rat) / 25000000000000000000) /\
    ((5507880803571428577 : Rat) / 2000000000000000000) = block325RightR)

theorem block325RightChainCertificate_eq_true :
    block325RightChainCertificate = true := by
  native_decide

def block325LeftBoxCount : Nat := boxCount block325LeftBoxes
def block325RightBoxCount : Nat := 60

def block325_rational_certificate : Prop :=
    block325LeftCertificate = true /\
    block325RightChainCertificate = true /\
    block325RightChunk000Certificate = true

theorem block325_rational_certificate_proof :
    block325_rational_certificate := by
  exact ⟨block325LeftCertificate_eq_true, block325RightChainCertificate_eq_true, block325RightChunk000Certificate_eq_true⟩

end Block325
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block325

open Set

def block325W1 : Rat := ((4801301767797357 : Rat) / 5000000000000000)
def block325W2 : Rat := ((23266081636169257 : Rat) / 500000000000000000)
def block325W3 : Rat := ((14255829249693697 : Rat) / 100000000000000000)
def block325W4 : Rat := ((1366466809614847 : Rat) / 10000000000000000)
def block325S1 : Rat := ((18174751 : Rat) / 10000000)
def block325S2 : Rat := ((511587 : Rat) / 200000)
def block325S3 : Rat := ((107000619 : Rat) / 40000000)
def block325S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block325V (y : ℝ) : ℝ :=
  ratPotential block325W1 block325W2 block325W3 block325W4 block325S1 block325S2 block325S3 block325S4 y

def block325LeftParamsCertificate : Bool :=
  allBoxesSameParams block325LeftBoxes block325W1 block325W2 block325W3 block325W4 block325S1 block325S2 block325S3 block325S4

theorem block325LeftParamsCertificate_eq_true :
    block325LeftParamsCertificate = true := by
  native_decide

theorem block325_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block325LeftL : ℝ) (block325LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block325S1 : ℝ))
    (hy2ne : y ≠ (block325S2 : ℝ))
    (hy3ne : y ≠ (block325S3 : ℝ))
    (hy4ne : y ≠ (block325S4 : ℝ)) :
    0 < block325V y := by
  have hcert := block325LeftCertificate_eq_true
  unfold block325LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block325LeftBoxes) (lo := block325LeftL) (hi := block325LeftR)
    (w1 := block325W1) (w2 := block325W2) (w3 := block325W3) (w4 := block325W4)
    (s1 := block325S1) (s2 := block325S2) (s3 := block325S3) (s4 := block325S4)
    hboxes hcover block325LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block325RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block325RightChunk000 block325W1 block325W2 block325W3 block325W4 block325S1 block325S2 block325S3 block325S4

theorem block325RightChunk000ParamsCertificate_eq_true :
    block325RightChunk000ParamsCertificate = true := by
  native_decide

theorem block325_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block325RightChunk000L : ℝ) (block325RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block325S1 : ℝ))
    (hy2ne : y ≠ (block325S2 : ℝ))
    (hy3ne : y ≠ (block325S3 : ℝ))
    (hy4ne : y ≠ (block325S4 : ℝ)) :
    0 < block325V y := by
  have hcert := block325RightChunk000Certificate_eq_true
  unfold block325RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block325RightChunk000) (lo := block325RightChunk000L) (hi := block325RightChunk000R)
    (w1 := block325W1) (w2 := block325W2) (w3 := block325W3) (w4 := block325W4)
    (s1 := block325S1) (s2 := block325S2) (s3 := block325S3) (s4 := block325S4)
    hboxes hcover block325RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block325_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block325RightL : ℝ) (block325RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block325S1 : ℝ))
    (hy2ne : y ≠ (block325S2 : ℝ))
    (hy3ne : y ≠ (block325S3 : ℝ))
    (hy4ne : y ≠ (block325S4 : ℝ)) :
    0 < block325V y := by
  have hL : (block325RightChunk000L : ℝ) = (block325RightL : ℝ) := by
    norm_num [block325RightChunk000L, block325RightL]
  have hR : (block325RightChunk000R : ℝ) = (block325RightR : ℝ) := by
    norm_num [block325RightChunk000R, block325RightR]
  have hyc : y ∈ Icc (block325RightChunk000L : ℝ) (block325RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block325_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block325_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block325LeftL : ℝ) (block325LeftR : ℝ) →
    y ≠ 0 → y ≠ (block325S1 : ℝ) → y ≠ (block325S2 : ℝ) →
    y ≠ (block325S3 : ℝ) → y ≠ (block325S4 : ℝ) → 0 < block325V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block325RightL : ℝ) (block325RightR : ℝ) →
    y ≠ 0 → y ≠ (block325S1 : ℝ) → y ≠ (block325S2 : ℝ) →
    y ≠ (block325S3 : ℝ) → y ≠ (block325S4 : ℝ) → 0 < block325V y)

theorem block325_reallog_certificate_proof :
    block325_reallog_certificate := by
  exact ⟨block325_left_V_pos, block325_right_V_pos⟩

end Block325
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block325.block325V
#check Erdos1038Lean.M1817475.Block325.block325_left_V_pos
#check Erdos1038Lean.M1817475.Block325.block325_right_V_pos
#check Erdos1038Lean.M1817475.Block325.block325_reallog_certificate_proof
