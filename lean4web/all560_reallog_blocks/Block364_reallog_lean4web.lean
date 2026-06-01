/-
Self-contained Lean4Web paste file.
Block 364 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block364

def block364LeftL : Rat := ((7461207589285714317 : Rat) / 10000000000000000000)
def block364LeftR : Rat := ((9328953125000000039 : Rat) / 12500000000000000000)
def block364RightL : Rat := ((17461207589285714317 : Rat) / 10000000000000000000)
def block364RightR : Rat := ((34328953125000000039 : Rat) / 12500000000000000000)

def block364LeftBoxes : List RatBox := [
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((7461207589285714317 : Rat) / 10000000000000000000), R := ((9328953125000000039 : Rat) / 12500000000000000000), D0 := ((9328953125000000039 : Rat) / 12500000000000000000), D1 := ((10713543410714285683 : Rat) / 10000000000000000000), D2 := ((18118142410714285683 : Rat) / 10000000000000000000), D3 := ((9571164428571428559 : Rat) / 5000000000000000000), D4 := ((101312468482142852013 : Rat) / 50000000000000000000), LB := ((12353194137847967 : Rat) / 2000000000000000000) }
]

def block364LeftCertificate : Bool :=
  allBoxesValid block364LeftBoxes &&
  coversFromBool block364LeftBoxes block364LeftL block364LeftR

theorem block364LeftCertificate_eq_true :
    block364LeftCertificate = true := by
  native_decide

def block364RightChunk000 : List RatBox := [
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((17461207589285714317 : Rat) / 10000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((713543410714285683 : Rat) / 10000000000000000000), D2 := ((8118142410714285683 : Rat) / 10000000000000000000), D3 := ((4571164428571428559 : Rat) / 5000000000000000000), D4 := ((51312468482142852013 : Rat) / 50000000000000000000), LB := ((4357300197026271 : Rat) / 2500000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((1685757089285714287 : Rat) / 2000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((3431377702235177 : Rat) / 25000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((945297189285714287 : Rat) / 2000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((8934349027965607 : Rat) / 100000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((760182214285714287 : Rat) / 2000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((11289962949383489 : Rat) / 200000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((667624726785714287 : Rat) / 2000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((5057347807981033 : Rat) / 2000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((575067239285714287 : Rat) / 2000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((2802560637713891 : Rat) / 500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((528788495535714287 : Rat) / 2000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((1356082098423729 : Rat) / 125000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((505649123660714287 : Rat) / 2000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((7378721697447077 : Rat) / 2000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((3103851023 : Rat) / 1280000000), D0 := ((3103851023 : Rat) / 1280000000), D1 := ((155496579 : Rat) / 256000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((482509751785714287 : Rat) / 2000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((4166668717039343 : Rat) / 500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3103851023 : Rat) / 1280000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((170305777 : Rat) / 1280000000), D3 := ((470940065848214287 : Rat) / 2000000000000000000), D4 := ((8687162921316961799 : Rat) / 25000000000000000000), LB := ((5646640696926497 : Rat) / 1000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((459370379910714287 : Rat) / 2000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((63756106880343 : Rat) / 19531250000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((447800693973214287 : Rat) / 2000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((46844936832447 : Rat) / 39062500000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((6259534239 : Rat) / 2560000000), D0 := ((6259534239 : Rat) / 2560000000), D1 := ((1606797983 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((436231008035714287 : Rat) / 2000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((37513191830159 : Rat) / 8000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6259534239 : Rat) / 2560000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((288779361 : Rat) / 2560000000), D3 := ((430446165066964287 : Rat) / 2000000000000000000), D4 := ((8180989161551336799 : Rat) / 25000000000000000000), LB := ((3932151774101861 : Rat) / 1000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((424661322098214287 : Rat) / 2000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((32646693143971173 : Rat) / 10000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((418876479129464287 : Rat) / 2000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((672285446533881 : Rat) / 250000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((413091636160714287 : Rat) / 2000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((4416369921268759 : Rat) / 2000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((407306793191964287 : Rat) / 2000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((9123037492754227 : Rat) / 5000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((401521950223214287 : Rat) / 2000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((1541430619961509 : Rat) / 1000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((395737107254464287 : Rat) / 2000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((6809552754328957 : Rat) / 5000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((389952264285714287 : Rat) / 2000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((6447821220818273 : Rat) / 5000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((384167421316964287 : Rat) / 2000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((265639796479733 : Rat) / 200000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((378382578348214287 : Rat) / 2000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((3704866518128569 : Rat) / 2500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((372597735379464287 : Rat) / 2000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((8776516478252311 : Rat) / 5000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((366812892410714287 : Rat) / 2000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((10765880130312877 : Rat) / 5000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((361028049441964287 : Rat) / 2000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((8377928647241 : Rat) / 3125000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((355243206473214287 : Rat) / 2000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((3344488996069539 : Rat) / 1000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((349458363504464287 : Rat) / 2000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((1037585111868057 : Rat) / 250000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((343673520535714287 : Rat) / 2000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((2267048649377823 : Rat) / 12500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((332103834598214287 : Rat) / 2000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((3260335155244147 : Rat) / 1250000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((320534148660714287 : Rat) / 2000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((717770871175933 : Rat) / 125000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((308964462723214287 : Rat) / 2000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((1936208432577663 : Rat) / 200000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((297394776785714287 : Rat) / 2000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((1256221605632199 : Rat) / 250000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((274255404910714287 : Rat) / 2000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1848073849433901 : Rat) / 100000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((251116033035714287 : Rat) / 2000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((20773844417117437 : Rat) / 1000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((20668317289285714287 : Rat) / 8000000000000000000), D0 := ((20668317289285714287 : Rat) / 8000000000000000000), D1 := ((6128516489285714287 : Rat) / 8000000000000000000), D2 := ((204837289285714287 : Rat) / 8000000000000000000), D3 := ((204837289285714287 : Rat) / 2000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((21606062321285063 : Rat) / 1000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((20668317289285714287 : Rat) / 8000000000000000000), R := ((10436577289285714287 : Rat) / 4000000000000000000), D0 := ((10436577289285714287 : Rat) / 4000000000000000000), D1 := ((3166676889285714287 : Rat) / 4000000000000000000), D2 := ((204837289285714287 : Rat) / 4000000000000000000), D3 := ((614511867857142861 : Rat) / 8000000000000000000), D4 := ((37766093482142837217 : Rat) / 200000000000000000000), LB := ((5916175643694871 : Rat) / 500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((10436577289285714287 : Rat) / 4000000000000000000), R := ((21077991867857142861 : Rat) / 8000000000000000000), D0 := ((21077991867857142861 : Rat) / 8000000000000000000), D1 := ((6538191067857142861 : Rat) / 8000000000000000000), D2 := ((614511867857142861 : Rat) / 8000000000000000000), D3 := ((204837289285714287 : Rat) / 4000000000000000000), D4 := ((16322580624999990021 : Rat) / 100000000000000000000), LB := ((745818280329833 : Rat) / 20000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((21077991867857142861 : Rat) / 8000000000000000000), R := ((5320707289285714287 : Rat) / 2000000000000000000), D0 := ((5320707289285714287 : Rat) / 2000000000000000000), D1 := ((1685757089285714287 : Rat) / 2000000000000000000), D2 := ((204837289285714287 : Rat) / 2000000000000000000), D3 := ((204837289285714287 : Rat) / 8000000000000000000), D4 := ((27524229017857122867 : Rat) / 200000000000000000000), LB := ((5839371673849317 : Rat) / 50000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((5320707289285714287 : Rat) / 2000000000000000000), R := ((536368859196428571681 : Rat) / 200000000000000000000), D0 := ((536368859196428571681 : Rat) / 200000000000000000000), D1 := ((172873839196428571681 : Rat) / 200000000000000000000), D2 := ((24781859196428571681 : Rat) / 200000000000000000000), D3 := ((4298130267857142981 : Rat) / 200000000000000000000), D4 := ((5600824196428566423 : Rat) / 50000000000000000000), LB := ((13309376484346497 : Rat) / 100000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((536368859196428571681 : Rat) / 200000000000000000000), R := ((270333494732142857331 : Rat) / 100000000000000000000), D0 := ((270333494732142857331 : Rat) / 100000000000000000000), D1 := ((88585984732142857331 : Rat) / 100000000000000000000), D2 := ((14539994732142857331 : Rat) / 100000000000000000000), D3 := ((4298130267857142981 : Rat) / 100000000000000000000), D4 := ((18105166517857122711 : Rat) / 200000000000000000000), LB := ((19515204036010203 : Rat) / 1000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270333494732142857331 : Rat) / 100000000000000000000), R := ((217126421839285714461 : Rat) / 80000000000000000000), D0 := ((217126421839285714461 : Rat) / 80000000000000000000), D1 := ((71728413839285714461 : Rat) / 80000000000000000000), D2 := ((12491621839285714461 : Rat) / 80000000000000000000), D3 := ((4298130267857142981 : Rat) / 80000000000000000000), D4 := ((1380703624999997973 : Rat) / 20000000000000000000), LB := ((645386065422783 : Rat) / 125000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((217126421839285714461 : Rat) / 80000000000000000000), R := ((2175562348660714287591 : Rat) / 800000000000000000000), D0 := ((2175562348660714287591 : Rat) / 800000000000000000000), D1 := ((721582268660714287591 : Rat) / 800000000000000000000), D2 := ((129214348660714287591 : Rat) / 800000000000000000000), D3 := ((47279432946428572791 : Rat) / 800000000000000000000), D4 := ((23315942232142816479 : Rat) / 400000000000000000000), LB := ((530640153125983 : Rat) / 100000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2175562348660714287591 : Rat) / 800000000000000000000), R := ((4355422827589285718163 : Rat) / 1600000000000000000000), D0 := ((4355422827589285718163 : Rat) / 1600000000000000000000), D1 := ((1447462667589285718163 : Rat) / 1600000000000000000000), D2 := ((262726827589285718163 : Rat) / 1600000000000000000000), D3 := ((98856996160714288563 : Rat) / 1600000000000000000000), D4 := ((42333754196428489977 : Rat) / 800000000000000000000), LB := ((3793714160902101 : Rat) / 500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4355422827589285718163 : Rat) / 1600000000000000000000), R := ((544965119732142857643 : Rat) / 200000000000000000000), D0 := ((544965119732142857643 : Rat) / 200000000000000000000), D1 := ((181470099732142857643 : Rat) / 200000000000000000000), D2 := ((33378119732142857643 : Rat) / 200000000000000000000), D3 := ((12894390803571428943 : Rat) / 200000000000000000000), D4 := ((80369378124999836973 : Rat) / 1600000000000000000000), LB := ((992001702547221 : Rat) / 250000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((544965119732142857643 : Rat) / 200000000000000000000), R := ((34912152705000000033 : Rat) / 12800000000000000000), D0 := ((34912152705000000033 : Rat) / 12800000000000000000), D1 := ((11648471425000000033 : Rat) / 12800000000000000000), D2 := ((2170584705000000033 : Rat) / 12800000000000000000), D3 := ((4298130267857142981 : Rat) / 64000000000000000000), D4 := ((9508905982142836749 : Rat) / 200000000000000000000), LB := ((2586047735958913 : Rat) / 2500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((34912152705000000033 : Rat) / 12800000000000000000), R := ((8732336306517857151231 : Rat) / 3200000000000000000000), D0 := ((8732336306517857151231 : Rat) / 3200000000000000000000), D1 := ((2916415986517857151231 : Rat) / 3200000000000000000000), D2 := ((546944306517857151231 : Rat) / 3200000000000000000000), D3 := ((219204643660714292031 : Rat) / 3200000000000000000000), D4 := ((71773117589285551011 : Rat) / 1600000000000000000000), LB := ((9852670270330821 : Rat) / 2500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8732336306517857151231 : Rat) / 3200000000000000000000), R := ((2184158609196428573553 : Rat) / 800000000000000000000), D0 := ((2184158609196428573553 : Rat) / 800000000000000000000), D1 := ((730178529196428573553 : Rat) / 800000000000000000000), D2 := ((137810609196428573553 : Rat) / 800000000000000000000), D3 := ((55875693482142858753 : Rat) / 800000000000000000000), D4 := ((139248104910713959041 : Rat) / 3200000000000000000000), LB := ((15227581153779701 : Rat) / 5000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2184158609196428573553 : Rat) / 800000000000000000000), R := ((8740932567053571437193 : Rat) / 3200000000000000000000), D0 := ((8740932567053571437193 : Rat) / 3200000000000000000000), D1 := ((2925012247053571437193 : Rat) / 3200000000000000000000), D2 := ((555540567053571437193 : Rat) / 3200000000000000000000), D3 := ((227800904196428577993 : Rat) / 3200000000000000000000), D4 := ((6747498732142840803 : Rat) / 160000000000000000000), LB := ((23443634343663367 : Rat) / 10000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8740932567053571437193 : Rat) / 3200000000000000000000), R := ((4372615348660714290087 : Rat) / 1600000000000000000000), D0 := ((4372615348660714290087 : Rat) / 1600000000000000000000), D1 := ((1464655188660714290087 : Rat) / 1600000000000000000000), D2 := ((279919348660714290087 : Rat) / 1600000000000000000000), D3 := ((116049517232142860487 : Rat) / 1600000000000000000000), D4 := ((130651844374999673079 : Rat) / 3200000000000000000000), LB := ((3688075369270627 : Rat) / 2000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4372615348660714290087 : Rat) / 1600000000000000000000), R := ((1749905765517857144631 : Rat) / 640000000000000000000), D0 := ((1749905765517857144631 : Rat) / 640000000000000000000), D1 := ((586721701517857144631 : Rat) / 640000000000000000000), D2 := ((112827365517857144631 : Rat) / 640000000000000000000), D3 := ((47279432946428572791 : Rat) / 640000000000000000000), D4 := ((63176857053571265049 : Rat) / 1600000000000000000000), LB := ((62077892875263 : Rat) / 40000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1749905765517857144631 : Rat) / 640000000000000000000), R := ((1094228369732142858267 : Rat) / 400000000000000000000), D0 := ((1094228369732142858267 : Rat) / 400000000000000000000), D1 := ((367238329732142858267 : Rat) / 400000000000000000000), D2 := ((71054369732142858267 : Rat) / 400000000000000000000), D3 := ((30086911875000000867 : Rat) / 400000000000000000000), D4 := ((122055583839285387117 : Rat) / 3200000000000000000000), LB := ((115358758697383 : Rat) / 78125000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1094228369732142858267 : Rat) / 400000000000000000000), R := ((8758125088125000009117 : Rat) / 3200000000000000000000), D0 := ((8758125088125000009117 : Rat) / 3200000000000000000000), D1 := ((2942204768125000009117 : Rat) / 3200000000000000000000), D2 := ((572733088125000009117 : Rat) / 3200000000000000000000), D3 := ((244993425267857149917 : Rat) / 3200000000000000000000), D4 := ((14719681696428530517 : Rat) / 400000000000000000000), LB := ((4069241163630749 : Rat) / 2500000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8758125088125000009117 : Rat) / 3200000000000000000000), R := ((4381211609196428576049 : Rat) / 1600000000000000000000), D0 := ((4381211609196428576049 : Rat) / 1600000000000000000000), D1 := ((1473251449196428576049 : Rat) / 1600000000000000000000), D2 := ((288515609196428576049 : Rat) / 1600000000000000000000), D3 := ((124645777767857146449 : Rat) / 1600000000000000000000), D4 := ((22691864660714220231 : Rat) / 640000000000000000000), LB := ((20163695439733287 : Rat) / 10000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4381211609196428576049 : Rat) / 1600000000000000000000), R := ((8766721348660714295079 : Rat) / 3200000000000000000000), D0 := ((8766721348660714295079 : Rat) / 3200000000000000000000), D1 := ((2950801028660714295079 : Rat) / 3200000000000000000000), D2 := ((581329348660714295079 : Rat) / 3200000000000000000000), D3 := ((253589685803571435879 : Rat) / 3200000000000000000000), D4 := ((54580596517856979087 : Rat) / 1600000000000000000000), LB := ((3319122800323343 : Rat) / 1250000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8766721348660714295079 : Rat) / 3200000000000000000000), R := ((438550973946428571903 : Rat) / 160000000000000000000), D0 := ((438550973946428571903 : Rat) / 160000000000000000000), D1 := ((147754957946428571903 : Rat) / 160000000000000000000), D2 := ((29281373946428571903 : Rat) / 160000000000000000000), D3 := ((12894390803571428943 : Rat) / 160000000000000000000), D4 := ((104863062767856815193 : Rat) / 3200000000000000000000), LB := ((3558980781108889 : Rat) / 1000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((438550973946428571903 : Rat) / 160000000000000000000), R := ((4389807869732142862011 : Rat) / 1600000000000000000000), D0 := ((4389807869732142862011 : Rat) / 1600000000000000000000), D1 := ((1481847709732142862011 : Rat) / 1600000000000000000000), D2 := ((297111869732142862011 : Rat) / 1600000000000000000000), D3 := ((133242038303571432411 : Rat) / 1600000000000000000000), D4 := ((25141233124999918053 : Rat) / 800000000000000000000), LB := ((1461900607473421 : Rat) / 10000000000000000000) },
  { w1 := ((439452233163061 : Rat) / 500000000000000), w2 := ((2363670877726161 : Rat) / 50000000000000000), w3 := ((3061891501628649 : Rat) / 20000000000000000), w4 := ((696339742839641 : Rat) / 5000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((5320707289285714287 : Rat) / 2000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4389807869732142862011 : Rat) / 1600000000000000000000), R := ((34328953125000000039 : Rat) / 12500000000000000000), D0 := ((34328953125000000039 : Rat) / 12500000000000000000), D1 := ((11610514375000000039 : Rat) / 12500000000000000000), D2 := ((2354765625000000039 : Rat) / 12500000000000000000), D3 := ((4298130267857142981 : Rat) / 50000000000000000000), D4 := ((73574937571428309 : Rat) / 2560000000000000000), LB := ((17634034221462591 : Rat) / 5000000000000000000) }
]

def block364RightChunk000L : Rat := ((17461207589285714317 : Rat) / 10000000000000000000)
def block364RightChunk000R : Rat := ((34328953125000000039 : Rat) / 12500000000000000000)

def block364RightChunk000Certificate : Bool :=
  allBoxesValid block364RightChunk000 &&
  coversFromBool block364RightChunk000 block364RightChunk000L block364RightChunk000R

theorem block364RightChunk000Certificate_eq_true :
    block364RightChunk000Certificate = true := by
  native_decide

def block364RightChainCertificate : Bool :=
  decide (
    block364RightL = ((17461207589285714317 : Rat) / 10000000000000000000) /\
    ((34328953125000000039 : Rat) / 12500000000000000000) = block364RightR)

theorem block364RightChainCertificate_eq_true :
    block364RightChainCertificate = true := by
  native_decide

def block364LeftBoxCount : Nat := boxCount block364LeftBoxes
def block364RightBoxCount : Nat := 58

def block364_rational_certificate : Prop :=
    block364LeftCertificate = true /\
    block364RightChainCertificate = true /\
    block364RightChunk000Certificate = true

theorem block364_rational_certificate_proof :
    block364_rational_certificate := by
  exact ⟨block364LeftCertificate_eq_true, block364RightChainCertificate_eq_true, block364RightChunk000Certificate_eq_true⟩

end Block364
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block364

open Set

def block364W1 : Rat := ((439452233163061 : Rat) / 500000000000000)
def block364W2 : Rat := ((2363670877726161 : Rat) / 50000000000000000)
def block364W3 : Rat := ((3061891501628649 : Rat) / 20000000000000000)
def block364W4 : Rat := ((696339742839641 : Rat) / 5000000000000000)
def block364S1 : Rat := ((18174751 : Rat) / 10000000)
def block364S2 : Rat := ((511587 : Rat) / 200000)
def block364S3 : Rat := ((5320707289285714287 : Rat) / 2000000000000000000)
def block364S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block364V (y : ℝ) : ℝ :=
  ratPotential block364W1 block364W2 block364W3 block364W4 block364S1 block364S2 block364S3 block364S4 y

def block364LeftParamsCertificate : Bool :=
  allBoxesSameParams block364LeftBoxes block364W1 block364W2 block364W3 block364W4 block364S1 block364S2 block364S3 block364S4

theorem block364LeftParamsCertificate_eq_true :
    block364LeftParamsCertificate = true := by
  native_decide

theorem block364_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block364LeftL : ℝ) (block364LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block364S1 : ℝ))
    (hy2ne : y ≠ (block364S2 : ℝ))
    (hy3ne : y ≠ (block364S3 : ℝ))
    (hy4ne : y ≠ (block364S4 : ℝ)) :
    0 < block364V y := by
  have hcert := block364LeftCertificate_eq_true
  unfold block364LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block364LeftBoxes) (lo := block364LeftL) (hi := block364LeftR)
    (w1 := block364W1) (w2 := block364W2) (w3 := block364W3) (w4 := block364W4)
    (s1 := block364S1) (s2 := block364S2) (s3 := block364S3) (s4 := block364S4)
    hboxes hcover block364LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block364RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block364RightChunk000 block364W1 block364W2 block364W3 block364W4 block364S1 block364S2 block364S3 block364S4

theorem block364RightChunk000ParamsCertificate_eq_true :
    block364RightChunk000ParamsCertificate = true := by
  native_decide

theorem block364_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block364RightChunk000L : ℝ) (block364RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block364S1 : ℝ))
    (hy2ne : y ≠ (block364S2 : ℝ))
    (hy3ne : y ≠ (block364S3 : ℝ))
    (hy4ne : y ≠ (block364S4 : ℝ)) :
    0 < block364V y := by
  have hcert := block364RightChunk000Certificate_eq_true
  unfold block364RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block364RightChunk000) (lo := block364RightChunk000L) (hi := block364RightChunk000R)
    (w1 := block364W1) (w2 := block364W2) (w3 := block364W3) (w4 := block364W4)
    (s1 := block364S1) (s2 := block364S2) (s3 := block364S3) (s4 := block364S4)
    hboxes hcover block364RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block364_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block364RightL : ℝ) (block364RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block364S1 : ℝ))
    (hy2ne : y ≠ (block364S2 : ℝ))
    (hy3ne : y ≠ (block364S3 : ℝ))
    (hy4ne : y ≠ (block364S4 : ℝ)) :
    0 < block364V y := by
  have hL : (block364RightChunk000L : ℝ) = (block364RightL : ℝ) := by
    norm_num [block364RightChunk000L, block364RightL]
  have hR : (block364RightChunk000R : ℝ) = (block364RightR : ℝ) := by
    norm_num [block364RightChunk000R, block364RightR]
  have hyc : y ∈ Icc (block364RightChunk000L : ℝ) (block364RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block364_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block364_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block364LeftL : ℝ) (block364LeftR : ℝ) →
    y ≠ 0 → y ≠ (block364S1 : ℝ) → y ≠ (block364S2 : ℝ) →
    y ≠ (block364S3 : ℝ) → y ≠ (block364S4 : ℝ) → 0 < block364V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block364RightL : ℝ) (block364RightR : ℝ) →
    y ≠ 0 → y ≠ (block364S1 : ℝ) → y ≠ (block364S2 : ℝ) →
    y ≠ (block364S3 : ℝ) → y ≠ (block364S4 : ℝ) → 0 < block364V y)

theorem block364_reallog_certificate_proof :
    block364_reallog_certificate := by
  exact ⟨block364_left_V_pos, block364_right_V_pos⟩

end Block364
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block364.block364V
#check Erdos1038Lean.M1817475.Block364.block364_left_V_pos
#check Erdos1038Lean.M1817475.Block364.block364_right_V_pos
#check Erdos1038Lean.M1817475.Block364.block364_reallog_certificate_proof
