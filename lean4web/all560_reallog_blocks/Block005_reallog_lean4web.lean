/-
Self-contained Lean4Web paste file.
Block 5 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block005

def block005LeftL : Rat := ((20407551339285714287 : Rat) / 25000000000000000000)
def block005LeftR : Rat := ((8164975446428571429 : Rat) / 10000000000000000000)
def block005RightL : Rat := ((45407551339285714287 : Rat) / 25000000000000000000)
def block005RightR : Rat := ((28164975446428571429 : Rat) / 10000000000000000000)

def block005LeftBoxes : List RatBox := [
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((20407551339285714287 : Rat) / 25000000000000000000), R := ((8164975446428571429 : Rat) / 10000000000000000000), D0 := ((8164975446428571429 : Rat) / 10000000000000000000), D1 := ((25029326160714285713 : Rat) / 25000000000000000000), D2 := ((43540823660714285713 : Rat) / 25000000000000000000), D3 := ((46467835535714285713 : Rat) / 25000000000000000000), D4 := ((50377659464285711733 : Rat) / 25000000000000000000), LB := ((3512382654975381 : Rat) / 250000000000000000) }
]

def block005LeftCertificate : Bool :=
  allBoxesValid block005LeftBoxes &&
  coversFromBool block005LeftBoxes block005LeftL block005LeftR

theorem block005LeftCertificate_eq_true :
    block005LeftCertificate = true := by
  native_decide

def block005RightChunk000 : List RatBox := [
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((45407551339285714287 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((29326160714285713 : Rat) / 25000000000000000000), D2 := ((18540823660714285713 : Rat) / 25000000000000000000), D3 := ((21467835535714285713 : Rat) / 25000000000000000000), D4 := ((25377659464285711733 : Rat) / 25000000000000000000), LB := ((3728869708497313 : Rat) / 50000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((1267416665178571301 : Rat) / 1250000000000000000), LB := ((5199415672157687 : Rat) / 2000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((341841790178571301 : Rat) / 1250000000000000000), LB := ((11514092590038743 : Rat) / 10000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((54915130196428571429 : Rat) / 20000000000000000000), D0 := ((54915130196428571429 : Rat) / 20000000000000000000), D1 := ((18565628196428571429 : Rat) / 20000000000000000000), D2 := ((3756430196428571429 : Rat) / 20000000000000000000), D3 := ((1414820696428571429 : Rat) / 20000000000000000000), D4 := ((195491196428571301 : Rat) / 1250000000000000000), LB := ((16515377035746573 : Rat) / 50000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((54915130196428571429 : Rat) / 20000000000000000000), R := ((111245081089285714287 : Rat) / 40000000000000000000), D0 := ((111245081089285714287 : Rat) / 40000000000000000000), D1 := ((38546077089285714287 : Rat) / 40000000000000000000), D2 := ((8927681089285714287 : Rat) / 40000000000000000000), D3 := ((4244462089285714287 : Rat) / 40000000000000000000), D4 := ((1713038446428569387 : Rat) / 20000000000000000000), LB := ((2691711762549087 : Rat) / 100000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((111245081089285714287 : Rat) / 40000000000000000000), R := ((446395145053571428577 : Rat) / 160000000000000000000), D0 := ((446395145053571428577 : Rat) / 160000000000000000000), D1 := ((155599129053571428577 : Rat) / 160000000000000000000), D2 := ((37125545053571428577 : Rat) / 160000000000000000000), D3 := ((18392669053571428577 : Rat) / 160000000000000000000), D4 := ((402251239285713469 : Rat) / 8000000000000000000), LB := ((24495093495124687 : Rat) / 500000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((446395145053571428577 : Rat) / 160000000000000000000), R := ((894205110803571428583 : Rat) / 320000000000000000000), D0 := ((894205110803571428583 : Rat) / 320000000000000000000), D1 := ((312613078803571428583 : Rat) / 320000000000000000000), D2 := ((75665910803571428583 : Rat) / 320000000000000000000), D3 := ((38200158803571428583 : Rat) / 320000000000000000000), D4 := ((6630204089285697951 : Rat) / 160000000000000000000), LB := ((211007896578711 : Rat) / 5000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((894205110803571428583 : Rat) / 320000000000000000000), R := ((223904982875000000003 : Rat) / 80000000000000000000), D0 := ((223904982875000000003 : Rat) / 80000000000000000000), D1 := ((78506974875000000003 : Rat) / 80000000000000000000), D2 := ((19270182875000000003 : Rat) / 80000000000000000000), D3 := ((9903744875000000003 : Rat) / 80000000000000000000), D4 := ((11845587482142824473 : Rat) / 320000000000000000000), LB := ((3886128318443427 : Rat) / 250000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((223904982875000000003 : Rat) / 80000000000000000000), R := ((1792654683696428571453 : Rat) / 640000000000000000000), D0 := ((1792654683696428571453 : Rat) / 640000000000000000000), D1 := ((629470619696428571453 : Rat) / 640000000000000000000), D2 := ((155576283696428571453 : Rat) / 640000000000000000000), D3 := ((80644779696428571453 : Rat) / 640000000000000000000), D4 := ((2607691696428563261 : Rat) / 80000000000000000000), LB := ((1997127844635571 : Rat) / 100000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1792654683696428571453 : Rat) / 640000000000000000000), R := ((897034752196428571441 : Rat) / 320000000000000000000), D0 := ((897034752196428571441 : Rat) / 320000000000000000000), D1 := ((315442720196428571441 : Rat) / 320000000000000000000), D2 := ((78495552196428571441 : Rat) / 320000000000000000000), D3 := ((41029800196428571441 : Rat) / 320000000000000000000), D4 := ((19446712874999934659 : Rat) / 640000000000000000000), LB := ((10241492074119951 : Rat) / 1000000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((897034752196428571441 : Rat) / 320000000000000000000), R := ((1795484325089285714311 : Rat) / 640000000000000000000), D0 := ((1795484325089285714311 : Rat) / 640000000000000000000), D1 := ((632300261089285714311 : Rat) / 640000000000000000000), D2 := ((158405925089285714311 : Rat) / 640000000000000000000), D3 := ((83474421089285714311 : Rat) / 640000000000000000000), D4 := ((1803189217857136323 : Rat) / 64000000000000000000), LB := ((18960819827591457 : Rat) / 10000000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1795484325089285714311 : Rat) / 640000000000000000000), R := ((3592383470875000000051 : Rat) / 1280000000000000000000), D0 := ((3592383470875000000051 : Rat) / 1280000000000000000000), D1 := ((1266015342875000000051 : Rat) / 1280000000000000000000), D2 := ((318226670875000000051 : Rat) / 1280000000000000000000), D3 := ((168363662875000000051 : Rat) / 1280000000000000000000), D4 := ((16617071482142791801 : Rat) / 640000000000000000000), LB := ((4356176058989969 : Rat) / 500000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3592383470875000000051 : Rat) / 1280000000000000000000), R := ((89844957289285714287 : Rat) / 32000000000000000000), D0 := ((89844957289285714287 : Rat) / 32000000000000000000), D1 := ((31685754089285714287 : Rat) / 32000000000000000000), D2 := ((7991037289285714287 : Rat) / 32000000000000000000), D3 := ((4244462089285714287 : Rat) / 32000000000000000000), D4 := ((31819322267857012173 : Rat) / 1280000000000000000000), LB := ((6008390881352299 : Rat) / 1000000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((89844957289285714287 : Rat) / 32000000000000000000), R := ((3595213112267857142909 : Rat) / 1280000000000000000000), D0 := ((3595213112267857142909 : Rat) / 1280000000000000000000), D1 := ((1268844984267857142909 : Rat) / 1280000000000000000000), D2 := ((321056312267857142909 : Rat) / 1280000000000000000000), D3 := ((171193304267857142909 : Rat) / 1280000000000000000000), D4 := ((3800562696428555093 : Rat) / 160000000000000000000), LB := ((38131606765069437 : Rat) / 10000000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3595213112267857142909 : Rat) / 1280000000000000000000), R := ((1798313966482142857169 : Rat) / 640000000000000000000), D0 := ((1798313966482142857169 : Rat) / 640000000000000000000), D1 := ((635129902482142857169 : Rat) / 640000000000000000000), D2 := ((161235566482142857169 : Rat) / 640000000000000000000), D3 := ((86304062482142857169 : Rat) / 640000000000000000000), D4 := ((5797936174999973863 : Rat) / 256000000000000000000), LB := ((1086855381462859 : Rat) / 500000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1798313966482142857169 : Rat) / 640000000000000000000), R := ((3598042753660714285767 : Rat) / 1280000000000000000000), D0 := ((3598042753660714285767 : Rat) / 1280000000000000000000), D1 := ((1271674625660714285767 : Rat) / 1280000000000000000000), D2 := ((323885953660714285767 : Rat) / 1280000000000000000000), D3 := ((174022945660714285767 : Rat) / 1280000000000000000000), D4 := ((13787430089285648943 : Rat) / 640000000000000000000), LB := ((1144159323582583 : Rat) / 1000000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3598042753660714285767 : Rat) / 1280000000000000000000), R := ((899864393589285714299 : Rat) / 320000000000000000000), D0 := ((899864393589285714299 : Rat) / 320000000000000000000), D1 := ((318272361589285714299 : Rat) / 320000000000000000000), D2 := ((81325193589285714299 : Rat) / 320000000000000000000), D3 := ((43859441589285714299 : Rat) / 320000000000000000000), D4 := ((26160039482142726457 : Rat) / 1280000000000000000000), LB := ((7871814686254419 : Rat) / 10000000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((899864393589285714299 : Rat) / 320000000000000000000), R := ((28806979160428571429 : Rat) / 10240000000000000000), D0 := ((28806979160428571429 : Rat) / 10240000000000000000), D1 := ((10196034136428571429 : Rat) / 10240000000000000000), D2 := ((2613724760428571429 : Rat) / 10240000000000000000), D3 := ((1414820696428571429 : Rat) / 10240000000000000000), D4 := ((6186304696428538757 : Rat) / 320000000000000000000), LB := ((117590886839547 : Rat) / 100000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((28806979160428571429 : Rat) / 10240000000000000000), R := ((1801143607875000000027 : Rat) / 640000000000000000000), D0 := ((1801143607875000000027 : Rat) / 640000000000000000000), D1 := ((637959543875000000027 : Rat) / 640000000000000000000), D2 := ((164065207875000000027 : Rat) / 640000000000000000000), D3 := ((89133703875000000027 : Rat) / 640000000000000000000), D4 := ((23330398089285583599 : Rat) / 1280000000000000000000), LB := ((2396384141941321 : Rat) / 1000000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1801143607875000000027 : Rat) / 640000000000000000000), R := ((3603702036446428571483 : Rat) / 1280000000000000000000), D0 := ((3603702036446428571483 : Rat) / 1280000000000000000000), D1 := ((1277333908446428571483 : Rat) / 1280000000000000000000), D2 := ((329545236446428571483 : Rat) / 1280000000000000000000), D3 := ((179682228446428571483 : Rat) / 1280000000000000000000), D4 := ((2191557739285701217 : Rat) / 128000000000000000000), LB := ((4550773425987531 : Rat) / 1000000000000000000) },
  { w1 := ((5894429855721839 : Rat) / 500000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((24956195071173903 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((3603702036446428571483 : Rat) / 1280000000000000000000), R := ((28164975446428571429 : Rat) / 10000000000000000000), D0 := ((28164975446428571429 : Rat) / 10000000000000000000), D1 := ((9990224446428571429 : Rat) / 10000000000000000000), D2 := ((2585625446428571429 : Rat) / 10000000000000000000), D3 := ((1414820696428571429 : Rat) / 10000000000000000000), D4 := ((20500756696428440741 : Rat) / 1280000000000000000000), LB := ((3880815305200791 : Rat) / 500000000000000000) }
]

def block005RightChunk000L : Rat := ((45407551339285714287 : Rat) / 25000000000000000000)
def block005RightChunk000R : Rat := ((28164975446428571429 : Rat) / 10000000000000000000)

def block005RightChunk000Certificate : Bool :=
  allBoxesValid block005RightChunk000 &&
  coversFromBool block005RightChunk000 block005RightChunk000L block005RightChunk000R

theorem block005RightChunk000Certificate_eq_true :
    block005RightChunk000Certificate = true := by
  native_decide

def block005RightChainCertificate : Bool :=
  decide (
    block005RightL = ((45407551339285714287 : Rat) / 25000000000000000000) /\
    ((28164975446428571429 : Rat) / 10000000000000000000) = block005RightR)

theorem block005RightChainCertificate_eq_true :
    block005RightChainCertificate = true := by
  native_decide

def block005LeftBoxCount : Nat := boxCount block005LeftBoxes
def block005RightBoxCount : Nat := 21

def block005_rational_certificate : Prop :=
    block005LeftCertificate = true /\
    block005RightChainCertificate = true /\
    block005RightChunk000Certificate = true

theorem block005_rational_certificate_proof :
    block005_rational_certificate := by
  exact ⟨block005LeftCertificate_eq_true, block005RightChainCertificate_eq_true, block005RightChunk000Certificate_eq_true⟩

end Block005
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block005

open Set

def block005W1 : Rat := ((5894429855721839 : Rat) / 500000000000000)
def block005W2 : Rat := (0 : Rat)
def block005W3 : Rat := (0 : Rat)
def block005W4 : Rat := ((24956195071173903 : Rat) / 100000000000000000)
def block005S1 : Rat := ((18174751 : Rat) / 10000000)
def block005S2 : Rat := ((511587 : Rat) / 200000)
def block005S3 : Rat := ((107000619 : Rat) / 40000000)
def block005S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block005V (y : ℝ) : ℝ :=
  ratPotential block005W1 block005W2 block005W3 block005W4 block005S1 block005S2 block005S3 block005S4 y

def block005LeftParamsCertificate : Bool :=
  allBoxesSameParams block005LeftBoxes block005W1 block005W2 block005W3 block005W4 block005S1 block005S2 block005S3 block005S4

theorem block005LeftParamsCertificate_eq_true :
    block005LeftParamsCertificate = true := by
  native_decide

theorem block005_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block005LeftL : ℝ) (block005LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block005S1 : ℝ))
    (hy2ne : y ≠ (block005S2 : ℝ))
    (hy3ne : y ≠ (block005S3 : ℝ))
    (hy4ne : y ≠ (block005S4 : ℝ)) :
    0 < block005V y := by
  have hcert := block005LeftCertificate_eq_true
  unfold block005LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block005LeftBoxes) (lo := block005LeftL) (hi := block005LeftR)
    (w1 := block005W1) (w2 := block005W2) (w3 := block005W3) (w4 := block005W4)
    (s1 := block005S1) (s2 := block005S2) (s3 := block005S3) (s4 := block005S4)
    hboxes hcover block005LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block005RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block005RightChunk000 block005W1 block005W2 block005W3 block005W4 block005S1 block005S2 block005S3 block005S4

theorem block005RightChunk000ParamsCertificate_eq_true :
    block005RightChunk000ParamsCertificate = true := by
  native_decide

theorem block005_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block005RightChunk000L : ℝ) (block005RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block005S1 : ℝ))
    (hy2ne : y ≠ (block005S2 : ℝ))
    (hy3ne : y ≠ (block005S3 : ℝ))
    (hy4ne : y ≠ (block005S4 : ℝ)) :
    0 < block005V y := by
  have hcert := block005RightChunk000Certificate_eq_true
  unfold block005RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block005RightChunk000) (lo := block005RightChunk000L) (hi := block005RightChunk000R)
    (w1 := block005W1) (w2 := block005W2) (w3 := block005W3) (w4 := block005W4)
    (s1 := block005S1) (s2 := block005S2) (s3 := block005S3) (s4 := block005S4)
    hboxes hcover block005RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block005_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block005RightL : ℝ) (block005RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block005S1 : ℝ))
    (hy2ne : y ≠ (block005S2 : ℝ))
    (hy3ne : y ≠ (block005S3 : ℝ))
    (hy4ne : y ≠ (block005S4 : ℝ)) :
    0 < block005V y := by
  have hL : (block005RightChunk000L : ℝ) = (block005RightL : ℝ) := by
    norm_num [block005RightChunk000L, block005RightL]
  have hR : (block005RightChunk000R : ℝ) = (block005RightR : ℝ) := by
    norm_num [block005RightChunk000R, block005RightR]
  have hyc : y ∈ Icc (block005RightChunk000L : ℝ) (block005RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block005_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block005_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block005LeftL : ℝ) (block005LeftR : ℝ) →
    y ≠ 0 → y ≠ (block005S1 : ℝ) → y ≠ (block005S2 : ℝ) →
    y ≠ (block005S3 : ℝ) → y ≠ (block005S4 : ℝ) → 0 < block005V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block005RightL : ℝ) (block005RightR : ℝ) →
    y ≠ 0 → y ≠ (block005S1 : ℝ) → y ≠ (block005S2 : ℝ) →
    y ≠ (block005S3 : ℝ) → y ≠ (block005S4 : ℝ) → 0 < block005V y)

theorem block005_reallog_certificate_proof :
    block005_reallog_certificate := by
  exact ⟨block005_left_V_pos, block005_right_V_pos⟩

end Block005
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block005.block005V
#check Erdos1038Lean.M1817475.Block005.block005_left_V_pos
#check Erdos1038Lean.M1817475.Block005.block005_right_V_pos
#check Erdos1038Lean.M1817475.Block005.block005_reallog_certificate_proof
