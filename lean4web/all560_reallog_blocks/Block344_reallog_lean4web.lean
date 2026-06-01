/-
Self-contained Lean4Web paste file.
Block 344 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block344

def block344LeftL : Rat := ((7500305803571428601 : Rat) / 10000000000000000000)
def block344LeftR : Rat := ((4688912946428571447 : Rat) / 6250000000000000000)
def block344RightL : Rat := ((17500305803571428601 : Rat) / 10000000000000000000)
def block344RightR : Rat := ((17188912946428571447 : Rat) / 6250000000000000000)

def block344LeftBoxes : List RatBox := [
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((7500305803571428601 : Rat) / 10000000000000000000), R := ((4688912946428571447 : Rat) / 6250000000000000000), D0 := ((4688912946428571447 : Rat) / 6250000000000000000), D1 := ((10674445196428571399 : Rat) / 10000000000000000000), D2 := ((18079044196428571399 : Rat) / 10000000000000000000), D3 := ((9590713535714285701 : Rat) / 5000000000000000000), D4 := ((101116977410714280593 : Rat) / 50000000000000000000), LB := ((25240153063461 : Rat) / 4000000000000000) }
]

def block344LeftCertificate : Bool :=
  allBoxesValid block344LeftBoxes &&
  coversFromBool block344LeftBoxes block344LeftL block344LeftR

theorem block344LeftCertificate_eq_true :
    block344LeftCertificate = true := by
  native_decide

def block344RightChunk000 : List RatBox := [
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((17500305803571428601 : Rat) / 10000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((674445196428571399 : Rat) / 10000000000000000000), D2 := ((8079044196428571399 : Rat) / 10000000000000000000), D3 := ((4590713535714285701 : Rat) / 5000000000000000000), D4 := ((51116977410714280593 : Rat) / 50000000000000000000), LB := ((9500269351497639 : Rat) / 5000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((8506981875000000003 : Rat) / 10000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((17466215495043777 : Rat) / 100000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((4804682375000000003 : Rat) / 10000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((705130125482927 : Rat) / 6250000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((3879107500000000003 : Rat) / 10000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((185170256599323 : Rat) / 2500000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((3416320062500000003 : Rat) / 10000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((15390384340127503 : Rat) / 1000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((2953532625000000003 : Rat) / 10000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((15307614160677413 : Rat) / 1000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((2722138906250000003 : Rat) / 10000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((943450862452773 : Rat) / 50000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((2606442046875000003 : Rat) / 10000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((1044784565848883 : Rat) / 100000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((2490745187500000003 : Rat) / 10000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((3875351035985547 : Rat) / 1250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((2375048328125000003 : Rat) / 10000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((390952306290919 : Rat) / 50000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((2317199898437500003 : Rat) / 10000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((5092252836048111 : Rat) / 1000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((2259351468750000003 : Rat) / 10000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((538060409283353 : Rat) / 200000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((2201503039062500003 : Rat) / 10000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((6289946274434521 : Rat) / 10000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((2143654609375000003 : Rat) / 10000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((4251755166508747 : Rat) / 1000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((2114730394531250003 : Rat) / 10000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((352135843305057 : Rat) / 100000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((2085806179687500003 : Rat) / 10000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((3611095924700887 : Rat) / 1250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((2056881964843750003 : Rat) / 10000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((11787195057008787 : Rat) / 5000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2027957750000000003 : Rat) / 10000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((2413036072416927 : Rat) / 1250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((1999033535156250003 : Rat) / 10000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((16115137893382703 : Rat) / 10000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((1970109320312500003 : Rat) / 10000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((14046790315995483 : Rat) / 10000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((1941185105468750003 : Rat) / 10000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((1642833578422917 : Rat) / 1250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((1912260890625000003 : Rat) / 10000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((336255652952179 : Rat) / 250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((1883336675781250003 : Rat) / 10000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((3004297505702691 : Rat) / 2000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((1854412460937500003 : Rat) / 10000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((8956844509428463 : Rat) / 5000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((1825488246093750003 : Rat) / 10000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((2773755023705339 : Rat) / 1250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((1796564031250000003 : Rat) / 10000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((6980159430787919 : Rat) / 2500000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((1767639816406250003 : Rat) / 10000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((3518356899404773 : Rat) / 1000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((1738715601562500003 : Rat) / 10000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((2203312794752041 : Rat) / 500000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((1709791386718750003 : Rat) / 10000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((10933421089598827 : Rat) / 2000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((1680867171875000003 : Rat) / 10000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((42141440817553 : Rat) / 25000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((1623018742187500003 : Rat) / 10000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((961659724108721 : Rat) / 200000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((1565170312500000003 : Rat) / 10000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((8841797259123207 : Rat) / 1000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((1507321882812500003 : Rat) / 10000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((3489983363823279 : Rat) / 250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((1449473453125000003 : Rat) / 10000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1068616543396389 : Rat) / 100000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((1333776593750000003 : Rat) / 10000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((52363190802657 : Rat) / 5000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((103419782875000000003 : Rat) / 40000000000000000000), D0 := ((103419782875000000003 : Rat) / 40000000000000000000), D1 := ((30720778875000000003 : Rat) / 40000000000000000000), D2 := ((1102382875000000003 : Rat) / 40000000000000000000), D3 := ((1102382875000000003 : Rat) / 10000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((6887966245625043 : Rat) / 100000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((103419782875000000003 : Rat) / 40000000000000000000), R := ((207941948625000000009 : Rat) / 80000000000000000000), D0 := ((207941948625000000009 : Rat) / 80000000000000000000), D1 := ((62543940625000000009 : Rat) / 80000000000000000000), D2 := ((3307148625000000009 : Rat) / 80000000000000000000), D3 := ((3307148625000000009 : Rat) / 40000000000000000000), D4 := ((37375111339285694377 : Rat) / 200000000000000000000), LB := ((10252940300720617 : Rat) / 500000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((207941948625000000009 : Rat) / 80000000000000000000), R := ((52261082875000000003 : Rat) / 20000000000000000000), D0 := ((52261082875000000003 : Rat) / 20000000000000000000), D1 := ((15911580875000000003 : Rat) / 20000000000000000000), D2 := ((1102382875000000003 : Rat) / 20000000000000000000), D3 := ((1102382875000000003 : Rat) / 16000000000000000000), D4 := ((69238308303571388739 : Rat) / 400000000000000000000), LB := ((716379139034053 : Rat) / 31250000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((52261082875000000003 : Rat) / 20000000000000000000), R := ((105624548625000000009 : Rat) / 40000000000000000000), D0 := ((105624548625000000009 : Rat) / 40000000000000000000), D1 := ((32925544625000000009 : Rat) / 40000000000000000000), D2 := ((3307148625000000009 : Rat) / 40000000000000000000), D3 := ((1102382875000000003 : Rat) / 20000000000000000000), D4 := ((15931598482142847181 : Rat) / 100000000000000000000), LB := ((3100324607127447 : Rat) / 500000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((105624548625000000009 : Rat) / 40000000000000000000), R := ((26681732875000000003 : Rat) / 10000000000000000000), D0 := ((26681732875000000003 : Rat) / 10000000000000000000), D1 := ((8506981875000000003 : Rat) / 10000000000000000000), D2 := ((1102382875000000003 : Rat) / 10000000000000000000), D3 := ((1102382875000000003 : Rat) / 40000000000000000000), D4 := ((26351282589285694347 : Rat) / 200000000000000000000), LB := ((4009380421473663 : Rat) / 50000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((26681732875000000003 : Rat) / 10000000000000000000), R := ((537737296696428571621 : Rat) / 200000000000000000000), D0 := ((537737296696428571621 : Rat) / 200000000000000000000), D1 := ((174242276696428571621 : Rat) / 200000000000000000000), D2 := ((26150296696428571621 : Rat) / 200000000000000000000), D3 := ((4102639196428571561 : Rat) / 200000000000000000000), D4 := ((5209842053571423583 : Rat) / 50000000000000000000), LB := ((2959243134365397 : Rat) / 25000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((537737296696428571621 : Rat) / 200000000000000000000), R := ((270919967946428571591 : Rat) / 100000000000000000000), D0 := ((270919967946428571591 : Rat) / 100000000000000000000), D1 := ((89172457946428571591 : Rat) / 100000000000000000000), D2 := ((15126467946428571591 : Rat) / 100000000000000000000), D3 := ((4102639196428571561 : Rat) / 100000000000000000000), D4 := ((16736729017857122771 : Rat) / 200000000000000000000), LB := ((2111871159767209 : Rat) / 200000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270919967946428571591 : Rat) / 100000000000000000000), R := ((2171462382767857144289 : Rat) / 800000000000000000000), D0 := ((2171462382767857144289 : Rat) / 800000000000000000000), D1 := ((717482302767857144289 : Rat) / 800000000000000000000), D2 := ((125114382767857144289 : Rat) / 800000000000000000000), D3 := ((36923752767857144049 : Rat) / 800000000000000000000), D4 := ((1263408982142855121 : Rat) / 20000000000000000000), LB := ((23209764789860143 : Rat) / 1000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2171462382767857144289 : Rat) / 800000000000000000000), R := ((43511300439285714317 : Rat) / 16000000000000000000), D0 := ((43511300439285714317 : Rat) / 16000000000000000000), D1 := ((14431698839285714317 : Rat) / 16000000000000000000), D2 := ((2584340439285714317 : Rat) / 16000000000000000000), D3 := ((4102639196428571561 : Rat) / 80000000000000000000), D4 := ((46433720089285633279 : Rat) / 800000000000000000000), LB := ((5347632695796911 : Rat) / 500000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43511300439285714317 : Rat) / 16000000000000000000), R := ((2179667661160714287411 : Rat) / 800000000000000000000), D0 := ((2179667661160714287411 : Rat) / 800000000000000000000), D1 := ((725687581160714287411 : Rat) / 800000000000000000000), D2 := ((133319661160714287411 : Rat) / 800000000000000000000), D3 := ((45129031160714287171 : Rat) / 800000000000000000000), D4 := ((21165540446428530859 : Rat) / 400000000000000000000), LB := ((64245519790407 : Rat) / 78125000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2179667661160714287411 : Rat) / 800000000000000000000), R := ((4363437961517857146383 : Rat) / 1600000000000000000000), D0 := ((4363437961517857146383 : Rat) / 1600000000000000000000), D1 := ((1455477801517857146383 : Rat) / 1600000000000000000000), D2 := ((270741961517857146383 : Rat) / 1600000000000000000000), D3 := ((94360701517857145903 : Rat) / 1600000000000000000000), D4 := ((38228441696428490157 : Rat) / 800000000000000000000), LB := ((4060233292375703 : Rat) / 1000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4363437961517857146383 : Rat) / 1600000000000000000000), R := ((545942575089285714743 : Rat) / 200000000000000000000), D0 := ((545942575089285714743 : Rat) / 200000000000000000000), D1 := ((182447555089285714743 : Rat) / 200000000000000000000), D2 := ((34355575089285714743 : Rat) / 200000000000000000000), D3 := ((12307917589285714683 : Rat) / 200000000000000000000), D4 := ((72354244196428408753 : Rat) / 1600000000000000000000), LB := ((5746390539517199 : Rat) / 5000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545942575089285714743 : Rat) / 200000000000000000000), R := ((8739183840625000007449 : Rat) / 3200000000000000000000), D0 := ((8739183840625000007449 : Rat) / 3200000000000000000000), D1 := ((2923263520625000007449 : Rat) / 3200000000000000000000), D2 := ((553791840625000007449 : Rat) / 3200000000000000000000), D3 := ((201029320625000006489 : Rat) / 3200000000000000000000), D4 := ((8531450624999979649 : Rat) / 200000000000000000000), LB := ((16165566269011 : Rat) / 4000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8739183840625000007449 : Rat) / 3200000000000000000000), R := ((874328647982142857901 : Rat) / 320000000000000000000), D0 := ((874328647982142857901 : Rat) / 320000000000000000000), D1 := ((292736615982142857901 : Rat) / 320000000000000000000), D2 := ((55789447982142857901 : Rat) / 320000000000000000000), D3 := ((4102639196428571561 : Rat) / 64000000000000000000), D4 := ((132400570803571102823 : Rat) / 3200000000000000000000), LB := ((395164385374909 : Rat) / 125000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((874328647982142857901 : Rat) / 320000000000000000000), R := ((8747389119017857150571 : Rat) / 3200000000000000000000), D0 := ((8747389119017857150571 : Rat) / 3200000000000000000000), D1 := ((2931468799017857150571 : Rat) / 3200000000000000000000), D2 := ((561997119017857150571 : Rat) / 3200000000000000000000), D3 := ((209234599017857149611 : Rat) / 3200000000000000000000), D4 := ((64148965803571265631 : Rat) / 1600000000000000000000), LB := ((24771278267261 : Rat) / 10000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8747389119017857150571 : Rat) / 3200000000000000000000), R := ((2187872939553571430533 : Rat) / 800000000000000000000), D0 := ((2187872939553571430533 : Rat) / 800000000000000000000), D1 := ((733892859553571430533 : Rat) / 800000000000000000000), D2 := ((141524939553571430533 : Rat) / 800000000000000000000), D3 := ((53334309553571430293 : Rat) / 800000000000000000000), D4 := ((124195292410713959701 : Rat) / 3200000000000000000000), LB := ((2493878372682723 : Rat) / 1250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2187872939553571430533 : Rat) / 800000000000000000000), R := ((8755594397410714293693 : Rat) / 3200000000000000000000), D0 := ((8755594397410714293693 : Rat) / 3200000000000000000000), D1 := ((2939674077410714293693 : Rat) / 3200000000000000000000), D2 := ((570202397410714293693 : Rat) / 3200000000000000000000), D3 := ((217439877410714292733 : Rat) / 3200000000000000000000), D4 := ((6004632660714269407 : Rat) / 160000000000000000000), LB := ((17225116168102517 : Rat) / 10000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8755594397410714293693 : Rat) / 3200000000000000000000), R := ((4379848518303571432627 : Rat) / 1600000000000000000000), D0 := ((4379848518303571432627 : Rat) / 1600000000000000000000), D1 := ((1471888358303571432627 : Rat) / 1600000000000000000000), D2 := ((287152518303571432627 : Rat) / 1600000000000000000000), D3 := ((110771258303571432147 : Rat) / 1600000000000000000000), D4 := ((115990014017856816579 : Rat) / 3200000000000000000000), LB := ((16677363570166137 : Rat) / 10000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4379848518303571432627 : Rat) / 1600000000000000000000), R := ((1752759935160714287363 : Rat) / 640000000000000000000), D0 := ((1752759935160714287363 : Rat) / 640000000000000000000), D1 := ((589575871160714287363 : Rat) / 640000000000000000000), D2 := ((115681535160714287363 : Rat) / 640000000000000000000), D3 := ((45129031160714287171 : Rat) / 640000000000000000000), D4 := ((55943687410714122509 : Rat) / 1600000000000000000000), LB := ((18404020139342059 : Rat) / 10000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1752759935160714287363 : Rat) / 640000000000000000000), R := ((1095987789375000001047 : Rat) / 400000000000000000000), D0 := ((1095987789375000001047 : Rat) / 400000000000000000000), D1 := ((368997749375000001047 : Rat) / 400000000000000000000), D2 := ((72813789375000001047 : Rat) / 400000000000000000000), D3 := ((28718474375000000927 : Rat) / 400000000000000000000), D4 := ((107784735624999673457 : Rat) / 3200000000000000000000), LB := ((4503075755713959 : Rat) / 2000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1095987789375000001047 : Rat) / 400000000000000000000), R := ((8772004954196428579937 : Rat) / 3200000000000000000000), D0 := ((8772004954196428579937 : Rat) / 3200000000000000000000), D1 := ((2956084634196428579937 : Rat) / 3200000000000000000000), D2 := ((586612954196428579937 : Rat) / 3200000000000000000000), D3 := ((233850434196428578977 : Rat) / 3200000000000000000000), D4 := ((12960262053571387737 : Rat) / 400000000000000000000), LB := ((1456885915235323 : Rat) / 500000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8772004954196428579937 : Rat) / 3200000000000000000000), R := ((4388053796696428575749 : Rat) / 1600000000000000000000), D0 := ((4388053796696428575749 : Rat) / 1600000000000000000000), D1 := ((1480093636696428575749 : Rat) / 1600000000000000000000), D2 := ((295357796696428575749 : Rat) / 1600000000000000000000), D3 := ((118976536696428575269 : Rat) / 1600000000000000000000), D4 := ((19915891446428506067 : Rat) / 640000000000000000000), LB := ((38415661402545487 : Rat) / 10000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4388053796696428575749 : Rat) / 1600000000000000000000), R := ((439215643589285714731 : Rat) / 160000000000000000000), D0 := ((439215643589285714731 : Rat) / 160000000000000000000), D1 := ((148419627589285714731 : Rat) / 160000000000000000000), D2 := ((29946043589285714731 : Rat) / 160000000000000000000), D3 := ((12307917589285714683 : Rat) / 160000000000000000000), D4 := ((47738409017856979387 : Rat) / 1600000000000000000000), LB := ((1022358167199977 : Rat) / 2000000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((439215643589285714731 : Rat) / 160000000000000000000), R := ((4396259075089285718871 : Rat) / 1600000000000000000000), D0 := ((4396259075089285718871 : Rat) / 1600000000000000000000), D1 := ((1488298915089285718871 : Rat) / 1600000000000000000000), D2 := ((303563075089285718871 : Rat) / 1600000000000000000000), D3 := ((127181815089285718391 : Rat) / 1600000000000000000000), D4 := ((21817884910714203913 : Rat) / 800000000000000000000), LB := ((986380883076357 : Rat) / 250000000000000000) },
  { w1 := ((9189273727476001 : Rat) / 10000000000000000), w2 := ((4745623717054629 : Rat) / 100000000000000000), w3 := ((7366056140907719 : Rat) / 50000000000000000), w4 := ((13778216259028853 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((26681732875000000003 : Rat) / 10000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4396259075089285718871 : Rat) / 1600000000000000000000), R := ((17188912946428571447 : Rat) / 6250000000000000000), D0 := ((17188912946428571447 : Rat) / 6250000000000000000), D1 := ((5829693571428571447 : Rat) / 6250000000000000000), D2 := ((1201819196428571447 : Rat) / 6250000000000000000), D3 := ((4102639196428571561 : Rat) / 50000000000000000000), D4 := ((7906626124999967253 : Rat) / 320000000000000000000), LB := ((1754629407923991 : Rat) / 200000000000000000) }
]

def block344RightChunk000L : Rat := ((17500305803571428601 : Rat) / 10000000000000000000)
def block344RightChunk000R : Rat := ((17188912946428571447 : Rat) / 6250000000000000000)

def block344RightChunk000Certificate : Bool :=
  allBoxesValid block344RightChunk000 &&
  coversFromBool block344RightChunk000 block344RightChunk000L block344RightChunk000R

theorem block344RightChunk000Certificate_eq_true :
    block344RightChunk000Certificate = true := by
  native_decide

def block344RightChainCertificate : Bool :=
  decide (
    block344RightL = ((17500305803571428601 : Rat) / 10000000000000000000) /\
    ((17188912946428571447 : Rat) / 6250000000000000000) = block344RightR)

theorem block344RightChainCertificate_eq_true :
    block344RightChainCertificate = true := by
  native_decide

def block344LeftBoxCount : Nat := boxCount block344LeftBoxes
def block344RightBoxCount : Nat := 60

def block344_rational_certificate : Prop :=
    block344LeftCertificate = true /\
    block344RightChainCertificate = true /\
    block344RightChunk000Certificate = true

theorem block344_rational_certificate_proof :
    block344_rational_certificate := by
  exact ⟨block344LeftCertificate_eq_true, block344RightChainCertificate_eq_true, block344RightChunk000Certificate_eq_true⟩

end Block344
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block344

open Set

def block344W1 : Rat := ((9189273727476001 : Rat) / 10000000000000000)
def block344W2 : Rat := ((4745623717054629 : Rat) / 100000000000000000)
def block344W3 : Rat := ((7366056140907719 : Rat) / 50000000000000000)
def block344W4 : Rat := ((13778216259028853 : Rat) / 100000000000000000)
def block344S1 : Rat := ((18174751 : Rat) / 10000000)
def block344S2 : Rat := ((511587 : Rat) / 200000)
def block344S3 : Rat := ((26681732875000000003 : Rat) / 10000000000000000000)
def block344S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block344V (y : ℝ) : ℝ :=
  ratPotential block344W1 block344W2 block344W3 block344W4 block344S1 block344S2 block344S3 block344S4 y

def block344LeftParamsCertificate : Bool :=
  allBoxesSameParams block344LeftBoxes block344W1 block344W2 block344W3 block344W4 block344S1 block344S2 block344S3 block344S4

theorem block344LeftParamsCertificate_eq_true :
    block344LeftParamsCertificate = true := by
  native_decide

theorem block344_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block344LeftL : ℝ) (block344LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block344S1 : ℝ))
    (hy2ne : y ≠ (block344S2 : ℝ))
    (hy3ne : y ≠ (block344S3 : ℝ))
    (hy4ne : y ≠ (block344S4 : ℝ)) :
    0 < block344V y := by
  have hcert := block344LeftCertificate_eq_true
  unfold block344LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block344LeftBoxes) (lo := block344LeftL) (hi := block344LeftR)
    (w1 := block344W1) (w2 := block344W2) (w3 := block344W3) (w4 := block344W4)
    (s1 := block344S1) (s2 := block344S2) (s3 := block344S3) (s4 := block344S4)
    hboxes hcover block344LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block344RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block344RightChunk000 block344W1 block344W2 block344W3 block344W4 block344S1 block344S2 block344S3 block344S4

theorem block344RightChunk000ParamsCertificate_eq_true :
    block344RightChunk000ParamsCertificate = true := by
  native_decide

theorem block344_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block344RightChunk000L : ℝ) (block344RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block344S1 : ℝ))
    (hy2ne : y ≠ (block344S2 : ℝ))
    (hy3ne : y ≠ (block344S3 : ℝ))
    (hy4ne : y ≠ (block344S4 : ℝ)) :
    0 < block344V y := by
  have hcert := block344RightChunk000Certificate_eq_true
  unfold block344RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block344RightChunk000) (lo := block344RightChunk000L) (hi := block344RightChunk000R)
    (w1 := block344W1) (w2 := block344W2) (w3 := block344W3) (w4 := block344W4)
    (s1 := block344S1) (s2 := block344S2) (s3 := block344S3) (s4 := block344S4)
    hboxes hcover block344RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block344_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block344RightL : ℝ) (block344RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block344S1 : ℝ))
    (hy2ne : y ≠ (block344S2 : ℝ))
    (hy3ne : y ≠ (block344S3 : ℝ))
    (hy4ne : y ≠ (block344S4 : ℝ)) :
    0 < block344V y := by
  have hL : (block344RightChunk000L : ℝ) = (block344RightL : ℝ) := by
    norm_num [block344RightChunk000L, block344RightL]
  have hR : (block344RightChunk000R : ℝ) = (block344RightR : ℝ) := by
    norm_num [block344RightChunk000R, block344RightR]
  have hyc : y ∈ Icc (block344RightChunk000L : ℝ) (block344RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block344_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block344_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block344LeftL : ℝ) (block344LeftR : ℝ) →
    y ≠ 0 → y ≠ (block344S1 : ℝ) → y ≠ (block344S2 : ℝ) →
    y ≠ (block344S3 : ℝ) → y ≠ (block344S4 : ℝ) → 0 < block344V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block344RightL : ℝ) (block344RightR : ℝ) →
    y ≠ 0 → y ≠ (block344S1 : ℝ) → y ≠ (block344S2 : ℝ) →
    y ≠ (block344S3 : ℝ) → y ≠ (block344S4 : ℝ) → 0 < block344V y)

theorem block344_reallog_certificate_proof :
    block344_reallog_certificate := by
  exact ⟨block344_left_V_pos, block344_right_V_pos⟩

end Block344
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block344.block344V
#check Erdos1038Lean.M1817475.Block344.block344_left_V_pos
#check Erdos1038Lean.M1817475.Block344.block344_right_V_pos
#check Erdos1038Lean.M1817475.Block344.block344_reallog_certificate_proof
