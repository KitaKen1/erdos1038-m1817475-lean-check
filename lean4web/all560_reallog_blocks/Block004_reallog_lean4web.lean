/-
Self-contained Lean4Web paste file.
Block 4 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block004

def block004LeftL : Rat := ((8164975446428571429 : Rat) / 10000000000000000000)
def block004LeftR : Rat := ((10208662946428571429 : Rat) / 12500000000000000000)
def block004RightL : Rat := ((18164975446428571429 : Rat) / 10000000000000000000)
def block004RightR : Rat := ((35208662946428571429 : Rat) / 12500000000000000000)

def block004LeftBoxes : List RatBox := [
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((8164975446428571429 : Rat) / 10000000000000000000), R := ((10208662946428571429 : Rat) / 12500000000000000000), D0 := ((10208662946428571429 : Rat) / 12500000000000000000), D1 := ((10009775553571428571 : Rat) / 10000000000000000000), D2 := ((17414374553571428571 : Rat) / 10000000000000000000), D3 := ((18585179303571428571 : Rat) / 10000000000000000000), D4 := ((20149108874999998979 : Rat) / 10000000000000000000), LB := ((15869547665191913 : Rat) / 1000000000000000000) }
]

def block004LeftCertificate : Bool :=
  allBoxesValid block004LeftBoxes &&
  coversFromBool block004LeftBoxes block004LeftL block004LeftR

theorem block004LeftCertificate_eq_true :
    block004LeftCertificate = true := by
  native_decide

def block004RightChunk000 : List RatBox := [
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18164975446428571429 : Rat) / 10000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((9775553571428571 : Rat) / 10000000000000000000), D2 := ((7414374553571428571 : Rat) / 10000000000000000000), D3 := ((8585179303571428571 : Rat) / 10000000000000000000), D4 := ((10149108874999998979 : Rat) / 10000000000000000000), LB := ((497098673518793 : Rat) / 6250000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((1267416665178571301 : Rat) / 1250000000000000000), LB := ((27828447468443933 : Rat) / 10000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((341841790178571301 : Rat) / 1250000000000000000), LB := ((12444660688251699 : Rat) / 10000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((68646356383928571429 : Rat) / 25000000000000000000), D0 := ((68646356383928571429 : Rat) / 25000000000000000000), D1 := ((23209478883928571429 : Rat) / 25000000000000000000), D2 := ((4697981383928571429 : Rat) / 25000000000000000000), D3 := ((1770969508928571429 : Rat) / 25000000000000000000), D4 := ((195491196428571301 : Rat) / 1250000000000000000), LB := ((37345201955271057 : Rat) / 100000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((68646356383928571429 : Rat) / 25000000000000000000), R := ((139063682276785714287 : Rat) / 50000000000000000000), D0 := ((139063682276785714287 : Rat) / 50000000000000000000), D1 := ((48189927276785714287 : Rat) / 50000000000000000000), D2 := ((11166932276785714287 : Rat) / 50000000000000000000), D3 := ((5312908526785714287 : Rat) / 50000000000000000000), D4 := ((2138854419642854591 : Rat) / 25000000000000000000), LB := ((4667515490235863 : Rat) / 100000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((139063682276785714287 : Rat) / 50000000000000000000), R := ((558025698616071428577 : Rat) / 200000000000000000000), D0 := ((558025698616071428577 : Rat) / 200000000000000000000), D1 := ((194530678616071428577 : Rat) / 200000000000000000000), D2 := ((46438698616071428577 : Rat) / 200000000000000000000), D3 := ((23022603616071428577 : Rat) / 200000000000000000000), D4 := ((2506739330357137753 : Rat) / 50000000000000000000), LB := ((3161583568726567 : Rat) / 50000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((558025698616071428577 : Rat) / 200000000000000000000), R := ((1117822366741071428583 : Rat) / 400000000000000000000), D0 := ((1117822366741071428583 : Rat) / 400000000000000000000), D1 := ((390832326741071428583 : Rat) / 400000000000000000000), D2 := ((94648366741071428583 : Rat) / 400000000000000000000), D3 := ((47816176741071428583 : Rat) / 400000000000000000000), D4 := ((8255987812499979583 : Rat) / 200000000000000000000), LB := ((10749321538430423 : Rat) / 200000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1117822366741071428583 : Rat) / 400000000000000000000), R := ((279898334062500000003 : Rat) / 100000000000000000000), D0 := ((279898334062500000003 : Rat) / 100000000000000000000), D1 := ((98150824062500000003 : Rat) / 100000000000000000000), D2 := ((24104834062500000003 : Rat) / 100000000000000000000), D3 := ((12396786562500000003 : Rat) / 100000000000000000000), D4 := ((14741006116071387737 : Rat) / 400000000000000000000), LB := ((6092641320665143 : Rat) / 250000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((279898334062500000003 : Rat) / 100000000000000000000), R := ((2240957642008928571453 : Rat) / 800000000000000000000), D0 := ((2240957642008928571453 : Rat) / 800000000000000000000), D1 := ((786977562008928571453 : Rat) / 800000000000000000000), D2 := ((194609642008928571453 : Rat) / 800000000000000000000), D3 := ((100945262008928571453 : Rat) / 800000000000000000000), D4 := ((3242509151785704077 : Rat) / 100000000000000000000), LB := ((6882456309071111 : Rat) / 250000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2240957642008928571453 : Rat) / 800000000000000000000), R := ((1121364305758928571441 : Rat) / 400000000000000000000), D0 := ((1121364305758928571441 : Rat) / 400000000000000000000), D1 := ((394374265758928571441 : Rat) / 400000000000000000000), D2 := ((98190305758928571441 : Rat) / 400000000000000000000), D3 := ((51358115758928571441 : Rat) / 400000000000000000000), D4 := ((24169103705357061187 : Rat) / 800000000000000000000), LB := ((2060636120716483 : Rat) / 125000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1121364305758928571441 : Rat) / 400000000000000000000), R := ((2244499581026785714311 : Rat) / 800000000000000000000), D0 := ((2244499581026785714311 : Rat) / 800000000000000000000), D1 := ((790519501026785714311 : Rat) / 800000000000000000000), D2 := ((198151581026785714311 : Rat) / 800000000000000000000), D3 := ((104487201026785714311 : Rat) / 800000000000000000000), D4 := ((11199067098214244879 : Rat) / 400000000000000000000), LB := ((1711121768807361 : Rat) / 250000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2244499581026785714311 : Rat) / 800000000000000000000), R := ((4490770131562500000051 : Rat) / 1600000000000000000000), D0 := ((4490770131562500000051 : Rat) / 1600000000000000000000), D1 := ((1582809971562500000051 : Rat) / 1600000000000000000000), D2 := ((398074131562500000051 : Rat) / 1600000000000000000000), D3 := ((210745371562500000051 : Rat) / 1600000000000000000000), D4 := ((20627164687499918329 : Rat) / 800000000000000000000), LB := ((654379199608579 : Rat) / 50000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4490770131562500000051 : Rat) / 1600000000000000000000), R := ((112313527526785714287 : Rat) / 40000000000000000000), D0 := ((112313527526785714287 : Rat) / 40000000000000000000), D1 := ((39614523526785714287 : Rat) / 40000000000000000000), D2 := ((9996127526785714287 : Rat) / 40000000000000000000), D3 := ((5312908526785714287 : Rat) / 40000000000000000000), D4 := ((39483359866071265229 : Rat) / 1600000000000000000000), LB := ((9758261794829637 : Rat) / 1000000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((112313527526785714287 : Rat) / 40000000000000000000), R := ((4494312070580357142909 : Rat) / 1600000000000000000000), D0 := ((4494312070580357142909 : Rat) / 1600000000000000000000), D1 := ((1586351910580357142909 : Rat) / 1600000000000000000000), D2 := ((401616070580357142909 : Rat) / 1600000000000000000000), D3 := ((214287310580357142909 : Rat) / 1600000000000000000000), D4 := ((188561951785713469 : Rat) / 8000000000000000000), LB := ((3473109578419009 : Rat) / 500000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4494312070580357142909 : Rat) / 1600000000000000000000), R := ((2248041520044642857169 : Rat) / 800000000000000000000), D0 := ((2248041520044642857169 : Rat) / 800000000000000000000), D1 := ((794061440044642857169 : Rat) / 800000000000000000000), D2 := ((201693520044642857169 : Rat) / 800000000000000000000), D3 := ((108029140044642857169 : Rat) / 800000000000000000000), D4 := ((35941420848214122371 : Rat) / 1600000000000000000000), LB := ((2349845839853759 : Rat) / 500000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2248041520044642857169 : Rat) / 800000000000000000000), R := ((4497854009598214285767 : Rat) / 1600000000000000000000), D0 := ((4497854009598214285767 : Rat) / 1600000000000000000000), D1 := ((1589893849598214285767 : Rat) / 1600000000000000000000), D2 := ((405158009598214285767 : Rat) / 1600000000000000000000), D3 := ((217829249598214285767 : Rat) / 1600000000000000000000), D4 := ((17085225669642775471 : Rat) / 800000000000000000000), LB := ((15371168145317249 : Rat) / 5000000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4497854009598214285767 : Rat) / 1600000000000000000000), R := ((1124906244776785714299 : Rat) / 400000000000000000000), D0 := ((1124906244776785714299 : Rat) / 400000000000000000000), D1 := ((397916204776785714299 : Rat) / 400000000000000000000), D2 := ((101732244776785714299 : Rat) / 400000000000000000000), D3 := ((54900054776785714299 : Rat) / 400000000000000000000), D4 := ((32399481830356979513 : Rat) / 1600000000000000000000), LB := ((10671371626891357 : Rat) / 5000000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((1124906244776785714299 : Rat) / 400000000000000000000), R := ((36011167588928571429 : Rat) / 12800000000000000000), D0 := ((36011167588928571429 : Rat) / 12800000000000000000), D1 := ((12747486308928571429 : Rat) / 12800000000000000000), D2 := ((3269599588928571429 : Rat) / 12800000000000000000), D3 := ((1770969508928571429 : Rat) / 12800000000000000000), D4 := ((7657128080357102021 : Rat) / 400000000000000000000), LB := ((4887774056889227 : Rat) / 2500000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((36011167588928571429 : Rat) / 12800000000000000000), R := ((2251583459062500000027 : Rat) / 800000000000000000000), D0 := ((2251583459062500000027 : Rat) / 800000000000000000000), D1 := ((797603379062500000027 : Rat) / 800000000000000000000), D2 := ((205235459062500000027 : Rat) / 800000000000000000000), D3 := ((111571079062500000027 : Rat) / 800000000000000000000), D4 := ((5771508562499967331 : Rat) / 320000000000000000000), LB := ((26254813504369423 : Rat) / 10000000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((2251583459062500000027 : Rat) / 800000000000000000000), R := ((4504937887633928571483 : Rat) / 1600000000000000000000), D0 := ((4504937887633928571483 : Rat) / 1600000000000000000000), D1 := ((1596977727633928571483 : Rat) / 1600000000000000000000), D2 := ((412241887633928571483 : Rat) / 1600000000000000000000), D3 := ((224913127633928571483 : Rat) / 1600000000000000000000), D4 := ((13543286651785632613 : Rat) / 800000000000000000000), LB := ((212548132352397 : Rat) / 50000000000000000) },
  { w1 := ((1549788951109419 : Rat) / 125000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((1556831174919787 : Rat) / 6250000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((3539260540178571301 : Rat) / 1250000000000000000), L := ((4504937887633928571483 : Rat) / 1600000000000000000000), R := ((35208662946428571429 : Rat) / 12500000000000000000), D0 := ((35208662946428571429 : Rat) / 12500000000000000000), D1 := ((12490224196428571429 : Rat) / 12500000000000000000), D2 := ((3234475446428571429 : Rat) / 12500000000000000000), D3 := ((1770969508928571429 : Rat) / 12500000000000000000), D4 := ((25315603794642693797 : Rat) / 1600000000000000000000), LB := ((3479232289796519 : Rat) / 500000000000000000) }
]

def block004RightChunk000L : Rat := ((18164975446428571429 : Rat) / 10000000000000000000)
def block004RightChunk000R : Rat := ((35208662946428571429 : Rat) / 12500000000000000000)

def block004RightChunk000Certificate : Bool :=
  allBoxesValid block004RightChunk000 &&
  coversFromBool block004RightChunk000 block004RightChunk000L block004RightChunk000R

theorem block004RightChunk000Certificate_eq_true :
    block004RightChunk000Certificate = true := by
  native_decide

def block004RightChainCertificate : Bool :=
  decide (
    block004RightL = ((18164975446428571429 : Rat) / 10000000000000000000) /\
    ((35208662946428571429 : Rat) / 12500000000000000000) = block004RightR)

theorem block004RightChainCertificate_eq_true :
    block004RightChainCertificate = true := by
  native_decide

def block004LeftBoxCount : Nat := boxCount block004LeftBoxes
def block004RightBoxCount : Nat := 21

def block004_rational_certificate : Prop :=
    block004LeftCertificate = true /\
    block004RightChainCertificate = true /\
    block004RightChunk000Certificate = true

theorem block004_rational_certificate_proof :
    block004_rational_certificate := by
  exact ⟨block004LeftCertificate_eq_true, block004RightChainCertificate_eq_true, block004RightChunk000Certificate_eq_true⟩

end Block004
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block004

open Set

def block004W1 : Rat := ((1549788951109419 : Rat) / 125000000000000)
def block004W2 : Rat := (0 : Rat)
def block004W3 : Rat := (0 : Rat)
def block004W4 : Rat := ((1556831174919787 : Rat) / 6250000000000000)
def block004S1 : Rat := ((18174751 : Rat) / 10000000)
def block004S2 : Rat := ((511587 : Rat) / 200000)
def block004S3 : Rat := ((107000619 : Rat) / 40000000)
def block004S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block004V (y : ℝ) : ℝ :=
  ratPotential block004W1 block004W2 block004W3 block004W4 block004S1 block004S2 block004S3 block004S4 y

def block004LeftParamsCertificate : Bool :=
  allBoxesSameParams block004LeftBoxes block004W1 block004W2 block004W3 block004W4 block004S1 block004S2 block004S3 block004S4

theorem block004LeftParamsCertificate_eq_true :
    block004LeftParamsCertificate = true := by
  native_decide

theorem block004_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block004LeftL : ℝ) (block004LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block004S1 : ℝ))
    (hy2ne : y ≠ (block004S2 : ℝ))
    (hy3ne : y ≠ (block004S3 : ℝ))
    (hy4ne : y ≠ (block004S4 : ℝ)) :
    0 < block004V y := by
  have hcert := block004LeftCertificate_eq_true
  unfold block004LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block004LeftBoxes) (lo := block004LeftL) (hi := block004LeftR)
    (w1 := block004W1) (w2 := block004W2) (w3 := block004W3) (w4 := block004W4)
    (s1 := block004S1) (s2 := block004S2) (s3 := block004S3) (s4 := block004S4)
    hboxes hcover block004LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block004RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block004RightChunk000 block004W1 block004W2 block004W3 block004W4 block004S1 block004S2 block004S3 block004S4

theorem block004RightChunk000ParamsCertificate_eq_true :
    block004RightChunk000ParamsCertificate = true := by
  native_decide

theorem block004_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block004RightChunk000L : ℝ) (block004RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block004S1 : ℝ))
    (hy2ne : y ≠ (block004S2 : ℝ))
    (hy3ne : y ≠ (block004S3 : ℝ))
    (hy4ne : y ≠ (block004S4 : ℝ)) :
    0 < block004V y := by
  have hcert := block004RightChunk000Certificate_eq_true
  unfold block004RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block004RightChunk000) (lo := block004RightChunk000L) (hi := block004RightChunk000R)
    (w1 := block004W1) (w2 := block004W2) (w3 := block004W3) (w4 := block004W4)
    (s1 := block004S1) (s2 := block004S2) (s3 := block004S3) (s4 := block004S4)
    hboxes hcover block004RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block004_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block004RightL : ℝ) (block004RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block004S1 : ℝ))
    (hy2ne : y ≠ (block004S2 : ℝ))
    (hy3ne : y ≠ (block004S3 : ℝ))
    (hy4ne : y ≠ (block004S4 : ℝ)) :
    0 < block004V y := by
  have hL : (block004RightChunk000L : ℝ) = (block004RightL : ℝ) := by
    norm_num [block004RightChunk000L, block004RightL]
  have hR : (block004RightChunk000R : ℝ) = (block004RightR : ℝ) := by
    norm_num [block004RightChunk000R, block004RightR]
  have hyc : y ∈ Icc (block004RightChunk000L : ℝ) (block004RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block004_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block004_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block004LeftL : ℝ) (block004LeftR : ℝ) →
    y ≠ 0 → y ≠ (block004S1 : ℝ) → y ≠ (block004S2 : ℝ) →
    y ≠ (block004S3 : ℝ) → y ≠ (block004S4 : ℝ) → 0 < block004V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block004RightL : ℝ) (block004RightR : ℝ) →
    y ≠ 0 → y ≠ (block004S1 : ℝ) → y ≠ (block004S2 : ℝ) →
    y ≠ (block004S3 : ℝ) → y ≠ (block004S4 : ℝ) → 0 < block004V y)

theorem block004_reallog_certificate_proof :
    block004_reallog_certificate := by
  exact ⟨block004_left_V_pos, block004_right_V_pos⟩

end Block004
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block004.block004V
#check Erdos1038Lean.M1817475.Block004.block004_left_V_pos
#check Erdos1038Lean.M1817475.Block004.block004_right_V_pos
#check Erdos1038Lean.M1817475.Block004.block004_reallog_certificate_proof
