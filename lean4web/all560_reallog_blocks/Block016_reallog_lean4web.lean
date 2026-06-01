/-
Self-contained Lean4Web paste file.
Block 16 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block016

def block016LeftL : Rat := ((40707582589285714293 : Rat) / 50000000000000000000)
def block016LeftR : Rat := ((2544834821428571429 : Rat) / 3125000000000000000)
def block016RightL : Rat := ((90707582589285714293 : Rat) / 50000000000000000000)
def block016RightR : Rat := ((8794834821428571429 : Rat) / 3125000000000000000)

def block016LeftBoxes : List RatBox := [
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((40707582589285714293 : Rat) / 50000000000000000000), R := ((2544834821428571429 : Rat) / 3125000000000000000), D0 := ((2544834821428571429 : Rat) / 3125000000000000000), D1 := ((50166172410714285707 : Rat) / 50000000000000000000), D2 := ((87189167410714285707 : Rat) / 50000000000000000000), D3 := ((93043191160714285707 : Rat) / 50000000000000000000), D4 := ((100706446160714280611 : Rat) / 50000000000000000000), LB := ((3625917302327447 : Rat) / 1000000000000000000) }
]

def block016LeftCertificate : Bool :=
  allBoxesValid block016LeftBoxes &&
  coversFromBool block016LeftBoxes block016LeftL block016LeftR

theorem block016LeftCertificate_eq_true :
    block016LeftCertificate = true := by
  native_decide

def block016RightChunk000 : List RatBox := [
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((90707582589285714293 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((166172410714285707 : Rat) / 50000000000000000000), D2 := ((37189167410714285707 : Rat) / 50000000000000000000), D3 := ((43043191160714285707 : Rat) / 50000000000000000000), D4 := ((50706446160714280611 : Rat) / 50000000000000000000), LB := ((4725114991256889 : Rat) / 100000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((18174751 : Rat) / 10000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((6860323 : Rat) / 8000000), D4 := ((6317534218749999363 : Rat) / 6250000000000000000), LB := ((15996983491349073 : Rat) / 10000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((511587 : Rat) / 200000), R := ((107000619 : Rat) / 40000000), D0 := ((107000619 : Rat) / 40000000), D1 := ((6860323 : Rat) / 8000000), D2 := ((4683219 : Rat) / 40000000), D3 := ((4683219 : Rat) / 40000000), D4 := ((1689659843749999363 : Rat) / 6250000000000000000), LB := ((6404246553691681 : Rat) / 10000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((107000619 : Rat) / 40000000), R := ((17154258180803571429 : Rat) / 6250000000000000000), D0 := ((17154258180803571429 : Rat) / 6250000000000000000), D1 := ((5795038805803571429 : Rat) / 6250000000000000000), D2 := ((1167164430803571429 : Rat) / 6250000000000000000), D3 := ((435411462053571429 : Rat) / 6250000000000000000), D4 := ((957906874999999363 : Rat) / 6250000000000000000), LB := ((94835011091701 : Rat) / 1000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((17154258180803571429 : Rat) / 6250000000000000000), R := ((13810488837053571429 : Rat) / 5000000000000000000), D0 := ((13810488837053571429 : Rat) / 5000000000000000000), D1 := ((4723113337053571429 : Rat) / 5000000000000000000), D2 := ((1020813837053571429 : Rat) / 5000000000000000000), D3 := ((435411462053571429 : Rat) / 5000000000000000000), D4 := ((261247706473213967 : Rat) / 3125000000000000000), LB := ((203636694122237 : Rat) / 2500000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((13810488837053571429 : Rat) / 5000000000000000000), R := ((138540299832589285719 : Rat) / 50000000000000000000), D0 := ((138540299832589285719 : Rat) / 50000000000000000000), D1 := ((47666544832589285719 : Rat) / 50000000000000000000), D2 := ((10643549832589285719 : Rat) / 50000000000000000000), D3 := ((4789526082589285719 : Rat) / 50000000000000000000), D4 := ((1654570189732140307 : Rat) / 25000000000000000000), LB := ((5863685925292461 : Rat) / 100000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((138540299832589285719 : Rat) / 50000000000000000000), R := ((34743927823660714287 : Rat) / 12500000000000000000), D0 := ((34743927823660714287 : Rat) / 12500000000000000000), D1 := ((12025489073660714287 : Rat) / 12500000000000000000), D2 := ((2769740323660714287 : Rat) / 12500000000000000000), D3 := ((1306234386160714287 : Rat) / 12500000000000000000), D4 := ((574745783482141837 : Rat) / 10000000000000000000), LB := ((6790743783245179 : Rat) / 500000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((34743927823660714287 : Rat) / 12500000000000000000), R := ((11135473362053571429 : Rat) / 4000000000000000000), D0 := ((11135473362053571429 : Rat) / 4000000000000000000), D1 := ((3865572962053571429 : Rat) / 4000000000000000000), D2 := ((903733362053571429 : Rat) / 4000000000000000000), D3 := ((435411462053571429 : Rat) / 4000000000000000000), D4 := ((609579363839284439 : Rat) / 12500000000000000000), LB := ((2915156604231961 : Rat) / 200000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((11135473362053571429 : Rat) / 4000000000000000000), R := ((557209079564732142879 : Rat) / 200000000000000000000), D0 := ((557209079564732142879 : Rat) / 200000000000000000000), D1 := ((193714059564732142879 : Rat) / 200000000000000000000), D2 := ((45622079564732142879 : Rat) / 200000000000000000000), D3 := ((22205984564732142879 : Rat) / 200000000000000000000), D4 := ((4441223448660704083 : Rat) / 100000000000000000000), LB := ((1795971340169833 : Rat) / 100000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((557209079564732142879 : Rat) / 200000000000000000000), R := ((139411122756696428577 : Rat) / 50000000000000000000), D0 := ((139411122756696428577 : Rat) / 50000000000000000000), D1 := ((48537367756696428577 : Rat) / 50000000000000000000), D2 := ((11514372756696428577 : Rat) / 50000000000000000000), D3 := ((5660349006696428577 : Rat) / 50000000000000000000), D4 := ((8447035435267836737 : Rat) / 200000000000000000000), LB := ((66596969231867 : Rat) / 6250000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((139411122756696428577 : Rat) / 50000000000000000000), R := ((558079902488839285737 : Rat) / 200000000000000000000), D0 := ((558079902488839285737 : Rat) / 200000000000000000000), D1 := ((194584882488839285737 : Rat) / 200000000000000000000), D2 := ((46492902488839285737 : Rat) / 200000000000000000000), D3 := ((23076807488839285737 : Rat) / 200000000000000000000), D4 := ((2002905993303566327 : Rat) / 50000000000000000000), LB := ((2027201366023579 : Rat) / 500000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((558079902488839285737 : Rat) / 200000000000000000000), R := ((1116595216439732142903 : Rat) / 400000000000000000000), D0 := ((1116595216439732142903 : Rat) / 400000000000000000000), D1 := ((389605176439732142903 : Rat) / 400000000000000000000), D2 := ((93421216439732142903 : Rat) / 400000000000000000000), D3 := ((46589026439732142903 : Rat) / 400000000000000000000), D4 := ((7576212511160693879 : Rat) / 200000000000000000000), LB := ((4033626193770179 : Rat) / 500000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((1116595216439732142903 : Rat) / 400000000000000000000), R := ((279257656975446428583 : Rat) / 100000000000000000000), D0 := ((279257656975446428583 : Rat) / 100000000000000000000), D1 := ((97510146975446428583 : Rat) / 100000000000000000000), D2 := ((23464156975446428583 : Rat) / 100000000000000000000), D3 := ((11756109475446428583 : Rat) / 100000000000000000000), D4 := ((14717013560267816329 : Rat) / 400000000000000000000), LB := ((5462104766875697 : Rat) / 1000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((279257656975446428583 : Rat) / 100000000000000000000), R := ((1117466039363839285761 : Rat) / 400000000000000000000), D0 := ((1117466039363839285761 : Rat) / 400000000000000000000), D1 := ((390475999363839285761 : Rat) / 400000000000000000000), D2 := ((94292039363839285761 : Rat) / 400000000000000000000), D3 := ((47459849363839285761 : Rat) / 400000000000000000000), D4 := ((142816020982142449 : Rat) / 4000000000000000000), LB := ((3084861217357293 : Rat) / 1000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((1117466039363839285761 : Rat) / 400000000000000000000), R := ((111790145082589285719 : Rat) / 40000000000000000000), D0 := ((111790145082589285719 : Rat) / 40000000000000000000), D1 := ((39091141082589285719 : Rat) / 40000000000000000000), D2 := ((9472745082589285719 : Rat) / 40000000000000000000), D3 := ((4789526082589285719 : Rat) / 40000000000000000000), D4 := ((13846190636160673471 : Rat) / 400000000000000000000), LB := ((9489507904554273 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((111790145082589285719 : Rat) / 40000000000000000000), R := ((2236238313113839285809 : Rat) / 800000000000000000000), D0 := ((2236238313113839285809 : Rat) / 800000000000000000000), D1 := ((782258233113839285809 : Rat) / 800000000000000000000), D2 := ((189890313113839285809 : Rat) / 800000000000000000000), D3 := ((96225933113839285809 : Rat) / 800000000000000000000), D4 := ((6705389587053551021 : Rat) / 200000000000000000000), LB := ((794079718022811 : Rat) / 200000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2236238313113839285809 : Rat) / 800000000000000000000), R := ((1118336862287946428619 : Rat) / 400000000000000000000), D0 := ((1118336862287946428619 : Rat) / 400000000000000000000), D1 := ((391346822287946428619 : Rat) / 400000000000000000000), D2 := ((95162862287946428619 : Rat) / 400000000000000000000), D3 := ((48330672287946428619 : Rat) / 400000000000000000000), D4 := ((5277229377232126531 : Rat) / 160000000000000000000), LB := ((7822067963534629 : Rat) / 2500000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((1118336862287946428619 : Rat) / 400000000000000000000), R := ((2237109136037946428667 : Rat) / 800000000000000000000), D0 := ((2237109136037946428667 : Rat) / 800000000000000000000), D1 := ((783129056037946428667 : Rat) / 800000000000000000000), D2 := ((190761136037946428667 : Rat) / 800000000000000000000), D3 := ((97096756037946428667 : Rat) / 800000000000000000000), D4 := ((12975367712053530613 : Rat) / 400000000000000000000), LB := ((11787317189207447 : Rat) / 5000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2237109136037946428667 : Rat) / 800000000000000000000), R := ((69923267109375000003 : Rat) / 25000000000000000000), D0 := ((69923267109375000003 : Rat) / 25000000000000000000), D1 := ((24486389609375000003 : Rat) / 25000000000000000000), D2 := ((5974892109375000003 : Rat) / 25000000000000000000), D3 := ((3047880234375000003 : Rat) / 25000000000000000000), D4 := ((25515323962053489797 : Rat) / 800000000000000000000), LB := ((3317181188187579 : Rat) / 2000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((69923267109375000003 : Rat) / 25000000000000000000), R := ((89519198358482142861 : Rat) / 32000000000000000000), D0 := ((89519198358482142861 : Rat) / 32000000000000000000), D1 := ((31359995158482142861 : Rat) / 32000000000000000000), D2 := ((7665278358482142861 : Rat) / 32000000000000000000), D3 := ((3918703158482142861 : Rat) / 32000000000000000000), D4 := ((783747265624997449 : Rat) / 25000000000000000000), LB := ((10346099622728921 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((89519198358482142861 : Rat) / 32000000000000000000), R := ((1119207685212053571477 : Rat) / 400000000000000000000), D0 := ((1119207685212053571477 : Rat) / 400000000000000000000), D1 := ((392217645212053571477 : Rat) / 400000000000000000000), D2 := ((96033685212053571477 : Rat) / 400000000000000000000), D3 := ((49201495212053571477 : Rat) / 400000000000000000000), D4 := ((24644501037946346939 : Rat) / 800000000000000000000), LB := ((2440245913971073 : Rat) / 5000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((1119207685212053571477 : Rat) / 400000000000000000000), R := ((2238850781886160714383 : Rat) / 800000000000000000000), D0 := ((2238850781886160714383 : Rat) / 800000000000000000000), D1 := ((784870701886160714383 : Rat) / 800000000000000000000), D2 := ((192502781886160714383 : Rat) / 800000000000000000000), D3 := ((98838401886160714383 : Rat) / 800000000000000000000), D4 := ((2420908957589277551 : Rat) / 80000000000000000000), LB := ((21571236447304187 : Rat) / 1000000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2238850781886160714383 : Rat) / 800000000000000000000), R := ((895627395046875000039 : Rat) / 320000000000000000000), D0 := ((895627395046875000039 : Rat) / 320000000000000000000), D1 := ((314035363046875000039 : Rat) / 320000000000000000000), D2 := ((77088195046875000039 : Rat) / 320000000000000000000), D3 := ((39622443046875000039 : Rat) / 320000000000000000000), D4 := ((23773678113839204081 : Rat) / 800000000000000000000), LB := ((2080362953039039 : Rat) / 1000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((895627395046875000039 : Rat) / 320000000000000000000), R := ((559821548337053571453 : Rat) / 200000000000000000000), D0 := ((559821548337053571453 : Rat) / 200000000000000000000), D1 := ((196326528337053571453 : Rat) / 200000000000000000000), D2 := ((48234548337053571453 : Rat) / 200000000000000000000), D3 := ((24818453337053571453 : Rat) / 200000000000000000000), D4 := ((47111944765624836733 : Rat) / 1600000000000000000000), LB := ((19199139534810117 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((559821548337053571453 : Rat) / 200000000000000000000), R := ((4479007798158482143053 : Rat) / 1600000000000000000000), D0 := ((4479007798158482143053 : Rat) / 1600000000000000000000), D1 := ((1571047638158482143053 : Rat) / 1600000000000000000000), D2 := ((386311798158482143053 : Rat) / 1600000000000000000000), D3 := ((198983038158482143053 : Rat) / 1600000000000000000000), D4 := ((5834566662946408163 : Rat) / 200000000000000000000), LB := ((3562624770789391 : Rat) / 2000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((4479007798158482143053 : Rat) / 1600000000000000000000), R := ((2239721604810267857241 : Rat) / 800000000000000000000), D0 := ((2239721604810267857241 : Rat) / 800000000000000000000), D1 := ((785741524810267857241 : Rat) / 800000000000000000000), D2 := ((193373604810267857241 : Rat) / 800000000000000000000), D3 := ((99709224810267857241 : Rat) / 800000000000000000000), D4 := ((369928974732141551 : Rat) / 12800000000000000000), LB := ((3329910079932663 : Rat) / 2000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2239721604810267857241 : Rat) / 800000000000000000000), R := ((4479878621082589285911 : Rat) / 1600000000000000000000), D0 := ((4479878621082589285911 : Rat) / 1600000000000000000000), D1 := ((1571918461082589285911 : Rat) / 1600000000000000000000), D2 := ((387182621082589285911 : Rat) / 1600000000000000000000), D3 := ((199853861082589285911 : Rat) / 1600000000000000000000), D4 := ((22902855189732061223 : Rat) / 800000000000000000000), LB := ((1571249980745093 : Rat) / 1000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((4479878621082589285911 : Rat) / 1600000000000000000000), R := ((224015701627232142867 : Rat) / 80000000000000000000), D0 := ((224015701627232142867 : Rat) / 80000000000000000000), D1 := ((78617693627232142867 : Rat) / 80000000000000000000), D2 := ((19380901627232142867 : Rat) / 80000000000000000000), D3 := ((10014463627232142867 : Rat) / 80000000000000000000), D4 := ((45370298917410551017 : Rat) / 1600000000000000000000), LB := ((15006169742453057 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((224015701627232142867 : Rat) / 80000000000000000000), R := ((4480749444006696428769 : Rat) / 1600000000000000000000), D0 := ((4480749444006696428769 : Rat) / 1600000000000000000000), D1 := ((1572789284006696428769 : Rat) / 1600000000000000000000), D2 := ((388053444006696428769 : Rat) / 1600000000000000000000), D3 := ((200724684006696428769 : Rat) / 1600000000000000000000), D4 := ((11233721863839244897 : Rat) / 400000000000000000000), LB := ((2906975882634999 : Rat) / 2000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((4480749444006696428769 : Rat) / 1600000000000000000000), R := ((2240592427734375000099 : Rat) / 800000000000000000000), D0 := ((2240592427734375000099 : Rat) / 800000000000000000000), D1 := ((786612347734375000099 : Rat) / 800000000000000000000), D2 := ((194244427734375000099 : Rat) / 800000000000000000000), D3 := ((100580047734375000099 : Rat) / 800000000000000000000), D4 := ((44499475993303408159 : Rat) / 1600000000000000000000), LB := ((446971072021983 : Rat) / 312500000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2240592427734375000099 : Rat) / 800000000000000000000), R := ((4481620266930803571627 : Rat) / 1600000000000000000000), D0 := ((4481620266930803571627 : Rat) / 1600000000000000000000), D1 := ((1573660106930803571627 : Rat) / 1600000000000000000000), D2 := ((388924266930803571627 : Rat) / 1600000000000000000000), D3 := ((201595506930803571627 : Rat) / 1600000000000000000000), D4 := ((4406406453124983673 : Rat) / 160000000000000000000), LB := ((14315331144649779 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((4481620266930803571627 : Rat) / 1600000000000000000000), R := ((280128479899553571441 : Rat) / 100000000000000000000), D0 := ((280128479899553571441 : Rat) / 100000000000000000000), D1 := ((98380969899553571441 : Rat) / 100000000000000000000), D2 := ((24334979899553571441 : Rat) / 100000000000000000000), D3 := ((12626932399553571441 : Rat) / 100000000000000000000), D4 := ((43628653069196265301 : Rat) / 1600000000000000000000), LB := ((3644090778855691 : Rat) / 2500000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((280128479899553571441 : Rat) / 100000000000000000000), R := ((896498217970982142897 : Rat) / 320000000000000000000), D0 := ((896498217970982142897 : Rat) / 320000000000000000000), D1 := ((314906185970982142897 : Rat) / 320000000000000000000), D2 := ((77959017970982142897 : Rat) / 320000000000000000000), D3 := ((40493265970982142897 : Rat) / 320000000000000000000), D4 := ((2699577600446418367 : Rat) / 100000000000000000000), LB := ((7545512663921783 : Rat) / 5000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((896498217970982142897 : Rat) / 320000000000000000000), R := ((2241463250658482142957 : Rat) / 800000000000000000000), D0 := ((2241463250658482142957 : Rat) / 800000000000000000000), D1 := ((787483170658482142957 : Rat) / 800000000000000000000), D2 := ((195115250658482142957 : Rat) / 800000000000000000000), D3 := ((101450870658482142957 : Rat) / 800000000000000000000), D4 := ((42757830145089122443 : Rat) / 1600000000000000000000), LB := ((15864320571812307 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2241463250658482142957 : Rat) / 800000000000000000000), R := ((4483361912779017857343 : Rat) / 1600000000000000000000), D0 := ((4483361912779017857343 : Rat) / 1600000000000000000000), D1 := ((1575401752779017857343 : Rat) / 1600000000000000000000), D2 := ((390665912779017857343 : Rat) / 1600000000000000000000), D3 := ((203337152779017857343 : Rat) / 1600000000000000000000), D4 := ((21161209341517775507 : Rat) / 800000000000000000000), LB := ((4126319668219 : Rat) / 2441406250000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((4483361912779017857343 : Rat) / 1600000000000000000000), R := ((1120949331060267857193 : Rat) / 400000000000000000000), D0 := ((1120949331060267857193 : Rat) / 400000000000000000000), D1 := ((393959291060267857193 : Rat) / 400000000000000000000), D2 := ((97775331060267857193 : Rat) / 400000000000000000000), D3 := ((50943141060267857193 : Rat) / 400000000000000000000), D4 := ((8377401444196395917 : Rat) / 320000000000000000000), LB := ((3641519258021697 : Rat) / 2000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((1120949331060267857193 : Rat) / 400000000000000000000), R := ((4484232735703125000201 : Rat) / 1600000000000000000000), D0 := ((4484232735703125000201 : Rat) / 1600000000000000000000), D1 := ((1576272575703125000201 : Rat) / 1600000000000000000000), D2 := ((391536735703125000201 : Rat) / 1600000000000000000000), D3 := ((204207975703125000201 : Rat) / 1600000000000000000000), D4 := ((10362898939732102039 : Rat) / 400000000000000000000), LB := ((1236773545212691 : Rat) / 625000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((4484232735703125000201 : Rat) / 1600000000000000000000), R := ((448466814716517857163 : Rat) / 160000000000000000000), D0 := ((448466814716517857163 : Rat) / 160000000000000000000), D1 := ((157670798716517857163 : Rat) / 160000000000000000000), D2 := ((39197214716517857163 : Rat) / 160000000000000000000), D3 := ((20464338716517857163 : Rat) / 160000000000000000000), D4 := ((41016184296874836727 : Rat) / 1600000000000000000000), LB := ((10824701918320523 : Rat) / 5000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((448466814716517857163 : Rat) / 160000000000000000000), R := ((4485103558627232143059 : Rat) / 1600000000000000000000), D0 := ((4485103558627232143059 : Rat) / 1600000000000000000000), D1 := ((1577143398627232143059 : Rat) / 1600000000000000000000), D2 := ((392407558627232143059 : Rat) / 1600000000000000000000), D3 := ((205078798627232143059 : Rat) / 1600000000000000000000), D4 := ((20290386417410632649 : Rat) / 800000000000000000000), LB := ((2974564504235333 : Rat) / 1250000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((4485103558627232143059 : Rat) / 1600000000000000000000), R := ((560692371261160714311 : Rat) / 200000000000000000000), D0 := ((560692371261160714311 : Rat) / 200000000000000000000), D1 := ((197197351261160714311 : Rat) / 200000000000000000000), D2 := ((49105371261160714311 : Rat) / 200000000000000000000), D3 := ((25689276261160714311 : Rat) / 200000000000000000000), D4 := ((40145361372767693869 : Rat) / 1600000000000000000000), LB := ((1311787038202783 : Rat) / 500000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((560692371261160714311 : Rat) / 200000000000000000000), R := ((2243204896506696428673 : Rat) / 800000000000000000000), D0 := ((2243204896506696428673 : Rat) / 800000000000000000000), D1 := ((789224816506696428673 : Rat) / 800000000000000000000), D2 := ((196856896506696428673 : Rat) / 800000000000000000000), D3 := ((103192516506696428673 : Rat) / 800000000000000000000), D4 := ((992748747767853061 : Rat) / 40000000000000000000), LB := ((11669183447723941 : Rat) / 25000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2243204896506696428673 : Rat) / 800000000000000000000), R := ((1121820153984375000051 : Rat) / 400000000000000000000), D0 := ((1121820153984375000051 : Rat) / 400000000000000000000), D1 := ((394830113984375000051 : Rat) / 400000000000000000000), D2 := ((98646153984375000051 : Rat) / 400000000000000000000), D3 := ((51813963984375000051 : Rat) / 400000000000000000000), D4 := ((19419563493303489791 : Rat) / 800000000000000000000), LB := ((346150128045751 : Rat) / 312500000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((1121820153984375000051 : Rat) / 400000000000000000000), R := ((2244075719430803571531 : Rat) / 800000000000000000000), D0 := ((2244075719430803571531 : Rat) / 800000000000000000000), D1 := ((790095639430803571531 : Rat) / 800000000000000000000), D2 := ((197727719430803571531 : Rat) / 800000000000000000000), D3 := ((104063339430803571531 : Rat) / 800000000000000000000), D4 := ((9492076015624959181 : Rat) / 400000000000000000000), LB := ((1875929408166943 : Rat) / 1000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2244075719430803571531 : Rat) / 800000000000000000000), R := ((28056389136160714287 : Rat) / 10000000000000000000), D0 := ((28056389136160714287 : Rat) / 10000000000000000000), D1 := ((9881638136160714287 : Rat) / 10000000000000000000), D2 := ((2477039136160714287 : Rat) / 10000000000000000000), D3 := ((1306234386160714287 : Rat) / 10000000000000000000), D4 := ((18548740569196346933 : Rat) / 800000000000000000000), LB := ((13886498083488519 : Rat) / 5000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((28056389136160714287 : Rat) / 10000000000000000000), R := ((2244946542354910714389 : Rat) / 800000000000000000000), D0 := ((2244946542354910714389 : Rat) / 800000000000000000000), D1 := ((790966462354910714389 : Rat) / 800000000000000000000), D2 := ((198598542354910714389 : Rat) / 800000000000000000000), D3 := ((104934162354910714389 : Rat) / 800000000000000000000), D4 := ((1132083069196423469 : Rat) / 50000000000000000000), LB := ((38179887128730883 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((2244946542354910714389 : Rat) / 800000000000000000000), R := ((1122690976908482142909 : Rat) / 400000000000000000000), D0 := ((1122690976908482142909 : Rat) / 400000000000000000000), D1 := ((395700936908482142909 : Rat) / 400000000000000000000), D2 := ((99516976908482142909 : Rat) / 400000000000000000000), D3 := ((52684786908482142909 : Rat) / 400000000000000000000), D4 := ((707116705803568163 : Rat) / 32000000000000000000), LB := ((500464685824209 : Rat) / 100000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((1122690976908482142909 : Rat) / 400000000000000000000), R := ((561563194185267857169 : Rat) / 200000000000000000000), D0 := ((561563194185267857169 : Rat) / 200000000000000000000), D1 := ((198068174185267857169 : Rat) / 200000000000000000000), D2 := ((49976194185267857169 : Rat) / 200000000000000000000), D3 := ((26560099185267857169 : Rat) / 200000000000000000000), D4 := ((8621253091517816323 : Rat) / 400000000000000000000), LB := ((15008673934979733 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((561563194185267857169 : Rat) / 200000000000000000000), R := ((1123561799832589285767 : Rat) / 400000000000000000000), D0 := ((1123561799832589285767 : Rat) / 400000000000000000000), D1 := ((396571759832589285767 : Rat) / 400000000000000000000), D2 := ((100387799832589285767 : Rat) / 400000000000000000000), D3 := ((53555609832589285767 : Rat) / 400000000000000000000), D4 := ((4092920814732122447 : Rat) / 200000000000000000000), LB := ((1169084796111497 : Rat) / 250000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((1123561799832589285767 : Rat) / 400000000000000000000), R := ((280999302823660714299 : Rat) / 100000000000000000000), D0 := ((280999302823660714299 : Rat) / 100000000000000000000), D1 := ((99251792823660714299 : Rat) / 100000000000000000000), D2 := ((25205802823660714299 : Rat) / 100000000000000000000), D3 := ((13497755323660714299 : Rat) / 100000000000000000000), D4 := ((1550086033482134693 : Rat) / 80000000000000000000), LB := ((4282447204108031 : Rat) / 500000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((280999302823660714299 : Rat) / 100000000000000000000), R := ((562434017109375000027 : Rat) / 200000000000000000000), D0 := ((562434017109375000027 : Rat) / 200000000000000000000), D1 := ((198938997109375000027 : Rat) / 200000000000000000000), D2 := ((50847017109375000027 : Rat) / 200000000000000000000), D3 := ((27430922109375000027 : Rat) / 200000000000000000000), D4 := ((1828754676339275509 : Rat) / 100000000000000000000), LB := ((35994101292282643 : Rat) / 10000000000000000000) },
  { w1 := ((845824143343439 : Rat) / 100000000000000), w2 := (0 : Rat), w3 := (0 : Rat), w4 := ((4960924743124191 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((107000619 : Rat) / 40000000), s4 := ((17676753593749999363 : Rat) / 6250000000000000000), L := ((562434017109375000027 : Rat) / 200000000000000000000), R := ((8794834821428571429 : Rat) / 3125000000000000000), D0 := ((8794834821428571429 : Rat) / 3125000000000000000), D1 := ((3115225133928571429 : Rat) / 3125000000000000000), D2 := ((801287946428571429 : Rat) / 3125000000000000000), D3 := ((435411462053571429 : Rat) / 3125000000000000000), D4 := ((3222097890624979589 : Rat) / 200000000000000000000), LB := ((3943042444056577 : Rat) / 250000000000000000) }
]

def block016RightChunk000L : Rat := ((90707582589285714293 : Rat) / 50000000000000000000)
def block016RightChunk000R : Rat := ((8794834821428571429 : Rat) / 3125000000000000000)

def block016RightChunk000Certificate : Bool :=
  allBoxesValid block016RightChunk000 &&
  coversFromBool block016RightChunk000 block016RightChunk000L block016RightChunk000R

theorem block016RightChunk000Certificate_eq_true :
    block016RightChunk000Certificate = true := by
  native_decide

def block016RightChainCertificate : Bool :=
  decide (
    block016RightL = ((90707582589285714293 : Rat) / 50000000000000000000) /\
    ((8794834821428571429 : Rat) / 3125000000000000000) = block016RightR)

theorem block016RightChainCertificate_eq_true :
    block016RightChainCertificate = true := by
  native_decide

def block016LeftBoxCount : Nat := boxCount block016LeftBoxes
def block016RightBoxCount : Nat := 51

def block016_rational_certificate : Prop :=
    block016LeftCertificate = true /\
    block016RightChainCertificate = true /\
    block016RightChunk000Certificate = true

theorem block016_rational_certificate_proof :
    block016_rational_certificate := by
  exact ⟨block016LeftCertificate_eq_true, block016RightChainCertificate_eq_true, block016RightChunk000Certificate_eq_true⟩

end Block016
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block016

open Set

def block016W1 : Rat := ((845824143343439 : Rat) / 100000000000000)
def block016W2 : Rat := (0 : Rat)
def block016W3 : Rat := (0 : Rat)
def block016W4 : Rat := ((4960924743124191 : Rat) / 20000000000000000)
def block016S1 : Rat := ((18174751 : Rat) / 10000000)
def block016S2 : Rat := ((511587 : Rat) / 200000)
def block016S3 : Rat := ((107000619 : Rat) / 40000000)
def block016S4 : Rat := ((17676753593749999363 : Rat) / 6250000000000000000)

noncomputable def block016V (y : ℝ) : ℝ :=
  ratPotential block016W1 block016W2 block016W3 block016W4 block016S1 block016S2 block016S3 block016S4 y

def block016LeftParamsCertificate : Bool :=
  allBoxesSameParams block016LeftBoxes block016W1 block016W2 block016W3 block016W4 block016S1 block016S2 block016S3 block016S4

theorem block016LeftParamsCertificate_eq_true :
    block016LeftParamsCertificate = true := by
  native_decide

theorem block016_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block016LeftL : ℝ) (block016LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block016S1 : ℝ))
    (hy2ne : y ≠ (block016S2 : ℝ))
    (hy3ne : y ≠ (block016S3 : ℝ))
    (hy4ne : y ≠ (block016S4 : ℝ)) :
    0 < block016V y := by
  have hcert := block016LeftCertificate_eq_true
  unfold block016LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block016LeftBoxes) (lo := block016LeftL) (hi := block016LeftR)
    (w1 := block016W1) (w2 := block016W2) (w3 := block016W3) (w4 := block016W4)
    (s1 := block016S1) (s2 := block016S2) (s3 := block016S3) (s4 := block016S4)
    hboxes hcover block016LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block016RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block016RightChunk000 block016W1 block016W2 block016W3 block016W4 block016S1 block016S2 block016S3 block016S4

theorem block016RightChunk000ParamsCertificate_eq_true :
    block016RightChunk000ParamsCertificate = true := by
  native_decide

theorem block016_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block016RightChunk000L : ℝ) (block016RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block016S1 : ℝ))
    (hy2ne : y ≠ (block016S2 : ℝ))
    (hy3ne : y ≠ (block016S3 : ℝ))
    (hy4ne : y ≠ (block016S4 : ℝ)) :
    0 < block016V y := by
  have hcert := block016RightChunk000Certificate_eq_true
  unfold block016RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block016RightChunk000) (lo := block016RightChunk000L) (hi := block016RightChunk000R)
    (w1 := block016W1) (w2 := block016W2) (w3 := block016W3) (w4 := block016W4)
    (s1 := block016S1) (s2 := block016S2) (s3 := block016S3) (s4 := block016S4)
    hboxes hcover block016RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block016_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block016RightL : ℝ) (block016RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block016S1 : ℝ))
    (hy2ne : y ≠ (block016S2 : ℝ))
    (hy3ne : y ≠ (block016S3 : ℝ))
    (hy4ne : y ≠ (block016S4 : ℝ)) :
    0 < block016V y := by
  have hL : (block016RightChunk000L : ℝ) = (block016RightL : ℝ) := by
    norm_num [block016RightChunk000L, block016RightL]
  have hR : (block016RightChunk000R : ℝ) = (block016RightR : ℝ) := by
    norm_num [block016RightChunk000R, block016RightR]
  have hyc : y ∈ Icc (block016RightChunk000L : ℝ) (block016RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block016_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block016_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block016LeftL : ℝ) (block016LeftR : ℝ) →
    y ≠ 0 → y ≠ (block016S1 : ℝ) → y ≠ (block016S2 : ℝ) →
    y ≠ (block016S3 : ℝ) → y ≠ (block016S4 : ℝ) → 0 < block016V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block016RightL : ℝ) (block016RightR : ℝ) →
    y ≠ 0 → y ≠ (block016S1 : ℝ) → y ≠ (block016S2 : ℝ) →
    y ≠ (block016S3 : ℝ) → y ≠ (block016S4 : ℝ) → 0 < block016V y)

theorem block016_reallog_certificate_proof :
    block016_reallog_certificate := by
  exact ⟨block016_left_V_pos, block016_right_V_pos⟩

end Block016
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block016.block016V
#check Erdos1038Lean.M1817475.Block016.block016_left_V_pos
#check Erdos1038Lean.M1817475.Block016.block016_right_V_pos
#check Erdos1038Lean.M1817475.Block016.block016_reallog_certificate_proof
