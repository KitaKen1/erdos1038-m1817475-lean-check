/-
Self-contained Lean4Web paste file.
Block 332 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block332

def block332LeftL : Rat := ((37618823660714285857 : Rat) / 50000000000000000000)
def block332LeftR : Rat := ((9407149553571428607 : Rat) / 12500000000000000000)
def block332RightL : Rat := ((87618823660714285857 : Rat) / 50000000000000000000)
def block332RightR : Rat := ((34407149553571428607 : Rat) / 12500000000000000000)

def block332LeftBoxes : List RatBox := [
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37618823660714285857 : Rat) / 50000000000000000000), R := ((9407149553571428607 : Rat) / 12500000000000000000), D0 := ((9407149553571428607 : Rat) / 12500000000000000000), D1 := ((53254931339285714143 : Rat) / 50000000000000000000), D2 := ((90277926339285714143 : Rat) / 50000000000000000000), D3 := ((48012214999999999931 : Rat) / 25000000000000000000), D4 := ((100999682767857137741 : Rat) / 50000000000000000000), LB := ((65156172777181 : Rat) / 10000000000000000) }
]

def block332LeftCertificate : Bool :=
  allBoxesValid block332LeftBoxes &&
  coversFromBool block332LeftBoxes block332LeftL block332LeftR

theorem block332LeftCertificate_eq_true :
    block332LeftCertificate = true := by
  native_decide

def block332RightChunk000 : List RatBox := [
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87618823660714285857 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3254931339285714143 : Rat) / 50000000000000000000), D2 := ((40277926339285714143 : Rat) / 50000000000000000000), D3 := ((23012214999999999931 : Rat) / 25000000000000000000), D4 := ((50999682767857137741 : Rat) / 50000000000000000000), LB := ((20040455762007703 : Rat) / 10000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42769498660714285719 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((1992980112521123 : Rat) / 10000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24258001160714285719 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((3212658522703661 : Rat) / 25000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19630126785714285719 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((8599239507415703 : Rat) / 100000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17316189598214285719 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((12123872110053481 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((15002252410714285719 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((4431445361357711 : Rat) / 200000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13845283816964285719 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((15060142246999253 : Rat) / 10000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12688315223214285719 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((3631232461917447 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((12109830926339285719 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((23403831956853027 : Rat) / 100000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11531346629464285719 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((5422178881159201 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11242104481026785719 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((73267784944063 : Rat) / 25000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10952862332589285719 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((3964098805311067 : Rat) / 5000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10663620184151785719 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((886323502330999 : Rat) / 200000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10518999109933035719 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((1838383286477313 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10374378035714285719 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((30246620876815677 : Rat) / 10000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10229756961495535719 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((24788790225039603 : Rat) / 10000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((10085135887276785719 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((10216523886940887 : Rat) / 5000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9940514813058035719 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((172217805667213 : Rat) / 100000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9795893738839285719 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((3800335866438187 : Rat) / 2500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9651272664620535719 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((14422594215822149 : Rat) / 10000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9506651590401785719 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((3735381690163353 : Rat) / 2500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9362030516183035719 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((4205006421662827 : Rat) / 2500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9217409441964285719 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((5031692795782819 : Rat) / 2500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((9072788367745535719 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((1558645789867287 : Rat) / 625000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8928167293526785719 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((3134050082048201 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8783546219308035719 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((1971496242184137 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8638925145089285719 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((2465807133519529 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((8494304070870535719 : Rat) / 50000000000000000000), D4 := ((6734778419363836799 : Rat) / 25000000000000000000), LB := ((3056206289082153 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8349682996651785719 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((300131794399687 : Rat) / 125000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((8060440848214285719 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((11800139039233437 : Rat) / 2000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7771198699776785719 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((1046554986107559 : Rat) / 100000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7481956551339285719 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((6405585498775679 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6903472254464285719 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((1821995261436693 : Rat) / 400000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028920503660714285719 : Rat) / 400000000000000000000), D0 := ((1028920503660714285719 : Rat) / 400000000000000000000), D1 := ((301930463660714285719 : Rat) / 400000000000000000000), D2 := ((5746503660714285719 : Rat) / 400000000000000000000), D3 := ((5746503660714285719 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((4374394259819317 : Rat) / 100000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028920503660714285719 : Rat) / 400000000000000000000), R := ((517333503660714285719 : Rat) / 200000000000000000000), D0 := ((517333503660714285719 : Rat) / 200000000000000000000), D1 := ((153838483660714285719 : Rat) / 200000000000000000000), D2 := ((5746503660714285719 : Rat) / 200000000000000000000), D3 := ((40225525625000000033 : Rat) / 400000000000000000000), D4 := ((16005509553571420613 : Rat) / 80000000000000000000), LB := ((8173771339478733 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517333503660714285719 : Rat) / 200000000000000000000), R := ((1040413510982142857157 : Rat) / 400000000000000000000), D0 := ((1040413510982142857157 : Rat) / 400000000000000000000), D1 := ((313423470982142857157 : Rat) / 400000000000000000000), D2 := ((17239510982142857157 : Rat) / 400000000000000000000), D3 := ((17239510982142857157 : Rat) / 200000000000000000000), D4 := ((37140522053571408673 : Rat) / 200000000000000000000), LB := ((3286286160574539 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1040413510982142857157 : Rat) / 400000000000000000000), R := ((261540003660714285719 : Rat) / 100000000000000000000), D0 := ((261540003660714285719 : Rat) / 100000000000000000000), D1 := ((79792493660714285719 : Rat) / 100000000000000000000), D2 := ((5746503660714285719 : Rat) / 100000000000000000000), D3 := ((5746503660714285719 : Rat) / 80000000000000000000), D4 := ((68534540446428531627 : Rat) / 400000000000000000000), LB := ((1517272696199079 : Rat) / 200000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261540003660714285719 : Rat) / 100000000000000000000), R := ((210381303660714285719 : Rat) / 80000000000000000000), D0 := ((210381303660714285719 : Rat) / 80000000000000000000), D1 := ((64983295660714285719 : Rat) / 80000000000000000000), D2 := ((5746503660714285719 : Rat) / 80000000000000000000), D3 := ((5746503660714285719 : Rat) / 100000000000000000000), D4 := ((15697009196428561477 : Rat) / 100000000000000000000), LB := ((150631543372441 : Rat) / 8000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((210381303660714285719 : Rat) / 80000000000000000000), R := ((528826510982142857157 : Rat) / 200000000000000000000), D0 := ((528826510982142857157 : Rat) / 200000000000000000000), D1 := ((165331490982142857157 : Rat) / 200000000000000000000), D2 := ((17239510982142857157 : Rat) / 200000000000000000000), D3 := ((17239510982142857157 : Rat) / 400000000000000000000), D4 := ((57041533124999960189 : Rat) / 400000000000000000000), LB := ((8554073218994973 : Rat) / 200000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528826510982142857157 : Rat) / 200000000000000000000), R := ((133643253660714285719 : Rat) / 50000000000000000000), D0 := ((133643253660714285719 : Rat) / 50000000000000000000), D1 := ((42769498660714285719 : Rat) / 50000000000000000000), D2 := ((5746503660714285719 : Rat) / 50000000000000000000), D3 := ((5746503660714285719 : Rat) / 200000000000000000000), D4 := ((5129502946428567447 : Rat) / 40000000000000000000), LB := ((11802314315870699 : Rat) / 200000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133643253660714285719 : Rat) / 50000000000000000000), R := ((107711671839285714317 : Rat) / 40000000000000000000), D0 := ((107711671839285714317 : Rat) / 40000000000000000000), D1 := ((35012667839285714317 : Rat) / 40000000000000000000), D2 := ((5394271839285714317 : Rat) / 40000000000000000000), D3 := ((3985344553571428709 : Rat) / 200000000000000000000), D4 := ((4975252767857137879 : Rat) / 50000000000000000000), LB := ((10969944712167573 : Rat) / 100000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((107711671839285714317 : Rat) / 40000000000000000000), R := ((271271851875000000147 : Rat) / 100000000000000000000), D0 := ((271271851875000000147 : Rat) / 100000000000000000000), D1 := ((89524341875000000147 : Rat) / 100000000000000000000), D2 := ((15478351875000000147 : Rat) / 100000000000000000000), D3 := ((3985344553571428709 : Rat) / 100000000000000000000), D4 := ((15915666517857122807 : Rat) / 200000000000000000000), LB := ((10635080293877941 : Rat) / 2000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((271271851875000000147 : Rat) / 100000000000000000000), R := ((434832031910714285977 : Rat) / 160000000000000000000), D0 := ((434832031910714285977 : Rat) / 160000000000000000000), D1 := ((144036015910714285977 : Rat) / 160000000000000000000), D2 := ((25562431910714285977 : Rat) / 160000000000000000000), D3 := ((35868100982142858381 : Rat) / 800000000000000000000), D4 := ((5965160982142847049 : Rat) / 100000000000000000000), LB := ((961920410914377 : Rat) / 50000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((434832031910714285977 : Rat) / 160000000000000000000), R := ((1089072752053571429297 : Rat) / 400000000000000000000), D0 := ((1089072752053571429297 : Rat) / 400000000000000000000), D1 := ((362082712053571429297 : Rat) / 400000000000000000000), D2 := ((65898752053571429297 : Rat) / 400000000000000000000), D3 := ((3985344553571428709 : Rat) / 80000000000000000000), D4 := ((43735943303571347683 : Rat) / 800000000000000000000), LB := ((7507244509341593 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1089072752053571429297 : Rat) / 400000000000000000000), R := ((4360276352767857145897 : Rat) / 1600000000000000000000), D0 := ((4360276352767857145897 : Rat) / 1600000000000000000000), D1 := ((1452316192767857145897 : Rat) / 1600000000000000000000), D2 := ((267580352767857145897 : Rat) / 1600000000000000000000), D3 := ((83692235625000002889 : Rat) / 1600000000000000000000), D4 := ((19875299374999959487 : Rat) / 400000000000000000000), LB := ((145955983323281 : Rat) / 15625000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4360276352767857145897 : Rat) / 1600000000000000000000), R := ((2182130848660714287303 : Rat) / 800000000000000000000), D0 := ((2182130848660714287303 : Rat) / 800000000000000000000), D1 := ((728150768660714287303 : Rat) / 800000000000000000000), D2 := ((135782848660714287303 : Rat) / 800000000000000000000), D3 := ((43838790089285715799 : Rat) / 800000000000000000000), D4 := ((75515852946428409239 : Rat) / 1600000000000000000000), LB := ((5480900323869553 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2182130848660714287303 : Rat) / 800000000000000000000), R := ((873649408375000000663 : Rat) / 320000000000000000000), D0 := ((873649408375000000663 : Rat) / 320000000000000000000), D1 := ((292057376375000000663 : Rat) / 320000000000000000000), D2 := ((55110208375000000663 : Rat) / 320000000000000000000), D3 := ((91662924732142860307 : Rat) / 1600000000000000000000), D4 := ((7153050839285698053 : Rat) / 160000000000000000000), LB := ((5795946002739999 : Rat) / 2500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((873649408375000000663 : Rat) / 320000000000000000000), R := ((8740479428303571435339 : Rat) / 3200000000000000000000), D0 := ((8740479428303571435339 : Rat) / 3200000000000000000000), D1 := ((2924559108303571435339 : Rat) / 3200000000000000000000), D2 := ((555087428303571435339 : Rat) / 3200000000000000000000), D3 := ((187311194017857149323 : Rat) / 3200000000000000000000), D4 := ((67545163839285551821 : Rat) / 1600000000000000000000), LB := ((12460979442327491 : Rat) / 2500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8740479428303571435339 : Rat) / 3200000000000000000000), R := ((546529048303571429003 : Rat) / 200000000000000000000), D0 := ((546529048303571429003 : Rat) / 200000000000000000000), D1 := ((183034028303571429003 : Rat) / 200000000000000000000), D2 := ((34942048303571429003 : Rat) / 200000000000000000000), D3 := ((11956033660714286127 : Rat) / 200000000000000000000), D4 := ((131104983124999674933 : Rat) / 3200000000000000000000), LB := ((3971301767752067 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546529048303571429003 : Rat) / 200000000000000000000), R := ((8748450117410714292757 : Rat) / 3200000000000000000000), D0 := ((8748450117410714292757 : Rat) / 3200000000000000000000), D1 := ((2932529797410714292757 : Rat) / 3200000000000000000000), D2 := ((563058117410714292757 : Rat) / 3200000000000000000000), D3 := ((195281883125000006741 : Rat) / 3200000000000000000000), D4 := ((7944977410714265389 : Rat) / 200000000000000000000), LB := ((1575824587152469 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8748450117410714292757 : Rat) / 3200000000000000000000), R := ((4376217730982142860733 : Rat) / 1600000000000000000000), D0 := ((4376217730982142860733 : Rat) / 1600000000000000000000), D1 := ((1468257570982142860733 : Rat) / 1600000000000000000000), D2 := ((283521730982142860733 : Rat) / 1600000000000000000000), D3 := ((3985344553571428709 : Rat) / 64000000000000000000), D4 := ((24626858803571363503 : Rat) / 640000000000000000000), LB := ((1581833195625007 : Rat) / 625000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4376217730982142860733 : Rat) / 1600000000000000000000), R := ((350256832260714286007 : Rat) / 128000000000000000000), D0 := ((350256832260714286007 : Rat) / 128000000000000000000), D1 := ((117620019460714286007 : Rat) / 128000000000000000000), D2 := ((22841152260714286007 : Rat) / 128000000000000000000), D3 := ((203252572232142864159 : Rat) / 3200000000000000000000), D4 := ((59574474732142694403 : Rat) / 1600000000000000000000), LB := ((2115599682681879 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((350256832260714286007 : Rat) / 128000000000000000000), R := ((2190101537767857144721 : Rat) / 800000000000000000000), D0 := ((2190101537767857144721 : Rat) / 800000000000000000000), D1 := ((736121457767857144721 : Rat) / 800000000000000000000), D2 := ((143753537767857144721 : Rat) / 800000000000000000000), D3 := ((51809479196428573217 : Rat) / 800000000000000000000), D4 := ((115163604910713960097 : Rat) / 3200000000000000000000), LB := ((19131386670178663 : Rat) / 10000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190101537767857144721 : Rat) / 800000000000000000000), R := ((8764391495625000007593 : Rat) / 3200000000000000000000), D0 := ((8764391495625000007593 : Rat) / 3200000000000000000000), D1 := ((2948471175625000007593 : Rat) / 3200000000000000000000), D2 := ((578999495625000007593 : Rat) / 3200000000000000000000), D3 := ((211223261339285721577 : Rat) / 3200000000000000000000), D4 := ((27794565089285632847 : Rat) / 800000000000000000000), LB := ((19322004424799921 : Rat) / 10000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8764391495625000007593 : Rat) / 3200000000000000000000), R := ((4384188420089285718151 : Rat) / 1600000000000000000000), D0 := ((4384188420089285718151 : Rat) / 1600000000000000000000), D1 := ((1476228260089285718151 : Rat) / 1600000000000000000000), D2 := ((291492420089285718151 : Rat) / 1600000000000000000000), D3 := ((107604302946428575143 : Rat) / 1600000000000000000000), D4 := ((107192915803571102679 : Rat) / 3200000000000000000000), LB := ((2182737151833203 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4384188420089285718151 : Rat) / 1600000000000000000000), R := ((8772362184732142865011 : Rat) / 3200000000000000000000), D0 := ((8772362184732142865011 : Rat) / 3200000000000000000000), D1 := ((2956441864732142865011 : Rat) / 3200000000000000000000), D2 := ((586970184732142865011 : Rat) / 3200000000000000000000), D3 := ((43838790089285715799 : Rat) / 640000000000000000000), D4 := ((10320757124999967397 : Rat) / 320000000000000000000), LB := ((26761733294777823 : Rat) / 10000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8772362184732142865011 : Rat) / 3200000000000000000000), R := ((219408688232142857343 : Rat) / 80000000000000000000), D0 := ((219408688232142857343 : Rat) / 80000000000000000000), D1 := ((74010680232142857343 : Rat) / 80000000000000000000), D2 := ((14773888232142857343 : Rat) / 80000000000000000000), D3 := ((27897411875000000963 : Rat) / 400000000000000000000), D4 := ((99222226696428245261 : Rat) / 3200000000000000000000), LB := ((685122527827331 : Rat) / 200000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((219408688232142857343 : Rat) / 80000000000000000000), R := ((8780332873839285722429 : Rat) / 3200000000000000000000), D0 := ((8780332873839285722429 : Rat) / 3200000000000000000000), D1 := ((2964412553839285722429 : Rat) / 3200000000000000000000), D2 := ((594940873839285722429 : Rat) / 3200000000000000000000), D3 := ((227164639553571436413 : Rat) / 3200000000000000000000), D4 := ((11904610267857102069 : Rat) / 400000000000000000000), LB := ((4446089335505221 : Rat) / 1000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8780332873839285722429 : Rat) / 3200000000000000000000), R := ((4392159109196428575569 : Rat) / 1600000000000000000000), D0 := ((4392159109196428575569 : Rat) / 1600000000000000000000), D1 := ((1484198949196428575569 : Rat) / 1600000000000000000000), D2 := ((299463109196428575569 : Rat) / 1600000000000000000000), D3 := ((115574992053571432561 : Rat) / 1600000000000000000000), D4 := ((91251537589285387843 : Rat) / 3200000000000000000000), LB := ((1438718918519849 : Rat) / 250000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4392159109196428575569 : Rat) / 1600000000000000000000), R := ((2198072226875000002139 : Rat) / 800000000000000000000), D0 := ((2198072226875000002139 : Rat) / 800000000000000000000), D1 := ((744092146875000002139 : Rat) / 800000000000000000000), D2 := ((151724226875000002139 : Rat) / 800000000000000000000), D3 := ((11956033660714286127 : Rat) / 160000000000000000000), D4 := ((43633096517856979567 : Rat) / 1600000000000000000000), LB := ((1460289299396983 : Rat) / 500000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2198072226875000002139 : Rat) / 800000000000000000000), R := ((4400129798303571432987 : Rat) / 1600000000000000000000), D0 := ((4400129798303571432987 : Rat) / 1600000000000000000000), D1 := ((1492169638303571432987 : Rat) / 1600000000000000000000), D2 := ((307433798303571432987 : Rat) / 1600000000000000000000), D3 := ((123545681160714289979 : Rat) / 1600000000000000000000), D4 := ((19823875982142775429 : Rat) / 800000000000000000000), LB := ((36306295352047657 : Rat) / 5000000000000000000) },
  { w1 := ((9451693809362539 : Rat) / 10000000000000000), w2 := ((4722103213713541 : Rat) / 100000000000000000), w3 := ((7200413462786287 : Rat) / 50000000000000000), w4 := ((27380479480649 : Rat) / 200000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133643253660714285719 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4400129798303571432987 : Rat) / 1600000000000000000000), R := ((34407149553571428607 : Rat) / 12500000000000000000), D0 := ((34407149553571428607 : Rat) / 12500000000000000000), D1 := ((11688710803571428607 : Rat) / 12500000000000000000), D2 := ((2432962053571428607 : Rat) / 12500000000000000000), D3 := ((3985344553571428709 : Rat) / 50000000000000000000), D4 := ((35662407410714122149 : Rat) / 1600000000000000000000), LB := ((13157660850942277 : Rat) / 1000000000000000000) }
]

def block332RightChunk000L : Rat := ((87618823660714285857 : Rat) / 50000000000000000000)
def block332RightChunk000R : Rat := ((34407149553571428607 : Rat) / 12500000000000000000)

def block332RightChunk000Certificate : Bool :=
  allBoxesValid block332RightChunk000 &&
  coversFromBool block332RightChunk000 block332RightChunk000L block332RightChunk000R

theorem block332RightChunk000Certificate_eq_true :
    block332RightChunk000Certificate = true := by
  native_decide

def block332RightChainCertificate : Bool :=
  decide (
    block332RightL = ((87618823660714285857 : Rat) / 50000000000000000000) /\
    ((34407149553571428607 : Rat) / 12500000000000000000) = block332RightR)

theorem block332RightChainCertificate_eq_true :
    block332RightChainCertificate = true := by
  native_decide

def block332LeftBoxCount : Nat := boxCount block332LeftBoxes
def block332RightBoxCount : Nat := 62

def block332_rational_certificate : Prop :=
    block332LeftCertificate = true /\
    block332RightChainCertificate = true /\
    block332RightChunk000Certificate = true

theorem block332_rational_certificate_proof :
    block332_rational_certificate := by
  exact ⟨block332LeftCertificate_eq_true, block332RightChainCertificate_eq_true, block332RightChunk000Certificate_eq_true⟩

end Block332
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block332

open Set

def block332W1 : Rat := ((9451693809362539 : Rat) / 10000000000000000)
def block332W2 : Rat := ((4722103213713541 : Rat) / 100000000000000000)
def block332W3 : Rat := ((7200413462786287 : Rat) / 50000000000000000)
def block332W4 : Rat := ((27380479480649 : Rat) / 200000000000000)
def block332S1 : Rat := ((18174751 : Rat) / 10000000)
def block332S2 : Rat := ((511587 : Rat) / 200000)
def block332S3 : Rat := ((133643253660714285719 : Rat) / 50000000000000000000)
def block332S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block332V (y : ℝ) : ℝ :=
  ratPotential block332W1 block332W2 block332W3 block332W4 block332S1 block332S2 block332S3 block332S4 y

def block332LeftParamsCertificate : Bool :=
  allBoxesSameParams block332LeftBoxes block332W1 block332W2 block332W3 block332W4 block332S1 block332S2 block332S3 block332S4

theorem block332LeftParamsCertificate_eq_true :
    block332LeftParamsCertificate = true := by
  native_decide

theorem block332_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block332LeftL : ℝ) (block332LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block332S1 : ℝ))
    (hy2ne : y ≠ (block332S2 : ℝ))
    (hy3ne : y ≠ (block332S3 : ℝ))
    (hy4ne : y ≠ (block332S4 : ℝ)) :
    0 < block332V y := by
  have hcert := block332LeftCertificate_eq_true
  unfold block332LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block332LeftBoxes) (lo := block332LeftL) (hi := block332LeftR)
    (w1 := block332W1) (w2 := block332W2) (w3 := block332W3) (w4 := block332W4)
    (s1 := block332S1) (s2 := block332S2) (s3 := block332S3) (s4 := block332S4)
    hboxes hcover block332LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block332RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block332RightChunk000 block332W1 block332W2 block332W3 block332W4 block332S1 block332S2 block332S3 block332S4

theorem block332RightChunk000ParamsCertificate_eq_true :
    block332RightChunk000ParamsCertificate = true := by
  native_decide

theorem block332_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block332RightChunk000L : ℝ) (block332RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block332S1 : ℝ))
    (hy2ne : y ≠ (block332S2 : ℝ))
    (hy3ne : y ≠ (block332S3 : ℝ))
    (hy4ne : y ≠ (block332S4 : ℝ)) :
    0 < block332V y := by
  have hcert := block332RightChunk000Certificate_eq_true
  unfold block332RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block332RightChunk000) (lo := block332RightChunk000L) (hi := block332RightChunk000R)
    (w1 := block332W1) (w2 := block332W2) (w3 := block332W3) (w4 := block332W4)
    (s1 := block332S1) (s2 := block332S2) (s3 := block332S3) (s4 := block332S4)
    hboxes hcover block332RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block332_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block332RightL : ℝ) (block332RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block332S1 : ℝ))
    (hy2ne : y ≠ (block332S2 : ℝ))
    (hy3ne : y ≠ (block332S3 : ℝ))
    (hy4ne : y ≠ (block332S4 : ℝ)) :
    0 < block332V y := by
  have hL : (block332RightChunk000L : ℝ) = (block332RightL : ℝ) := by
    norm_num [block332RightChunk000L, block332RightL]
  have hR : (block332RightChunk000R : ℝ) = (block332RightR : ℝ) := by
    norm_num [block332RightChunk000R, block332RightR]
  have hyc : y ∈ Icc (block332RightChunk000L : ℝ) (block332RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block332_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block332_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block332LeftL : ℝ) (block332LeftR : ℝ) →
    y ≠ 0 → y ≠ (block332S1 : ℝ) → y ≠ (block332S2 : ℝ) →
    y ≠ (block332S3 : ℝ) → y ≠ (block332S4 : ℝ) → 0 < block332V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block332RightL : ℝ) (block332RightR : ℝ) →
    y ≠ 0 → y ≠ (block332S1 : ℝ) → y ≠ (block332S2 : ℝ) →
    y ≠ (block332S3 : ℝ) → y ≠ (block332S4 : ℝ) → 0 < block332V y)

theorem block332_reallog_certificate_proof :
    block332_reallog_certificate := by
  exact ⟨block332_left_V_pos, block332_right_V_pos⟩

end Block332
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block332.block332V
#check Erdos1038Lean.M1817475.Block332.block332_left_V_pos
#check Erdos1038Lean.M1817475.Block332.block332_right_V_pos
#check Erdos1038Lean.M1817475.Block332.block332_reallog_certificate_proof
