/-
Self-contained Lean4Web paste file.
Block 337 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block337

def block337LeftL : Rat := ((18784975446428571501 : Rat) / 25000000000000000000)
def block337LeftR : Rat := ((37579725446428571573 : Rat) / 50000000000000000000)
def block337RightL : Rat := ((43784975446428571501 : Rat) / 25000000000000000000)
def block337RightR : Rat := ((137579725446428571573 : Rat) / 50000000000000000000)

def block337LeftBoxes : List RatBox := [
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18784975446428571501 : Rat) / 25000000000000000000), R := ((37579725446428571573 : Rat) / 50000000000000000000), D0 := ((37579725446428571573 : Rat) / 50000000000000000000), D1 := ((26651902053571428499 : Rat) / 25000000000000000000), D2 := ((45163399553571428499 : Rat) / 25000000000000000000), D3 := ((95975557232142857007 : Rat) / 50000000000000000000), D4 := ((25262138883928570149 : Rat) / 12500000000000000000), LB := ((200557926529071 : Rat) / 31250000000000000) }
]

def block337LeftCertificate : Bool :=
  allBoxesValid block337LeftBoxes &&
  coversFromBool block337LeftBoxes block337LeftL block337LeftR

theorem block337LeftCertificate_eq_true :
    block337LeftCertificate = true := by
  native_decide

def block337RightChunk000 : List RatBox := [
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43784975446428571501 : Rat) / 25000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1651902053571428499 : Rat) / 25000000000000000000), D2 := ((20163399553571428499 : Rat) / 25000000000000000000), D3 := ((45975557232142857007 : Rat) / 50000000000000000000), D4 := ((12762138883928570149 : Rat) / 12500000000000000000), LB := ((392039334537931 : Rat) / 200000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42671753125000000009 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((9448396208030871 : Rat) / 50000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24160255625000000009 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((1523817197974563 : Rat) / 12500000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19532381250000000009 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((8095849687198671 : Rat) / 100000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17218444062500000009 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((10246589669074359 : Rat) / 500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14904506875000000009 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((192378755783173 : Rat) / 10000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13747538281250000009 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((2217715183302993 : Rat) / 100000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((13169053984375000009 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((6642771740683853 : Rat) / 500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12590569687500000009 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((5462247732598707 : Rat) / 1000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((12012085390625000009 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((9840335113810689 : Rat) / 1000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11722843242187500009 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((686780880220117 : Rat) / 100000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11433601093750000009 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((2108865339177507 : Rat) / 500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11144358945312500009 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((3811249260395333 : Rat) / 2000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10855116796875000009 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((1335871978151569 : Rat) / 250000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10710495722656250009 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((1793871344334097 : Rat) / 400000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10565874648437500009 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((9307291694229461 : Rat) / 2500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10421253574218750009 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((3061285180720963 : Rat) / 1000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10276632500000000009 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((78222452950979 : Rat) / 31250000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10132011425781250009 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((2052032582978619 : Rat) / 1000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9987390351562500009 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((17119583658583293 : Rat) / 10000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9842769277343750009 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((7435904165352253 : Rat) / 5000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9698148203125000009 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((13823847997991023 : Rat) / 10000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9553527128906250009 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((3506771822958249 : Rat) / 2500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9408906054687500009 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((15538084271745911 : Rat) / 10000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9264284980468750009 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((9209664532764811 : Rat) / 5000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9119663906250000009 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((4548030742150433 : Rat) / 2000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8975042832031250009 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((571556629421599 : Rat) / 200000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8830421757812500009 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((1800945788992911 : Rat) / 500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8685800683593750009 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((4516088526271639 : Rat) / 1000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8541179609375000009 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((81732118996777 : Rat) / 156250000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8251937460937500009 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((33449150758755597 : Rat) / 10000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7962695312500000009 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((282755519738771 : Rat) / 40000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7673453164062500009 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((11867651924135747 : Rat) / 1000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7384211015625000009 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((1017471734321089 : Rat) / 125000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6805726718750000009 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((87323838541363 : Rat) / 12500000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028822758125000000009 : Rat) / 400000000000000000000), D0 := ((1028822758125000000009 : Rat) / 400000000000000000000), D1 := ((301832718125000000009 : Rat) / 400000000000000000000), D2 := ((5648758125000000009 : Rat) / 400000000000000000000), D3 := ((5648758125000000009 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((4836196077341667 : Rat) / 100000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028822758125000000009 : Rat) / 400000000000000000000), R := ((517235758125000000009 : Rat) / 200000000000000000000), D0 := ((517235758125000000009 : Rat) / 200000000000000000000), D1 := ((153740738125000000009 : Rat) / 200000000000000000000), D2 := ((5648758125000000009 : Rat) / 200000000000000000000), D3 := ((39541306875000000063 : Rat) / 400000000000000000000), D4 := ((3205011732142855551 : Rat) / 16000000000000000000), LB := ((2145873388280481 : Rat) / 100000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517235758125000000009 : Rat) / 200000000000000000000), R := ((1040120274375000000027 : Rat) / 400000000000000000000), D0 := ((1040120274375000000027 : Rat) / 400000000000000000000), D1 := ((313130234375000000027 : Rat) / 400000000000000000000), D2 := ((16946274375000000027 : Rat) / 400000000000000000000), D3 := ((16946274375000000027 : Rat) / 200000000000000000000), D4 := ((37238267589285694383 : Rat) / 200000000000000000000), LB := ((12211635365002443 : Rat) / 1000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1040120274375000000027 : Rat) / 400000000000000000000), R := ((261442258125000000009 : Rat) / 100000000000000000000), D0 := ((261442258125000000009 : Rat) / 100000000000000000000), D1 := ((79694748125000000009 : Rat) / 100000000000000000000), D2 := ((5648758125000000009 : Rat) / 100000000000000000000), D3 := ((5648758125000000009 : Rat) / 80000000000000000000), D4 := ((68827777053571388757 : Rat) / 400000000000000000000), LB := ((275241785003999 : Rat) / 20000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261442258125000000009 : Rat) / 100000000000000000000), R := ((210283558125000000009 : Rat) / 80000000000000000000), D0 := ((210283558125000000009 : Rat) / 80000000000000000000), D1 := ((64885550125000000009 : Rat) / 80000000000000000000), D2 := ((5648758125000000009 : Rat) / 80000000000000000000), D3 := ((5648758125000000009 : Rat) / 100000000000000000000), D4 := ((15794754732142847187 : Rat) / 100000000000000000000), LB := ((1596738499494179 : Rat) / 62500000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((210283558125000000009 : Rat) / 80000000000000000000), R := ((528533274375000000027 : Rat) / 200000000000000000000), D0 := ((528533274375000000027 : Rat) / 200000000000000000000), D1 := ((165038254375000000027 : Rat) / 200000000000000000000), D2 := ((16946274375000000027 : Rat) / 200000000000000000000), D3 := ((16946274375000000027 : Rat) / 400000000000000000000), D4 := ((57530260803571388739 : Rat) / 400000000000000000000), LB := ((5005092231983971 : Rat) / 100000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528533274375000000027 : Rat) / 200000000000000000000), R := ((133545508125000000009 : Rat) / 50000000000000000000), D0 := ((133545508125000000009 : Rat) / 50000000000000000000), D1 := ((42671753125000000009 : Rat) / 50000000000000000000), D2 := ((5648758125000000009 : Rat) / 50000000000000000000), D3 := ((5648758125000000009 : Rat) / 200000000000000000000), D4 := ((5188150267857138873 : Rat) / 40000000000000000000), LB := ((1685029357681403 : Rat) / 25000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133545508125000000009 : Rat) / 50000000000000000000), R := ((1345540624553571429 : Rat) / 500000000000000000), D0 := ((1345540624553571429 : Rat) / 500000000000000000), D1 := ((436803074553571429 : Rat) / 500000000000000000), D2 := ((66573124553571429 : Rat) / 500000000000000000), D3 := ((1008554330357142891 : Rat) / 50000000000000000000), D4 := ((5072998303571423589 : Rat) / 50000000000000000000), LB := ((11287934178105469 : Rat) / 100000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1345540624553571429 : Rat) / 500000000000000000), R := ((135562616785714285791 : Rat) / 50000000000000000000), D0 := ((135562616785714285791 : Rat) / 50000000000000000000), D1 := ((44688861785714285791 : Rat) / 50000000000000000000), D2 := ((7665866785714285791 : Rat) / 50000000000000000000), D3 := ((1008554330357142891 : Rat) / 25000000000000000000), D4 := ((2032221986607140349 : Rat) / 25000000000000000000), LB := ((3627911891141783 : Rat) / 500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((135562616785714285791 : Rat) / 50000000000000000000), R := ((108651804294642857211 : Rat) / 40000000000000000000), D0 := ((108651804294642857211 : Rat) / 40000000000000000000), D1 := ((35952800294642857211 : Rat) / 40000000000000000000), D2 := ((6334404294642857211 : Rat) / 40000000000000000000), D3 := ((9076988973214286019 : Rat) / 200000000000000000000), D4 := ((3055889642857137807 : Rat) / 50000000000000000000), LB := ((20707697033748917 : Rat) / 1000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((108651804294642857211 : Rat) / 40000000000000000000), R := ((272133787901785714473 : Rat) / 100000000000000000000), D0 := ((272133787901785714473 : Rat) / 100000000000000000000), D1 := ((90386277901785714473 : Rat) / 100000000000000000000), D2 := ((16340287901785714473 : Rat) / 100000000000000000000), D3 := ((1008554330357142891 : Rat) / 20000000000000000000), D4 := ((11215004241071408337 : Rat) / 200000000000000000000), LB := ((1736477222237387 : Rat) / 200000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((272133787901785714473 : Rat) / 100000000000000000000), R := ((1089543705937500000783 : Rat) / 400000000000000000000), D0 := ((1089543705937500000783 : Rat) / 400000000000000000000), D1 := ((362553665937500000783 : Rat) / 400000000000000000000), D2 := ((66369705937500000783 : Rat) / 400000000000000000000), D3 := ((21179640937500000711 : Rat) / 400000000000000000000), D4 := ((5103224955357132723 : Rat) / 100000000000000000000), LB := ((5148397825092743 : Rat) / 500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1089543705937500000783 : Rat) / 400000000000000000000), R := ((545276130133928571837 : Rat) / 200000000000000000000), D0 := ((545276130133928571837 : Rat) / 200000000000000000000), D1 := ((181781110133928571837 : Rat) / 200000000000000000000), D2 := ((33689130133928571837 : Rat) / 200000000000000000000), D3 := ((11094097633928571801 : Rat) / 200000000000000000000), D4 := ((19404345491071388001 : Rat) / 400000000000000000000), LB := ((12545946831116761 : Rat) / 2000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545276130133928571837 : Rat) / 200000000000000000000), R := ((218312162919642857313 : Rat) / 80000000000000000000), D0 := ((218312162919642857313 : Rat) / 80000000000000000000), D1 := ((72914154919642857313 : Rat) / 80000000000000000000), D2 := ((13677362919642857313 : Rat) / 80000000000000000000), D3 := ((23196749598214286493 : Rat) / 400000000000000000000), D4 := ((1839579116071424511 : Rat) / 40000000000000000000), LB := ((5879555399465497 : Rat) / 2000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((218312162919642857313 : Rat) / 80000000000000000000), R := ((68285585558035714341 : Rat) / 25000000000000000000), D0 := ((68285585558035714341 : Rat) / 25000000000000000000), D1 := ((22848708058035714341 : Rat) / 25000000000000000000), D2 := ((4337210558035714341 : Rat) / 25000000000000000000), D3 := ((3025662991071428673 : Rat) / 50000000000000000000), D4 := ((17387236830357102219 : Rat) / 400000000000000000000), LB := ((1566198869747959 : Rat) / 5000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((68285585558035714341 : Rat) / 25000000000000000000), R := ((2186147292187500001803 : Rat) / 800000000000000000000), D0 := ((2186147292187500001803 : Rat) / 800000000000000000000), D1 := ((732167212187500001803 : Rat) / 800000000000000000000), D2 := ((139799292187500001803 : Rat) / 800000000000000000000), D3 := ((49419162187500001659 : Rat) / 800000000000000000000), D4 := ((511833828124998729 : Rat) / 12500000000000000000), LB := ((34402755802100393 : Rat) / 10000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2186147292187500001803 : Rat) / 800000000000000000000), R := ((1093577923258928572347 : Rat) / 400000000000000000000), D0 := ((1093577923258928572347 : Rat) / 400000000000000000000), D1 := ((366587883258928572347 : Rat) / 400000000000000000000), D2 := ((70403923258928572347 : Rat) / 400000000000000000000), D3 := ((1008554330357142891 : Rat) / 16000000000000000000), D4 := ((6349762133928555153 : Rat) / 160000000000000000000), LB := ((543562526646979 : Rat) / 200000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1093577923258928572347 : Rat) / 400000000000000000000), R := ((437632880169642857517 : Rat) / 160000000000000000000), D0 := ((437632880169642857517 : Rat) / 160000000000000000000), D1 := ((146836864169642857517 : Rat) / 160000000000000000000), D2 := ((28363280169642857517 : Rat) / 160000000000000000000), D3 := ((51436270848214287441 : Rat) / 800000000000000000000), D4 := ((15370128169642816437 : Rat) / 400000000000000000000), LB := ((10982921023386383 : Rat) / 5000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((437632880169642857517 : Rat) / 160000000000000000000), R := ((547293238794642857619 : Rat) / 200000000000000000000), D0 := ((547293238794642857619 : Rat) / 200000000000000000000), D1 := ((183798218794642857619 : Rat) / 200000000000000000000), D2 := ((35706238794642857619 : Rat) / 200000000000000000000), D3 := ((13111206294642857583 : Rat) / 200000000000000000000), D4 := ((29731702008928489983 : Rat) / 800000000000000000000), LB := ((4708885978324251 : Rat) / 2500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((547293238794642857619 : Rat) / 200000000000000000000), R := ((2190181509508928573367 : Rat) / 800000000000000000000), D0 := ((2190181509508928573367 : Rat) / 800000000000000000000), D1 := ((736201429508928573367 : Rat) / 800000000000000000000), D2 := ((143833509508928573367 : Rat) / 800000000000000000000), D3 := ((53453379508928573223 : Rat) / 800000000000000000000), D4 := ((7180786919642836773 : Rat) / 200000000000000000000), LB := ((17867757959689201 : Rat) / 10000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190181509508928573367 : Rat) / 800000000000000000000), R := ((1095595031919642858129 : Rat) / 400000000000000000000), D0 := ((1095595031919642858129 : Rat) / 400000000000000000000), D1 := ((368604991919642858129 : Rat) / 400000000000000000000), D2 := ((72421031919642858129 : Rat) / 400000000000000000000), D3 := ((27230966919642858057 : Rat) / 400000000000000000000), D4 := ((27714593348214204201 : Rat) / 800000000000000000000), LB := ((2394396271651611 : Rat) / 1250000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1095595031919642858129 : Rat) / 400000000000000000000), R := ((2192198618169642859149 : Rat) / 800000000000000000000), D0 := ((2192198618169642859149 : Rat) / 800000000000000000000), D1 := ((738218538169642859149 : Rat) / 800000000000000000000), D2 := ((145850618169642859149 : Rat) / 800000000000000000000), D3 := ((11094097633928571801 : Rat) / 160000000000000000000), D4 := ((2670603901785706131 : Rat) / 80000000000000000000), LB := ((182433316647721 : Rat) / 80000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2192198618169642859149 : Rat) / 800000000000000000000), R := ((54830179312500000051 : Rat) / 20000000000000000000), D0 := ((54830179312500000051 : Rat) / 20000000000000000000), D1 := ((18480677312500000051 : Rat) / 20000000000000000000), D2 := ((3671479312500000051 : Rat) / 20000000000000000000), D3 := ((7059880312500000237 : Rat) / 100000000000000000000), D4 := ((25697484687499918419 : Rat) / 800000000000000000000), LB := ((28936682334144703 : Rat) / 10000000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((54830179312500000051 : Rat) / 20000000000000000000), R := ((2194215726830357144931 : Rat) / 800000000000000000000), D0 := ((2194215726830357144931 : Rat) / 800000000000000000000), D1 := ((740235646830357144931 : Rat) / 800000000000000000000), D2 := ((147867726830357144931 : Rat) / 800000000000000000000), D3 := ((57487596830357144787 : Rat) / 800000000000000000000), D4 := ((3086116294642846941 : Rat) / 100000000000000000000), LB := ((117788988190589 : Rat) / 31250000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2194215726830357144931 : Rat) / 800000000000000000000), R := ((1097612140580357143911 : Rat) / 400000000000000000000), D0 := ((1097612140580357143911 : Rat) / 400000000000000000000), D1 := ((370622100580357143911 : Rat) / 400000000000000000000), D2 := ((74438140580357143911 : Rat) / 400000000000000000000), D3 := ((29248075580357143839 : Rat) / 400000000000000000000), D4 := ((23680376026785632637 : Rat) / 800000000000000000000), LB := ((984637142393019 : Rat) / 200000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1097612140580357143911 : Rat) / 400000000000000000000), R := ((549310347455357143401 : Rat) / 200000000000000000000), D0 := ((549310347455357143401 : Rat) / 200000000000000000000), D1 := ((185815327455357143401 : Rat) / 200000000000000000000), D2 := ((37723347455357143401 : Rat) / 200000000000000000000), D3 := ((3025662991071428673 : Rat) / 40000000000000000000), D4 := ((11335910848214244873 : Rat) / 400000000000000000000), LB := ((4722439688002733 : Rat) / 2500000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((549310347455357143401 : Rat) / 200000000000000000000), R := ((1099629249241071429693 : Rat) / 400000000000000000000), D0 := ((1099629249241071429693 : Rat) / 400000000000000000000), D1 := ((372639209241071429693 : Rat) / 400000000000000000000), D2 := ((76455249241071429693 : Rat) / 400000000000000000000), D3 := ((31265184241071429621 : Rat) / 400000000000000000000), D4 := ((5163678258928550991 : Rat) / 200000000000000000000), LB := ((58564075833617 : Rat) / 10000000000000000) },
  { w1 := ((583864449938457 : Rat) / 625000000000000), w2 := ((23697123752953627 : Rat) / 500000000000000000), w3 := ((453582220245449 : Rat) / 3125000000000000), w4 := ((274857657627737 : Rat) / 2000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133545508125000000009 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1099629249241071429693 : Rat) / 400000000000000000000), R := ((137579725446428571573 : Rat) / 50000000000000000000), D0 := ((137579725446428571573 : Rat) / 50000000000000000000), D1 := ((46705970446428571573 : Rat) / 50000000000000000000), D2 := ((9682975446428571573 : Rat) / 50000000000000000000), D3 := ((1008554330357142891 : Rat) / 12500000000000000000), D4 := ((9318802187499959091 : Rat) / 400000000000000000000), LB := ((1130785645795307 : Rat) / 100000000000000000) }
]

def block337RightChunk000L : Rat := ((43784975446428571501 : Rat) / 25000000000000000000)
def block337RightChunk000R : Rat := ((137579725446428571573 : Rat) / 50000000000000000000)

def block337RightChunk000Certificate : Bool :=
  allBoxesValid block337RightChunk000 &&
  coversFromBool block337RightChunk000 block337RightChunk000L block337RightChunk000R

theorem block337RightChunk000Certificate_eq_true :
    block337RightChunk000Certificate = true := by
  native_decide

def block337RightChainCertificate : Bool :=
  decide (
    block337RightL = ((43784975446428571501 : Rat) / 25000000000000000000) /\
    ((137579725446428571573 : Rat) / 50000000000000000000) = block337RightR)

theorem block337RightChainCertificate_eq_true :
    block337RightChainCertificate = true := by
  native_decide

def block337LeftBoxCount : Nat := boxCount block337LeftBoxes
def block337RightBoxCount : Nat := 63

def block337_rational_certificate : Prop :=
    block337LeftCertificate = true /\
    block337RightChainCertificate = true /\
    block337RightChunk000Certificate = true

theorem block337_rational_certificate_proof :
    block337_rational_certificate := by
  exact ⟨block337LeftCertificate_eq_true, block337RightChainCertificate_eq_true, block337RightChunk000Certificate_eq_true⟩

end Block337
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block337

open Set

def block337W1 : Rat := ((583864449938457 : Rat) / 625000000000000)
def block337W2 : Rat := ((23697123752953627 : Rat) / 500000000000000000)
def block337W3 : Rat := ((453582220245449 : Rat) / 3125000000000000)
def block337W4 : Rat := ((274857657627737 : Rat) / 2000000000000000)
def block337S1 : Rat := ((18174751 : Rat) / 10000000)
def block337S2 : Rat := ((511587 : Rat) / 200000)
def block337S3 : Rat := ((133545508125000000009 : Rat) / 50000000000000000000)
def block337S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block337V (y : ℝ) : ℝ :=
  ratPotential block337W1 block337W2 block337W3 block337W4 block337S1 block337S2 block337S3 block337S4 y

def block337LeftParamsCertificate : Bool :=
  allBoxesSameParams block337LeftBoxes block337W1 block337W2 block337W3 block337W4 block337S1 block337S2 block337S3 block337S4

theorem block337LeftParamsCertificate_eq_true :
    block337LeftParamsCertificate = true := by
  native_decide

theorem block337_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block337LeftL : ℝ) (block337LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block337S1 : ℝ))
    (hy2ne : y ≠ (block337S2 : ℝ))
    (hy3ne : y ≠ (block337S3 : ℝ))
    (hy4ne : y ≠ (block337S4 : ℝ)) :
    0 < block337V y := by
  have hcert := block337LeftCertificate_eq_true
  unfold block337LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block337LeftBoxes) (lo := block337LeftL) (hi := block337LeftR)
    (w1 := block337W1) (w2 := block337W2) (w3 := block337W3) (w4 := block337W4)
    (s1 := block337S1) (s2 := block337S2) (s3 := block337S3) (s4 := block337S4)
    hboxes hcover block337LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block337RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block337RightChunk000 block337W1 block337W2 block337W3 block337W4 block337S1 block337S2 block337S3 block337S4

theorem block337RightChunk000ParamsCertificate_eq_true :
    block337RightChunk000ParamsCertificate = true := by
  native_decide

theorem block337_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block337RightChunk000L : ℝ) (block337RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block337S1 : ℝ))
    (hy2ne : y ≠ (block337S2 : ℝ))
    (hy3ne : y ≠ (block337S3 : ℝ))
    (hy4ne : y ≠ (block337S4 : ℝ)) :
    0 < block337V y := by
  have hcert := block337RightChunk000Certificate_eq_true
  unfold block337RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block337RightChunk000) (lo := block337RightChunk000L) (hi := block337RightChunk000R)
    (w1 := block337W1) (w2 := block337W2) (w3 := block337W3) (w4 := block337W4)
    (s1 := block337S1) (s2 := block337S2) (s3 := block337S3) (s4 := block337S4)
    hboxes hcover block337RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block337_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block337RightL : ℝ) (block337RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block337S1 : ℝ))
    (hy2ne : y ≠ (block337S2 : ℝ))
    (hy3ne : y ≠ (block337S3 : ℝ))
    (hy4ne : y ≠ (block337S4 : ℝ)) :
    0 < block337V y := by
  have hL : (block337RightChunk000L : ℝ) = (block337RightL : ℝ) := by
    norm_num [block337RightChunk000L, block337RightL]
  have hR : (block337RightChunk000R : ℝ) = (block337RightR : ℝ) := by
    norm_num [block337RightChunk000R, block337RightR]
  have hyc : y ∈ Icc (block337RightChunk000L : ℝ) (block337RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block337_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block337_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block337LeftL : ℝ) (block337LeftR : ℝ) →
    y ≠ 0 → y ≠ (block337S1 : ℝ) → y ≠ (block337S2 : ℝ) →
    y ≠ (block337S3 : ℝ) → y ≠ (block337S4 : ℝ) → 0 < block337V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block337RightL : ℝ) (block337RightR : ℝ) →
    y ≠ 0 → y ≠ (block337S1 : ℝ) → y ≠ (block337S2 : ℝ) →
    y ≠ (block337S3 : ℝ) → y ≠ (block337S4 : ℝ) → 0 < block337V y)

theorem block337_reallog_certificate_proof :
    block337_reallog_certificate := by
  exact ⟨block337_left_V_pos, block337_right_V_pos⟩

end Block337
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block337.block337V
#check Erdos1038Lean.M1817475.Block337.block337_left_V_pos
#check Erdos1038Lean.M1817475.Block337.block337_right_V_pos
#check Erdos1038Lean.M1817475.Block337.block337_reallog_certificate_proof
