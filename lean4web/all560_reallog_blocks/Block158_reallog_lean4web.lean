/-
Self-contained Lean4Web paste file.
Block 158 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block158

def block158LeftL : Rat := ((39319595982142857211 : Rat) / 50000000000000000000)
def block158LeftR : Rat := ((19664685267857142891 : Rat) / 25000000000000000000)
def block158RightL : Rat := ((89319595982142857211 : Rat) / 50000000000000000000)
def block158RightR : Rat := ((69664685267857142891 : Rat) / 25000000000000000000)

def block158LeftBoxes : List RatBox := [
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((39319595982142857211 : Rat) / 50000000000000000000), R := ((19664685267857142891 : Rat) / 25000000000000000000), D0 := ((19664685267857142891 : Rat) / 25000000000000000000), D1 := ((51554159017857142789 : Rat) / 50000000000000000000), D2 := ((88577154017857142789 : Rat) / 50000000000000000000), D3 := ((48364098928571428487 : Rat) / 25000000000000000000), D4 := ((99904932767857137789 : Rat) / 50000000000000000000), LB := ((32870401373476937 : Rat) / 10000000000000000000) }
]

def block158LeftCertificate : Bool :=
  allBoxesValid block158LeftBoxes &&
  coversFromBool block158LeftBoxes block158LeftL block158LeftR

theorem block158LeftCertificate_eq_true :
    block158LeftCertificate = true := by
  native_decide

def block158RightChunk000 : List RatBox := [
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((89319595982142857211 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((1554159017857142789 : Rat) / 50000000000000000000), D2 := ((38577154017857142789 : Rat) / 50000000000000000000), D3 := ((23364098928571428487 : Rat) / 25000000000000000000), D4 := ((49904932767857137789 : Rat) / 50000000000000000000), LB := ((5904405689172637 : Rat) / 1000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((9034807767857142837 : Rat) / 10000000000000000000), D4 := ((9670154749999999 : Rat) / 10000000000000000), LB := ((10950397186941323 : Rat) / 10000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43754101 : Rat) / 20000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((5332508267857142837 : Rat) / 10000000000000000000), D4 := ((5967855249999999 : Rat) / 10000000000000000), LB := ((978867102131167 : Rat) / 2500000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((94912801 : Rat) / 40000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((7404599 : Rat) / 40000000), D3 := ((3481358517857142837 : Rat) / 10000000000000000000), D4 := ((4116705499999999 : Rat) / 10000000000000000), LB := ((108083697446799 : Rat) / 625000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((197230201 : Rat) / 80000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((7404599 : Rat) / 80000000), D3 := ((2555783642857142837 : Rat) / 10000000000000000000), D4 := ((3191130624999999 : Rat) / 10000000000000000), LB := ((2039886643048209 : Rat) / 20000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((401865001 : Rat) / 160000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((2092996205357142837 : Rat) / 10000000000000000000), D4 := ((2728343187499999 : Rat) / 10000000000000000), LB := ((11763201914316901 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((511587 : Rat) / 200000), R := ((206265008767857142837 : Rat) / 80000000000000000000), D0 := ((206265008767857142837 : Rat) / 80000000000000000000), D1 := ((60867000767857142837 : Rat) / 80000000000000000000), D2 := ((1630208767857142837 : Rat) / 80000000000000000000), D3 := ((1630208767857142837 : Rat) / 10000000000000000000), D4 := ((2265555749999999 : Rat) / 10000000000000000), LB := ((12917506435029313 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((206265008767857142837 : Rat) / 80000000000000000000), R := ((414160226303571428511 : Rat) / 160000000000000000000), D0 := ((414160226303571428511 : Rat) / 160000000000000000000), D1 := ((123364210303571428511 : Rat) / 160000000000000000000), D2 := ((4890626303571428511 : Rat) / 160000000000000000000), D3 := ((11411461374999999859 : Rat) / 80000000000000000000), D4 := ((16494237232142849163 : Rat) / 80000000000000000000), LB := ((1942722746392879 : Rat) / 125000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((414160226303571428511 : Rat) / 160000000000000000000), R := ((103947608767857142837 : Rat) / 40000000000000000000), D0 := ((103947608767857142837 : Rat) / 40000000000000000000), D1 := ((31248604767857142837 : Rat) / 40000000000000000000), D2 := ((1630208767857142837 : Rat) / 40000000000000000000), D3 := ((21192713982142856881 : Rat) / 160000000000000000000), D4 := ((31358265696428555489 : Rat) / 160000000000000000000), LB := ((4341719368242403 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((103947608767857142837 : Rat) / 40000000000000000000), R := ((833211078910714285533 : Rat) / 320000000000000000000), D0 := ((833211078910714285533 : Rat) / 320000000000000000000), D1 := ((251619046910714285533 : Rat) / 320000000000000000000), D2 := ((14671878910714285533 : Rat) / 320000000000000000000), D3 := ((4890626303571428511 : Rat) / 40000000000000000000), D4 := ((7432014232142853163 : Rat) / 40000000000000000000), LB := ((8745399065235943 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((833211078910714285533 : Rat) / 320000000000000000000), R := ((83484128767857142837 : Rat) / 32000000000000000000), D0 := ((83484128767857142837 : Rat) / 32000000000000000000), D1 := ((25324925567857142837 : Rat) / 32000000000000000000), D2 := ((1630208767857142837 : Rat) / 32000000000000000000), D3 := ((37494801660714285251 : Rat) / 320000000000000000000), D4 := ((57825905089285682467 : Rat) / 320000000000000000000), LB := ((4497864706952431 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((83484128767857142837 : Rat) / 32000000000000000000), R := ((836471496446428571207 : Rat) / 320000000000000000000), D0 := ((836471496446428571207 : Rat) / 320000000000000000000), D1 := ((254879464446428571207 : Rat) / 320000000000000000000), D2 := ((17932296446428571207 : Rat) / 320000000000000000000), D3 := ((17932296446428571207 : Rat) / 160000000000000000000), D4 := ((5619569632142853963 : Rat) / 32000000000000000000), LB := ((7195801841031191 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((836471496446428571207 : Rat) / 320000000000000000000), R := ((1674573201660714285251 : Rat) / 640000000000000000000), D0 := ((1674573201660714285251 : Rat) / 640000000000000000000), D1 := ((511389137660714285251 : Rat) / 640000000000000000000), D2 := ((37494801660714285251 : Rat) / 640000000000000000000), D3 := ((34234384124999999577 : Rat) / 320000000000000000000), D4 := ((54565487553571396793 : Rat) / 320000000000000000000), LB := ((4367381422456351 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1674573201660714285251 : Rat) / 640000000000000000000), R := ((209525426303571428511 : Rat) / 80000000000000000000), D0 := ((209525426303571428511 : Rat) / 80000000000000000000), D1 := ((64127418303571428511 : Rat) / 80000000000000000000), D2 := ((4890626303571428511 : Rat) / 80000000000000000000), D3 := ((66838559482142856317 : Rat) / 640000000000000000000), D4 := ((107500766339285650749 : Rat) / 640000000000000000000), LB := ((29084860991267503 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((209525426303571428511 : Rat) / 80000000000000000000), R := ((67113344767857142837 : Rat) / 25600000000000000000), D0 := ((67113344767857142837 : Rat) / 25600000000000000000), D1 := ((20585982207857142837 : Rat) / 25600000000000000000), D2 := ((1630208767857142837 : Rat) / 25600000000000000000), D3 := ((1630208767857142837 : Rat) / 16000000000000000000), D4 := ((13233819696428563489 : Rat) / 80000000000000000000), LB := ((1986608979347021 : Rat) / 1250000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((67113344767857142837 : Rat) / 25600000000000000000), R := ((839731913982142856881 : Rat) / 320000000000000000000), D0 := ((839731913982142856881 : Rat) / 320000000000000000000), D1 := ((258139881982142856881 : Rat) / 320000000000000000000), D2 := ((21192713982142856881 : Rat) / 320000000000000000000), D3 := ((63578141946428570643 : Rat) / 640000000000000000000), D4 := ((4169613952142854603 : Rat) / 25600000000000000000), LB := ((5190662649599137 : Rat) / 12500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((839731913982142856881 : Rat) / 320000000000000000000), R := ((3360557864696428570361 : Rat) / 1280000000000000000000), D0 := ((3360557864696428570361 : Rat) / 1280000000000000000000), D1 := ((1034189736696428570361 : Rat) / 1280000000000000000000), D2 := ((86401064696428570361 : Rat) / 1280000000000000000000), D3 := ((30973966589285713903 : Rat) / 320000000000000000000), D4 := ((51305070017857111119 : Rat) / 320000000000000000000), LB := ((7056445700683589 : Rat) / 2500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3360557864696428570361 : Rat) / 1280000000000000000000), R := ((1681094036732142856599 : Rat) / 640000000000000000000), D0 := ((1681094036732142856599 : Rat) / 640000000000000000000), D1 := ((517909972732142856599 : Rat) / 640000000000000000000), D2 := ((44015636732142856599 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 51200000000000000000), D4 := ((203590071303571301639 : Rat) / 1280000000000000000000), LB := ((2364821457804367 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1681094036732142856599 : Rat) / 640000000000000000000), R := ((672763656446428571207 : Rat) / 256000000000000000000), D0 := ((672763656446428571207 : Rat) / 256000000000000000000), D1 := ((207490030846428571207 : Rat) / 256000000000000000000), D2 := ((17932296446428571207 : Rat) / 256000000000000000000), D3 := ((60317724410714284969 : Rat) / 640000000000000000000), D4 := ((100979931267857079401 : Rat) / 640000000000000000000), LB := ((243406981017609 : Rat) / 125000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((672763656446428571207 : Rat) / 256000000000000000000), R := ((420681061374999999859 : Rat) / 160000000000000000000), D0 := ((420681061374999999859 : Rat) / 160000000000000000000), D1 := ((129885045374999999859 : Rat) / 160000000000000000000), D2 := ((11411461374999999859 : Rat) / 160000000000000000000), D3 := ((119005240053571427101 : Rat) / 1280000000000000000000), D4 := ((40065930753571403193 : Rat) / 256000000000000000000), LB := ((1570752725693847 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((420681061374999999859 : Rat) / 160000000000000000000), R := ((3367078699767857141709 : Rat) / 1280000000000000000000), D0 := ((3367078699767857141709 : Rat) / 1280000000000000000000), D1 := ((1040710571767857141709 : Rat) / 1280000000000000000000), D2 := ((92921899767857141709 : Rat) / 1280000000000000000000), D3 := ((14671878910714285533 : Rat) / 160000000000000000000), D4 := ((24837430624999984141 : Rat) / 160000000000000000000), LB := ((618109115501489 : Rat) / 500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3367078699767857141709 : Rat) / 1280000000000000000000), R := ((1684354454267857142273 : Rat) / 640000000000000000000), D0 := ((1684354454267857142273 : Rat) / 640000000000000000000), D1 := ((521170390267857142273 : Rat) / 640000000000000000000), D2 := ((47276054267857142273 : Rat) / 640000000000000000000), D3 := ((115744822517857141427 : Rat) / 1280000000000000000000), D4 := ((197069236232142730291 : Rat) / 1280000000000000000000), LB := ((944595254716657 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1684354454267857142273 : Rat) / 640000000000000000000), R := ((3370339117303571427383 : Rat) / 1280000000000000000000), D0 := ((3370339117303571427383 : Rat) / 1280000000000000000000), D1 := ((1043970989303571427383 : Rat) / 1280000000000000000000), D2 := ((96182317303571427383 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 128000000000000000000), D4 := ((97719513732142793727 : Rat) / 640000000000000000000), LB := ((1393730905207613 : Rat) / 2000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3370339117303571427383 : Rat) / 1280000000000000000000), R := ((168598466303571428511 : Rat) / 64000000000000000000), D0 := ((168598466303571428511 : Rat) / 64000000000000000000), D1 := ((52280059903571428511 : Rat) / 64000000000000000000), D2 := ((4890626303571428511 : Rat) / 64000000000000000000), D3 := ((112484404982142855753 : Rat) / 1280000000000000000000), D4 := ((193808818696428444617 : Rat) / 1280000000000000000000), LB := ((1235128506961239 : Rat) / 2500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((168598466303571428511 : Rat) / 64000000000000000000), R := ((3373599534839285713057 : Rat) / 1280000000000000000000), D0 := ((3373599534839285713057 : Rat) / 1280000000000000000000), D1 := ((1047231406839285713057 : Rat) / 1280000000000000000000), D2 := ((99442734839285713057 : Rat) / 1280000000000000000000), D3 := ((27713549053571428229 : Rat) / 320000000000000000000), D4 := ((9608930496428565089 : Rat) / 64000000000000000000), LB := ((337218917472043 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3373599534839285713057 : Rat) / 1280000000000000000000), R := ((1687614871803571427947 : Rat) / 640000000000000000000), D0 := ((1687614871803571427947 : Rat) / 640000000000000000000), D1 := ((524430807803571427947 : Rat) / 640000000000000000000), D2 := ((50536471803571427947 : Rat) / 640000000000000000000), D3 := ((109223987446428570079 : Rat) / 1280000000000000000000), D4 := ((190548401160714158943 : Rat) / 1280000000000000000000), LB := ((1421747017700363 : Rat) / 6250000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1687614871803571427947 : Rat) / 640000000000000000000), R := ((3376859952374999998731 : Rat) / 1280000000000000000000), D0 := ((3376859952374999998731 : Rat) / 1280000000000000000000), D1 := ((1050491824374999998731 : Rat) / 1280000000000000000000), D2 := ((102703152374999998731 : Rat) / 1280000000000000000000), D3 := ((53796889339285713621 : Rat) / 640000000000000000000), D4 := ((94459096196428508053 : Rat) / 640000000000000000000), LB := ((829965609718819 : Rat) / 5000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3376859952374999998731 : Rat) / 1280000000000000000000), R := ((52788908767857142837 : Rat) / 20000000000000000000), D0 := ((52788908767857142837 : Rat) / 20000000000000000000), D1 := ((16439406767857142837 : Rat) / 20000000000000000000), D2 := ((1630208767857142837 : Rat) / 20000000000000000000), D3 := ((21192713982142856881 : Rat) / 256000000000000000000), D4 := ((187287983624999873269 : Rat) / 1280000000000000000000), LB := ((307941714935811 : Rat) / 2000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((52788908767857142837 : Rat) / 20000000000000000000), R := ((676024073982142856881 : Rat) / 256000000000000000000), D0 := ((676024073982142856881 : Rat) / 256000000000000000000), D1 := ((210750448382142856881 : Rat) / 256000000000000000000), D2 := ((21192713982142856881 : Rat) / 256000000000000000000), D3 := ((1630208767857142837 : Rat) / 20000000000000000000), D4 := ((2900902732142855163 : Rat) / 20000000000000000000), LB := ((9633909620065939 : Rat) / 50000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((676024073982142856881 : Rat) / 256000000000000000000), R := ((1690875289339285713621 : Rat) / 640000000000000000000), D0 := ((1690875289339285713621 : Rat) / 640000000000000000000), D1 := ((527691225339285713621 : Rat) / 640000000000000000000), D2 := ((53796889339285713621 : Rat) / 640000000000000000000), D3 := ((102703152374999998731 : Rat) / 1280000000000000000000), D4 := ((36805513217857117519 : Rat) / 256000000000000000000), LB := ((28343822932533347 : Rat) / 100000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1690875289339285713621 : Rat) / 640000000000000000000), R := ((3383380787446428570079 : Rat) / 1280000000000000000000), D0 := ((3383380787446428570079 : Rat) / 1280000000000000000000), D1 := ((1057012659446428570079 : Rat) / 1280000000000000000000), D2 := ((109223987446428570079 : Rat) / 1280000000000000000000), D3 := ((50536471803571427947 : Rat) / 640000000000000000000), D4 := ((91198678660714222379 : Rat) / 640000000000000000000), LB := ((4276352908167691 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3383380787446428570079 : Rat) / 1280000000000000000000), R := ((846252749053571428229 : Rat) / 320000000000000000000), D0 := ((846252749053571428229 : Rat) / 320000000000000000000), D1 := ((264660717053571428229 : Rat) / 320000000000000000000), D2 := ((27713549053571428229 : Rat) / 320000000000000000000), D3 := ((99442734839285713057 : Rat) / 1280000000000000000000), D4 := ((180767148553571301921 : Rat) / 1280000000000000000000), LB := ((1253437572513949 : Rat) / 2000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((846252749053571428229 : Rat) / 320000000000000000000), R := ((3386641204982142855753 : Rat) / 1280000000000000000000), D0 := ((3386641204982142855753 : Rat) / 1280000000000000000000), D1 := ((1060273076982142855753 : Rat) / 1280000000000000000000), D2 := ((112484404982142855753 : Rat) / 1280000000000000000000), D3 := ((4890626303571428511 : Rat) / 64000000000000000000), D4 := ((44784234946428539771 : Rat) / 320000000000000000000), LB := ((8822073931928909 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3386641204982142855753 : Rat) / 1280000000000000000000), R := ((338827141374999999859 : Rat) / 128000000000000000000), D0 := ((338827141374999999859 : Rat) / 128000000000000000000), D1 := ((106190328574999999859 : Rat) / 128000000000000000000), D2 := ((11411461374999999859 : Rat) / 128000000000000000000), D3 := ((96182317303571427383 : Rat) / 1280000000000000000000), D4 := ((177506731017857016247 : Rat) / 1280000000000000000000), LB := ((1195693584681523 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((338827141374999999859 : Rat) / 128000000000000000000), R := ((3389901622517857141427 : Rat) / 1280000000000000000000), D0 := ((3389901622517857141427 : Rat) / 1280000000000000000000), D1 := ((1063533494517857141427 : Rat) / 1280000000000000000000), D2 := ((115744822517857141427 : Rat) / 1280000000000000000000), D3 := ((47276054267857142273 : Rat) / 640000000000000000000), D4 := ((17587652224999987341 : Rat) / 128000000000000000000), LB := ((3922121344497459 : Rat) / 2500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3389901622517857141427 : Rat) / 1280000000000000000000), R := ((423941478910714285533 : Rat) / 160000000000000000000), D0 := ((423941478910714285533 : Rat) / 160000000000000000000), D1 := ((133145462910714285533 : Rat) / 160000000000000000000), D2 := ((14671878910714285533 : Rat) / 160000000000000000000), D3 := ((92921899767857141709 : Rat) / 1280000000000000000000), D4 := ((174246313482142730573 : Rat) / 1280000000000000000000), LB := ((801370985112837 : Rat) / 400000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((423941478910714285533 : Rat) / 160000000000000000000), R := ((3393162040053571427101 : Rat) / 1280000000000000000000), D0 := ((3393162040053571427101 : Rat) / 1280000000000000000000), D1 := ((1066793912053571427101 : Rat) / 1280000000000000000000), D2 := ((119005240053571427101 : Rat) / 1280000000000000000000), D3 := ((11411461374999999859 : Rat) / 160000000000000000000), D4 := ((21577013089285698467 : Rat) / 160000000000000000000), LB := ((25012753970690693 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3393162040053571427101 : Rat) / 1280000000000000000000), R := ((1697396124410714284969 : Rat) / 640000000000000000000), D0 := ((1697396124410714284969 : Rat) / 640000000000000000000), D1 := ((534212060410714284969 : Rat) / 640000000000000000000), D2 := ((60317724410714284969 : Rat) / 640000000000000000000), D3 := ((17932296446428571207 : Rat) / 256000000000000000000), D4 := ((170985895946428444899 : Rat) / 1280000000000000000000), LB := ((30643335141724293 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1697396124410714284969 : Rat) / 640000000000000000000), R := ((849513166589285713903 : Rat) / 320000000000000000000), D0 := ((849513166589285713903 : Rat) / 320000000000000000000), D1 := ((267921134589285713903 : Rat) / 320000000000000000000), D2 := ((30973966589285713903 : Rat) / 320000000000000000000), D3 := ((44015636732142856599 : Rat) / 640000000000000000000), D4 := ((84677843589285651031 : Rat) / 640000000000000000000), LB := ((36809543563054437 : Rat) / 100000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((849513166589285713903 : Rat) / 320000000000000000000), R := ((1700656541946428570643 : Rat) / 640000000000000000000), D0 := ((1700656541946428570643 : Rat) / 640000000000000000000), D1 := ((537472477946428570643 : Rat) / 640000000000000000000), D2 := ((63578141946428570643 : Rat) / 640000000000000000000), D3 := ((21192713982142856881 : Rat) / 320000000000000000000), D4 := ((41523817410714254097 : Rat) / 320000000000000000000), LB := ((18483221078749723 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1700656541946428570643 : Rat) / 640000000000000000000), R := ((42557168767857142837 : Rat) / 16000000000000000000), D0 := ((42557168767857142837 : Rat) / 16000000000000000000), D1 := ((13477567167857142837 : Rat) / 16000000000000000000), D2 := ((1630208767857142837 : Rat) / 16000000000000000000), D3 := ((1630208767857142837 : Rat) / 25600000000000000000), D4 := ((81417426053571365357 : Rat) / 640000000000000000000), LB := ((18124842226508453 : Rat) / 5000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((42557168767857142837 : Rat) / 16000000000000000000), R := ((1703916959482142856317 : Rat) / 640000000000000000000), D0 := ((1703916959482142856317 : Rat) / 640000000000000000000), D1 := ((540732895482142856317 : Rat) / 640000000000000000000), D2 := ((66838559482142856317 : Rat) / 640000000000000000000), D3 := ((4890626303571428511 : Rat) / 80000000000000000000), D4 := ((1994680432142855563 : Rat) / 16000000000000000000), LB := ((2859481506526873 : Rat) / 500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1703916959482142856317 : Rat) / 640000000000000000000), R := ((852773584124999999577 : Rat) / 320000000000000000000), D0 := ((852773584124999999577 : Rat) / 320000000000000000000), D1 := ((271181552124999999577 : Rat) / 320000000000000000000), D2 := ((34234384124999999577 : Rat) / 320000000000000000000), D3 := ((37494801660714285251 : Rat) / 640000000000000000000), D4 := ((78157008517857079683 : Rat) / 640000000000000000000), LB := ((127403323638487 : Rat) / 15625000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((852773584124999999577 : Rat) / 320000000000000000000), R := ((427201896446428571207 : Rat) / 160000000000000000000), D0 := ((427201896446428571207 : Rat) / 160000000000000000000), D1 := ((136405880446428571207 : Rat) / 160000000000000000000), D2 := ((17932296446428571207 : Rat) / 160000000000000000000), D3 := ((17932296446428571207 : Rat) / 320000000000000000000), D4 := ((38263399874999968423 : Rat) / 320000000000000000000), LB := ((4406171870471071 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((427201896446428571207 : Rat) / 160000000000000000000), R := ((856034001660714285251 : Rat) / 320000000000000000000), D0 := ((856034001660714285251 : Rat) / 320000000000000000000), D1 := ((274441969660714285251 : Rat) / 320000000000000000000), D2 := ((37494801660714285251 : Rat) / 320000000000000000000), D3 := ((1630208767857142837 : Rat) / 32000000000000000000), D4 := ((18316595553571412793 : Rat) / 160000000000000000000), LB := ((5636321604389413 : Rat) / 500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((856034001660714285251 : Rat) / 320000000000000000000), R := ((107208026303571428511 : Rat) / 40000000000000000000), D0 := ((107208026303571428511 : Rat) / 40000000000000000000), D1 := ((34509022303571428511 : Rat) / 40000000000000000000), D2 := ((4890626303571428511 : Rat) / 40000000000000000000), D3 := ((14671878910714285533 : Rat) / 320000000000000000000), D4 := ((35002982339285682749 : Rat) / 320000000000000000000), LB := ((31297625043311 : Rat) / 1562500000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((107208026303571428511 : Rat) / 40000000000000000000), R := ((430462313982142856881 : Rat) / 160000000000000000000), D0 := ((430462313982142856881 : Rat) / 160000000000000000000), D1 := ((139666297982142856881 : Rat) / 160000000000000000000), D2 := ((21192713982142856881 : Rat) / 160000000000000000000), D3 := ((1630208767857142837 : Rat) / 40000000000000000000), D4 := ((4171596696428567489 : Rat) / 40000000000000000000), LB := ((1823858574480519 : Rat) / 100000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((430462313982142856881 : Rat) / 160000000000000000000), R := ((216046261374999999859 : Rat) / 80000000000000000000), D0 := ((216046261374999999859 : Rat) / 80000000000000000000), D1 := ((70648253374999999859 : Rat) / 80000000000000000000), D2 := ((11411461374999999859 : Rat) / 80000000000000000000), D3 := ((4890626303571428511 : Rat) / 160000000000000000000), D4 := ((15056178017857127119 : Rat) / 160000000000000000000), LB := ((1245374165532459 : Rat) / 25000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((216046261374999999859 : Rat) / 80000000000000000000), R := ((27209558767857142837 : Rat) / 10000000000000000000), D0 := ((27209558767857142837 : Rat) / 10000000000000000000), D1 := ((9034807767857142837 : Rat) / 10000000000000000000), D2 := ((1630208767857142837 : Rat) / 10000000000000000000), D3 := ((1630208767857142837 : Rat) / 80000000000000000000), D4 := ((6712984624999992141 : Rat) / 80000000000000000000), LB := ((3841269597870797 : Rat) / 50000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27209558767857142837 : Rat) / 10000000000000000000), R := ((109473582053571427511 : Rat) / 40000000000000000000), D0 := ((109473582053571427511 : Rat) / 40000000000000000000), D1 := ((36774578053571427511 : Rat) / 40000000000000000000), D2 := ((7156182053571427511 : Rat) / 40000000000000000000), D3 := ((635346982142856163 : Rat) / 40000000000000000000), D4 := ((635346982142856163 : Rat) / 10000000000000000000), LB := ((2699777229557561 : Rat) / 25000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((109473582053571427511 : Rat) / 40000000000000000000), R := ((43916502217857142237 : Rat) / 16000000000000000000), D0 := ((43916502217857142237 : Rat) / 16000000000000000000), D1 := ((14836900617857142237 : Rat) / 16000000000000000000), D2 := ((2989542217857142237 : Rat) / 16000000000000000000), D3 := ((1906040946428568489 : Rat) / 80000000000000000000), D4 := ((1906040946428568489 : Rat) / 40000000000000000000), LB := ((5470573866979517 : Rat) / 100000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((43916502217857142237 : Rat) / 16000000000000000000), R := ((55054464517857141837 : Rat) / 20000000000000000000), D0 := ((55054464517857141837 : Rat) / 20000000000000000000), D1 := ((18704962517857141837 : Rat) / 20000000000000000000), D2 := ((3895764517857141837 : Rat) / 20000000000000000000), D3 := ((635346982142856163 : Rat) / 20000000000000000000), D4 := ((635346982142856163 : Rat) / 16000000000000000000), LB := ((920696256237391 : Rat) / 100000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((55054464517857141837 : Rat) / 20000000000000000000), R := ((441071063124999990859 : Rat) / 160000000000000000000), D0 := ((441071063124999990859 : Rat) / 160000000000000000000), D1 := ((150275047124999990859 : Rat) / 160000000000000000000), D2 := ((31801463124999990859 : Rat) / 160000000000000000000), D3 := ((5718122839285705467 : Rat) / 160000000000000000000), D4 := ((635346982142856163 : Rat) / 20000000000000000000), LB := ((2377994253481397 : Rat) / 500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((441071063124999990859 : Rat) / 160000000000000000000), R := ((882777473232142837881 : Rat) / 320000000000000000000), D0 := ((882777473232142837881 : Rat) / 320000000000000000000), D1 := ((301185441232142837881 : Rat) / 320000000000000000000), D2 := ((64238273232142837881 : Rat) / 320000000000000000000), D3 := ((12071592660714267097 : Rat) / 320000000000000000000), D4 := ((4447428874999993141 : Rat) / 160000000000000000000), LB := ((1131543862505513 : Rat) / 200000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((882777473232142837881 : Rat) / 320000000000000000000), R := ((220853205053571423511 : Rat) / 80000000000000000000), D0 := ((220853205053571423511 : Rat) / 80000000000000000000), D1 := ((75455197053571423511 : Rat) / 80000000000000000000), D2 := ((16218405053571423511 : Rat) / 80000000000000000000), D3 := ((635346982142856163 : Rat) / 16000000000000000000), D4 := ((8259510767857130119 : Rat) / 320000000000000000000), LB := ((847953788750827 : Rat) / 1250000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((220853205053571423511 : Rat) / 80000000000000000000), R := ((1767460987410714244251 : Rat) / 640000000000000000000), D0 := ((1767460987410714244251 : Rat) / 640000000000000000000), D1 := ((604276923410714244251 : Rat) / 640000000000000000000), D2 := ((130382587410714244251 : Rat) / 640000000000000000000), D3 := ((26049226267857102683 : Rat) / 640000000000000000000), D4 := ((1906040946428568489 : Rat) / 80000000000000000000), LB := ((36592105066377 : Rat) / 12500000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1767460987410714244251 : Rat) / 640000000000000000000), R := ((884048167196428550207 : Rat) / 320000000000000000000), D0 := ((884048167196428550207 : Rat) / 320000000000000000000), D1 := ((302456135196428550207 : Rat) / 320000000000000000000), D2 := ((65508967196428550207 : Rat) / 320000000000000000000), D3 := ((13342286624999979423 : Rat) / 320000000000000000000), D4 := ((14612980589285691749 : Rat) / 640000000000000000000), LB := ((798937478141519 : Rat) / 625000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((884048167196428550207 : Rat) / 320000000000000000000), R := ((3536828015767857056991 : Rat) / 1280000000000000000000), D0 := ((3536828015767857056991 : Rat) / 1280000000000000000000), D1 := ((1210459887767857056991 : Rat) / 1280000000000000000000), D2 := ((262671215767857056991 : Rat) / 1280000000000000000000), D3 := ((10800898696428554771 : Rat) / 256000000000000000000), D4 := ((6988816803571417793 : Rat) / 320000000000000000000), LB := ((2959007671562819 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3536828015767857056991 : Rat) / 1280000000000000000000), R := ((1768731681374999956577 : Rat) / 640000000000000000000), D0 := ((1768731681374999956577 : Rat) / 640000000000000000000), D1 := ((605547617374999956577 : Rat) / 640000000000000000000), D2 := ((131653281374999956577 : Rat) / 640000000000000000000), D3 := ((27319920232142815009 : Rat) / 640000000000000000000), D4 := ((27319920232142815009 : Rat) / 1280000000000000000000), LB := ((5936531982238119 : Rat) / 2500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1768731681374999956577 : Rat) / 640000000000000000000), R := ((3538098709732142769317 : Rat) / 1280000000000000000000), D0 := ((3538098709732142769317 : Rat) / 1280000000000000000000), D1 := ((1211730581732142769317 : Rat) / 1280000000000000000000), D2 := ((263941909732142769317 : Rat) / 1280000000000000000000), D3 := ((55275187446428486181 : Rat) / 1280000000000000000000), D4 := ((13342286624999979423 : Rat) / 640000000000000000000), LB := ((1168810549850019 : Rat) / 625000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3538098709732142769317 : Rat) / 1280000000000000000000), R := ((88468351417857140637 : Rat) / 32000000000000000000), D0 := ((88468351417857140637 : Rat) / 32000000000000000000), D1 := ((30309148217857140637 : Rat) / 32000000000000000000), D2 := ((6614431417857140637 : Rat) / 32000000000000000000), D3 := ((6988816803571417793 : Rat) / 160000000000000000000), D4 := ((26049226267857102683 : Rat) / 1280000000000000000000), LB := ((1447742819562059 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((88468351417857140637 : Rat) / 32000000000000000000), R := ((3539369403696428481643 : Rat) / 1280000000000000000000), D0 := ((3539369403696428481643 : Rat) / 1280000000000000000000), D1 := ((1213001275696428481643 : Rat) / 1280000000000000000000), D2 := ((265212603696428481643 : Rat) / 1280000000000000000000), D3 := ((56545881410714198507 : Rat) / 1280000000000000000000), D4 := ((635346982142856163 : Rat) / 32000000000000000000), LB := ((5550279495452337 : Rat) / 5000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3539369403696428481643 : Rat) / 1280000000000000000000), R := ((1770002375339285668903 : Rat) / 640000000000000000000), D0 := ((1770002375339285668903 : Rat) / 640000000000000000000), D1 := ((606818311339285668903 : Rat) / 640000000000000000000), D2 := ((132923975339285668903 : Rat) / 640000000000000000000), D3 := ((5718122839285705467 : Rat) / 128000000000000000000), D4 := ((24778532303571390357 : Rat) / 1280000000000000000000), LB := ((8597837878181469 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1770002375339285668903 : Rat) / 640000000000000000000), R := ((3540640097660714193969 : Rat) / 1280000000000000000000), D0 := ((3540640097660714193969 : Rat) / 1280000000000000000000), D1 := ((1214271969660714193969 : Rat) / 1280000000000000000000), D2 := ((266483297660714193969 : Rat) / 1280000000000000000000), D3 := ((57816575374999910833 : Rat) / 1280000000000000000000), D4 := ((12071592660714267097 : Rat) / 640000000000000000000), LB := ((6999392231717971 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3540640097660714193969 : Rat) / 1280000000000000000000), R := ((885318861160714262533 : Rat) / 320000000000000000000), D0 := ((885318861160714262533 : Rat) / 320000000000000000000), D1 := ((303726829160714262533 : Rat) / 320000000000000000000), D2 := ((66779661160714262533 : Rat) / 320000000000000000000), D3 := ((14612980589285691749 : Rat) / 320000000000000000000), D4 := ((23507838339285678031 : Rat) / 1280000000000000000000), LB := ((6338258091206361 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((885318861160714262533 : Rat) / 320000000000000000000), R := ((708382158324999981259 : Rat) / 256000000000000000000), D0 := ((708382158324999981259 : Rat) / 256000000000000000000), D1 := ((243108532724999981259 : Rat) / 256000000000000000000), D2 := ((53550798324999981259 : Rat) / 256000000000000000000), D3 := ((59087269339285623159 : Rat) / 1280000000000000000000), D4 := ((5718122839285705467 : Rat) / 320000000000000000000), LB := ((3325337074537027 : Rat) / 5000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((708382158324999981259 : Rat) / 256000000000000000000), R := ((1771273069303571381229 : Rat) / 640000000000000000000), D0 := ((1771273069303571381229 : Rat) / 640000000000000000000), D1 := ((608089005303571381229 : Rat) / 640000000000000000000), D2 := ((134194669303571381229 : Rat) / 640000000000000000000), D3 := ((29861308160714239661 : Rat) / 640000000000000000000), D4 := ((4447428874999993141 : Rat) / 256000000000000000000), LB := ((997052189565667 : Rat) / 1250000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1771273069303571381229 : Rat) / 640000000000000000000), R := ((3543181485589285618621 : Rat) / 1280000000000000000000), D0 := ((3543181485589285618621 : Rat) / 1280000000000000000000), D1 := ((1216813357589285618621 : Rat) / 1280000000000000000000), D2 := ((269024685589285618621 : Rat) / 1280000000000000000000), D3 := ((12071592660714267097 : Rat) / 256000000000000000000), D4 := ((10800898696428554771 : Rat) / 640000000000000000000), LB := ((10359188144197229 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3543181485589285618621 : Rat) / 1280000000000000000000), R := ((110744276017857139837 : Rat) / 40000000000000000000), D0 := ((110744276017857139837 : Rat) / 40000000000000000000), D1 := ((38045272017857139837 : Rat) / 40000000000000000000), D2 := ((8426876017857139837 : Rat) / 40000000000000000000), D3 := ((1906040946428568489 : Rat) / 40000000000000000000), D4 := ((20966450410714253379 : Rat) / 1280000000000000000000), LB := ((13847050105294523 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((110744276017857139837 : Rat) / 40000000000000000000), R := ((3544452179553571330947 : Rat) / 1280000000000000000000), D0 := ((3544452179553571330947 : Rat) / 1280000000000000000000), D1 := ((1218084051553571330947 : Rat) / 1280000000000000000000), D2 := ((270295379553571330947 : Rat) / 1280000000000000000000), D3 := ((61628657267857047811 : Rat) / 1280000000000000000000), D4 := ((635346982142856163 : Rat) / 40000000000000000000), LB := ((1849293956881437 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((3544452179553571330947 : Rat) / 1280000000000000000000), R := ((354508752653571418711 : Rat) / 128000000000000000000), D0 := ((354508752653571418711 : Rat) / 128000000000000000000), D1 := ((121871939853571418711 : Rat) / 128000000000000000000), D2 := ((27093072653571418711 : Rat) / 128000000000000000000), D3 := ((31132002124999951987 : Rat) / 640000000000000000000), D4 := ((19695756446428541053 : Rat) / 1280000000000000000000), LB := ((6088812816266581 : Rat) / 2500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((354508752653571418711 : Rat) / 128000000000000000000), R := ((886589555124999974859 : Rat) / 320000000000000000000), D0 := ((886589555124999974859 : Rat) / 320000000000000000000), D1 := ((304997523124999974859 : Rat) / 320000000000000000000), D2 := ((68050355124999974859 : Rat) / 320000000000000000000), D3 := ((635346982142856163 : Rat) / 12800000000000000000), D4 := ((1906040946428568489 : Rat) / 128000000000000000000), LB := ((3861385069324763 : Rat) / 10000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((886589555124999974859 : Rat) / 320000000000000000000), R := ((1773814457232142805881 : Rat) / 640000000000000000000), D0 := ((1773814457232142805881 : Rat) / 640000000000000000000), D1 := ((610630393232142805881 : Rat) / 640000000000000000000), D2 := ((136736057232142805881 : Rat) / 640000000000000000000), D3 := ((32402696089285664313 : Rat) / 640000000000000000000), D4 := ((4447428874999993141 : Rat) / 320000000000000000000), LB := ((2261258028970703 : Rat) / 1000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((1773814457232142805881 : Rat) / 640000000000000000000), R := ((443612451053571415511 : Rat) / 160000000000000000000), D0 := ((443612451053571415511 : Rat) / 160000000000000000000), D1 := ((152816435053571415511 : Rat) / 160000000000000000000), D2 := ((34342851053571415511 : Rat) / 160000000000000000000), D3 := ((8259510767857130119 : Rat) / 160000000000000000000), D4 := ((8259510767857130119 : Rat) / 640000000000000000000), LB := ((593018340574257 : Rat) / 125000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((443612451053571415511 : Rat) / 160000000000000000000), R := ((177572049817857137437 : Rat) / 64000000000000000000), D0 := ((177572049817857137437 : Rat) / 64000000000000000000), D1 := ((61253643417857137437 : Rat) / 64000000000000000000), D2 := ((13864209817857137437 : Rat) / 64000000000000000000), D3 := ((17154368517857116401 : Rat) / 320000000000000000000), D4 := ((1906040946428568489 : Rat) / 160000000000000000000), LB := ((13124682851253233 : Rat) / 5000000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((177572049817857137437 : Rat) / 64000000000000000000), R := ((222123899017857135837 : Rat) / 80000000000000000000), D0 := ((222123899017857135837 : Rat) / 80000000000000000000), D1 := ((76725891017857135837 : Rat) / 80000000000000000000), D2 := ((17489099017857135837 : Rat) / 80000000000000000000), D3 := ((4447428874999993141 : Rat) / 80000000000000000000), D4 := ((635346982142856163 : Rat) / 64000000000000000000), LB := ((2903027478954101 : Rat) / 250000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((222123899017857135837 : Rat) / 80000000000000000000), R := ((444883145017857127837 : Rat) / 160000000000000000000), D0 := ((444883145017857127837 : Rat) / 160000000000000000000), D1 := ((154087129017857127837 : Rat) / 160000000000000000000), D2 := ((35613545017857127837 : Rat) / 160000000000000000000), D3 := ((1906040946428568489 : Rat) / 32000000000000000000), D4 := ((635346982142856163 : Rat) / 80000000000000000000), LB := ((7533466117823129 : Rat) / 500000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((444883145017857127837 : Rat) / 160000000000000000000), R := ((27844905749999999 : Rat) / 10000000000000000), D0 := ((27844905749999999 : Rat) / 10000000000000000), D1 := ((9670154749999999 : Rat) / 10000000000000000), D2 := ((2265555749999999 : Rat) / 10000000000000000), D3 := ((635346982142856163 : Rat) / 10000000000000000000), D4 := ((635346982142856163 : Rat) / 160000000000000000000), LB := ((3327521365871011 : Rat) / 50000000000000000) },
  { w1 := ((18699629862222447 : Rat) / 10000000000000000), w2 := (0 : Rat), w3 := ((1602382889761217 : Rat) / 10000000000000000), w4 := ((10659795420268289 : Rat) / 100000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((27209558767857142837 : Rat) / 10000000000000000000), s4 := ((27844905749999999 : Rat) / 10000000000000000), L := ((27844905749999999 : Rat) / 10000000000000000), R := ((69664685267857142891 : Rat) / 25000000000000000000), D0 := ((69664685267857142891 : Rat) / 25000000000000000000), D1 := ((24227807767857142891 : Rat) / 25000000000000000000), D2 := ((5716310267857142891 : Rat) / 25000000000000000000), D3 := ((3281576696428571597 : Rat) / 50000000000000000000), D4 := ((52420892857145391 : Rat) / 25000000000000000000), LB := ((1123064597164879 : Rat) / 10000000000000000) }
]

def block158RightChunk000L : Rat := ((89319595982142857211 : Rat) / 50000000000000000000)
def block158RightChunk000R : Rat := ((69664685267857142891 : Rat) / 25000000000000000000)

def block158RightChunk000Certificate : Bool :=
  allBoxesValid block158RightChunk000 &&
  coversFromBool block158RightChunk000 block158RightChunk000L block158RightChunk000R

theorem block158RightChunk000Certificate_eq_true :
    block158RightChunk000Certificate = true := by
  native_decide

def block158RightChainCertificate : Bool :=
  decide (
    block158RightL = ((89319595982142857211 : Rat) / 50000000000000000000) /\
    ((69664685267857142891 : Rat) / 25000000000000000000) = block158RightR)

theorem block158RightChainCertificate_eq_true :
    block158RightChainCertificate = true := by
  native_decide

def block158LeftBoxCount : Nat := boxCount block158LeftBoxes
def block158RightBoxCount : Nat := 79

def block158_rational_certificate : Prop :=
    block158LeftCertificate = true /\
    block158RightChainCertificate = true /\
    block158RightChunk000Certificate = true

theorem block158_rational_certificate_proof :
    block158_rational_certificate := by
  exact ⟨block158LeftCertificate_eq_true, block158RightChainCertificate_eq_true, block158RightChunk000Certificate_eq_true⟩

end Block158
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block158

open Set

def block158W1 : Rat := ((18699629862222447 : Rat) / 10000000000000000)
def block158W2 : Rat := (0 : Rat)
def block158W3 : Rat := ((1602382889761217 : Rat) / 10000000000000000)
def block158W4 : Rat := ((10659795420268289 : Rat) / 100000000000000000)
def block158S1 : Rat := ((18174751 : Rat) / 10000000)
def block158S2 : Rat := ((511587 : Rat) / 200000)
def block158S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block158S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block158V (y : ℝ) : ℝ :=
  ratPotential block158W1 block158W2 block158W3 block158W4 block158S1 block158S2 block158S3 block158S4 y

def block158LeftParamsCertificate : Bool :=
  allBoxesSameParams block158LeftBoxes block158W1 block158W2 block158W3 block158W4 block158S1 block158S2 block158S3 block158S4

theorem block158LeftParamsCertificate_eq_true :
    block158LeftParamsCertificate = true := by
  native_decide

theorem block158_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block158LeftL : ℝ) (block158LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block158S1 : ℝ))
    (hy2ne : y ≠ (block158S2 : ℝ))
    (hy3ne : y ≠ (block158S3 : ℝ))
    (hy4ne : y ≠ (block158S4 : ℝ)) :
    0 < block158V y := by
  have hcert := block158LeftCertificate_eq_true
  unfold block158LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block158LeftBoxes) (lo := block158LeftL) (hi := block158LeftR)
    (w1 := block158W1) (w2 := block158W2) (w3 := block158W3) (w4 := block158W4)
    (s1 := block158S1) (s2 := block158S2) (s3 := block158S3) (s4 := block158S4)
    hboxes hcover block158LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block158RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block158RightChunk000 block158W1 block158W2 block158W3 block158W4 block158S1 block158S2 block158S3 block158S4

theorem block158RightChunk000ParamsCertificate_eq_true :
    block158RightChunk000ParamsCertificate = true := by
  native_decide

theorem block158_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block158RightChunk000L : ℝ) (block158RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block158S1 : ℝ))
    (hy2ne : y ≠ (block158S2 : ℝ))
    (hy3ne : y ≠ (block158S3 : ℝ))
    (hy4ne : y ≠ (block158S4 : ℝ)) :
    0 < block158V y := by
  have hcert := block158RightChunk000Certificate_eq_true
  unfold block158RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block158RightChunk000) (lo := block158RightChunk000L) (hi := block158RightChunk000R)
    (w1 := block158W1) (w2 := block158W2) (w3 := block158W3) (w4 := block158W4)
    (s1 := block158S1) (s2 := block158S2) (s3 := block158S3) (s4 := block158S4)
    hboxes hcover block158RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block158_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block158RightL : ℝ) (block158RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block158S1 : ℝ))
    (hy2ne : y ≠ (block158S2 : ℝ))
    (hy3ne : y ≠ (block158S3 : ℝ))
    (hy4ne : y ≠ (block158S4 : ℝ)) :
    0 < block158V y := by
  have hL : (block158RightChunk000L : ℝ) = (block158RightL : ℝ) := by
    norm_num [block158RightChunk000L, block158RightL]
  have hR : (block158RightChunk000R : ℝ) = (block158RightR : ℝ) := by
    norm_num [block158RightChunk000R, block158RightR]
  have hyc : y ∈ Icc (block158RightChunk000L : ℝ) (block158RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block158_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block158_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block158LeftL : ℝ) (block158LeftR : ℝ) →
    y ≠ 0 → y ≠ (block158S1 : ℝ) → y ≠ (block158S2 : ℝ) →
    y ≠ (block158S3 : ℝ) → y ≠ (block158S4 : ℝ) → 0 < block158V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block158RightL : ℝ) (block158RightR : ℝ) →
    y ≠ 0 → y ≠ (block158S1 : ℝ) → y ≠ (block158S2 : ℝ) →
    y ≠ (block158S3 : ℝ) → y ≠ (block158S4 : ℝ) → 0 < block158V y)

theorem block158_reallog_certificate_proof :
    block158_reallog_certificate := by
  exact ⟨block158_left_V_pos, block158_right_V_pos⟩

end Block158
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block158.block158V
#check Erdos1038Lean.M1817475.Block158.block158_left_V_pos
#check Erdos1038Lean.M1817475.Block158.block158_right_V_pos
#check Erdos1038Lean.M1817475.Block158.block158_reallog_certificate_proof
