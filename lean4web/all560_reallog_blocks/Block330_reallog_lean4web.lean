/-
Self-contained Lean4Web paste file.
Block 330 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block330

def block330LeftL : Rat := ((37638372767857142999 : Rat) / 50000000000000000000)
def block330LeftR : Rat := ((3764814732142857157 : Rat) / 5000000000000000000)
def block330RightL : Rat := ((87638372767857142999 : Rat) / 50000000000000000000)
def block330RightR : Rat := ((13764814732142857157 : Rat) / 5000000000000000000)

def block330LeftBoxes : List RatBox := [
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37638372767857142999 : Rat) / 50000000000000000000), R := ((3764814732142857157 : Rat) / 5000000000000000000), D0 := ((3764814732142857157 : Rat) / 5000000000000000000), D1 := ((53235382232142857001 : Rat) / 50000000000000000000), D2 := ((90258377232142857001 : Rat) / 50000000000000000000), D3 := ((24010994776785714251 : Rat) / 12500000000000000000), D4 := ((100980133660714280599 : Rat) / 50000000000000000000), LB := ((6559676108703033 : Rat) / 1000000000000000000) }
]

def block330LeftCertificate : Bool :=
  allBoxesValid block330LeftBoxes &&
  coversFromBool block330LeftBoxes block330LeftL block330LeftR

theorem block330LeftCertificate_eq_true :
    block330LeftCertificate = true := by
  native_decide

def block330RightChunk000 : List RatBox := [
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87638372767857142999 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3235382232142857001 : Rat) / 50000000000000000000), D2 := ((40258377232142857001 : Rat) / 50000000000000000000), D3 := ((11510994776785714251 : Rat) / 12500000000000000000), D4 := ((50980133660714280599 : Rat) / 50000000000000000000), LB := ((20225007400241273 : Rat) / 10000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42808596875000000003 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((1018477475064577 : Rat) / 5000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((24297099375000000003 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((13132146636987127 : Rat) / 100000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19669225000000000003 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((4407139088778593 : Rat) / 50000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((17355287812500000003 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((12927569314981 : Rat) / 500000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((15041350625000000003 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((468229801763379 : Rat) / 20000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13884382031250000003 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((24824661704015427 : Rat) / 10000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12727413437500000003 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((8043976263339997 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((12148929140625000003 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((135932817115921 : Rat) / 156250000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11570444843750000003 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((2976392930390759 : Rat) / 500000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((11281202695312500003 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((6771558579584891 : Rat) / 2000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10991960546875000003 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((2342977964324533 : Rat) / 2000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10702718398437500003 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((950773107682007 : Rat) / 200000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10558097324218750003 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((791969806579601 : Rat) / 200000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10413476250000000003 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((3268297972382983 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((10268855175781250003 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((26827716640750177 : Rat) / 10000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((10124234101562500003 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((2207140953029041 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9979613027343750003 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((9228135063742149 : Rat) / 5000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9834991953125000003 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((2003558415149681 : Rat) / 1250000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9690370878906250003 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((23185408114777 : Rat) / 15625000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9545749804687500003 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((2988527034114341 : Rat) / 2000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9401128730468750003 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((328040982682537 : Rat) / 200000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((9256507656250000003 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((60266696395311 : Rat) / 31250000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((9111886582031250003 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((4733765553301461 : Rat) / 2000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((6392817021 : Rat) / 2560000000), D0 := ((6392817021 : Rat) / 2560000000), D1 := ((348016153 : Rat) / 512000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8967265507812500003 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((592760343036447 : Rat) / 200000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6392817021 : Rat) / 2560000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((155496579 : Rat) / 2560000000), D3 := ((8822644433593750003 : Rat) / 50000000000000000000), D4 := ((6879399493582586799 : Rat) / 25000000000000000000), LB := ((7457852113165131 : Rat) / 2000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((6407626219 : Rat) / 2560000000), D0 := ((6407626219 : Rat) / 2560000000), D1 := ((1754889963 : Rat) / 2560000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8678023359375000003 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((1168294286519371 : Rat) / 250000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6407626219 : Rat) / 2560000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((140687381 : Rat) / 2560000000), D3 := ((8533402285156250003 : Rat) / 50000000000000000000), D4 := ((6734778419363836799 : Rat) / 25000000000000000000), LB := ((5809016832439201 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((8388781210937500003 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((50813392578547 : Rat) / 25000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((3222324607 : Rat) / 1280000000), D0 := ((3222324607 : Rat) / 1280000000), D1 := ((895956479 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((8099539062500000003 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((2175395545695169 : Rat) / 400000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3222324607 : Rat) / 1280000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((51832193 : Rat) / 1280000000), D3 := ((7810296914062500003 : Rat) / 50000000000000000000), D4 := ((6373225733816961799 : Rat) / 25000000000000000000), LB := ((9907826363249383 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7521054765625000003 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((5710245171805711 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6942570468750000003 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((35733885714945013 : Rat) / 10000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((1028959601875000000003 : Rat) / 400000000000000000000), D0 := ((1028959601875000000003 : Rat) / 400000000000000000000), D1 := ((301969561875000000003 : Rat) / 400000000000000000000), D2 := ((5785601875000000003 : Rat) / 400000000000000000000), D3 := ((5785601875000000003 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((4187869903234279 : Rat) / 100000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1028959601875000000003 : Rat) / 400000000000000000000), R := ((517372601875000000003 : Rat) / 200000000000000000000), D0 := ((517372601875000000003 : Rat) / 200000000000000000000), D1 := ((153877581875000000003 : Rat) / 200000000000000000000), D2 := ((5785601875000000003 : Rat) / 200000000000000000000), D3 := ((40499213125000000021 : Rat) / 400000000000000000000), D4 := ((79988449553571388781 : Rat) / 400000000000000000000), LB := ((712198548784361 : Rat) / 50000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((517372601875000000003 : Rat) / 200000000000000000000), R := ((1040530805625000000009 : Rat) / 400000000000000000000), D0 := ((1040530805625000000009 : Rat) / 400000000000000000000), D1 := ((313540765625000000009 : Rat) / 400000000000000000000), D2 := ((17356805625000000009 : Rat) / 400000000000000000000), D3 := ((17356805625000000009 : Rat) / 200000000000000000000), D4 := ((37101423839285694389 : Rat) / 200000000000000000000), LB := ((844015748319743 : Rat) / 200000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1040530805625000000009 : Rat) / 400000000000000000000), R := ((261579101875000000003 : Rat) / 100000000000000000000), D0 := ((261579101875000000003 : Rat) / 100000000000000000000), D1 := ((79831591875000000003 : Rat) / 100000000000000000000), D2 := ((5785601875000000003 : Rat) / 100000000000000000000), D3 := ((5785601875000000003 : Rat) / 80000000000000000000), D4 := ((2736689832142855551 : Rat) / 16000000000000000000), LB := ((1244851597699527 : Rat) / 250000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261579101875000000003 : Rat) / 100000000000000000000), R := ((210420401875000000003 : Rat) / 80000000000000000000), D0 := ((210420401875000000003 : Rat) / 80000000000000000000), D1 := ((65022393875000000003 : Rat) / 80000000000000000000), D2 := ((5785601875000000003 : Rat) / 80000000000000000000), D3 := ((5785601875000000003 : Rat) / 100000000000000000000), D4 := ((15657910982142847193 : Rat) / 100000000000000000000), LB := ((1595923214576017 : Rat) / 100000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((210420401875000000003 : Rat) / 80000000000000000000), R := ((528943805625000000009 : Rat) / 200000000000000000000), D0 := ((528943805625000000009 : Rat) / 200000000000000000000), D1 := ((165448785625000000009 : Rat) / 200000000000000000000), D2 := ((17356805625000000009 : Rat) / 200000000000000000000), D3 := ((17356805625000000009 : Rat) / 400000000000000000000), D4 := ((56846042053571388769 : Rat) / 400000000000000000000), LB := ((1980976920044253 : Rat) / 50000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((528943805625000000009 : Rat) / 200000000000000000000), R := ((133682351875000000003 : Rat) / 50000000000000000000), D0 := ((133682351875000000003 : Rat) / 50000000000000000000), D1 := ((42808596875000000003 : Rat) / 50000000000000000000), D2 := ((5785601875000000003 : Rat) / 50000000000000000000), D3 := ((5785601875000000003 : Rat) / 200000000000000000000), D4 := ((25530220089285694383 : Rat) / 200000000000000000000), LB := ((1106589205384807 : Rat) / 20000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133682351875000000003 : Rat) / 50000000000000000000), R := ((538695202946428571579 : Rat) / 200000000000000000000), D0 := ((538695202946428571579 : Rat) / 200000000000000000000), D1 := ((175200182946428571579 : Rat) / 200000000000000000000), D2 := ((27108202946428571579 : Rat) / 200000000000000000000), D3 := ((3965795446428571567 : Rat) / 200000000000000000000), D4 := ((987230910714284719 : Rat) / 10000000000000000000), LB := ((10803277425481539 : Rat) / 100000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((538695202946428571579 : Rat) / 200000000000000000000), R := ((271330499196428571573 : Rat) / 100000000000000000000), D0 := ((271330499196428571573 : Rat) / 100000000000000000000), D1 := ((89582989196428571573 : Rat) / 100000000000000000000), D2 := ((15536999196428571573 : Rat) / 100000000000000000000), D3 := ((3965795446428571567 : Rat) / 100000000000000000000), D4 := ((15778822767857122813 : Rat) / 200000000000000000000), LB := ((43244412034949 : Rat) / 10000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((271330499196428571573 : Rat) / 100000000000000000000), R := ((2174609789017857144151 : Rat) / 800000000000000000000), D0 := ((2174609789017857144151 : Rat) / 800000000000000000000), D1 := ((720629709017857144151 : Rat) / 800000000000000000000), D2 := ((128261789017857144151 : Rat) / 800000000000000000000), D3 := ((35692159017857144103 : Rat) / 800000000000000000000), D4 := ((5906513660714275623 : Rat) / 100000000000000000000), LB := ((1850586799715037 : Rat) / 100000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2174609789017857144151 : Rat) / 800000000000000000000), R := ((1089287792232142857859 : Rat) / 400000000000000000000), D0 := ((1089287792232142857859 : Rat) / 400000000000000000000), D1 := ((362297752232142857859 : Rat) / 400000000000000000000), D2 := ((66113792232142857859 : Rat) / 400000000000000000000), D3 := ((3965795446428571567 : Rat) / 80000000000000000000), D4 := ((43286313839285633417 : Rat) / 800000000000000000000), LB := ((6928426248843267 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1089287792232142857859 : Rat) / 400000000000000000000), R := ((4361116964375000003003 : Rat) / 1600000000000000000000), D0 := ((4361116964375000003003 : Rat) / 1600000000000000000000), D1 := ((1453156804375000003003 : Rat) / 1600000000000000000000), D2 := ((268420964375000003003 : Rat) / 1600000000000000000000), D3 := ((83281704375000002907 : Rat) / 1600000000000000000000), D4 := ((786410367857141237 : Rat) / 16000000000000000000), LB := ((8876969402584811 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4361116964375000003003 : Rat) / 1600000000000000000000), R := ((436508275982142857457 : Rat) / 160000000000000000000), D0 := ((436508275982142857457 : Rat) / 160000000000000000000), D1 := ((145712259982142857457 : Rat) / 160000000000000000000), D2 := ((27238675982142857457 : Rat) / 160000000000000000000), D3 := ((43623749910714287237 : Rat) / 800000000000000000000), D4 := ((74675241339285552133 : Rat) / 1600000000000000000000), LB := ((5100570800769033 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((436508275982142857457 : Rat) / 160000000000000000000), R := ((4369048555267857146137 : Rat) / 1600000000000000000000), D0 := ((4369048555267857146137 : Rat) / 1600000000000000000000), D1 := ((1461088395267857146137 : Rat) / 1600000000000000000000), D2 := ((276352555267857146137 : Rat) / 1600000000000000000000), D3 := ((91213295267857146041 : Rat) / 1600000000000000000000), D4 := ((35354722946428490283 : Rat) / 800000000000000000000), LB := ((4050010140398963 : Rat) / 2000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4369048555267857146137 : Rat) / 1600000000000000000000), R := ((8742062905982142863841 : Rat) / 3200000000000000000000), D0 := ((8742062905982142863841 : Rat) / 3200000000000000000000), D1 := ((2926142585982142863841 : Rat) / 3200000000000000000000), D2 := ((556670905982142863841 : Rat) / 3200000000000000000000), D3 := ((186392385982142863649 : Rat) / 3200000000000000000000), D4 := ((66743650446428408999 : Rat) / 1600000000000000000000), LB := ((1190499884213339 : Rat) / 250000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8742062905982142863841 : Rat) / 3200000000000000000000), R := ((546626793839285714713 : Rat) / 200000000000000000000), D0 := ((546626793839285714713 : Rat) / 200000000000000000000), D1 := ((183131773839285714713 : Rat) / 200000000000000000000), D2 := ((35039793839285714713 : Rat) / 200000000000000000000), D3 := ((11897386339285714701 : Rat) / 200000000000000000000), D4 := ((129521505446428246431 : Rat) / 3200000000000000000000), LB := ((4745771677744301 : Rat) / 1250000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((546626793839285714713 : Rat) / 200000000000000000000), R := ((349999779875000000279 : Rat) / 128000000000000000000), D0 := ((349999779875000000279 : Rat) / 128000000000000000000), D1 := ((117362967075000000279 : Rat) / 128000000000000000000), D2 := ((22584099875000000279 : Rat) / 128000000000000000000), D3 := ((194323976875000006783 : Rat) / 3200000000000000000000), D4 := ((7847231874999979679 : Rat) / 200000000000000000000), LB := ((15130625416796273 : Rat) / 5000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((349999779875000000279 : Rat) / 128000000000000000000), R := ((4376980146160714289271 : Rat) / 1600000000000000000000), D0 := ((4376980146160714289271 : Rat) / 1600000000000000000000), D1 := ((1469019986160714289271 : Rat) / 1600000000000000000000), D2 := ((284284146160714289271 : Rat) / 1600000000000000000000), D3 := ((3965795446428571567 : Rat) / 64000000000000000000), D4 := ((121589914553571103297 : Rat) / 3200000000000000000000), LB := ((2456211107623063 : Rat) / 1000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4376980146160714289271 : Rat) / 1600000000000000000000), R := ((8757926087767857150109 : Rat) / 3200000000000000000000), D0 := ((8757926087767857150109 : Rat) / 3200000000000000000000), D1 := ((2942005767767857150109 : Rat) / 3200000000000000000000), D2 := ((572534087767857150109 : Rat) / 3200000000000000000000), D3 := ((202255567767857149917 : Rat) / 3200000000000000000000), D4 := ((11762411910714253173 : Rat) / 320000000000000000000), LB := ((10467669316017447 : Rat) / 5000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8757926087767857150109 : Rat) / 3200000000000000000000), R := ((2190472970803571430419 : Rat) / 800000000000000000000), D0 := ((2190472970803571430419 : Rat) / 800000000000000000000), D1 := ((736492890803571430419 : Rat) / 800000000000000000000), D2 := ((144124970803571430419 : Rat) / 800000000000000000000), D3 := ((51555340803571430371 : Rat) / 800000000000000000000), D4 := ((113658323660713960163 : Rat) / 3200000000000000000000), LB := ((4864557025841959 : Rat) / 2500000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2190472970803571430419 : Rat) / 800000000000000000000), R := ((8765857678660714293243 : Rat) / 3200000000000000000000), D0 := ((8765857678660714293243 : Rat) / 3200000000000000000000), D1 := ((2949937358660714293243 : Rat) / 3200000000000000000000), D2 := ((580465678660714293243 : Rat) / 3200000000000000000000), D3 := ((210187158660714293051 : Rat) / 3200000000000000000000), D4 := ((27423132053571347149 : Rat) / 800000000000000000000), LB := ((10110002158158493 : Rat) / 5000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8765857678660714293243 : Rat) / 3200000000000000000000), R := ((876982347410714286481 : Rat) / 320000000000000000000), D0 := ((876982347410714286481 : Rat) / 320000000000000000000), D1 := ((295390315410714286481 : Rat) / 320000000000000000000), D2 := ((58443147410714286481 : Rat) / 320000000000000000000), D3 := ((107076477053571432309 : Rat) / 1600000000000000000000), D4 := ((105726732767856817029 : Rat) / 3200000000000000000000), LB := ((5830824093661091 : Rat) / 2500000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((876982347410714286481 : Rat) / 320000000000000000000), R := ((8773789269553571436377 : Rat) / 3200000000000000000000), D0 := ((8773789269553571436377 : Rat) / 3200000000000000000000), D1 := ((2957868949553571436377 : Rat) / 3200000000000000000000), D2 := ((588397269553571436377 : Rat) / 3200000000000000000000), D3 := ((43623749910714287237 : Rat) / 640000000000000000000), D4 := ((50880468660714122731 : Rat) / 1600000000000000000000), LB := ((3610740076968183 : Rat) / 1250000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8773789269553571436377 : Rat) / 3200000000000000000000), R := ((1097219383125000000993 : Rat) / 400000000000000000000), D0 := ((1097219383125000000993 : Rat) / 400000000000000000000), D1 := ((370229343125000000993 : Rat) / 400000000000000000000), D2 := ((74045383125000000993 : Rat) / 400000000000000000000), D3 := ((27760568125000000969 : Rat) / 400000000000000000000), D4 := ((19559028374999934779 : Rat) / 640000000000000000000), LB := ((37043043156421707 : Rat) / 10000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1097219383125000000993 : Rat) / 400000000000000000000), R := ((4392843327946428575539 : Rat) / 1600000000000000000000), D0 := ((4392843327946428575539 : Rat) / 1600000000000000000000), D1 := ((1484883167946428575539 : Rat) / 1600000000000000000000), D2 := ((300147327946428575539 : Rat) / 1600000000000000000000), D3 := ((115008067946428575443 : Rat) / 1600000000000000000000), D4 := ((11728668303571387791 : Rat) / 400000000000000000000), LB := ((537245116898899 : Rat) / 2000000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4392843327946428575539 : Rat) / 1600000000000000000000), R := ((2198404561696428573553 : Rat) / 800000000000000000000), D0 := ((2198404561696428573553 : Rat) / 800000000000000000000), D1 := ((744424481696428573553 : Rat) / 800000000000000000000), D2 := ((152056561696428573553 : Rat) / 800000000000000000000), D3 := ((11897386339285714701 : Rat) / 160000000000000000000), D4 := ((42948877767856979597 : Rat) / 1600000000000000000000), LB := ((172030644566451 : Rat) / 50000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2198404561696428573553 : Rat) / 800000000000000000000), R := ((4400774918839285718673 : Rat) / 1600000000000000000000), D0 := ((4400774918839285718673 : Rat) / 1600000000000000000000), D1 := ((1492814758839285718673 : Rat) / 1600000000000000000000), D2 := ((308078918839285718673 : Rat) / 1600000000000000000000), D3 := ((122939658839285718577 : Rat) / 1600000000000000000000), D4 := ((3898308232142840803 : Rat) / 160000000000000000000), LB := ((3979667301600931 : Rat) / 500000000000000000) },
  { w1 := ((9498486707815261 : Rat) / 10000000000000000), w2 := ((1179365044608273 : Rat) / 25000000000000000), w3 := ((7166933576613979 : Rat) / 50000000000000000), w4 := ((2736970013854167 : Rat) / 20000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133682351875000000003 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4400774918839285718673 : Rat) / 1600000000000000000000), R := ((13764814732142857157 : Rat) / 5000000000000000000), D0 := ((13764814732142857157 : Rat) / 5000000000000000000), D1 := ((4677439232142857157 : Rat) / 5000000000000000000), D2 := ((975139732142857157 : Rat) / 5000000000000000000), D3 := ((3965795446428571567 : Rat) / 50000000000000000000), D4 := ((35017286874999836463 : Rat) / 1600000000000000000000), LB := ((3516566979372887 : Rat) / 250000000000000000) }
]

def block330RightChunk000L : Rat := ((87638372767857142999 : Rat) / 50000000000000000000)
def block330RightChunk000R : Rat := ((13764814732142857157 : Rat) / 5000000000000000000)

def block330RightChunk000Certificate : Bool :=
  allBoxesValid block330RightChunk000 &&
  coversFromBool block330RightChunk000 block330RightChunk000L block330RightChunk000R

theorem block330RightChunk000Certificate_eq_true :
    block330RightChunk000Certificate = true := by
  native_decide

def block330RightChainCertificate : Bool :=
  decide (
    block330RightL = ((87638372767857142999 : Rat) / 50000000000000000000) /\
    ((13764814732142857157 : Rat) / 5000000000000000000) = block330RightR)

theorem block330RightChainCertificate_eq_true :
    block330RightChainCertificate = true := by
  native_decide

def block330LeftBoxCount : Nat := boxCount block330LeftBoxes
def block330RightBoxCount : Nat := 61

def block330_rational_certificate : Prop :=
    block330LeftCertificate = true /\
    block330RightChainCertificate = true /\
    block330RightChunk000Certificate = true

theorem block330_rational_certificate_proof :
    block330_rational_certificate := by
  exact ⟨block330LeftCertificate_eq_true, block330RightChainCertificate_eq_true, block330RightChunk000Certificate_eq_true⟩

end Block330
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block330

open Set

def block330W1 : Rat := ((9498486707815261 : Rat) / 10000000000000000)
def block330W2 : Rat := ((1179365044608273 : Rat) / 25000000000000000)
def block330W3 : Rat := ((7166933576613979 : Rat) / 50000000000000000)
def block330W4 : Rat := ((2736970013854167 : Rat) / 20000000000000000)
def block330S1 : Rat := ((18174751 : Rat) / 10000000)
def block330S2 : Rat := ((511587 : Rat) / 200000)
def block330S3 : Rat := ((133682351875000000003 : Rat) / 50000000000000000000)
def block330S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block330V (y : ℝ) : ℝ :=
  ratPotential block330W1 block330W2 block330W3 block330W4 block330S1 block330S2 block330S3 block330S4 y

def block330LeftParamsCertificate : Bool :=
  allBoxesSameParams block330LeftBoxes block330W1 block330W2 block330W3 block330W4 block330S1 block330S2 block330S3 block330S4

theorem block330LeftParamsCertificate_eq_true :
    block330LeftParamsCertificate = true := by
  native_decide

theorem block330_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block330LeftL : ℝ) (block330LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block330S1 : ℝ))
    (hy2ne : y ≠ (block330S2 : ℝ))
    (hy3ne : y ≠ (block330S3 : ℝ))
    (hy4ne : y ≠ (block330S4 : ℝ)) :
    0 < block330V y := by
  have hcert := block330LeftCertificate_eq_true
  unfold block330LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block330LeftBoxes) (lo := block330LeftL) (hi := block330LeftR)
    (w1 := block330W1) (w2 := block330W2) (w3 := block330W3) (w4 := block330W4)
    (s1 := block330S1) (s2 := block330S2) (s3 := block330S3) (s4 := block330S4)
    hboxes hcover block330LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block330RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block330RightChunk000 block330W1 block330W2 block330W3 block330W4 block330S1 block330S2 block330S3 block330S4

theorem block330RightChunk000ParamsCertificate_eq_true :
    block330RightChunk000ParamsCertificate = true := by
  native_decide

theorem block330_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block330RightChunk000L : ℝ) (block330RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block330S1 : ℝ))
    (hy2ne : y ≠ (block330S2 : ℝ))
    (hy3ne : y ≠ (block330S3 : ℝ))
    (hy4ne : y ≠ (block330S4 : ℝ)) :
    0 < block330V y := by
  have hcert := block330RightChunk000Certificate_eq_true
  unfold block330RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block330RightChunk000) (lo := block330RightChunk000L) (hi := block330RightChunk000R)
    (w1 := block330W1) (w2 := block330W2) (w3 := block330W3) (w4 := block330W4)
    (s1 := block330S1) (s2 := block330S2) (s3 := block330S3) (s4 := block330S4)
    hboxes hcover block330RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block330_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block330RightL : ℝ) (block330RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block330S1 : ℝ))
    (hy2ne : y ≠ (block330S2 : ℝ))
    (hy3ne : y ≠ (block330S3 : ℝ))
    (hy4ne : y ≠ (block330S4 : ℝ)) :
    0 < block330V y := by
  have hL : (block330RightChunk000L : ℝ) = (block330RightL : ℝ) := by
    norm_num [block330RightChunk000L, block330RightL]
  have hR : (block330RightChunk000R : ℝ) = (block330RightR : ℝ) := by
    norm_num [block330RightChunk000R, block330RightR]
  have hyc : y ∈ Icc (block330RightChunk000L : ℝ) (block330RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block330_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block330_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block330LeftL : ℝ) (block330LeftR : ℝ) →
    y ≠ 0 → y ≠ (block330S1 : ℝ) → y ≠ (block330S2 : ℝ) →
    y ≠ (block330S3 : ℝ) → y ≠ (block330S4 : ℝ) → 0 < block330V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block330RightL : ℝ) (block330RightR : ℝ) →
    y ≠ 0 → y ≠ (block330S1 : ℝ) → y ≠ (block330S2 : ℝ) →
    y ≠ (block330S3 : ℝ) → y ≠ (block330S4 : ℝ) → 0 < block330V y)

theorem block330_reallog_certificate_proof :
    block330_reallog_certificate := by
  exact ⟨block330_left_V_pos, block330_right_V_pos⟩

end Block330
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block330.block330V
#check Erdos1038Lean.M1817475.Block330.block330_left_V_pos
#check Erdos1038Lean.M1817475.Block330.block330_right_V_pos
#check Erdos1038Lean.M1817475.Block330.block330_reallog_certificate_proof
