/-
Self-contained Lean4Web paste file.
Block 350 real-log V_i(y) > 0 check for the M=1.817475 candidate.

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
namespace Block350

def block350LeftL : Rat := ((37442881696428571579 : Rat) / 50000000000000000000)
def block350LeftR : Rat := ((749053125000000003 : Rat) / 1000000000000000000)
def block350RightL : Rat := ((87442881696428571579 : Rat) / 50000000000000000000)
def block350RightR : Rat := ((2749053125000000003 : Rat) / 1000000000000000000)

def block350LeftBoxes : List RatBox := [
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((37442881696428571579 : Rat) / 50000000000000000000), R := ((749053125000000003 : Rat) / 1000000000000000000), D0 := ((749053125000000003 : Rat) / 1000000000000000000), D1 := ((53430873303571428421 : Rat) / 50000000000000000000), D2 := ((90453868303571428421 : Rat) / 50000000000000000000), D3 := ((5990530502232142849 : Rat) / 3125000000000000000), D4 := ((101175624732142852019 : Rat) / 50000000000000000000), LB := ((1560892453891783 : Rat) / 250000000000000000) }
]

def block350LeftCertificate : Bool :=
  allBoxesValid block350LeftBoxes &&
  coversFromBool block350LeftBoxes block350LeftL block350LeftR

theorem block350LeftCertificate_eq_true :
    block350LeftCertificate = true := by
  native_decide

def block350RightChunk000 : List RatBox := [
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((87442881696428571579 : Rat) / 50000000000000000000), R := ((18174751 : Rat) / 10000000), D0 := ((18174751 : Rat) / 10000000), D1 := ((3430873303571428421 : Rat) / 50000000000000000000), D2 := ((40453868303571428421 : Rat) / 50000000000000000000), D3 := ((2865530502232142849 : Rat) / 3125000000000000000), D4 := ((51175624732142852019 : Rat) / 50000000000000000000), LB := ((46263255027731 : Rat) / 25000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((18174751 : Rat) / 10000000), R := ((43754101 : Rat) / 20000000), D0 := ((43754101 : Rat) / 20000000), D1 := ((7404599 : Rat) / 20000000), D2 := ((7404599 : Rat) / 10000000), D3 := ((42417614732142857163 : Rat) / 50000000000000000000), D4 := ((23872375714285711799 : Rat) / 25000000000000000000), LB := ((16285047519554777 : Rat) / 100000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((43754101 : Rat) / 20000000), R := ((182421003 : Rat) / 80000000), D0 := ((182421003 : Rat) / 80000000), D1 := ((7404599 : Rat) / 16000000), D2 := ((7404599 : Rat) / 20000000), D3 := ((23906117232142857163 : Rat) / 50000000000000000000), D4 := ((14616626964285711799 : Rat) / 25000000000000000000), LB := ((526779474183681 : Rat) / 5000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((182421003 : Rat) / 80000000), R := ((74449321 : Rat) / 32000000), D0 := ((74449321 : Rat) / 32000000), D1 := ((81450589 : Rat) / 160000000), D2 := ((22213797 : Rat) / 80000000), D3 := ((19278242857142857163 : Rat) / 50000000000000000000), D4 := ((12302689776785711799 : Rat) / 25000000000000000000), LB := ((3421579719428493 : Rat) / 50000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((74449321 : Rat) / 32000000), R := ((94912801 : Rat) / 40000000), D0 := ((94912801 : Rat) / 40000000), D1 := ((22213797 : Rat) / 40000000), D2 := ((7404599 : Rat) / 32000000), D3 := ((16964305669642857163 : Rat) / 50000000000000000000), D4 := ((11145721183035711799 : Rat) / 25000000000000000000), LB := ((2248321729305977 : Rat) / 200000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((94912801 : Rat) / 40000000), R := ((766707007 : Rat) / 320000000), D0 := ((766707007 : Rat) / 320000000), D1 := ((7404599 : Rat) / 12800000), D2 := ((7404599 : Rat) / 40000000), D3 := ((14650368482142857163 : Rat) / 50000000000000000000), D4 := ((9988752589285711799 : Rat) / 25000000000000000000), LB := ((1517658739965639 : Rat) / 125000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((766707007 : Rat) / 320000000), R := ((1540818613 : Rat) / 640000000), D0 := ((1540818613 : Rat) / 640000000), D1 := ((377634549 : Rat) / 640000000), D2 := ((51832193 : Rat) / 320000000), D3 := ((13493399888392857163 : Rat) / 50000000000000000000), D4 := ((9410268292410711799 : Rat) / 25000000000000000000), LB := ((8112650662546003 : Rat) / 500000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1540818613 : Rat) / 640000000), R := ((387055803 : Rat) / 160000000), D0 := ((387055803 : Rat) / 160000000), D1 := ((96259787 : Rat) / 160000000), D2 := ((96259787 : Rat) / 640000000), D3 := ((12914915591517857163 : Rat) / 50000000000000000000), D4 := ((9121026143973211799 : Rat) / 25000000000000000000), LB := ((409889811524973 : Rat) / 50000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((387055803 : Rat) / 160000000), R := ((1555627811 : Rat) / 640000000), D0 := ((1555627811 : Rat) / 640000000), D1 := ((392443747 : Rat) / 640000000), D2 := ((22213797 : Rat) / 160000000), D3 := ((12336431294642857163 : Rat) / 50000000000000000000), D4 := ((8831783995535711799 : Rat) / 25000000000000000000), LB := ((156096797010747 : Rat) / 125000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1555627811 : Rat) / 640000000), R := ((3118660221 : Rat) / 1280000000), D0 := ((3118660221 : Rat) / 1280000000), D1 := ((792292093 : Rat) / 1280000000), D2 := ((81450589 : Rat) / 640000000), D3 := ((11757946997767857163 : Rat) / 50000000000000000000), D4 := ((8542541847098211799 : Rat) / 25000000000000000000), LB := ((3127518162917689 : Rat) / 500000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3118660221 : Rat) / 1280000000), R := ((156303241 : Rat) / 64000000), D0 := ((156303241 : Rat) / 64000000), D1 := ((199924173 : Rat) / 320000000), D2 := ((155496579 : Rat) / 1280000000), D3 := ((11468704849330357163 : Rat) / 50000000000000000000), D4 := ((8397920772879461799 : Rat) / 25000000000000000000), LB := ((37345716129167927 : Rat) / 10000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((156303241 : Rat) / 64000000), R := ((3133469419 : Rat) / 1280000000), D0 := ((3133469419 : Rat) / 1280000000), D1 := ((807101291 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 64000000), D3 := ((11179462700892857163 : Rat) / 50000000000000000000), D4 := ((8253299698660711799 : Rat) / 25000000000000000000), LB := ((15411228271181299 : Rat) / 10000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3133469419 : Rat) / 1280000000), R := ((6274343437 : Rat) / 2560000000), D0 := ((6274343437 : Rat) / 2560000000), D1 := ((1621607181 : Rat) / 2560000000), D2 := ((140687381 : Rat) / 1280000000), D3 := ((10890220552455357163 : Rat) / 50000000000000000000), D4 := ((8108678624441961799 : Rat) / 25000000000000000000), LB := ((1249798767142589 : Rat) / 250000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6274343437 : Rat) / 2560000000), R := ((1570437009 : Rat) / 640000000), D0 := ((1570437009 : Rat) / 640000000), D1 := ((81450589 : Rat) / 128000000), D2 := ((273970163 : Rat) / 2560000000), D3 := ((10745599478236607163 : Rat) / 50000000000000000000), D4 := ((8036368087332586799 : Rat) / 25000000000000000000), LB := ((4188175081043993 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1570437009 : Rat) / 640000000), R := ((1257830527 : Rat) / 512000000), D0 := ((1257830527 : Rat) / 512000000), D1 := ((1636416379 : Rat) / 2560000000), D2 := ((66641391 : Rat) / 640000000), D3 := ((10600978404017857163 : Rat) / 50000000000000000000), D4 := ((7964057550223211799 : Rat) / 25000000000000000000), LB := ((8675464132832239 : Rat) / 2500000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1257830527 : Rat) / 512000000), R := ((3148278617 : Rat) / 1280000000), D0 := ((3148278617 : Rat) / 1280000000), D1 := ((821910489 : Rat) / 1280000000), D2 := ((51832193 : Rat) / 512000000), D3 := ((10456357329799107163 : Rat) / 50000000000000000000), D4 := ((7891747013113836799 : Rat) / 25000000000000000000), LB := ((28479575571343507 : Rat) / 10000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3148278617 : Rat) / 1280000000), R := ((6303961833 : Rat) / 2560000000), D0 := ((6303961833 : Rat) / 2560000000), D1 := ((1651225577 : Rat) / 2560000000), D2 := ((125878183 : Rat) / 1280000000), D3 := ((10311736255580357163 : Rat) / 50000000000000000000), D4 := ((7819436476004461799 : Rat) / 25000000000000000000), LB := ((23244307507404027 : Rat) / 10000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6303961833 : Rat) / 2560000000), R := ((197230201 : Rat) / 80000000), D0 := ((197230201 : Rat) / 80000000), D1 := ((51832193 : Rat) / 80000000), D2 := ((244351767 : Rat) / 2560000000), D3 := ((10167115181361607163 : Rat) / 50000000000000000000), D4 := ((7747125938895086799 : Rat) / 25000000000000000000), LB := ((380555327069243 : Rat) / 200000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((197230201 : Rat) / 80000000), R := ((6318771031 : Rat) / 2560000000), D0 := ((6318771031 : Rat) / 2560000000), D1 := ((66641391 : Rat) / 102400000), D2 := ((7404599 : Rat) / 80000000), D3 := ((10022494107142857163 : Rat) / 50000000000000000000), D4 := ((7674815401785711799 : Rat) / 25000000000000000000), LB := ((7932117905157521 : Rat) / 5000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6318771031 : Rat) / 2560000000), R := ((632617563 : Rat) / 256000000), D0 := ((632617563 : Rat) / 256000000), D1 := ((836719687 : Rat) / 1280000000), D2 := ((229542569 : Rat) / 2560000000), D3 := ((9877873032924107163 : Rat) / 50000000000000000000), D4 := ((7602504864676336799 : Rat) / 25000000000000000000), LB := ((1379086326311063 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((632617563 : Rat) / 256000000), R := ((6333580229 : Rat) / 2560000000), D0 := ((6333580229 : Rat) / 2560000000), D1 := ((1680843973 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 256000000), D3 := ((9733251958705357163 : Rat) / 50000000000000000000), D4 := ((7530194327566961799 : Rat) / 25000000000000000000), LB := ((1284799998926639 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6333580229 : Rat) / 2560000000), R := ((1585246207 : Rat) / 640000000), D0 := ((1585246207 : Rat) / 640000000), D1 := ((422062143 : Rat) / 640000000), D2 := ((214733371 : Rat) / 2560000000), D3 := ((9588630884486607163 : Rat) / 50000000000000000000), D4 := ((7457883790457586799 : Rat) / 25000000000000000000), LB := ((1634949599341913 : Rat) / 1250000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1585246207 : Rat) / 640000000), R := ((6348389427 : Rat) / 2560000000), D0 := ((6348389427 : Rat) / 2560000000), D1 := ((1695653171 : Rat) / 2560000000), D2 := ((51832193 : Rat) / 640000000), D3 := ((9444009810267857163 : Rat) / 50000000000000000000), D4 := ((7385573253348211799 : Rat) / 25000000000000000000), LB := ((7266833271227513 : Rat) / 5000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6348389427 : Rat) / 2560000000), R := ((3177897013 : Rat) / 1280000000), D0 := ((3177897013 : Rat) / 1280000000), D1 := ((170305777 : Rat) / 256000000), D2 := ((199924173 : Rat) / 2560000000), D3 := ((9299388736049107163 : Rat) / 50000000000000000000), D4 := ((7313262716238836799 : Rat) / 25000000000000000000), LB := ((1726282793455991 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3177897013 : Rat) / 1280000000), R := ((50905589 : Rat) / 20480000), D0 := ((50905589 : Rat) / 20480000), D1 := ((1710462369 : Rat) / 2560000000), D2 := ((96259787 : Rat) / 1280000000), D3 := ((9154767661830357163 : Rat) / 50000000000000000000), D4 := ((7240952179129461799 : Rat) / 25000000000000000000), LB := ((2132494867997381 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((50905589 : Rat) / 20480000), R := ((796325403 : Rat) / 320000000), D0 := ((796325403 : Rat) / 320000000), D1 := ((214733371 : Rat) / 320000000), D2 := ((7404599 : Rat) / 102400000), D3 := ((9010146587611607163 : Rat) / 50000000000000000000), D4 := ((7168641642020086799 : Rat) / 25000000000000000000), LB := ((2678391112978351 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((796325403 : Rat) / 320000000), R := ((6378007823 : Rat) / 2560000000), D0 := ((6378007823 : Rat) / 2560000000), D1 := ((1725271567 : Rat) / 2560000000), D2 := ((22213797 : Rat) / 320000000), D3 := ((8865525513392857163 : Rat) / 50000000000000000000), D4 := ((7096331104910711799 : Rat) / 25000000000000000000), LB := ((33710530027651897 : Rat) / 10000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((6378007823 : Rat) / 2560000000), R := ((3192706211 : Rat) / 1280000000), D0 := ((3192706211 : Rat) / 1280000000), D1 := ((866338083 : Rat) / 1280000000), D2 := ((170305777 : Rat) / 2560000000), D3 := ((8720904439174107163 : Rat) / 50000000000000000000), D4 := ((7024020567801336799 : Rat) / 25000000000000000000), LB := ((8436732164014249 : Rat) / 2000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3192706211 : Rat) / 1280000000), R := ((320011081 : Rat) / 128000000), D0 := ((320011081 : Rat) / 128000000), D1 := ((436871341 : Rat) / 640000000), D2 := ((81450589 : Rat) / 1280000000), D3 := ((8576283364955357163 : Rat) / 50000000000000000000), D4 := ((6951710030691961799 : Rat) / 25000000000000000000), LB := ((2230729223257899 : Rat) / 10000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((320011081 : Rat) / 128000000), R := ((3207515409 : Rat) / 1280000000), D0 := ((3207515409 : Rat) / 1280000000), D1 := ((881147281 : Rat) / 1280000000), D2 := ((7404599 : Rat) / 128000000), D3 := ((8287041216517857163 : Rat) / 50000000000000000000), D4 := ((6807088956473211799 : Rat) / 25000000000000000000), LB := ((70279673832159 : Rat) / 25000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((3207515409 : Rat) / 1280000000), R := ((401865001 : Rat) / 160000000), D0 := ((401865001 : Rat) / 160000000), D1 := ((22213797 : Rat) / 32000000), D2 := ((66641391 : Rat) / 1280000000), D3 := ((7997799068080357163 : Rat) / 50000000000000000000), D4 := ((6662467882254461799 : Rat) / 25000000000000000000), LB := ((6190444320096633 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((401865001 : Rat) / 160000000), R := ((1614864603 : Rat) / 640000000), D0 := ((1614864603 : Rat) / 640000000), D1 := ((451680539 : Rat) / 640000000), D2 := ((7404599 : Rat) / 160000000), D3 := ((7708556919642857163 : Rat) / 50000000000000000000), D4 := ((6517846808035711799 : Rat) / 25000000000000000000), LB := ((1834891676999531 : Rat) / 2500000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1614864603 : Rat) / 640000000), R := ((811134601 : Rat) / 320000000), D0 := ((811134601 : Rat) / 320000000), D1 := ((229542569 : Rat) / 320000000), D2 := ((22213797 : Rat) / 640000000), D3 := ((7130072622767857163 : Rat) / 50000000000000000000), D4 := ((6228604659598211799 : Rat) / 25000000000000000000), LB := ((64968386368187 : Rat) / 5000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((811134601 : Rat) / 320000000), R := ((511587 : Rat) / 200000), D0 := ((511587 : Rat) / 200000), D1 := ((7404599 : Rat) / 10000000), D2 := ((7404599 : Rat) / 320000000), D3 := ((6551588325892857163 : Rat) / 50000000000000000000), D4 := ((5939362511160711799 : Rat) / 25000000000000000000), LB := ((13585920903425919 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((511587 : Rat) / 200000), R := ((516981619732142857163 : Rat) / 200000000000000000000), D0 := ((516981619732142857163 : Rat) / 200000000000000000000), D1 := ((153486599732142857163 : Rat) / 200000000000000000000), D2 := ((5394619732142857163 : Rat) / 200000000000000000000), D3 := ((5394619732142857163 : Rat) / 50000000000000000000), D4 := ((5360878214285711799 : Rat) / 25000000000000000000), LB := ((12967778275668751 : Rat) / 2000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((516981619732142857163 : Rat) / 200000000000000000000), R := ((1039357859196428571489 : Rat) / 400000000000000000000), D0 := ((1039357859196428571489 : Rat) / 400000000000000000000), D1 := ((312367819196428571489 : Rat) / 400000000000000000000), D2 := ((16183859196428571489 : Rat) / 400000000000000000000), D3 := ((16183859196428571489 : Rat) / 200000000000000000000), D4 := ((37492405982142837229 : Rat) / 200000000000000000000), LB := ((345512871183239 : Rat) / 12500000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1039357859196428571489 : Rat) / 400000000000000000000), R := ((261188119732142857163 : Rat) / 100000000000000000000), D0 := ((261188119732142857163 : Rat) / 100000000000000000000), D1 := ((79440609732142857163 : Rat) / 100000000000000000000), D2 := ((5394619732142857163 : Rat) / 100000000000000000000), D3 := ((5394619732142857163 : Rat) / 80000000000000000000), D4 := ((13918038446428563459 : Rat) / 80000000000000000000), LB := ((30741396497618423 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((261188119732142857163 : Rat) / 100000000000000000000), R := ((527770859196428571489 : Rat) / 200000000000000000000), D0 := ((527770859196428571489 : Rat) / 200000000000000000000), D1 := ((164275839196428571489 : Rat) / 200000000000000000000), D2 := ((16183859196428571489 : Rat) / 200000000000000000000), D3 := ((5394619732142857163 : Rat) / 100000000000000000000), D4 := ((16048893124999990033 : Rat) / 100000000000000000000), LB := ((3062666434601291 : Rat) / 200000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((527770859196428571489 : Rat) / 200000000000000000000), R := ((133291369732142857163 : Rat) / 50000000000000000000), D0 := ((133291369732142857163 : Rat) / 50000000000000000000), D1 := ((42417614732142857163 : Rat) / 50000000000000000000), D2 := ((5394619732142857163 : Rat) / 50000000000000000000), D3 := ((5394619732142857163 : Rat) / 200000000000000000000), D4 := ((26703166517857122903 : Rat) / 200000000000000000000), LB := ((1816882204390049 : Rat) / 20000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((133291369732142857163 : Rat) / 50000000000000000000), R := ((537326765446428571639 : Rat) / 200000000000000000000), D0 := ((537326765446428571639 : Rat) / 200000000000000000000), D1 := ((173831745446428571639 : Rat) / 200000000000000000000), D2 := ((25739765446428571639 : Rat) / 200000000000000000000), D3 := ((4161286517857142987 : Rat) / 200000000000000000000), D4 := ((1065427339285713287 : Rat) / 10000000000000000000), LB := ((12258527124841123 : Rat) / 100000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((537326765446428571639 : Rat) / 200000000000000000000), R := ((270744025982142857313 : Rat) / 100000000000000000000), D0 := ((270744025982142857313 : Rat) / 100000000000000000000), D1 := ((88996515982142857313 : Rat) / 100000000000000000000), D2 := ((14950525982142857313 : Rat) / 100000000000000000000), D3 := ((4161286517857142987 : Rat) / 100000000000000000000), D4 := ((17147260267857122753 : Rat) / 200000000000000000000), LB := ((1641107134894397 : Rat) / 125000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((270744025982142857313 : Rat) / 100000000000000000000), R := ((1087137390446428572239 : Rat) / 400000000000000000000), D0 := ((1087137390446428572239 : Rat) / 400000000000000000000), D1 := ((360147350446428572239 : Rat) / 400000000000000000000), D2 := ((63963390446428572239 : Rat) / 400000000000000000000), D3 := ((4161286517857142987 : Rat) / 80000000000000000000), D4 := ((6492986874999989883 : Rat) / 100000000000000000000), LB := ((480896058776617 : Rat) / 625000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1087137390446428572239 : Rat) / 400000000000000000000), R := ((435687213482142857493 : Rat) / 160000000000000000000), D0 := ((435687213482142857493 : Rat) / 160000000000000000000), D1 := ((144891197482142857493 : Rat) / 160000000000000000000), D2 := ((26417613482142857493 : Rat) / 160000000000000000000), D3 := ((45774151696428572857 : Rat) / 800000000000000000000), D4 := ((4362132196428563309 : Rat) / 80000000000000000000), LB := ((2583599435386219 : Rat) / 1250000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((435687213482142857493 : Rat) / 160000000000000000000), R := ((4361033421339285717917 : Rat) / 1600000000000000000000), D0 := ((4361033421339285717917 : Rat) / 1600000000000000000000), D1 := ((1453073261339285717917 : Rat) / 1600000000000000000000), D2 := ((268337421339285717917 : Rat) / 1600000000000000000000), D3 := ((95709589910714288701 : Rat) / 1600000000000000000000), D4 := ((39460035446428490103 : Rat) / 800000000000000000000), LB := ((5013594506798169 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4361033421339285717917 : Rat) / 1600000000000000000000), R := ((545649338482142857613 : Rat) / 200000000000000000000), D0 := ((545649338482142857613 : Rat) / 200000000000000000000), D1 := ((182154318482142857613 : Rat) / 200000000000000000000), D2 := ((34062338482142857613 : Rat) / 200000000000000000000), D3 := ((12483859553571428961 : Rat) / 200000000000000000000), D4 := ((74758784374999837219 : Rat) / 1600000000000000000000), LB := ((4722230373730707 : Rat) / 2500000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((545649338482142857613 : Rat) / 200000000000000000000), R := ((1746910140446428572959 : Rat) / 640000000000000000000), D0 := ((1746910140446428572959 : Rat) / 640000000000000000000), D1 := ((583726076446428572959 : Rat) / 640000000000000000000), D2 := ((109831740446428572959 : Rat) / 640000000000000000000), D3 := ((203903039375000006363 : Rat) / 3200000000000000000000), D4 := ((8824687232142836779 : Rat) / 200000000000000000000), LB := ((460640770771481 : Rat) / 100000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1746910140446428572959 : Rat) / 640000000000000000000), R := ((4369355994375000003891 : Rat) / 1600000000000000000000), D0 := ((4369355994375000003891 : Rat) / 1600000000000000000000), D1 := ((1461395834375000003891 : Rat) / 1600000000000000000000), D2 := ((276659994375000003891 : Rat) / 1600000000000000000000), D3 := ((4161286517857142987 : Rat) / 64000000000000000000), D4 := ((137033709196428245477 : Rat) / 3200000000000000000000), LB := ((4509920543913637 : Rat) / 1250000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4369355994375000003891 : Rat) / 1600000000000000000000), R := ((8742873275267857150769 : Rat) / 3200000000000000000000), D0 := ((8742873275267857150769 : Rat) / 3200000000000000000000), D1 := ((2926952955267857150769 : Rat) / 3200000000000000000000), D2 := ((557481275267857150769 : Rat) / 3200000000000000000000), D3 := ((212225612410714292337 : Rat) / 3200000000000000000000), D4 := ((13287242267857110249 : Rat) / 320000000000000000000), LB := ((28013654031418533 : Rat) / 10000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8742873275267857150769 : Rat) / 3200000000000000000000), R := ((2186758640446428573439 : Rat) / 800000000000000000000), D0 := ((2186758640446428573439 : Rat) / 800000000000000000000), D1 := ((732778560446428573439 : Rat) / 800000000000000000000), D2 := ((140410640446428573439 : Rat) / 800000000000000000000), D3 := ((54096724732142858831 : Rat) / 800000000000000000000), D4 := ((128711136160713959503 : Rat) / 3200000000000000000000), LB := ((342571059845009 : Rat) / 156250000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2186758640446428573439 : Rat) / 800000000000000000000), R := ((8751195848303571436743 : Rat) / 3200000000000000000000), D0 := ((8751195848303571436743 : Rat) / 3200000000000000000000), D1 := ((2935275528303571436743 : Rat) / 3200000000000000000000), D2 := ((565803848303571436743 : Rat) / 3200000000000000000000), D3 := ((220548185446428578311 : Rat) / 3200000000000000000000), D4 := ((31137462410714204129 : Rat) / 800000000000000000000), LB := ((1117436645109611 : Rat) / 625000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8751195848303571436743 : Rat) / 3200000000000000000000), R := ((875535713482142857973 : Rat) / 320000000000000000000), D0 := ((875535713482142857973 : Rat) / 320000000000000000000), D1 := ((293943681482142857973 : Rat) / 320000000000000000000), D2 := ((56996513482142857973 : Rat) / 320000000000000000000), D3 := ((112354735982142860649 : Rat) / 1600000000000000000000), D4 := ((120388563124999673529 : Rat) / 3200000000000000000000), LB := ((15954238592331693 : Rat) / 10000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((875535713482142857973 : Rat) / 320000000000000000000), R := ((8759518421339285722717 : Rat) / 3200000000000000000000), D0 := ((8759518421339285722717 : Rat) / 3200000000000000000000), D1 := ((2943598101339285722717 : Rat) / 3200000000000000000000), D2 := ((574126421339285722717 : Rat) / 3200000000000000000000), D3 := ((45774151696428572857 : Rat) / 640000000000000000000), D4 := ((58113638303571265271 : Rat) / 1600000000000000000000), LB := ((2029886570470707 : Rat) / 1250000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8759518421339285722717 : Rat) / 3200000000000000000000), R := ((1095459963482142858213 : Rat) / 400000000000000000000), D0 := ((1095459963482142858213 : Rat) / 400000000000000000000), D1 := ((368469923482142858213 : Rat) / 400000000000000000000), D2 := ((72285963482142858213 : Rat) / 400000000000000000000), D3 := ((29129005625000000909 : Rat) / 400000000000000000000), D4 := ((22413198017857077511 : Rat) / 640000000000000000000), LB := ((9417643474222137 : Rat) / 5000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1095459963482142858213 : Rat) / 400000000000000000000), R := ((8767840994375000008691 : Rat) / 3200000000000000000000), D0 := ((8767840994375000008691 : Rat) / 3200000000000000000000), D1 := ((2951920674375000008691 : Rat) / 3200000000000000000000), D2 := ((582448994375000008691 : Rat) / 3200000000000000000000), D3 := ((237193331517857150259 : Rat) / 3200000000000000000000), D4 := ((13488087946428530571 : Rat) / 400000000000000000000), LB := ((1192961851261637 : Rat) / 500000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((8767840994375000008691 : Rat) / 3200000000000000000000), R := ((4386001140446428575839 : Rat) / 1600000000000000000000), D0 := ((4386001140446428575839 : Rat) / 1600000000000000000000), D1 := ((1478040980446428575839 : Rat) / 1600000000000000000000), D2 := ((293305140446428575839 : Rat) / 1600000000000000000000), D3 := ((120677309017857146623 : Rat) / 1600000000000000000000), D4 := ((103743417053571101581 : Rat) / 3200000000000000000000), LB := ((15722060573718777 : Rat) / 5000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4386001140446428575839 : Rat) / 1600000000000000000000), R := ((1755232713482142858933 : Rat) / 640000000000000000000), D0 := ((1755232713482142858933 : Rat) / 640000000000000000000), D1 := ((592048649482142858933 : Rat) / 640000000000000000000), D2 := ((118154313482142858933 : Rat) / 640000000000000000000), D3 := ((245515904553571436233 : Rat) / 3200000000000000000000), D4 := ((49791065267856979297 : Rat) / 1600000000000000000000), LB := ((4174241438708481 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((1755232713482142858933 : Rat) / 640000000000000000000), R := ((2195081213482142859413 : Rat) / 800000000000000000000), D0 := ((2195081213482142859413 : Rat) / 800000000000000000000), D1 := ((741101133482142859413 : Rat) / 800000000000000000000), D2 := ((148733213482142859413 : Rat) / 800000000000000000000), D3 := ((12483859553571428961 : Rat) / 160000000000000000000), D4 := ((95420844017856815607 : Rat) / 3200000000000000000000), LB := ((5492898182783257 : Rat) / 1000000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((2195081213482142859413 : Rat) / 800000000000000000000), R := ((4394323713482142861813 : Rat) / 1600000000000000000000), D0 := ((4394323713482142861813 : Rat) / 1600000000000000000000), D1 := ((1486363553482142861813 : Rat) / 1600000000000000000000), D2 := ((301627713482142861813 : Rat) / 1600000000000000000000), D3 := ((128999882053571432597 : Rat) / 1600000000000000000000), D4 := ((4562977874999983631 : Rat) / 160000000000000000000), LB := ((1313390746101123 : Rat) / 500000000000000000) },
  { w1 := ((9063165441676297 : Rat) / 10000000000000000), w2 := ((2377343432279637 : Rat) / 50000000000000000), w3 := ((1489142296114339 : Rat) / 10000000000000000), w4 := ((1382757398318953 : Rat) / 10000000000000000), s1 := ((18174751 : Rat) / 10000000), s2 := ((511587 : Rat) / 200000), s3 := ((133291369732142857163 : Rat) / 50000000000000000000), s4 := ((69309253214285711799 : Rat) / 25000000000000000000), L := ((4394323713482142861813 : Rat) / 1600000000000000000000), R := ((2749053125000000003 : Rat) / 1000000000000000000), D0 := ((2749053125000000003 : Rat) / 1000000000000000000), D1 := ((931578025000000003 : Rat) / 1000000000000000000), D2 := ((191118125000000003 : Rat) / 1000000000000000000), D3 := ((4161286517857142987 : Rat) / 50000000000000000000), D4 := ((41468492232142693323 : Rat) / 1600000000000000000000), LB := ((2795990059550979 : Rat) / 400000000000000000) }
]

def block350RightChunk000L : Rat := ((87442881696428571579 : Rat) / 50000000000000000000)
def block350RightChunk000R : Rat := ((2749053125000000003 : Rat) / 1000000000000000000)

def block350RightChunk000Certificate : Bool :=
  allBoxesValid block350RightChunk000 &&
  coversFromBool block350RightChunk000 block350RightChunk000L block350RightChunk000R

theorem block350RightChunk000Certificate_eq_true :
    block350RightChunk000Certificate = true := by
  native_decide

def block350RightChainCertificate : Bool :=
  decide (
    block350RightL = ((87442881696428571579 : Rat) / 50000000000000000000) /\
    ((2749053125000000003 : Rat) / 1000000000000000000) = block350RightR)

theorem block350RightChainCertificate_eq_true :
    block350RightChainCertificate = true := by
  native_decide

def block350LeftBoxCount : Nat := boxCount block350LeftBoxes
def block350RightBoxCount : Nat := 59

def block350_rational_certificate : Prop :=
    block350LeftCertificate = true /\
    block350RightChainCertificate = true /\
    block350RightChunk000Certificate = true

theorem block350_rational_certificate_proof :
    block350_rational_certificate := by
  exact ⟨block350LeftCertificate_eq_true, block350RightChainCertificate_eq_true, block350RightChunk000Certificate_eq_true⟩

end Block350
end M1817475
end Erdos1038Lean


set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block350

open Set

def block350W1 : Rat := ((9063165441676297 : Rat) / 10000000000000000)
def block350W2 : Rat := ((2377343432279637 : Rat) / 50000000000000000)
def block350W3 : Rat := ((1489142296114339 : Rat) / 10000000000000000)
def block350W4 : Rat := ((1382757398318953 : Rat) / 10000000000000000)
def block350S1 : Rat := ((18174751 : Rat) / 10000000)
def block350S2 : Rat := ((511587 : Rat) / 200000)
def block350S3 : Rat := ((133291369732142857163 : Rat) / 50000000000000000000)
def block350S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block350V (y : ℝ) : ℝ :=
  ratPotential block350W1 block350W2 block350W3 block350W4 block350S1 block350S2 block350S3 block350S4 y

def block350LeftParamsCertificate : Bool :=
  allBoxesSameParams block350LeftBoxes block350W1 block350W2 block350W3 block350W4 block350S1 block350S2 block350S3 block350S4

theorem block350LeftParamsCertificate_eq_true :
    block350LeftParamsCertificate = true := by
  native_decide

theorem block350_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block350LeftL : ℝ) (block350LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block350S1 : ℝ))
    (hy2ne : y ≠ (block350S2 : ℝ))
    (hy3ne : y ≠ (block350S3 : ℝ))
    (hy4ne : y ≠ (block350S4 : ℝ)) :
    0 < block350V y := by
  have hcert := block350LeftCertificate_eq_true
  unfold block350LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block350LeftBoxes) (lo := block350LeftL) (hi := block350LeftR)
    (w1 := block350W1) (w2 := block350W2) (w3 := block350W3) (w4 := block350W4)
    (s1 := block350S1) (s2 := block350S2) (s3 := block350S3) (s4 := block350S4)
    hboxes hcover block350LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block350RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block350RightChunk000 block350W1 block350W2 block350W3 block350W4 block350S1 block350S2 block350S3 block350S4

theorem block350RightChunk000ParamsCertificate_eq_true :
    block350RightChunk000ParamsCertificate = true := by
  native_decide

theorem block350_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block350RightChunk000L : ℝ) (block350RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block350S1 : ℝ))
    (hy2ne : y ≠ (block350S2 : ℝ))
    (hy3ne : y ≠ (block350S3 : ℝ))
    (hy4ne : y ≠ (block350S4 : ℝ)) :
    0 < block350V y := by
  have hcert := block350RightChunk000Certificate_eq_true
  unfold block350RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block350RightChunk000) (lo := block350RightChunk000L) (hi := block350RightChunk000R)
    (w1 := block350W1) (w2 := block350W2) (w3 := block350W3) (w4 := block350W4)
    (s1 := block350S1) (s2 := block350S2) (s3 := block350S3) (s4 := block350S4)
    hboxes hcover block350RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block350_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block350RightL : ℝ) (block350RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block350S1 : ℝ))
    (hy2ne : y ≠ (block350S2 : ℝ))
    (hy3ne : y ≠ (block350S3 : ℝ))
    (hy4ne : y ≠ (block350S4 : ℝ)) :
    0 < block350V y := by
  have hL : (block350RightChunk000L : ℝ) = (block350RightL : ℝ) := by
    norm_num [block350RightChunk000L, block350RightL]
  have hR : (block350RightChunk000R : ℝ) = (block350RightR : ℝ) := by
    norm_num [block350RightChunk000R, block350RightR]
  have hyc : y ∈ Icc (block350RightChunk000L : ℝ) (block350RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block350_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block350_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block350LeftL : ℝ) (block350LeftR : ℝ) →
    y ≠ 0 → y ≠ (block350S1 : ℝ) → y ≠ (block350S2 : ℝ) →
    y ≠ (block350S3 : ℝ) → y ≠ (block350S4 : ℝ) → 0 < block350V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block350RightL : ℝ) (block350RightR : ℝ) →
    y ≠ 0 → y ≠ (block350S1 : ℝ) → y ≠ (block350S2 : ℝ) →
    y ≠ (block350S3 : ℝ) → y ≠ (block350S4 : ℝ) → 0 < block350V y)

theorem block350_reallog_certificate_proof :
    block350_reallog_certificate := by
  exact ⟨block350_left_V_pos, block350_right_V_pos⟩

end Block350
end M1817475
end Erdos1038Lean

#check Erdos1038Lean.M1817475.Block350.block350V
#check Erdos1038Lean.M1817475.Block350.block350_left_V_pos
#check Erdos1038Lean.M1817475.Block350.block350_right_V_pos
#check Erdos1038Lean.M1817475.Block350.block350_reallog_certificate_proof
